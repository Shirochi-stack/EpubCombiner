"""
EPUB Combiner — Merge multiple EPUB files into one.

Features:
  • Add EPUBs via button or drag-and-drop onto the window
  • Reorder with drag-and-drop, Up/Down buttons, or Sort (A-Z / Z-A)
  • All HTML/XHTML content is renamed sequentially (1.xhtml, 2.xhtml, …)
  • A fresh content.opf, toc.ncx, and container.xml are generated
  • Images and stylesheets are collected and deduplicated
"""

import os
import re
import sys
import uuid
import shutil
import zipfile
import tempfile
from pathlib import Path
from collections import OrderedDict
from typing import Optional
from urllib.parse import unquote
from xml.etree import ElementTree as ET


def _natural_sort_key(name: str):
    """Sort key that handles embedded numbers naturally.
    e.g. 'Vol 2.epub' < 'Vol 10.epub'"""
    parts = re.split(r'(\d+)', name.lower())
    return [int(p) if p.isdigit() else p for p in parts]

# ---------------------------------------------------------------------------
# PySide6 GUI
# ---------------------------------------------------------------------------
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QPushButton, QLabel, QFileDialog, QMessageBox, QTreeWidget,
    QTreeWidgetItem, QAbstractItemView, QHeaderView, QProgressBar,
    QLineEdit, QGroupBox, QStyle,
)
from PySide6.QtCore import Qt, QMimeData, Signal
from PySide6.QtGui import QDragEnterEvent, QDropEvent


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

XHTML_EXTENSIONS = {'.xhtml', '.html', '.htm', '.xml'}
IMAGE_EXTENSIONS = {'.png', '.jpg', '.jpeg', '.gif', '.svg', '.webp', '.bmp', '.tif', '.tiff'}
STYLE_EXTENSIONS = {'.css'}
FONT_EXTENSIONS  = {'.ttf', '.otf', '.woff', '.woff2'}

MIMETYPE_MAP = {
    '.xhtml': 'application/xhtml+xml',
    '.html':  'application/xhtml+xml',
    '.htm':   'application/xhtml+xml',
    '.xml':   'application/xhtml+xml',
    '.css':   'text/css',
    '.png':   'image/png',
    '.jpg':   'image/jpeg',
    '.jpeg':  'image/jpeg',
    '.gif':   'image/gif',
    '.svg':   'image/svg+xml',
    '.webp':  'image/webp',
    '.bmp':   'image/bmp',
    '.tif':   'image/tiff',
    '.tiff':  'image/tiff',
    '.ttf':   'font/ttf',
    '.otf':   'font/otf',
    '.woff':  'font/woff',
    '.woff2': 'font/woff2',
    '.ncx':   'application/x-dtbncx+xml',
}


def _media_type(filename: str) -> str:
    ext = Path(filename).suffix.lower()
    return MIMETYPE_MAP.get(ext, 'application/octet-stream')


def _posix_norm(path: str) -> str:
    """Normalize a ZIP/EPUB internal path (always uses '/')."""
    path = (path or '').replace('\\', '/')
    # Strip leading '/' (EPUB hrefs are relative; some books still use leading slash)
    if path.startswith('/'):
        path = path.lstrip('/')
    parts: list[str] = []
    for p in path.split('/'):
        if p in ('', '.'):
            continue
        if p == '..':
            if parts:
                parts.pop()
            continue
        parts.append(p)
    return '/'.join(parts)


def _norm_key(path: str) -> str:
    """Canonical key for matching hrefs to ZIP entries (case-insensitive + url-decoded)."""
    return _posix_norm(unquote((path or '').replace('\\', '/'))).lower()


def _split_ref_suffix(ref: str) -> tuple[str, str]:
    """Split a URL-ish reference into (base, suffix), preserving ?query/#frag."""
    if not ref:
        return '', ''
    q = ref.find('?')
    h = ref.find('#')
    cut = -1
    if q != -1 and h != -1:
        cut = min(q, h)
    elif q != -1:
        cut = q
    elif h != -1:
        cut = h
    if cut == -1:
        return ref, ''
    return ref[:cut], ref[cut:]


class _AssetMapper:
    """Per-EPUB map from original asset paths to combined-EPUB relative hrefs."""

    def __init__(self):
        self._map: dict[str, str] = {}
        self._basename_targets: dict[str, set[str]] = {}
        self._basename_map: dict[str, str] = {}

    def add(self, original_zip_path: str, new_href: str):
        key = _norm_key(original_zip_path)
        if key:
            self._map[key] = new_href

        base = Path((original_zip_path or '').replace('\\', '/')).name
        bkey = _norm_key(base)
        if bkey:
            self._basename_targets.setdefault(bkey, set()).add(new_href)

    def finalize(self):
        # Only allow basename-only matching when it is unambiguous within this EPUB.
        self._basename_map = {
            b: next(iter(targets))
            for b, targets in self._basename_targets.items()
            if len(targets) == 1
        }

    def lookup(self, old_ref: str, content_path: str) -> Optional[str]:
        if not old_ref:
            return None

        base, suffix = _split_ref_suffix(old_ref)
        base = (base or '').strip()
        if not base:
            return None

        # Skip absolute URLs and non-file refs
        if base.startswith(('http://', 'https://', 'mailto:', 'tel:', 'data:')):
            return None
        if base.startswith('#'):
            return None

        base = base.replace('\\', '/')
        content_dir = _posix_norm(str(Path(content_path).parent).replace('\\', '/'))

        candidates: list[str] = []
        # Direct
        candidates.append(_norm_key(base))
        # Resolved relative to the content file's directory
        if content_dir and not base.startswith('/'):
            candidates.append(_norm_key(f"{content_dir}/{base}"))
        elif not content_dir and not base.startswith('/'):
            candidates.append(_norm_key(base))

        # Try exact/path-based matches first
        for c in candidates:
            if c in self._map:
                return self._map[c] + suffix

        # Finally, try basename-only when unique
        bkey = _norm_key(Path(base).name)
        if bkey in self._basename_map:
            return self._basename_map[bkey] + suffix

        return None


def _is_content_file(name: str) -> bool:
    return Path(name).suffix.lower() in XHTML_EXTENSIONS


def _is_image_file(name: str) -> bool:
    return Path(name).suffix.lower() in IMAGE_EXTENSIONS


def _is_style_file(name: str) -> bool:
    return Path(name).suffix.lower() in STYLE_EXTENSIONS


def _is_font_file(name: str) -> bool:
    return Path(name).suffix.lower() in FONT_EXTENSIONS


def _get_spine_order(zf: zipfile.ZipFile) -> list[str]:
    """Parse content.opf inside an EPUB and return the spine-ordered list of
    content file paths (relative to the OPF directory)."""
    # Find the OPF file via META-INF/container.xml
    try:
        container_xml = zf.read('META-INF/container.xml')
        root = ET.fromstring(container_xml)
        ns = {'c': 'urn:oasis:names:tc:opendocument:xmlns:container'}
        rootfile_el = root.find('.//c:rootfile', ns)
        if rootfile_el is not None:
            opf_path = rootfile_el.attrib.get('full-path', '')
        else:
            opf_path = ''
    except Exception:
        opf_path = ''

    # Fallback: search for .opf file
    if not opf_path:
        for name in zf.namelist():
            if name.endswith('.opf'):
                opf_path = name
                break

    if not opf_path:
        return []

    opf_dir = str(Path(opf_path).parent)
    if opf_dir == '.':
        opf_dir = ''

    try:
        opf_xml = zf.read(opf_path)
        tree = ET.fromstring(opf_xml)
    except Exception:
        return []

    ns_opf = {'opf': 'http://www.idpf.org/2007/opf'}

    # Build id -> href map from manifest
    id_to_href = {}
    manifest = tree.find('.//opf:manifest', ns_opf)
    if manifest is None:
        manifest = tree.find('.//{http://www.idpf.org/2007/opf}manifest')
    if manifest is not None:
        for item in manifest:
            item_id = item.attrib.get('id', '')
            href = item.attrib.get('href', '')
            if item_id and href:
                id_to_href[item_id] = href

    # Read spine order
    spine = tree.find('.//opf:spine', ns_opf)
    if spine is None:
        spine = tree.find('.//{http://www.idpf.org/2007/opf}spine')

    ordered = []
    if spine is not None:
        for itemref in spine:
            idref = itemref.attrib.get('idref', '')
            href = id_to_href.get(idref, '')
            if href:
                if opf_dir:
                    full = f"{opf_dir}/{href}"
                else:
                    full = href
                ordered.append(full)

    return ordered


# ---------------------------------------------------------------------------
# Core: Combine EPUBs
# ---------------------------------------------------------------------------

def combine_epubs(epub_paths: list[str], output_path: str,
                  title: str = "Combined EPUB",
                  progress_callback=None) -> str:
    """Combine multiple EPUBs into *output_path*.

    Returns the absolute path of the created file.
    """
    tmp_dir = tempfile.mkdtemp(prefix="epub_combine_")

    try:
        # Directories inside the new EPUB
        text_dir = os.path.join(tmp_dir, "OEBPS", "Text")
        image_dir = os.path.join(tmp_dir, "OEBPS", "Images")
        style_dir = os.path.join(tmp_dir, "OEBPS", "Styles")
        font_dir = os.path.join(tmp_dir, "OEBPS", "Fonts")
        meta_dir = os.path.join(tmp_dir, "META-INF")
        for d in (text_dir, image_dir, style_dir, font_dir, meta_dir):
            os.makedirs(d, exist_ok=True)

        # Counters
        html_counter = 0
        image_names_used: dict[str, str] = {}   # original hash -> new name
        style_names_used: dict[str, str] = {}
        font_names_used: dict[str, str] = {}
        manifest_items: list[dict] = []          # {id, href, media-type}
        spine_ids: list[str] = []

        total_epubs = len(epub_paths)

        for epub_idx, epub_path in enumerate(epub_paths):
            if progress_callback:
                progress_callback(int((epub_idx / total_epubs) * 100),
                                  f"Processing {Path(epub_path).name}…")

            if not zipfile.is_zipfile(epub_path):
                continue

            with zipfile.ZipFile(epub_path, 'r') as zf:
                # Determine spine order for this EPUB
                spine_order = _get_spine_order(zf)

                # Collect all content files; prefer spine order, append leftovers
                all_content = [
                    n for n in zf.namelist()
                    if _is_content_file(n)
                    and not n.lower().endswith('toc.ncx')
                ]

                ordered_content: list[str] = []
                remaining = set(all_content)
                for sp in spine_order:
                    # Try to match spine entries to actual zip entries
                    for candidate in list(remaining):
                        if candidate == sp or candidate.replace('\\', '/') == sp.replace('\\', '/'):
                            ordered_content.append(candidate)
                            remaining.discard(candidate)
                            break
                # Append anything not in spine (alphabetically)
                for leftover in sorted(remaining):
                    ordered_content.append(leftover)

                # Track old asset paths -> new hrefs for rewriting (per input EPUB)
                mapper = _AssetMapper()

                # --- Collect images ---
                for name in zf.namelist():
                    if _is_image_file(name):
                        data = zf.read(name)
                        # Deduplicate by content hash (across all input EPUBs)
                        import hashlib
                        h = hashlib.md5(data).hexdigest()
                        if h in image_names_used:
                            new_name = image_names_used[h]
                        else:
                            ext = Path(name).suffix.lower()
                            new_name = f"img_{len(image_names_used) + 1}{ext}"
                            image_names_used[h] = new_name
                            with open(os.path.join(image_dir, new_name), 'wb') as f:
                                f.write(data)
                            manifest_items.append({
                                'id': f"img_{len(image_names_used)}",
                                'href': f"Images/{new_name}",
                                'media-type': _media_type(new_name),
                            })
                        mapper.add(name, f"../Images/{new_name}")

                # --- Collect fonts ---
                for name in zf.namelist():
                    if _is_font_file(name):
                        data = zf.read(name)
                        import hashlib
                        h = hashlib.md5(data).hexdigest()
                        if h in font_names_used:
                            new_name = font_names_used[h]
                        else:
                            ext = Path(name).suffix.lower()
                            new_name = f"font_{len(font_names_used) + 1}{ext}"
                            font_names_used[h] = new_name
                            with open(os.path.join(font_dir, new_name), 'wb') as f:
                                f.write(data)
                            manifest_items.append({
                                'id': f"font_{len(font_names_used)}",
                                'href': f"Fonts/{new_name}",
                                'media-type': _media_type(new_name),
                            })
                        mapper.add(name, f"../Fonts/{new_name}")

                # Enable unambiguous basename matching for images/fonts before rewriting CSS.
                mapper.finalize()

                # --- Collect stylesheets (rewrite their internal url(...) refs first) ---
                for name in zf.namelist():
                    if _is_style_file(name):
                        raw = zf.read(name)
                        css_text = raw.decode('utf-8', errors='replace')
                        css_text = _rewrite_css_refs(css_text, mapper, name)
                        data = css_text.encode('utf-8')

                        import hashlib
                        h = hashlib.md5(data).hexdigest()
                        if h in style_names_used:
                            new_name = style_names_used[h]
                        else:
                            new_name = f"style_{len(style_names_used) + 1}.css"
                            style_names_used[h] = new_name
                            with open(os.path.join(style_dir, new_name), 'wb') as f:
                                f.write(data)
                            manifest_items.append({
                                'id': f"css_{len(style_names_used)}",
                                'href': f"Styles/{new_name}",
                                'media-type': 'text/css',
                            })
                        mapper.add(name, f"../Styles/{new_name}")


                # Pre-compute the new filenames for this EPUB's content files so that
                # intra-book links (e.g. a table-of-contents page with <a href="...">)
                # can be rewritten correctly.
                start_num = html_counter
                content_new_name: dict[str, str] = {}
                for i, content_name in enumerate(ordered_content, 1):
                    num = start_num + i
                    content_new_name[content_name] = f"{num}.xhtml"

                # Add content-file mappings to the mapper (so href= links get rewritten)
                for old_path, new_file in content_new_name.items():
                    mapper.add(old_path, f"../Text/{new_file}")

                mapper.finalize()

                # --- Process content files ---
                for i, content_name in enumerate(ordered_content, 1):
                    num = start_num + i
                    new_filename = content_new_name[content_name]
                    item_id = f"chapter_{num}"

                    try:
                        raw = zf.read(content_name)
                        text = raw.decode('utf-8', errors='replace')
                    except Exception:
                        continue

                    # Rewrite asset + content references
                    text = _rewrite_asset_refs(text, mapper, content_name)

                    out_path = os.path.join(text_dir, new_filename)
                    with open(out_path, 'w', encoding='utf-8') as f:
                        f.write(text)

                    manifest_items.append({
                        'id': item_id,
                        'href': f"Text/{new_filename}",
                        'media-type': 'application/xhtml+xml',
                    })
                    spine_ids.append(item_id)

                html_counter = start_num + len(ordered_content)

        if progress_callback:
            progress_callback(90, "Writing EPUB package…")

        # --- Write EPUB3 navigation document (nav.xhtml) ---
        # Many readers use this for the clickable table of contents.
        nav_xhtml = _build_nav_xhtml(title, html_counter)
        with open(os.path.join(text_dir, "nav.xhtml"), 'w', encoding='utf-8') as f:
            f.write(nav_xhtml)
        manifest_items.append({
            'id': 'nav',
            'href': 'Text/nav.xhtml',
            'media-type': 'application/xhtml+xml',
            'properties': 'nav',
        })

        # --- Write mimetype ---
        with open(os.path.join(tmp_dir, "mimetype"), 'w', encoding='ascii') as f:
            f.write("application/epub+zip")

        # --- Write container.xml ---
        container_xml = (
            '<?xml version="1.0" encoding="UTF-8"?>\n'
            '<container version="1.0" xmlns="urn:oasis:names:tc:opendocument:xmlns:container">\n'
            '  <rootfiles>\n'
            '    <rootfile full-path="OEBPS/content.opf" media-type="application/oebps-package+xml"/>\n'
            '  </rootfiles>\n'
            '</container>\n'
        )
        with open(os.path.join(meta_dir, "container.xml"), 'w', encoding='utf-8') as f:
            f.write(container_xml)

        # --- Write content.opf ---
        book_uuid = str(uuid.uuid4())
        opf = _build_content_opf(title, book_uuid, manifest_items, spine_ids)
        with open(os.path.join(tmp_dir, "OEBPS", "content.opf"), 'w', encoding='utf-8') as f:
            f.write(opf)

        # --- Write toc.ncx (minimal, for EPUB 2 readers) ---
        ncx = _build_toc_ncx(title, book_uuid, spine_ids)
        with open(os.path.join(tmp_dir, "OEBPS", "toc.ncx"), 'w', encoding='utf-8') as f:
            f.write(ncx)

        # Add toc.ncx to manifest (not in spine)
        # Already handled inside _build_content_opf

        # --- Pack EPUB ---
        _pack_epub(tmp_dir, output_path)

        if progress_callback:
            progress_callback(100, "Done!")

        return os.path.abspath(output_path)

    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)


_CSS_URL_FUNC_RE = re.compile(r"url\(\s*(?P<q>['\"]?)(?P<u>.*?)(?P=q)\s*\)", re.IGNORECASE)
_CSS_IMPORT_RE = re.compile(r"@import\s+(?P<q>['\"])(?P<u>.*?)(?P=q)", re.IGNORECASE)


def _rewrite_css_refs(css: str, mapper: _AssetMapper, content_path: str) -> str:
    """Rewrite url(...) and @import references inside CSS."""

    def _url_repl(m: re.Match) -> str:
        q = m.group('q') or ''
        u = m.group('u') or ''
        u_stripped = u.strip()
        if not u_stripped or u_stripped.startswith(('data:', 'http://', 'https://')):
            return m.group(0)
        new_u = mapper.lookup(u_stripped, content_path)
        if not new_u:
            return m.group(0)
        return f"url({q}{new_u}{q})"

    def _import_repl(m: re.Match) -> str:
        q = m.group('q')
        u = (m.group('u') or '').strip()
        if not u or u.startswith(('data:', 'http://', 'https://')):
            return m.group(0)
        new_u = mapper.lookup(u, content_path)
        if not new_u:
            return m.group(0)
        return f"@import {q}{new_u}{q}"

    css = _CSS_URL_FUNC_RE.sub(_url_repl, css)
    css = _CSS_IMPORT_RE.sub(_import_repl, css)
    return css


def _rewrite_asset_refs(html: str, mapper: _AssetMapper, content_path: str) -> str:
    """Rewrite common asset references in XHTML/HTML.

    Handles:
      - src/href/xlink:href/poster attributes
      - srcset attribute
      - inline style="...url(...)..."
      - <style> blocks (basic)
    """

    # 1) Rewrite common URL-bearing attributes
    def _attr_repl(match: re.Match) -> str:
        attr = match.group(1)
        quote = match.group(2)
        old_ref = match.group(3)

        # Skip absolute URLs / anchors
        if (old_ref or '').lstrip().startswith(('http://', 'https://', 'mailto:', 'tel:', '#', 'data:')):
            return match.group(0)

        new_ref = mapper.lookup(old_ref, content_path)
        if not new_ref:
            return match.group(0)
        return f"{attr}={quote}{new_ref}{quote}"

    attr_pattern = r"((?:xlink:)?(?:src|href|poster))\s*=\s*(['\"])(.*?)\2"
    html = re.sub(attr_pattern, _attr_repl, html, flags=re.IGNORECASE)

    # 2) Rewrite srcset="url 1x, url 2x" etc.
    def _srcset_repl(match: re.Match) -> str:
        quote = match.group(1)
        srcset = match.group(2) or ''
        parts = [p.strip() for p in srcset.split(',') if p.strip()]
        out_parts: list[str] = []
        for p in parts:
            # split into "url" + optional descriptor(s)
            bits = p.split()
            if not bits:
                continue
            url_part = bits[0]
            rest = ' '.join(bits[1:])
            new_url = mapper.lookup(url_part, content_path) or url_part
            out_parts.append((new_url + (f" {rest}" if rest else '')).strip())
        return f"srcset={quote}{', '.join(out_parts)}{quote}"

    html = re.sub(r"srcset\s*=\s*(['\"])(.*?)\1", _srcset_repl, html, flags=re.IGNORECASE | re.DOTALL)

    # 3) Rewrite inline style="... url(...) ..."
    def _style_attr_repl(match: re.Match) -> str:
        quote = match.group(1)
        style_val = match.group(2) or ''
        new_style = _rewrite_css_refs(style_val, mapper, content_path)
        return f"style={quote}{new_style}{quote}"

    html = re.sub(r"style\s*=\s*(['\"])(.*?)\1", _style_attr_repl, html, flags=re.IGNORECASE | re.DOTALL)

    # 4) Rewrite <style> blocks (best-effort; avoids breaking markup)
    def _style_block_repl(match: re.Match) -> str:
        before = match.group(1)
        css = match.group(2) or ''
        after = match.group(3)
        return before + _rewrite_css_refs(css, mapper, content_path) + after

    html = re.sub(r"(<style\b[^>]*>)(.*?)(</style>)", _style_block_repl, html, flags=re.IGNORECASE | re.DOTALL)

    return html


def _build_content_opf(title: str, uid: str,
                       manifest_items: list[dict],
                       spine_ids: list[str]) -> str:
    lines = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<package xmlns="http://www.idpf.org/2007/opf" unique-identifier="BookId" version="3.0">',
        '  <metadata xmlns:dc="http://purl.org/dc/elements/1.1/">',
        f'    <dc:title>{_xml_escape(title)}</dc:title>',
        f'    <dc:identifier id="BookId">urn:uuid:{uid}</dc:identifier>',
        '    <dc:language>en</dc:language>',
        f'    <meta property="dcterms:modified">{_now_utc()}</meta>',
        '  </metadata>',
        '  <manifest>',
        '    <item id="ncx" href="toc.ncx" media-type="application/x-dtbncx+xml"/>',
    ]
    for item in manifest_items:
        props = item.get('properties', '')
        prop_attr = f' properties="{_xml_escape(props)}"' if props else ''
        lines.append(
            f'    <item id="{_xml_escape(item["id"])}" '
            f'href="{_xml_escape(item["href"])}"'
            f'{prop_attr} '
            f'media-type="{item["media-type"]}"/>'
        )
    lines.append('  </manifest>')
    lines.append('  <spine toc="ncx">')
    for sid in spine_ids:
        lines.append(f'    <itemref idref="{_xml_escape(sid)}"/>')
    lines.append('  </spine>')
    lines.append('</package>')
    return '\n'.join(lines) + '\n'


def _build_toc_ncx(title: str, uid: str, spine_ids: list[str]) -> str:
    lines = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<ncx xmlns="http://www.daisy.org/z3986/2005/ncx/" version="2005-1">',
        '  <head>',
        f'    <meta name="dtb:uid" content="urn:uuid:{uid}"/>',
        '    <meta name="dtb:depth" content="1"/>',
        '    <meta name="dtb:totalPageCount" content="0"/>',
        '    <meta name="dtb:maxPageNumber" content="0"/>',
        '  </head>',
        f'  <docTitle><text>{_xml_escape(title)}</text></docTitle>',
        '  <navMap>',
    ]
    for i, sid in enumerate(spine_ids, 1):
        lines.append(f'    <navPoint id="nav_{i}" playOrder="{i}">')
        lines.append(f'      <navLabel><text>Section {i}</text></navLabel>')
        lines.append(f'      <content src="Text/{i}.xhtml"/>')
        lines.append('    </navPoint>')
    lines.append('  </navMap>')
    lines.append('</ncx>')
    return '\n'.join(lines) + '\n'


def _build_nav_xhtml(title: str, chapter_count: int) -> str:
    """Build an EPUB3 navigation document (nav.xhtml) with a clickable TOC."""
    items = []
    for i in range(1, chapter_count + 1):
        items.append(f'        <li><a href="{i}.xhtml">Section {i}</a></li>')

    return (
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        '<!DOCTYPE html>\n'
        '<html xmlns="http://www.w3.org/1999/xhtml" xmlns:epub="http://www.idpf.org/2007/ops">\n'
        '<head>\n'
        f'  <title>{_xml_escape(title)} - Contents</title>\n'
        '  <meta charset="utf-8"/>\n'
        '</head>\n'
        '<body>\n'
        f'  <h1>{_xml_escape(title)}</h1>\n'
        '  <nav epub:type="toc" id="toc">\n'
        '    <h2>Contents</h2>\n'
        '    <ol>\n'
        + "\n".join(items) + "\n"
        '    </ol>\n'
        '  </nav>\n'
        '</body>\n'
        '</html>\n'
    )


def _pack_epub(src_dir: str, output_path: str):
    """Create a valid EPUB zip (mimetype first, uncompressed)."""
    with zipfile.ZipFile(output_path, 'w', zipfile.ZIP_DEFLATED) as zf:
        # mimetype must be first and uncompressed
        mimetype_path = os.path.join(src_dir, "mimetype")
        zf.write(mimetype_path, "mimetype", compress_type=zipfile.ZIP_STORED)

        for root, _dirs, files in os.walk(src_dir):
            for fname in sorted(files):
                full = os.path.join(root, fname)
                arcname = os.path.relpath(full, src_dir).replace('\\', '/')
                if arcname == 'mimetype':
                    continue
                zf.write(full, arcname)


def _xml_escape(s: str) -> str:
    return (s.replace('&', '&amp;').replace('<', '&lt;')
             .replace('>', '&gt;').replace('"', '&quot;'))


def _now_utc() -> str:
    from datetime import datetime, timezone
    return datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')


# ---------------------------------------------------------------------------
# GUI
# ---------------------------------------------------------------------------

class EpubListWidget(QTreeWidget):
    """Tree widget with internal drag-and-drop reordering and external file drop."""

    files_dropped = Signal(list)  # emitted when .epub files are dropped from explorer

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setHeaderLabels(["#", "File Name", "Path"])
        self.setColumnWidth(0, 40)
        self.setColumnWidth(1, 320)
        self.setSelectionMode(QAbstractItemView.ExtendedSelection)
        self.setDragDropMode(QAbstractItemView.InternalMove)
        self.setDefaultDropAction(Qt.MoveAction)
        self.setAcceptDrops(True)
        self.setDragEnabled(True)
        self.setRootIsDecorated(False)
        self.setAlternatingRowColors(True)
        header = self.header()
        header.setStretchLastSection(True)
        header.setSectionResizeMode(0, QHeaderView.ResizeToContents)
        header.setSectionResizeMode(1, QHeaderView.Stretch)

        self.model().rowsMoved.connect(self._renumber)

    # -- External file drop --------------------------------------------------
    def dragEnterEvent(self, event: QDragEnterEvent):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()
        else:
            super().dragEnterEvent(event)

    def dragMoveEvent(self, event):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()
        else:
            super().dragMoveEvent(event)

    def dropEvent(self, event: QDropEvent):
        if event.mimeData().hasUrls():
            paths = []
            for url in event.mimeData().urls():
                p = url.toLocalFile()
                if p.lower().endswith('.epub'):
                    paths.append(p)
            if paths:
                self.files_dropped.emit(paths)
            event.acceptProposedAction()
        else:
            super().dropEvent(event)
            self._renumber()

    # -- Numbering -----------------------------------------------------------
    def _renumber(self):
        for i in range(self.topLevelItemCount()):
            self.topLevelItem(i).setText(0, str(i + 1))


class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("EPUB Combiner")
        self.resize(820, 560)
        self._apply_dark_theme()

        central = QWidget()
        self.setCentralWidget(central)
        layout = QVBoxLayout(central)
        layout.setContentsMargins(12, 12, 12, 12)
        layout.setSpacing(8)

        # --- Title row ---
        title_row = QHBoxLayout()
        title_row.addWidget(QLabel("Book Title:"))
        self.title_entry = QLineEdit("Combined EPUB")
        title_row.addWidget(self.title_entry)
        layout.addLayout(title_row)

        # --- List ---
        self.tree = EpubListWidget()
        self.tree.files_dropped.connect(self._add_paths)
        layout.addWidget(self.tree)

        # --- Buttons row ---
        btn_layout = QHBoxLayout()

        add_btn = QPushButton("➕ Add EPUBs")
        add_btn.clicked.connect(self._browse_files)
        btn_layout.addWidget(add_btn)

        up_btn = QPushButton("⬆ Up")
        up_btn.clicked.connect(lambda: self._move_selected(-1))
        btn_layout.addWidget(up_btn)

        down_btn = QPushButton("⬇ Down")
        down_btn.clicked.connect(lambda: self._move_selected(1))
        btn_layout.addWidget(down_btn)

        sort_num_btn = QPushButton("Sort 1-9")
        sort_num_btn.clicked.connect(self._sort_numeric)
        btn_layout.addWidget(sort_num_btn)

        sort_az_btn = QPushButton("Sort A→Z")
        sort_az_btn.clicked.connect(lambda: self._sort(False))
        btn_layout.addWidget(sort_az_btn)

        sort_za_btn = QPushButton("Sort Z→A")
        sort_za_btn.clicked.connect(lambda: self._sort(True))
        btn_layout.addWidget(sort_za_btn)

        remove_btn = QPushButton("🗑 Remove")
        remove_btn.clicked.connect(self._remove_selected)
        btn_layout.addWidget(remove_btn)

        clear_btn = QPushButton("Clear All")
        clear_btn.clicked.connect(self._clear_all)
        btn_layout.addWidget(clear_btn)

        layout.addLayout(btn_layout)

        # --- Progress ---
        self.progress = QProgressBar()
        self.progress.setTextVisible(True)
        self.progress.setValue(0)
        self.progress.setFormat("")
        layout.addWidget(self.progress)

        # --- Combine ---
        combine_btn = QPushButton("📚  Combine EPUBs")
        combine_btn.setStyleSheet(
            "QPushButton { background-color: #28a745; color: white; "
            "font-weight: bold; font-size: 13pt; padding: 8px; border-radius: 4px; }"
            "QPushButton:hover { background-color: #218838; }"
        )
        combine_btn.clicked.connect(self._combine)
        layout.addWidget(combine_btn)

        # --- Drag-drop hint ---
        hint = QLabel("Tip: drag & drop .epub files onto the list, or reorder by dragging rows.")
        hint.setStyleSheet("color: #888; font-size: 9pt;")
        hint.setAlignment(Qt.AlignCenter)
        layout.addWidget(hint)

    # -- Dark theme ----------------------------------------------------------
    def _apply_dark_theme(self):
        self.setStyleSheet("""
            QMainWindow, QWidget { background-color: #1e1e1e; color: #e0e0e0; }
            QLabel { color: #e0e0e0; }
            QLineEdit {
                background-color: #2d2d2d; color: #e0e0e0;
                border: 1px solid #3a3a3a; border-radius: 3px; padding: 4px;
            }
            QTreeWidget {
                background-color: #252526; color: #e0e0e0;
                alternate-background-color: #2a2a2a;
                border: 1px solid #3a3a3a; border-radius: 3px;
            }
            QTreeWidget::item:selected { background-color: #094771; }
            QHeaderView::section {
                background-color: #2d2d2d; color: #e0e0e0;
                border: 1px solid #3a3a3a; padding: 4px;
            }
            QPushButton {
                background-color: #2d2d2d; color: #e0e0e0;
                border: 1px solid #3a3a3a; border-radius: 3px;
                padding: 5px 12px; min-height: 20px;
            }
            QPushButton:hover { background-color: #3a3a3a; border-color: #5a5a5a; }
            QPushButton:pressed { background-color: #1a1a1a; }
            QProgressBar {
                background-color: #2d2d2d; border: 1px solid #3a3a3a;
                border-radius: 3px; text-align: center; color: #e0e0e0;
            }
            QProgressBar::chunk { background-color: #0078d4; border-radius: 2px; }
        """)

    # -- Actions -------------------------------------------------------------
    def _browse_files(self):
        files, _ = QFileDialog.getOpenFileNames(
            self, "Select EPUB Files", "",
            "EPUB files (*.epub);;All files (*.*)"
        )
        if files:
            self._add_paths(files)

    def _add_paths(self, paths: list[str]):
        for p in paths:
            if not p.lower().endswith('.epub'):
                continue
            # Avoid duplicates
            already = False
            for i in range(self.tree.topLevelItemCount()):
                if self.tree.topLevelItem(i).text(2) == p:
                    already = True
                    break
            if already:
                continue

            idx = self.tree.topLevelItemCount() + 1
            item = QTreeWidgetItem([str(idx), Path(p).name, p])
            item.setFlags(item.flags() & ~Qt.ItemIsDropEnabled)  # flat list
            self.tree.addTopLevelItem(item)

        # Auto-sort numerically after adding files
        self._sort_numeric()

    def _move_selected(self, direction: int):
        """Move selected items up (-1) or down (+1)."""
        items = self.tree.selectedItems()
        if not items:
            return

        indices = sorted([self.tree.indexOfTopLevelItem(it) for it in items])
        if direction < 0:
            # Move up — process top-to-bottom
            for idx in indices:
                if idx <= 0:
                    continue
                item = self.tree.takeTopLevelItem(idx)
                self.tree.insertTopLevelItem(idx - 1, item)
                item.setSelected(True)
        else:
            # Move down — process bottom-to-top
            for idx in reversed(indices):
                if idx >= self.tree.topLevelItemCount() - 1:
                    continue
                item = self.tree.takeTopLevelItem(idx)
                self.tree.insertTopLevelItem(idx + 1, item)
                item.setSelected(True)

        self.tree._renumber()

    def _sort_numeric(self):
        """Sort by natural numeric order (e.g. Vol 2 before Vol 10)."""
        items_data = []
        for i in range(self.tree.topLevelItemCount()):
            it = self.tree.topLevelItem(i)
            items_data.append((it.text(1), it.text(2)))

        items_data.sort(key=lambda x: _natural_sort_key(x[0]))

        self.tree.clear()
        for idx, (name, path) in enumerate(items_data, 1):
            item = QTreeWidgetItem([str(idx), name, path])
            item.setFlags(item.flags() & ~Qt.ItemIsDropEnabled)
            self.tree.addTopLevelItem(item)

    def _sort(self, reverse: bool):
        items_data = []
        for i in range(self.tree.topLevelItemCount()):
            it = self.tree.topLevelItem(i)
            items_data.append((it.text(1), it.text(2)))

        items_data.sort(key=lambda x: x[0].lower(), reverse=reverse)

        self.tree.clear()
        for idx, (name, path) in enumerate(items_data, 1):
            item = QTreeWidgetItem([str(idx), name, path])
            item.setFlags(item.flags() & ~Qt.ItemIsDropEnabled)
            self.tree.addTopLevelItem(item)

    def _remove_selected(self):
        for item in reversed(self.tree.selectedItems()):
            idx = self.tree.indexOfTopLevelItem(item)
            self.tree.takeTopLevelItem(idx)
        self.tree._renumber()

    def _clear_all(self):
        self.tree.clear()

    def _combine(self):
        count = self.tree.topLevelItemCount()
        if count < 2:
            QMessageBox.warning(self, "Not enough files",
                                "Please add at least 2 EPUB files to combine.")
            return

        # Collect paths in list order
        paths = [self.tree.topLevelItem(i).text(2) for i in range(count)]

        # Ask where to save
        default_name = self.title_entry.text().strip() or "Combined"
        save_path, _ = QFileDialog.getSaveFileName(
            self, "Save Combined EPUB",
            default_name + ".epub",
            "EPUB files (*.epub)"
        )
        if not save_path:
            return

        title = self.title_entry.text().strip() or "Combined EPUB"

        self.progress.setValue(0)
        self.progress.setFormat("Starting…")
        QApplication.processEvents()

        def on_progress(pct, msg):
            self.progress.setValue(pct)
            self.progress.setFormat(msg)
            QApplication.processEvents()

        try:
            result = combine_epubs(paths, save_path, title=title,
                                   progress_callback=on_progress)
            self.progress.setValue(100)
            self.progress.setFormat("Done!")
            QMessageBox.information(
                self, "Success",
                f"Combined {count} EPUBs into:\n{result}"
            )
        except Exception as e:
            self.progress.setValue(0)
            self.progress.setFormat("Error")
            QMessageBox.critical(self, "Error", f"Failed to combine EPUBs:\n{e}")


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main():
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    window = MainWindow()
    window.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
