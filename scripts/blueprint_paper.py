"""Paper source links, diagrams and TeX rendering for native hgraph."""
import hashlib
from html import escape
import re
import shutil
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo

from hgraph.sync import parse_blueprint, _brace_span

CORE = r'theorem|lemma|definition|corollary|proposition|fact'


def active_tex(text):
    # Preserve offsets/line numbers, including TeX's odd/even slash escaping.
    return re.sub(r'(\\*)%[^\n]*', lambda m: m[0] if len(m[1]) % 2
                  else m[1] + ' ' * (len(m[0]) - len(m[1])), text)


def source_statements(text):
    active = active_tex(text)
    return [{'kind': m[1], 'start_line': text.count('\n', 0, m.start()) + 1,
             'end_line': text.count('\n', 0, m.end()) + 1,
             'raw': text[m.start(2):m.end(2)].strip()}
            for m in re.finditer(r'\\begin\{(' + CORE + r')\}(.*?)\\end\{\1\}', active, re.S)]


def citation_keys(text):
    return {key.strip() for m in re.finditer(r'\\cite\w*\*?(?:\[[^\]]*\])?\{([^}]+)\}', active_tex(text))
            for key in m[1].split(',')}


def load_paper(root):
    """Read paper statements for source links and diagram rendering."""
    source = (root / 'AimPaper/main.tex').read_text()
    originals = {(r['kind'], r['start_line'], r['end_line']): r
                 for r in source_statements(source)}
    records = []
    for path in sorted((root / 'blueprint/chapters').glob('*.tex')):
        for number, kind, start, end in re.findall(
                r'^% AimPaper: (\d+\.\d+) (\w+) (\d+) (\d+)$', path.read_text(), re.M):
            original = originals.get((kind, int(start), int(end)))
            if original is not None:
                records.append({**original, 'number': number})
    return records


def paper_diagrams(records):
    """Locate the exact diagrams that the paper exporter will render."""
    for record in sorted(records, key=lambda r: (r['start_line'], r['number'])):
        for index, match in enumerate(re.finditer(r'\\xymatrix\s*\{', record['raw']), 1):
            _body, end = _brace_span(record['raw'], record['raw'].index('{', match.start()))
            yield {'raw': record['raw'][match.start():end],
                   'number': record['number'], 'index': index,
                   'stem': record['number'] + '-' + str(index)}


def diagram_key(raw):
    # Preserve token boundaries while ignoring comments and source indentation.
    return re.sub(r'\s+', ' ', active_tex(raw)).strip()


def diagram_targets(records):
    """Resolve diagrams by content, independently of merged statement labels."""
    targets = {}
    for diagram in paper_diagrams(records):
        targets.setdefault(diagram_key(diagram['raw']),
                           ('paper/diagrams/' + diagram['stem'] + '.svg',
                            'Commutative diagram ' + diagram['number']
                            + ' (' + str(diagram['index']) + ')'))
    return targets


def reference_targets(root, statements):
    refs = {alias: ('#/Kervaire126#' + row['label'], row['label'].removeprefix('paper:'))
            for row in statements for alias in row['labels']}
    # Resolve equation labels to their containing mathematical entry.
    for row in statements:
        for label in re.findall(r'\\label\{([^}]+)\}', row['body']):
            refs[label] = (refs[row['label']][0], 'equation in ' + refs[row['label']][1])
    from hgraph.sync import read_blueprint
    text = read_blueprint(root / 'blueprint/content.tex')
    authored, _ = parse_blueprint(text)
    for proof in re.finditer(r'\\begin\{proof\}(.*?)\\end\{proof\}', text, re.S):
        parents = [row for row in authored if row['pos'] < proof.start()]
        if parents:
            parent = parents[-1]
            for label in re.findall(r'\\label\{([^}]+)\}', proof[1]):
                refs[label] = (refs[parent['label']][0], 'proof of ' + refs[parent['label']][1])
    for figure in paper_figures(root):
        refs[figure['label']] = ('paper/diagrams/' + figure['stem'] + '.svg', 'AimPaper illustration')
    path = root / 'AimPaper/main.tex'
    if path.exists():
        source = path.read_text()
        for match in re.finditer(r'\\label\{([^}]+)\}', active_tex(source)):
            line = source.count('\n', 0, match.start()) + 1
            refs.setdefault(match[1], ('paper/main.tex.html#L' + str(line), 'original source'))
    return refs


def paper_figures(root):
    """Read referenced standalone TikZ figures verbatim, including their caption."""
    path = root / 'AimPaper/main.tex'
    if not path.exists():
        return []
    source = active_tex(path.read_text())
    from hgraph.sync import read_blueprint
    authored = read_blueprint(root / 'blueprint/content.tex')
    referenced = set(re.findall(r'\\ref\{([^}]+)\}', authored))
    figures = []
    for match in re.finditer(r'\\begin\{figure\}(?:\[[^\]]*\])?(.*?)\\end\{figure\}', source, re.S):
        body = match[1]
        labels = re.findall(r'\\label\{([^}]+)\}', body)
        if not labels or labels[-1] not in referenced:
            continue
        caption = re.search(r'\\caption\s*\{', body)
        if not caption:
            raise ValueError('Missing caption for AimPaper figure ' + labels[-1])
        caption_text, _end = _brace_span(body, body.index('{', caption.start()))
        figures.append({'label': labels[-1], 'stem': 'figure-' + labels[-1].removeprefix('fig:'),
                        'raw': body[:caption.start()].strip(),
                        'caption': caption_text,
                        'start_line': source.count('\n', 0, match.start()) + 1})
    return figures


def web_bibliography(text):
    """Normalize DOI fields in the rendering copy for native hgraph's parser.

    The pinned parser prepends https://doi.org/ to a DOI field verbatim.
    Authored bibliographies, explicit URL fields and bare DOIs stay intact.
    """
    def normalize(match):
        field = match[2]
        value = field[1:-1].strip()
        doi = re.sub(r'^https?://(?:dx\.)?doi\.org/', '', value, flags=re.I)
        return match[0] if doi == value else match[1] + field[0] + doi + field[-1]
    return re.sub(r'(?i)(\bdoi\s*=\s*)(\{[^{}]*\}|"[^"]*")', normalize, text)


def prepare_web_blueprint(root, destination):
    # Apply the same TeX conversion to chapter and graph-detail views.
    from hgraph.sync import read_blueprint
    statements, _proofs = parse_blueprint(read_blueprint(root / 'blueprint/content.tex'))
    refs = reference_targets(root, statements)
    diagrams = diagram_targets(load_paper(root))
    if destination.exists():
        shutil.rmtree(destination)
    destination.mkdir(parents=True, exist_ok=True)
    for path in sorted((root / 'blueprint').rglob('*')):
        if 'generated' in path.relative_to(root / 'blueprint').parts:
            continue
        if not path.is_file() or path.suffix not in ('.tex', '.sty', '.bib'):
            continue
        relative = path.relative_to(root / 'blueprint')
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if path.suffix == '.tex':
            target.write_text(display_chapter(path.read_text(), refs, diagrams))
        elif path.suffix == '.bib':
            target.write_text(web_bibliography(path.read_text()))
        else:
            # Use buffered reads/writes to preserve the exact source bytes.
            target.write_bytes(path.read_bytes())
    return destination


def display_chapter(text, refs, diagrams):
    """Render paper statements and their proofs within an ordinary chapter."""
    number = None

    def render(match):
        nonlocal number
        if match[1] != 'proof':
            # Paper-number aliases identify the source of a combined statement.
            paper = re.search(r'\\label\{paper:(\d+\.\d+)\}', active_tex(match[0]))
            if not paper and match[1] == 'notation':
                paper = re.search(r'From\s+\\cite\{LWX126\},\s+Notation\s+(\d+\.\d+)',
                                  active_tex(match[0]))
            number = paper[1] if paper else None
        if number or re.search(r'\\xymatrix\s*\{', active_tex(match[0])):
            return display_body(match[0], number, refs, diagrams)
        return match[0]

    return re.sub(r'\\begin\{(' + CORE + r'|remark|notation|proof)\}.*?\\end\{\1\}',
                  render, text, flags=re.S)



def display_enumeration(body):
    stack = []
    pattern = re.compile(r"\\begin\{enumerate\}(?:\[[^\]]*\])?|\\end\{enumerate\}|"
                         r"\\setcounter\{(enumi+)\}\{(\d+)\}|\\item\b(?:\[[^\]]*\])?")
    def token(match):
        text = match[0]
        if text.startswith(r'\begin'):
            stack.append([0, "'" if "arabic*'" in text else ''])
            return r'\begin{enumerate}'
        if text.startswith(r'\end'):
            if not stack:
                raise ValueError('Unbalanced AimPaper enumeration')
            stack.pop()
            return text
        if text.startswith(r'\setcounter'):
            if not stack:
                raise ValueError('Counter outside AimPaper enumeration')
            stack[-1][0] = int(match[2])
            return ''
        if stack:
            stack[-1][0] += 1
            return r'\item[(' + str(stack[-1][0]) + stack[-1][1] + ')]'
        return text
    result = pattern.sub(token, body)
    if stack:
        raise ValueError('Unbalanced AimPaper enumeration')
    return result


def display_body(body, number, reference_targets=None, diagrams=None):
    """Link exact-source SVG diagrams at their original reading positions."""
    body = display_enumeration(active_tex(body))
    if number == '1.4':
        # Suppress the self-reference in the permanence theorem heading.
        body = body.replace(r'[Theorem~\ref{thm:126survives}]', '', 1)
    spans = []
    for match in re.finditer(r'\\xymatrix\s*\{', body):
        _inner, end = _brace_span(body, body.index('{', match.start()))
        # Replace standalone diagram displays with links to the rendered SVG.
        opening = re.search(r'(\$\$|\\\[)\s*$', body[:match.start()])
        closing = re.match(r'\s*([.,;:]?)\s*' + (r'\$\$' if opening and opening[1] == '$$' else r'\\\]'), body[end:])
        if not opening or not closing:
            raise ValueError('Expected a standalone display for AimPaper diagram in '
                             + (number or 'a merged statement'))
        diagram = (diagrams or {}).get(diagram_key(body[match.start():end]))
        if diagram is None:
            raise ValueError('No exact paper source for diagram in '
                             + (number or 'a merged statement'))
        spans.append((opening.start(), end + closing.end(), closing[1], diagram))
    for start, end, punctuation, (url, caption) in reversed(spans):
        link = r'\href{' + url + '}{' + caption + punctuation + '}'
        body = body[:start] + '\n\n' + link + '\n\n' + body[end:]
    # Convert figure clauses and references for the browser text renderer.
    if reference_targets:
        def figure_clause(match):
            target = reference_targets.get(match[1])
            if target and target[0].startswith('paper/diagrams/figure-'):
                return '\n\n' + r'\ref{' + match[1] + '}\n\n'
            return match[0]
        # Replace the complete figure clause, including its punctuation.
        body = re.sub(r'\(?[Ss]ee Figure\s+\\ref\{([^}]+)\}\.?(?:\))?', figure_clause, body)
        def reference(match):
            label = match[1]
            target = reference_targets.get(label)
            # Native references retain numbering and navigate within the same
            # reader, including equations inside collapsed proof panels.
            if target and target[0].startswith('#/Kervaire126#'):
                return match[0]
            return ('\\href{' + target[0] + '}{' + target[1] + '}') if target else match[0]
        body = re.sub(r'\\ref\{([^}]+)\}', reference, body)
    # Display optional theorem and page locators beside citation links.
    body = re.sub(r'\\cite(\[[^\]]+\])\{([^}]+)\}', r'\\cite{\2} (\1)', body)
    body = re.sub(r'\\setcounter\{[^}]*\}\{[^}]*\}', '', body)
    body = re.sub(r'\\vspace\*?\{[^}]*\}', '', body)
    return body


def render_paper_svg(root, work, stem, document):
    """Compile exact source graphics, reusing a content-addressed local cache."""
    import subprocess
    input_path = work / (stem + '.tex')
    input_path.write_text(document)
    svg = work / (stem + '.svg')
    stamp = work / (stem + '.sha256')
    signature = hashlib.sha256((document + (root / 'AimPaper/algtop.sty').read_text()).encode()).hexdigest()
    if not svg.exists() or not stamp.exists() or stamp.read_text() != signature:
        for command in (['latex', '-interaction=nonstopmode', '-halt-on-error', '-output-directory=' + str(work), str(input_path)],
                        ['dvisvgm', '--no-fonts', '--exact', '--bbox=min', '-o', str(svg), str(work / (stem + '.dvi'))]):
            process = subprocess.run(command, cwd=root / 'AimPaper', capture_output=True, text=True)
            if process.returncode:
                raise ValueError('AimPaper diagram rendering failed: ' + process.stdout[-3000:] + process.stderr[-1000:])
        stamp.write_text(signature)
    return svg


def write_source_html(path):
    """Render source files with line anchors and download links."""
    lines = path.read_text().splitlines()
    rows = '\n'.join(
        '<span class="line" id="L' + str(number) + '"><a class="number" href="#L'
        + str(number) + '" aria-label="Line ' + str(number) + '">'
        + str(number) + '</a><code>' + escape(line) + '</code></span>'
        for number, line in enumerate(lines, 1))
    title = escape(path.name)
    document = '''<!doctype html>
<html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>''' + title + ''' · Kervaire126</title>
<style>
body{margin:0;color:#172032;background:#fff;font:14px/1.6 ui-monospace,monospace}
nav{position:sticky;top:0;padding:14px 22px;background:#f5f6fa;border-bottom:1px solid #dde1eb;font-family:system-ui,sans-serif}
nav a{margin-right:24px;color:#4938d1}pre{margin:0;padding:16px 0;white-space:pre;overflow:auto}
.line{display:block;min-height:1.6em;scroll-margin-top:64px}.line:target{background:#fff1b8}
.number{display:inline-block;width:5em;margin-right:18px;text-align:right;color:#718096;text-decoration:none;user-select:none}
code{font:inherit}
</style>
<nav><a href="../#/Kervaire126">Kervaire126</a><a href="''' + title + '''" download>Download source</a><a href="source.zip" download>Download all TeX sources</a><a href="ERRATA.txt">Paper erratum</a></nav>
<main><pre>''' + rows + '''</pre></main></html>
'''
    path.with_name(path.name + '.html').write_text(document)


def export_paper(root, out, records):
    target = out / 'paper'
    target.mkdir(parents=True, exist_ok=True)
    sources = ('main.tex', '112.tex', 'algtop.sty', 'main.bib', 'main.bbl')
    downloads = (*sources, 'ERRATA.txt')
    for filename in (*downloads, '2412.10879.pdf'):
        shutil.copyfile(root / 'AimPaper' / filename, target / filename)
    for filename in sources:
        write_source_html(target / filename)
    with ZipFile(target / 'source.zip', 'w', compression=ZIP_DEFLATED) as archive:
        for filename in downloads:
            entry = ZipInfo(filename, date_time=(1980, 1, 1, 0, 0, 0))
            entry.compress_type = ZIP_DEFLATED
            entry.external_attr = 0o100644 << 16
            archive.writestr(entry, (target / filename).read_bytes())
    source = (root / 'AimPaper/main.tex').read_text()
    # Render XY diagrams from their TeX source.
    diagram_dir = target / 'diagrams'
    diagram_dir.mkdir(exist_ok=True)
    work = root / '.lake/blueprint/paper-diagrams'
    work.mkdir(parents=True, exist_ok=True)
    for diagram in paper_diagrams(records):
        stem = diagram['stem']
        document = (r'\documentclass{article}\usepackage{algtop}\usepackage[all,cmtip]{xy}'
                    r'\usepackage{mathtools}\pagestyle{empty}\begin{document}$$'
                    + diagram['raw'] + r'$$\end{document}')
        svg = render_paper_svg(root, work, stem, document)
        shutil.copyfile(svg, diagram_dir / (stem + '.svg'))
    # Render standalone TikZ figures with the paper preamble and drawing commands.
    preamble = source.split(r'\title{', 1)[0]
    numbers = {label: r['number'] for r in records
               for label in re.findall(r'\\label\{([^}]+)\}', r['raw'])}
    for figure in paper_figures(root):
        caption = re.sub(r'\\ref\{([^}]+)\}', lambda m: numbers[m[1]], figure['caption'])
        document = (preamble + r'\pagestyle{empty}\begin{document}\thispagestyle{empty}' + figure['raw']
                    + r'\par\noindent ' + caption + r'\end{document}')
        svg = render_paper_svg(root, work, figure['stem'], document)
        shutil.copyfile(svg, diagram_dir / (figure['stem'] + '.svg'))
