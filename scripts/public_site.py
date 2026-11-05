"""Declaration excerpts, static graph layouts and reader controls for hgraph."""
from contextlib import contextmanager
import hashlib
import json
from pathlib import Path
import re
import shutil

from hgraph.lean_source import scan_lean, statement_prefix


COLLABORATION_FIELDS = {
    'reviews', 'comments', 'reviewed', 'maths_verdict', 'lean_verdict',
}

HGRAPH_MODIFICATION_NOTICE = (
    'Modified by SII-Kervaire126 for this project\'s hgraph publication.\n'
    'Original project: https://github.com/AxelDlv00/hgraph\n'
    'Fork: https://github.com/surenny/hgraph\n'
    'Changes: reader controls, navigation, references, status labels and asset URLs.\n'
    'See site-root NOTICE.txt for modification details and LICENSE.txt for Apache-2.0.\n'
    'Existing third-party licenses and attribution remain applicable.'
)


def declaration_body(text):
    """Trim trailing comments from a Lean declaration excerpt."""
    if '/-' not in text and '--' not in text:
        return text.rstrip()
    # Comment masking preserves strings, characters and quoted identifiers.
    masked = scan_lean(text).without_comments
    end = len(masked.rstrip())
    return text[:end].rstrip()


def normalize_graph_sources(graph):
    """Normalize exported declaration excerpts through the Graph API."""
    changes = 0
    for node in graph.nodes():
        if node.type != 'lean' or node.meta.get('generated') != 'lean':
            continue
        body = declaration_body(node.content)
        if body == node.content:
            continue
        kind = node.meta.get('content_type', '')
        graph.modify_node(node.id, content=body,
                          set_meta={'statement': statement_prefix(body, kind)})
        changes += 1
    return changes


def reader_data(value):
    """Remove unused collaboration records from every publication payload."""
    if isinstance(value, dict):
        return {key: reader_data(item) for key, item in value.items()
                if key not in COLLABORATION_FIELDS}
    if isinstance(value, list):
        return [reader_data(item) for item in value]
    return value


@contextmanager
def publication_export():
    """Export reader data with static graph layouts."""
    from hgraph import dashboard
    from hgraph.layout import render_svgs

    original = dashboard.project_data

    def project_data(*args, **kwargs):
        kwargs['include_layout'] = False
        data = original(*args, **kwargs)
        data = reader_data(data)
        data['gvsvg'] = render_svgs(data)
        return data

    dashboard.project_data = project_data
    try:
        yield
    finally:
        dashboard.project_data = original


def replace_once(text, old, new):
    """Replace one frontend compatibility target."""
    if text.count(old) != 1:
        raise ValueError('Pinned frontend compatibility target changed: ' + old[:80])
    return text.replace(old, new, 1)


def reader_frontend(out):
    """Select read-only components in the copied, version-pinned frontend."""
    assets = out / 'assets'
    project = next(assets.glob('ProjectView-*.js'))
    graph = next(assets.glob('GraphModal-*.js'))
    lazy_review = re.compile(
        r'(\w+)=\(0,\w+\.lazy\)\(\(\)=>\w+\(\(\)=>import\('
        r'`\./Reviews-[^`]+`\)\.then\(e=>\(\{default:e.Reviews\}\)\),'
        r'__vite__mapDeps\(\[[^\]]+\]\),import.meta.url\)\)')

    text = project.read_text()
    text = replace_once(text,
        'f&&(0,C.jsx)(S.Suspense,{fallback:(0,C.jsxs)(`span`,{className:`mtag rv`,children:[f.reviews.length,` reviews · `,f.comments.length,` comments`]}),children:(0,C.jsx)(le,{className:`mtag rv`,root:u,target:{id:e.id,label:e.label||null,title:e.title||null},reviews:f.reviews,comments:f.comments,repo:d})})',
        'null')
    start = text.index('function De({entries:')
    end = text.index('}var z=', start) + 1
    text = text[:start] + text[end:]
    text = replace_once(text,
        '{view:`summary`,icon:`▣`,label:`Blueprint summary`},', '')
    text = replace_once(text,
        't===`summary`?(0,C.jsx)(De,{entries:K,chapters:Y,refs:J,onSelect:X,onGotoChapter:Z}):',
        '')
    text, count = lazy_review.subn(r'\1=()=>null', text)
    if count != 1:
        raise ValueError('Pinned project review import changed')
    # Native refs retain label aliases when mathematical entries are merged.
    text = replace_once(text,
        'let i=n.entries.find(t=>t.label===e),a=n.entries.some(t=>t.id===e)?e:i?.id',
        'let i=n.entries.find(t=>t.label===e),a=n.entries.some(t=>t.id===e)?e:i?.id||n.refs?.[e]?.id')
    text = replace_once(text,
        'let t=K.find(t=>t.id===e||t.label===e);',
        'let t=K.find(t=>t.id===e||t.label===e||t.id===n?.refs?.[e]?.id);')
    text = replace_once(text,
        '[K,X,Z,n?.chapters]', '[K,X,Z,n?.chapters,n?.refs]')
    project.write_text(text)

    text = graph.read_text()
    text = replace_once(text,
        '(0,j.jsx)(_.Suspense,{fallback:(0,j.jsx)(`div`,{className:`stmt-reviews`,children:`Loading reviews…`}),children:(0,j.jsx)(R,{root:r,target:e,reviews:e.reviews,comments:e.comments,repo:i})})',
        'null')
    text, count = lazy_review.subn(r'\1=()=>null', text)
    if count != 1:
        raise ValueError('Pinned graph review import changed')
    graph.write_text(text)

    # TeX supplies the type in "Theorems~\ref{a} and~\ref{b}". Show
    # only the numbers in that list; bare references keep their type labels.
    latex = next(assets.glob('latex-*.js'))
    reference = r'[/\\ref\{([^{}]*)\}/g,(e,r)=>n(r,t)]'
    typed_reference = (
        r'[/((?:\b(?:Theorems?|Propositions?|Lemmas?|Corollar(?:y|ies)|'
        r'Definitions?|Facts?|Remarks?|Examples?|Notations?|Chapters?|'
        r'Sections?|Figures?|Tables?|Equations?|Thms?\.?|Props?\.?|'
        r'Lems?\.?|Cors?\.?|Defs?\.?))[\s~]+)'
        r'(\\ref\{[^{}]*\}(?:[\s~]*(?:(?:,|and|or|to|--?)[\s~]*)+'
        r'\\ref\{[^{}]*\})*)/gi,'
        r'(e,r,i)=>r+i.replace(/\\ref\{([^{}]*)\}/g,(e,r)=>n(r,t,!0))]'
    )
    text = replace_once(latex.read_text(), reference,
                        typed_reference + ',' + reference)
    # Preserve the literature locator in standard \cite[Theorem 1.2]{key}.
    citation = (
        r'[/\\cite[a-zA-Z]*\*?(?:\[[^\]]*\])?\{([^{}]*)\}/g,'
        r'(t,n)=>n.split(`,`).map(t=>{t=t.trim();let n=r[t];return'
        r'`<a class="cite" data-cite="${e(t)}">[${n??e(t)}]</a>`}).join(`, `)]'
    )
    citation_with_locator = (
        r'[/\\cite[a-zA-Z]*\*?(?:\[([^\]]*)\])?(?:\[([^\]]*)\])?'
        r'\{([^{}]*)\}/g,(t,n,i,a)=>{let o=n!==void 0||i!==void 0,'
        r's=i===void 0?``:n,c=i===void 0?n:i,l=a.split(`,`).map(t=>{'
        r't=t.trim();let n=r[t]??e(t);return'
        r'`<a class="cite" data-cite="${e(t)}">${o?n:`[${n}]`}</a>`'
        r'}).join(`, `);return o?`[${s?`${s} `:``}${l}${c?`, ${c}`:``}]`:l}]'
    )
    latex.write_text(replace_once(text, citation, citation_with_locator))

    # Translate graph status labels for the reader.
    labels = {
        '` formalized`': '` with local Lean bindings`',
        '`Local progress`': '`Local Lean bindings`',
        '`Dependency closure`': '`Lean prerequisite closure`',
        '[`blocked`,`blocked`]': '[`blocked`,`unbound prerequisites`]',
        '[`ready`,`ready to formalize`]': '[`ready`,`no Lean binding`]',
        '[`formalized`,`formalized`]': '[`formalized`,`Lean binding present`]',
        '[`notready`,`not ready`]': '[`notready`,`unbound prerequisites`]',
        '`Lean code incomplete`': '`Lean admissions`',
        '`locally formalized`': '`local Lean bindings`',
        '`+ dependencies complete`': '`bindings and stated dependencies`',
        '`Proof (fill)`': '`Lean bindings (fill)`',
    }
    review_names = [path.name for path in assets.glob('Reviews-*.js')]
    runtime = next(assets.glob('jsx-runtime-*.js')).name
    for path in assets.glob('*.js'):
        if path.name in review_names:
            path.unlink()
            continue
        text = path.read_text()
        for name in review_names:
            text = text.replace('./' + name, './' + runtime)
        for old, new in labels.items():
            text = text.replace(old, new)
        path.write_text(text)

    # Include the reader adapter version in bundle cache keys.
    version = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()[:10]
    names = {path.name: path.stem + '-reader-' + version + path.suffix
             for path in assets.glob('*.js')}
    for path in out.rglob('*'):
        if not path.is_file() or path.suffix not in {'.js', '.html', '.json'}:
            continue
        original = text = path.read_text()
        for old, new in names.items():
            text = text.replace(old, new)
        if path.suffix == '.js' and (path.parent == assets or text != original):
            text = '/*!\n' + HGRAPH_MODIFICATION_NOTICE + '\n*/\n' + text
        elif path.suffix == '.html' and (path == out / 'index.html' or text != original):
            notice = '<!--\n' + HGRAPH_MODIFICATION_NOTICE + '\n-->\n'
            if text.lower().startswith('<!doctype html>'):
                end = text.index('>') + 1
                text = text[:end] + '\n' + notice + text[end:]
            else:
                text = notice + text
        path.write_text(text)
    for old, new in names.items():
        (assets / old).rename(assets / new)


def finish_public_site(out):
    """Finish all copies, including lazy chapter and compatibility payloads."""
    root = Path(__file__).resolve().parent.parent
    shutil.copyfile(root / 'site/NOTICE.txt', out / 'NOTICE.txt')
    shutil.copyfile(root / 'LICENSE', out / 'LICENSE.txt')
    for path in out.rglob('*.json'):
        data = reader_data(json.loads(path.read_text()))
        path.write_text(json.dumps(data, ensure_ascii=False))
    reader_frontend(out)
