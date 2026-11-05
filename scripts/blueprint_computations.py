"""Export the finite Adams assumptions as a standalone mathematical table."""
from __future__ import annotations

import ast
from collections import Counter
from dataclasses import dataclass
from html import escape
from pathlib import Path
import re


@dataclass(frozen=True)
class Claim:
    spectrum: str
    kind: str
    r: int
    s: int
    t: int
    x: tuple[int, ...]
    ts: int
    tt: int
    y: tuple[int, ...]


def _list_body(text: str, marker: str) -> str:
    """Read one literal list, respecting brackets inside quoted labels."""
    start = text.index(marker) + len(marker)
    if text[start] != '[':
        raise ValueError(f'Expected literal list after {marker!r}')
    depth = 0
    quoted = False
    escaped = False
    for pos in range(start, len(text)):
        char = text[pos]
        if quoted:
            if escaped:
                escaped = False
            elif char == '\\':
                escaped = True
            elif char == '"':
                quoted = False
        elif char == '"':
            quoted = True
        elif char == '[':
            depth += 1
        elif char == ']':
            depth -= 1
            if depth == 0:
                return text[start + 1:pos]
    raise ValueError(f'Unclosed literal list after {marker!r}')


def _rows(body: str, pattern: re.Pattern) -> list[re.Match]:
    """Parse every row with the specified table syntax."""
    matches = list(pattern.finditer(body))
    cursor = 0
    for match in matches:
        if body[cursor:match.start()].strip(' \t\r\n,'):
            raise ValueError(f'Unrecognized table syntax: {body[cursor:match.start()]!r}')
        cursor = match.end()
    if body[cursor:].strip(' \t\r\n,'):
        raise ValueError(f'Unrecognized table syntax: {body[cursor:]!r}')
    return matches


def load_claims(root: Path) -> list[Claim]:
    source = (root / 'KIP126/SSComputation/Table/Data.lean').read_text()
    body = _list_body(source, 'public def claims : List Claim := ')
    pattern = re.compile(
        r'⟨\.(sphere|nuCofiber|moore),\s*\.(equation|reaches|boundaryBy|refutation),\s*'
        r'(\d+),\s*(\d+),\s*(\d+),\s*\[([\d,\s]*)\],\s*'
        r'(\d+),\s*(\d+),\s*\[([\d,\s]*)\]⟩')
    claims = []

    def vector(value):
        return tuple(ast.literal_eval('[' + value + ']'))

    for match in _rows(body, pattern):
        spectrum, kind, r, s, t, x, ts, tt, y = match.groups()
        claims.append(Claim(spectrum, kind, int(r), int(s), int(t), vector(x),
                            int(ts), int(tt), vector(y)))
    return claims


def _spectrum(name: str) -> str:
    return {
        'sphere': '<msup><mi>S</mi><mn>0</mn></msup>',
        'nuCofiber': '<mrow><mi>C</mi><mi>ν</mi></mrow>',
        'moore': '<msub><mi>C</mi><mn>2</mn></msub>',
    }[name]


def _math(body: str) -> str:
    return '<math xmlns="http://www.w3.org/1998/Math/MathML">' + body + '</math>'


def _vector(claim: Claim, target: bool = False) -> str:
    s, t, indices = (claim.ts, claim.tt, claim.y) if target else (claim.s, claim.t, claim.x)
    coordinate_spectrum = 'sphere' if claim.spectrum == 'moore' else claim.spectrum
    terms = [f'<msub><mi>b</mi><mrow>{_spectrum(coordinate_spectrum)}<mo>;</mo>'
             f'<mn>{s}</mn><mo>,</mo><mn>{t}</mn><mo>,</mo><mn>{i}</mn></mrow></msub>'
             for i in indices]
    if not terms:
        return '<mn>0</mn>'
    vector = '<mrow>' + '<mo>+</mo>'.join(terms) + '</mrow>'
    if claim.spectrum == 'moore':
        return '<mrow><msub><mi>i</mi><mo>*</mo></msub><mo>(</mo>' + vector + '<mo>)</mo></mrow>'
    return vector


def _statement(claim: Claim) -> str:
    source = _vector(claim)
    if claim.kind == 'reaches':
        page = f'<msub><mi>E</mi><mn>{claim.r}</mn></msub>'
        return _math(source) + ' has a representative on ' + _math(page) + ' (possibly zero).'
    if claim.kind == 'boundaryBy':
        return _math(source) + f' belongs to the boundary subgroup after page {claim.r}.'
    equation = (f'<msub><mi>d</mi><mn>{claim.r}</mn></msub><mo>(</mo>' + source
                + '<mo>)</mo><mo>=</mo>' + _vector(claim, target=True))
    if claim.kind == 'refutation':
        equation = '<mo>¬</mo><mrow><mo>(</mo>' + equation + '<mo>)</mo></mrow>'
    return _math('<mrow>' + equation + '</mrow>')


def export_computations(root: Path, out: Path) -> dict[str, int]:
    """Publish the finite input table in source order."""
    claims = load_claims(root)
    counts = Counter(claim.kind for claim in claims)
    rows = []
    for number, claim in enumerate(claims, 1):
        target = f'({claim.ts}, {claim.tt})' if claim.kind in ('equation', 'refutation') else '—'
        rows.append(f'<tr id="claim-{number}" data-kind="{claim.kind}">'
                    f'<th scope="row"><a href="#claim-{number}">{number}</a></th>'
                    f'<td>{_math(_spectrum(claim.spectrum))}</td><td>{claim.r}</td>'
                    f'<td>({claim.s}, {claim.t})</td><td>{target}</td>'
                    f'<td>{_statement(claim)}</td></tr>')
    page = '''<!doctype html>
<html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Finite Adams calculation assumptions</title>
<style>
:root{color-scheme:light dark}body{font:17px/1.6 Georgia,serif;max-width:90rem;margin:2rem auto;padding:0 1rem}
h1{font-size:1.8rem}p{max-width:75ch}a{color:inherit}table{border-collapse:collapse;width:100%;font-size:.95rem}
th,td{border-bottom:1px solid #8886;text-align:left;padding:.65rem .5rem;vertical-align:top}
thead{background:Canvas;position:sticky;top:0}td:nth-child(-n+5){white-space:nowrap}math{font-size:1.08em}
tr:target{background:#d3ab3833}.table-scroll{overflow-x:auto}caption{text-align:left;padding:1rem 0}
@media print{body{max-width:none;font-size:10pt;margin:0;padding:0}thead{display:table-header-group;position:static}tr{break-inside:avoid}a{text-decoration:none}.table-scroll{overflow:visible}}
</style>
<body><nav><a href="../index.html">Return to the blueprint</a></nav>
<h1>Finite Adams calculation assumptions</h1>
<p>This table lists INPUT_COUNT finite Adams spectral-sequence inputs for the sphere,
the cofiber of the Hopf map ν, and bottom-cell images in the completed mod-two
Moore spectrum.</p>
<p>The symbol <math><msub><mi>b</mi><mrow><mi>X</mi><mo>;</mo><mi>s</mi><mo>,</mo><mi>t</mi><mo>,</mo><mi>i</mi></mrow></msub></math>
denotes the <math><mi>i</mi></math>th element, starting at zero, of the complete ordered basis of
<math><msubsup><mi>E</mi><mn>2</mn><mrow><mi>s</mi><mo>,</mo><mi>t</mi></mrow></msubsup><mo>(</mo><mi>X</mi><mo>)</mo></math>
specified in the second-page chapter. Each degree is written as (filtration, internal degree);
the stem is <math><mi>t</mi><mo>−</mo><mi>s</mi></math>.
A sum with no terms is zero. For C₂, a coordinate list denotes the image of
the corresponding sphere vector under the bottom-cell map i_*.</p>
<p>A page representative of a second-page label comes from one cycle
whose projections give both the original label and its class on that page.
An equation <math><msub><mi>d</mi><mi>r</mi></msub><mo>(</mo><mi>x</mi><mo>)</mo><mo>=</mo><mi>y</mi></math>
asserts the existence of representatives of both labels on that page, satisfying
the differential equation, with zero targets allowed.
An excluded equation is the negation of this representative differential relation.
Reaching a page allows the representative there to be zero. A boundary bound
allows an earlier hit, a sum of boundaries, or zero. Dashes mean that the statement
has no target field.</p>
<p>The second-page chapter specifies the comparisons with Adams groups.
The computational methods and conventions are described in
<a href="https://arxiv.org/abs/2412.10876">Machine Proofs for Adams Differentials and Extension Problems Among CW Spectra</a>
and the <a href="https://doi.org/10.5281/zenodo.14875701">v126.3.cw49 data archive</a>.
The four direct second differentials and the two staircase continuations
are listed separately. Certification of the INPUT_COUNT inputs in this table is pending.</p>
<div class="table-scroll"><table><caption>COUNT_SUMMARY.</caption>
<thead><tr><th scope="col">No.</th><th scope="col">Spectrum</th><th scope="col">Page</th>
<th scope="col">Source degree</th><th scope="col">Target degree</th><th scope="col">Statement</th></tr></thead>
<tbody>TABLE_ROWS</tbody></table></div></body></html>
'''
    labels = {'equation': 'differential equations', 'reaches': 'page continuations',
              'boundaryBy': 'boundary bounds', 'refutation': 'negated equations'}
    summary = ', '.join(f'{counts[kind]} {labels[kind]}' for kind in labels)
    page = (page.replace('INPUT_COUNT', str(len(claims)))
            .replace('COUNT_SUMMARY', escape(summary))
            .replace('TABLE_ROWS', '\n'.join(rows)))
    directory = out / 'paper'
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'finite-calculations.html').write_text(page)
    return dict(counts)
