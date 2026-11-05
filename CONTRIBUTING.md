# Contributing

## Lean

Use the toolchain in [lean-toolchain](lean-toolchain) and the dependencies in
[lake-manifest.json](lake-manifest.json). From the repository root:

```sh
lake exe cache get
lake build
```

Name theorems after their mathematical objects, conclusions and essential
hypotheses. Keep established eponyms such as the Kervaire invariant, Adams
spectral sequence, Toda bracket, Moore spectrum and named convergence or
extension theorems. Put source authors, citation keys and paper numbering in
docstrings and Blueprint references; avoid author initials such as `bx`,
`iwx`, `hhr`, or bibliography keys such as `br21` in theorem names. When
renaming a declaration, update its Lean references and Blueprint bindings.

## Website

The website provides the hgraph reader at `#/Kervaire126`.
The Blueprint build requires Python 3.9+ and uses the pinned
[hgraph](https://github.com/surenny/hgraph)
dependency in [requirements-blueprint.txt](requirements-blueprint.txt).
The original project is [AxelDlv00/hgraph](https://github.com/AxelDlv00/hgraph),
licensed under Apache-2.0. Attribution and frontend modifications are documented
in [the website notices](site/NOTICE.txt).
Paper diagrams also require `latex`, `dvisvgm`, and the TeX packages used by
[AimPaper/algtop.sty](AimPaper/algtop.sty).

From the repository root:

```sh
python3 -m venv .lake/blueprint-env
.lake/blueprint-env/bin/python -m pip install -r requirements-blueprint.txt
.lake/blueprint-env/bin/python scripts/build-site.py
python3 -m http.server 18726 --bind 127.0.0.1 --directory _site
```

Open `http://127.0.0.1:18726/` for the project homepage,
`http://127.0.0.1:18726/#/Kervaire126` for the mathematical reader.
The static site is written to `_site/`, with build caches in `.lake/blueprint/`.

For a focused hgraph preview, run
`.lake/blueprint-env/bin/python scripts/build-site.py --out .lake/hgraph-preview`.
Add `--verbose` to show all hgraph warnings.

## Editing

- Mathematical exposition, sources and Lean bindings: [blueprint/](blueprint/content.tex).
- Website title, project card and navigation: [config.yaml](config.yaml).
- Blueprint and Lean paths and graph settings: [site/projects/Kervaire126/config.yaml](site/projects/Kervaire126/config.yaml).
- Page content, Proof Map and media: [site/](site/).

Keep mathematical statements, hypotheses, citations and Lean bindings consistent.
Run `lake build` after Lean changes and rebuild the website after presentation changes.

The finite calculation supplement is generated from
[the 200-row SS input table](KIP126/SSComputation/Table/Data.lean).
Moore coordinates are bottom-cell images of sphere basis vectors.
The [direct d₂ records](KIP126/AdamsComputation/Table/D2.lean) and
[staircase inputs](KIP126/SSComputation/Table/Archive.lean) have separate tables.
