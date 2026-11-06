<h1 align="center">Kervaire126</h1>

<p align="center">SII-Kervaire126</p>

<p align="center">
  <a href="https://gair-nlp.github.io/Kervaire126/#/Kervaire126"><img src="https://img.shields.io/badge/Blueprint-Read-0969da?style=flat-square" alt="Blueprint: Read"></a>
  <a href="LICENSE"><img src="https://img.shields.io/badge/License-Apache%202.0-yellow?style=flat-square" alt="License: Apache 2.0"></a>
  <a href="https://github.com/leanprover/lean4/releases/tag/v4.32.2"><img src="https://img.shields.io/badge/Lean-v4.32.2-6f42c1?style=flat-square" alt="Lean: v4.32.2"></a>
  <a href="https://github.com/leanprover-community/mathlib4/tree/905b95818eb32af7874a58b427f50c1711a5e96c"><img src="https://img.shields.io/badge/Mathlib-905b958-0969da?style=flat-square" alt="Mathlib: 905b958"></a>
</p>

<p align="center">
  A Lean 4 and Mathlib formalization of<br>
  Weinan Lin, Guozhen Wang and Zhouli Xu's
  <a href="https://arxiv.org/abs/2412.10879v2"><i>On the Last Kervaire Invariant Problem</i></a>.
</p>

**Project blog coming soon.**

**Formalization status:** Foundational constructions, comparisons and
computational certifications include `sorry` placeholders.

## Mathematics and scope

The main argument establishes nonzero permanent survival of $h_6^2$ in the
sphere Adams spectral sequence. Together with Browder's criterion and the
specified classical inputs, it yields Kervaire invariant one in dimension 126
and the dimension list $2,6,14,30,62,126$.

The [permanence theorem](KIP126/Main/H6SquarePermanent.lean) and
[geometric conclusions](KIP126/Geometry/Kervaire.lean) combine specified
foundational models, comparison maps, computational inputs and literature
results in Lean. The website graph connects mathematical statements with
Lean declarations, source annotations and proof dependencies.

## Repository structure

```text
KIP126/       Lean library: eight mathematical modules
blueprint/    Mathematical exposition, references and Lean bindings
site/         hgraph content, project settings and assets
config.yaml   Website manifest
AimPaper/     Paper sources, original PDF and erratum
scripts/      Mathematical Blueprint website build tools
```

Use `import KIP126` for the full library or `import KIP126.<Module>` for one module.

## Build

Install [elan](https://github.com/leanprover/elan). The project pins Lean
**v4.32.2** in [lean-toolchain](lean-toolchain) and its dependencies in
[lake-manifest.json](lake-manifest.json). From the repository root:

```sh
lake exe cache get
lake build
```

The [project website](https://gair-nlp.github.io/Kervaire126/) provides the
mathematical Blueprint at `#/Kervaire126`. For
dependencies, the website build and local preview, see the
[contributing guide](CONTRIBUTING.md).

## Authors and contributions

- **Mathematical guidance:** Guozhen Wang and Weinan Lin.
- **AI guidance:** Pengfei Liu.
- **Project development and formalization:** Jiashuo Zhang and Kangjie Bao.

## Acknowledgements

We would like to express our sincere thanks to Ruisong Yuan and
Qifan Pan for their valuable mathematical discussions related to
this project. We greatly appreciate the time they devoted to these
discussions and the mathematical insights they shared with us.

## License

[Apache License 2.0](LICENSE). Copyright (c) 2026 SII-Kervaire126.
