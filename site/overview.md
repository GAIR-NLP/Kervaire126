## The last Kervaire invariant problem

The last Kervaire invariant problem asks whether a smooth framed manifold
of Kervaire invariant one exists in dimension 126. Following Lin, Wang
and Xu's [*On the Last Kervaire Invariant Problem*](https://arxiv.org/abs/2412.10879v2),
the Lean library formalizes the argument through the nonzero permanent
survival of the class $h_6^2$ in the sphere Adams spectral sequence and
its geometric consequences.

The library covers spectral sequences and their representatives,
differentials, convergence and extension relations; classical and synthetic
homotopy theory; and the generalized Leibniz rule and Mahowald trick.
Its main theorem derives the permanence of $h_6^2$ and the dimension-126
existence theorem from the stated inputs.

The original proof combines theoretical arguments with programs that
compute Adams second pages and derive differential and extension relations.
The Lean statements identify the algebraic data, computational inputs and
literature results used by the argument. The Lean sources contain `sorry`
placeholders for foundational constructions, comparisons and
finite-computation certifications.

[Read the Blueprint](#/Kervaire126)
