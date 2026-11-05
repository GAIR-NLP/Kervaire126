module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Field.ZMod

@[expose] section

/-!
# Mod-two coefficient conventions

These aliases name the field `ZMod 2` and its category of modules, used for
Adams spectral sequences.
-/

namespace KIP126.Core.Algebra

/-- The project's mod--2 coefficient field. -/
public abbrev F2 := ZMod 2

/-- The abelian category of modules over the project's mod--2 coefficient field. -/
abbrev F2ModuleCat := ModuleCat F2

end KIP126.Core.Algebra
