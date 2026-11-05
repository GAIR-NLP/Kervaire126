module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.ZMod.Basic

/-! The eight archived one-line coordinates used by the project.
These are finite E₂ input data, not Milnor cocycles. The identifiers, names
and degrees refer to the complete archive in AdamsComputation. Comparison
with the actual Adams page is separate from these archive coordinates. -/

@[expose] section
namespace KIP126.AdamsSynthetic.SphereData

/-- Exactly h₀ through h₇; there is no definition of an out-of-range class. -/
public abbrev Index := Fin 8

/-- Original generator row, archived name, filtration and internal degree. -/
public def record : Index → ℕ × String × ℕ × ℕ
  | ⟨0, _⟩ => (0, "h_0", 1, 1)
  | ⟨1, _⟩ => (1, "h_1", 1, 2)
  | ⟨2, _⟩ => (2, "h_2", 1, 4)
  | ⟨3, _⟩ => (3, "h_3", 1, 8)
  | ⟨4, _⟩ => (7, "h_4", 1, 16)
  | ⟨5, _⟩ => (18, "h_5", 1, 32)
  | ⟨6, _⟩ => (69, "h_6", 1, 64)
  | ⟨7, _⟩ => (324, "h_7", 1, 128)

/-- The singleton coordinate module of the archived one-line basis. -/
public abbrev Component (_i : Index) := Fin 1 →₀ ZMod 2

/-- The archived generator is the basis vector at its sole coordinate. -/
public noncomputable def generator (i : Index) : Component i := Finsupp.single 0 1

public theorem generator_ne_zero (i : Index) : generator i ≠ 0 := by
  intro h
  have h := congrArg (fun f : Component i => f 0) h
  simpa [generator] using h

end KIP126.AdamsSynthetic.SphereData
