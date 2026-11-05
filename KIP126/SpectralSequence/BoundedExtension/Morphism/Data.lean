module

import all KIP126.SpectralSequence.FilteredComplex.SSData.Proofs

@[expose] section

/-!
# Filtered-complex morphism accessors

`FilteredComplexMorphism` is an abbreviation for the canonical
`FilteredComplex.Morphism`. Its accessors use the same category structure
on filtered complexes.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Compatibility name for Kervaire126's canonical filtration-preserving chain
map. -/
abbrev FilteredComplexMorphism (FC₁ FC₂ : FilteredComplex C) :=
  FilteredComplex.Morphism FC₁ FC₂

namespace FilteredComplexMorphism

/-- Degreewise-map accessor. -/
@[reducible] def f {FC₁ FC₂ : FilteredComplex C}
    (g : FilteredComplexMorphism FC₁ FC₂) (k : ℤ) :
    FC₁.A k ⟶ FC₂.A k :=
  g.map.f k

/-- The map induced on an associated-graded piece. -/
noncomputable def assocGradedMap
    {FC₁ FC₂ : FilteredComplex C} (g : FilteredComplexMorphism FC₁ FC₂)
    (s k : ℤ) : FC₁.assocGraded s k ⟶ FC₂.assocGraded s k :=
  g.associatedGradedMap s k

end FilteredComplexMorphism

end KIP126.Core.SpectralSequence
