module

import all KIP126.SpectralSequence.FilteredComplex.Data
import all KIP126.SpectralSequence.Internal.Algebra.Completion.Data

@[expose] section

/-!
# Bounded extension spectral sequences

The bounded two-term filtered-complex construction uses the canonical
`FilteredComplex` structure. Endpoint and convergence witnesses are supplied
by the endpoint construction.
-/

namespace KIP126.Core.SpectralSequence.BoundedExtension

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [CategoryTheory.Category.{v} C] [Abelian C]

/-! ### Two-term complex helpers

These two-term constructions are independent of the spectral-sequence
adapter and use the canonical `FilteredComplex` representation. -/

/-- The graded object supported in degrees `1` and `0`. -/
noncomputable def twoTermObj (X₁ X₂ : C) : ℤ → C := fun k =>
  if k = 1 then X₁ else if k = 0 then X₂ else ⊥_ C

/-- The only potentially nonzero differential is the map `X₁ ⟶ X₂`. -/
noncomputable def twoTermDiff (X₁ X₂ : C) (f : X₁ ⟶ X₂) (k : ℤ) :
    twoTermObj X₁ X₂ k ⟶ twoTermObj X₁ X₂ (k - 1) :=
  if h : k = 1 then
    eqToHom (show twoTermObj X₁ X₂ k = X₁ by simp [twoTermObj, h]) ≫ f ≫
      eqToHom (show X₂ = twoTermObj X₁ X₂ (k - 1) by simp [twoTermObj, h])
  else 0

/-- A two-term decreasing filtration, with the zero support degrees unconstrained. -/
noncomputable def twoTermFil {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) :
    ℤ → (k : ℤ) → Subobject (twoTermObj X₁ X₂ k) := fun s k =>
  if h₁ : k = 1 then h₁ ▸ fil₁ s
  else if h₀ : k = 0 then h₀ ▸ fil₂ s
  else ⊤

end KIP126.Core.SpectralSequence.BoundedExtension
