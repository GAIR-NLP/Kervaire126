module

public import KIP126.SpectralSequence.Computation.Predicates
import all KIP126.SpectralSequence.Computation.Predicates

@[expose] section

/-!
# Mathematical state predicates for computation interfaces

These predicates use the internal spectral sequence and its common
representatives. Permanent-cycle membership allows a zero E∞ class.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v

variable {R : Type u} [Ring R]

/-- The E₂ label has a representative, possibly zero, on the specified page. -/
public def ReachesPage
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) (p : ℤ × ℤ) (x : E.Page 2 p) : Prop :=
  ∃ xr : E.Page r p, RepresentsOnPage E r p x xr

/-- The E₂ label belongs to the cumulative boundary subobject after page `r`,
including zero and sums of earlier boundaries. -/
public def IsBoundaryBy
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) (p : ℤ × ℤ) (x : E.Page 2 p) : Prop :=
  2 ≤ r ∧
    let D := E.ssData p
    let n : WithTop ℕ := ↑(2 - E.r₀).toNat
    let m : WithTop ℕ := ↑(r + 1 - E.r₀).toNat
    ∃ b : (Subobject.underlying.obj (D.B m) : ModuleCat R),
      (Subobject.ofLE (D.B m) (D.B ⊤) (D.B_mono le_top) ≫
        Subobject.ofLE (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) ≫
        Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ D.pageπ n) b = x

/-- The E₂ label has a permanent-cycle representative, with possibly zero E∞ image. -/
public def IsPermanentCycle
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (p : ℤ × ℤ) (x : E.Page 2 p) : Prop :=
  let D := E.ssData p
  let n : WithTop ℕ := ↑(2 - E.r₀).toNat
  ∃ z : (Subobject.underlying.obj (D.Z ⊤) : ModuleCat R),
    (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ D.pageπ n) z = x

/-- The E₂ label belongs to the final boundary subobject, including the zero label. -/
public def IsFinalBoundary
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (p : ℤ × ℤ) (x : E.Page 2 p) : Prop :=
  let D := E.ssData p
  let n : WithTop ℕ := ↑(2 - E.r₀).toNat
  ∃ b : (Subobject.underlying.obj (D.B ⊤) : ModuleCat R),
    (Subobject.ofLE (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) ≫
      Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ D.pageπ n) b = x

/-- On every page in the specified nonempty window, the label has a representative
with zero outgoing differential. Representatives may be zero or incoming boundaries. -/
public def IsCycleOnWindow
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (first last : ℤ) (p : ℤ × ℤ) (x : E.Page 2 p) : Prop :=
  2 ≤ first ∧ first ≤ last ∧
    ∀ r : ℤ, first ≤ r → r ≤ last →
      ∃ xr : E.Page r p, RepresentsOnPage E r p x xr ∧ IsPageCycle E r p xr

/-- The label has a nonzero continuation on every page in the specified nonempty
window. -/
public def SurvivesOnWindow
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (first last : ℤ) (p : ℤ × ℤ) (x : E.Page 2 p) : Prop :=
  2 ≤ first ∧ first ≤ last ∧
    ∀ r : ℤ, first ≤ r → r ≤ last → SurvivesTo E r p x

/-- Exclusion of nonzero incoming differentials
in the specified nonempty page window. -/
public def NeverHitOnWindow
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (first last : ℤ) (p : ℤ × ℤ) (x : E.Page 2 p) : Prop :=
  2 ≤ first ∧ first ≤ last ∧
    ∀ r : ℤ, first ≤ r → r ≤ last → ¬ HitOnPage E r p x

/-- Vanishing of every outgoing differential at this bidegree
on every page from E₂ onward, allowing zero pages. -/
public def NoOutgoingAt
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)) (s t : ℤ) : Prop :=
  ∀ r : ℤ, 2 ≤ r → ∀ x : E.Page r (s, t), E.d r (s, t) x = 0

end KIP126.Core.SpectralSequence
