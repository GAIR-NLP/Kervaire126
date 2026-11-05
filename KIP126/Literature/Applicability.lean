module

public import KIP126.AdamsSynthetic

/-! BHS applicability hypotheses for the given Adams tower.
Completeness and separation are required in addition to an E∞ comparison. -/

@[expose] section
namespace KIP126.Literature
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Synthetic.Context
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : AdamsSyntheticBackground C Syn)

/-- Milnor's `1 - shift` map of the residual tower. Its invertibility
expresses vanishing of the sequential homotopy limit, including the
derived-limit term. -/
public def residualOneSubShift (products : HasProductsOfShape ℕ C) (X : C) :
    letI := products
    ∏ᶜ (D.classicalTower.tower X).stage ⟶ ∏ᶜ (D.classicalTower.tower X).stage := by
  letI := products
  let T := D.classicalTower.tower X
  exact 𝟙 _ - Pi.lift (fun n => Pi.π T.stage (n+1) ≫ T.map (Nat.le_succ n))

/-- The exact untruncated BHS applicability conditions, on the same
coefficient tower and actual homotopy filtration. Canonical convergence
is supplied separately by the same object's context. -/
public structure AdamsComparisonApplicability (products : HasProductsOfShape ℕ C)
    (X : C) : Prop where
  nilpotent_complete : letI := products; IsIso (residualOneSubShift D products X)
  complete : ∀ n : ℤ,
    Nonempty (Filtration.CompletionWitness (D.classicalTower.tower X).filtration n)
  separated : ∀ (n : ℤ) (S : Subobject (AbstractAdamsTower.homotopy X n)),
    (∀ s : ℤ, S ≤ (D.classicalTower.tower X).filtration.F s n) → S = ⊥
  associatedGraded : Nonempty (ClassicalTowerConvergence D.classicalTower X)

end
end KIP126.Literature
