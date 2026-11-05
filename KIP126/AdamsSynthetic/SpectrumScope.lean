module

public import KIP126.AdamsSynthetic.Context

/-! Object conditions in the ambient HF₂-local category. -/
@[expose] section
namespace KIP126.AdamsSynthetic
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]

/-- A spectrum has no negative stable homotopy groups. -/
public def IsConnective (X : C) : Prop :=
  ∀ n : ℤ, n < 0 → Subsingleton (HomotopyGroup n X)

/-- A spectrum has a lower bound on its nonzero stable homotopy groups. -/
public def IsBoundedBelow (X : C) : Prop :=
  ∃ b : ℤ, ∀ n : ℤ, n < b → Subsingleton (HomotopyGroup n X)

/-- Finite-dimensional HF₂ homology in each degree. -/
public def IsFiniteModTwoType (H : ModTwoCoefficients C) (X : C) : Prop :=
  ∀ n : ℤ, Finite (HomotopyGroup n (H.object ⊗ X))

/-- The suspension-stable range of the Adams tools. -/
public def IsBoundedBelowFiniteModTwoType (H : ModTwoCoefficients C) (X : C) : Prop :=
  IsBoundedBelow X ∧ IsFiniteModTwoType H X

public theorem IsConnective.isBoundedBelow {X : C} (hX : IsConnective X) : IsBoundedBelow X :=
  ⟨0, hX⟩
end KIP126.AdamsSynthetic
