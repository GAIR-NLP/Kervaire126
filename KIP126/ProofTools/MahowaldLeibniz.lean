module

public import KIP126.ProofTools.Language

/-!
# Mahowald--Leibniz composition under finite-layer surjectivity

These definitions specify Mahowald--Leibniz composition under finite-layer surjectivity
in the fixed model.
The E₂ connecting operation is constructed from the selected normalized
map on the first λ quotient. Its exactness uses the same normalized
triangle and the selected Adams suspension comparison.
-/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Completed KIP126.Kervaire.Route
open KIP126.Literature
noncomputable section

/-- The E₂ connecting operation of the selected normalized f with e(f)=1,
constructed on the first λ quotient with bidegree (1,1). The ordinary E₂
page map of f has bidegree (0,0); the normalized operation below retains
the specified positive weight shift. -/
public def cofiberFirstQuotientBoundary
    (T : TriangleData background.auxiliary)
    (hef : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ) (x : Ambient background T.X (s,t)) :
    Ambient background T.Y (s+1,t+1) :=
  let F : (SyntheticCategory.biShift (Syn := SyntheticSpectrum) (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary)) ⟶
      background.nu.functor.obj (T.Y.obj background.auxiliary) := by
    simpa only [hef, Nat.cast_one] using (background.normalizedMap T.X T.Y T.f).map
  let a := (background.firstQuotient T.X 1 s t).symm x
  let b := a ≫ XModLambdaN.map F 1 ≫
    XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app
      (background.nu.functor.obj (T.Y.obj background.auxiliary))) 1
  background.firstQuotient T.Y 0 (s+1) (t+1)
    (homotopyRegrade (by omega) (by omega) b)

/-- The finite-layer surjectivity condition for Mahowald--Leibniz composition,
using the actual h page
map and the fixed tower suspension comparison. All boundary denominators
are R+j-1, including the final j=K-1 layer. -/
public def MahowaldLeibnizFiniteLayerSurjectivity
    (T : TriangleData background.auxiliary) (R K : ℕ) (s t : ℤ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j < K →
    ∀ a : Ambient background T.X (s+R+j,t+R+j-1),
      IsCycle background T.X ((K:ℤ)-j) _ a →
      ∃ z : Ambient background T.Z (s+R+j,t+R+j),
        IsCycle background T.Z ((K:ℤ)-j) _ z ∧
        ∃ b : Ambient background T.X (s+R+j,t+R+j-1),
          (background.classicalSuspension T.X).DesuspendsClass (s+R+j) (t+R+j)
            ((background.classical.functor.map T.h).pageMap 2 (s+R+j,t+R+j) z) b ∧
          Congruent background T.X ((R:ℤ)+j-1) _ a b

/-- The Mahowald–Leibniz composition proposition under finite-layer
surjectivity, including `y = 0`. It uses the first-quotient boundary of the
normalized distinguished triangle from Proposition 3.20 and ranges over
the classical object family. -/
public def FiniteLayerSurjectivityMahowaldLeibnizStatement
    (T : TriangleData background.auxiliary)
    (hef : normalizedExponent background.classicalTower T.f = 1)
    (heg : normalizedExponent background.classicalTower T.g = 0)
    (heh : normalizedExponent background.classicalTower T.h = 0) : Prop :=
  ∀ (R K : ℕ), 2 ≤ R → 2 ≤ K → ∀ (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (z : Ambient background T.Z (s+R,t+R))
    (v : Ambient background T.Y (s+R+K,t+R+K-1)),
    IsCycle background T.X ((R:ℤ)-1) _ x →
    IsCycle background T.Z ((K:ℤ)-1) _ z →
    (∃ u : Ambient background T.X (s+R,t+R-1),
      (background.classicalSuspension T.X).DesuspendsClass (s+R) (t+R)
        ((background.classical.functor.map T.h).pageMap 2 (s+R,t+R) z) u ∧
      DifferentialAt background T.X R (s,t) (s+R,t+R-1) x u) →
    DifferentialAt background T.Z K (s+R,t+R) (s+R+K,t+R+K-1) z
      ((background.classical.functor.map T.g).pageMap 2 (s+R+K,t+R+K-1) v) →
    MahowaldLeibnizFiniteLayerSurjectivity T R K s t →
    let y := cofiberFirstQuotientBoundary T hef s t x
    IsCycle background T.Y ((R:ℤ)+K-2) (s+1,t+1) y ∧
    DifferentialAt background T.Y ((R:ℤ)+K-1)
      (s+1,t+1) (s+R+K,t+R+K-1) y v

end
end KIP126.ProofTools.Standard
