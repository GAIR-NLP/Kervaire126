module
import all KIP126.Literature.BocksteinNuTriangles
import KIP126.Literature.Standard
/-! The triangle-lift theorem on every positive actual Adams interval. -/

@[expose] section
namespace KIP126.Literature.Standard.Internal.LiftedAdamsTriangles
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Completed KIP126.Kervaire.Route
open KIP126.Literature.Standard.Internal.NuRelativeTriangles
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem zero_homology_filtration_one {X Y : Spectrum} (f : X ⟶ Y)
    (hf : ZeroOnModTwoHomology coefficients f) :
    MapFiltrationAtLeast classicalTower f 1 := by
  apply (factorization_filtration_iff f 1).mp
  intro n hn hn1
  have hn' : n=1 := by omega
  subst n
  exact AdamsMapFactorization.single f hf

/-- The specified triangle_lift applies to every positive actual
classical Adams interval, including its signed suspended composite. -/
private theorem exists_actual_relative_triangle_lift (X : Spectrum)
    {s t : ℕ} (hst : s<t) :
    let T := classicalTower.tower X
    let f := T.map (Nat.le_of_lt hst)
    let R := (Triangle.mk f (HasFunctorialCofiber.cofibι f)
      (HasFunctorialCofiber.cofibδ f)).rotate
    ∃ L : SyntheticTriangleLift background R, L.FullLiftComparison background := by
  let T := classicalTower.tower X
  let f := T.map (Nat.le_of_lt hst)
  let U := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hU : U ∈ distTriang Spectrum := HasFunctorialCofiber.cofib_distinguished f
  have hf : ZeroOnModTwoHomology coefficients f := composite_zero_homology T hst
  have hrot : ZeroOnModTwoHomology coefficients U.rotate.mor₃ :=
    zero_on_homology_neg _ (zero_on_homology_shift f 1 hf)
  exact triangle_lift U.rotate (rot_of_distTriang U hU)
    (zero_homology_filtration_one _ hrot) (hzero_rotated_short_exact U hU hf)

end
end KIP126.Literature.Standard.Internal.LiftedAdamsTriangles
