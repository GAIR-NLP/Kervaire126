module
import all KIP126.Literature.BocksteinFullLift
import all KIP126.Literature.Standard.FiniteQuotientPositive
/-! Comparison of a sphere representative under the selected-target and
diagonal-weight hypotheses. -/

@[expose] section
namespace KIP126.Literature.Standard.Internal.SelectedConnectingComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Completed KIP126.Kervaire.Route
open KIP126.Literature.Paper38FullLiftComposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Comparison of the prescribed connection and full lift on a common
sphere representative, under the selected-target hypothesis. -/
private theorem connecting_eq_normalized_on_same_sphere
    (T : Triangle Spectrum) (L : SyntheticTriangleLift background T)
    (k : ℕ) (hk : 1≤k) (F : SyntheticFullLift background T.mor₃ k)
    (Y : AdamsObject (coefficients := background.coefficients))
    (eY : background.nu.functor.obj (T.obj₁⟦(1:ℤ)⟧) ≅
      background.nu.functor.obj (Y.obj background.auxiliary))
    (m w : ℤ) (hw : w≤m)
    (a : BiHom m w (background.nu.functor.obj T.obj₃)) :
    a≫L.connecting = a≫F.normalizedMap background hk := by
  let γ := L.connecting - F.normalizedMap background hk
  let W := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  have hγ : γ≫SyntheticCategory.lam.app _=0 :=
    triangleFullLift_difference_lambda_zero background L hk F
  have hz : (a≫γ≫W.map eY.hom)≫SyntheticCategory.lam.app _=0 := by
    rw [Category.assoc, Category.assoc, SyntheticCategory.lam.naturality]
    change a≫γ≫SyntheticCategory.lam.app _≫eY.hom=0
    rw [←Category.assoc γ, hγ, zero_comp, comp_zero]
  have h0 : a≫γ≫W.map eY.hom=0 :=
    positive_lambda_one_injective_at_diagonal Y m w hw _ hz
  have h0' : a≫γ=0 := (cancel_mono (W.map eY.hom)).mp
    (by simpa only [Category.assoc, zero_comp] using h0)
  change a≫(L.connecting-F.normalizedMap background hk)=0 at h0'
  rw [Preadditive.comp_sub] at h0'
  exact sub_eq_zero.mp h0'

end
end KIP126.Literature.Standard.Internal.SelectedConnectingComparison
