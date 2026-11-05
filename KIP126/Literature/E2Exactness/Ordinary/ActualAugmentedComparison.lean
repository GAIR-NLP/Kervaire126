module
import all KIP126.Literature.E2Exactness.Ordinary.AugmentedComparison
import all KIP126.Literature.E2Exactness.Ordinary.FixedTensorComplex
import all KIP126.Literature.E2Exactness.Ordinary.E2MapComparison
import all KIP126.Literature.E2Exactness.Ordinary.HomotopyComplex
import all KIP126.Literature.E2Exactness.Ordinary.RelativeHomExactness

namespace KIP126.Literature.Standard.E2AugmentedComparison
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Completed
open KIP126.Literature.Standard.FixedTensorE2
open KIP126.Literature.Standard.ShiftedResolutionExact
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem actual_shiftedLayerComplex_negative {X : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X) (s : ℤ) (hs : s < 0) :
    IsZero ((shiftedLayerComplex T).X s) :=
  (shiftFunctor Spectrum s).map_isZero (E2MapComparison.layer_negative_isZero T s hs)

/-- Any two original shifted-layer cochain maps preserving the same augmentation
induce the same homology maps, for the fixed actual coefficient spectrum. -/
private theorem actual_homotopyCochain_homologyMap_eq {X Y : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X) (U : AbstractAdamsTower coefficients.unit Y)
    (φ ψ : shiftedLayerComplex T ⟶ shiftedLayerComplex U)
    (haug : (shiftFunctor Spectrum (0:ℤ)).map
        (HasFunctorialCofiber.cofibι (T.mapAt (show (0:ℤ) ≤ 0+1 by omega))) ≫ φ.f 0 =
      (shiftFunctor Spectrum (0:ℤ)).map
        (HasFunctorialCofiber.cofibι (T.mapAt (show (0:ℤ) ≤ 0+1 by omega))) ≫ ψ.f 0)
    (t s : ℤ) :
    HomologicalComplex.homologyMap (homotopyCochainMap φ t) s =
      HomologicalComplex.homologyMap (homotopyCochainMap ψ t) s := by
  apply mapped_homologyMap_eq φ ψ (shiftedInclusion T 0) haug
    ?_ ?_ (actual_shiftedLayerComplex_negative T) (homotopyModuleFunctor t) s
  · intro e he
    obtain ⟨q,hq⟩ := relative_exact_zero T U 0 0 e he
    exact ⟨q, by erw [shiftedLayerComplex_d]; exact hq⟩
  · intro n e he
    rw [shiftedLayerComplex_d] at he
    obtain ⟨q,hq⟩ := relative_exact_succ T U (n:ℤ) ((n:ℤ)+1) ((n:ℤ)+1) (by omega) e he
    exact ⟨q, by erw [shiftedLayerComplex_d]; exact hq⟩


end
end KIP126.Literature.Standard.E2AugmentedComparison
