module
public import KIP126.Literature.Standard.Filtration
import all KIP126.Main.Internal.High125.Filtration
/-! The BMQ product, multiplicative detection and higher-filtration tail
on the fixed system. The specified tmf image uses the non-odd-torsion
conclusion for the same unit map. -/
@[expose] section
namespace KIP126.Main.Internal.High125
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.Literature
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum Spectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem odd_postcompose {X Y Z : Spectrum} (a : X ⟶ Y) (f : Y ⟶ Z)
    (ha : IsOddTorsionMap a) : IsOddTorsionMap (a≫f) := by
  obtain ⟨n,hn,hp,hz⟩ := ha
  refine ⟨n,hn,hp,?_⟩
  rw [←Preadditive.nsmul_comp,hz,zero_comp]

private theorem odd_neg {X Y : Spectrum} (a : X ⟶ Y)
    (ha : IsOddTorsionMap (-a)) : IsOddTorsionMap a := by
  obtain ⟨n,hn,hp,hz⟩ := ha
  refine ⟨n,hn,hp,?_⟩
  simpa only [smul_neg,neg_eq_zero] using hz

theorem source_high_detected : ClassicalDetects (background.classicalConvergence .sphere) (25,150)
    KIP126.Computation.Standard.highClass Standard.high125 := by
  have hk := Standard.kappaBar_detection
  have hw := Standard.w_detection
  have hk2 := Standard.classical_product_detection 4 24 4 24 Standard.g Standard.g
    Standard.kappaBar Standard.kappaBar hk hk
  norm_num at hk2
  have hk4 := Standard.classical_product_detection 8 48 8 48 _ _ _ _ hk2 hk2
  norm_num at hk4
  have hprod := Standard.classical_product_detection 16 96 9 54 _ _ _ _ hk4 hw
  norm_num at hprod
  simpa [KIP126.Computation.Standard.highClass,KIP126.Computation.Standard.product,
    KIP126.Computation.Standard.g_agrees,KIP126.Computation.Standard.delta_agrees,
    eqToHom_refl,ModuleCat.id_apply,LinearMap.id_apply,Category.id_comp,Standard.high125,Standard.classicalSphereProduct] using hprod

theorem high_nonzero_survival : NonzeroSurvival background.classical.sphere (25,150)
    KIP126.Computation.Standard.highClass := by
  obtain ⟨z,hz,a,ha,hgrade⟩ := source_high_detected
  refine ⟨z,hz,?_⟩
  intro hzero
  let F := (background.classicalTower.tower SphereSpectrum).filtration
  have hg : F.toAssociatedGraded 25 (150-25) a=0 := by
    erw [←hgrade,hzero,map_zero]
  have hm := (F.toAssociatedGraded_eq_zero_iff 25 (150-25) a).mp hg
  erw [ha] at hm
  have hm' : Standard.high125 ∈
      (background.classicalTower.tower SphereSpectrum).filtrationSubmodule 26 125 := by
    simpa [F,AbstractAdamsTower.filtration,AbstractAdamsTower.homotopy,OrderIso.apply_symm_apply] using hm
  exact Standard.tmf_high125_nonzero (odd_postcompose Standard.high125 Standard.tmfUnit
    (classical_filtration26_odd_torsion Standard.high125 hm'))


end
end KIP126.Main.Internal.High125
