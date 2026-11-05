module

import all KIP126.Main.Internal.Moore.Reduction

/-! Independence of the h₀ product from the sixth-quotient representative. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Core.Algebra KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.Main.Internal KIP126.Main.Internal.AlphaOne KIP126.Main.Internal.Selected
open KIP126.Computation.Table
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- All three target basis vectors are boundaries by the fifth differential.
Only the two listed d₃ rows and the listed d₅ row are used. -/
private theorem sixth_h0_target_top_quotient :
    Subsingleton (CycleQuotient 1 6 (12,135)) := by
  let E := Normalized.sphere
  let B := boundaries 6 (12,135)
  have z0 : RepresentsOnPage E 7 (12,135) (Normalized.basis .sphere 12 135 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide)
      stem123_weight130_finite_quotients_d3_s9_t133_basis1_add_basis2
  have z12 : RepresentsOnPage E 7 (12,135)
      (Normalized.basis .sphere 12 135 1+Normalized.basis .sphere 12 135 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide)
      stem123_weight130_finite_quotients_d3_s9_t133_basis0_add_basis2
  have z2 : RepresentsOnPage E 7 (12,135) (Normalized.basis .sphere 12 135 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤5; omega) (by decide)
      stem123_weight130_finite_quotients_d5_s7_t131_basis1
  have b0 : Normalized.basis .sphere 12 135 0∈B :=
    stem123_weight130_finite_quotients_boundary_of_zero_representative (r := 7) (p := (12,135)) z0
  have b12 : Normalized.basis .sphere 12 135 1+Normalized.basis .sphere 12 135 2∈B :=
    stem123_weight130_finite_quotients_boundary_of_zero_representative (r := 7) (p := (12,135)) z12
  have b2 : Normalized.basis .sphere 12 135 2∈B :=
    stem123_weight130_finite_quotients_boundary_of_zero_representative (r := 7) (p := (12,135)) z2
  have b1 : Normalized.basis .sphere 12 135 1∈B := by
    simpa only [add_sub_cancel_right] using B.sub_mem b12 b2
  obtain ⟨e,he⟩ := Normalized.basis_correct
    ⟨.sphere,12,135,["408,1","0,1,386,1","0,2,69,1,80,1"]⟩
    (List.mem_of_getElem? (i := 199) rfl)
  change E.Page 2 (12,135) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1)=Normalized.basis .sphere 12 135 i.val at he
  apply stem123_weight130_finite_quotients_cycle_quotient_zero_of_le
  intro x _
  apply stem123_weight130_finite_quotients_basis_mem_submodule e B _ x
  intro i
  rw [he i]
  fin_cases i
  · exact b0
  · exact b1
  · exact b2

/-- The possible top filtration in the h₀ target vanishes; the remaining
filtrations lie outside the sixth-quotient window. -/
private theorem sixth_h0_target_filtration_twelve_zero
    (a : BiHom 123 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 6))
    (ha : FiltrationAtLeast background.syntheticTower 12 a) : a=0 := by
  apply sphere_quotient_high_filtration_zero 6 (by decide) 123 130 13 (by decide) a
  apply (filtration_iff_of_infinity_zero (background.convergence (.quotient 6 .sphere))
    12 13 123 130 (by decide) ?_ a).mp ha
  intro j hj hj'
  have hjeq : j=12 := by omega
  subst j
  haveI : Subsingleton (KIP126.Literature.CycleQuotient background .sphere
      (6-(123+12)+130) (1+(123+12)-130) (12,123+12)) :=
    quotient_vanishing_actual _ _ _ sixth_h0_target_top_quotient
  let e := KIP126.Literature.Standard.infinityFiniteWindow .sphere 6 (by decide)
    (12,123+12) 130 (by decide)
  haveI : Subsingleton (((background.family.quotient
      (background.nu.functor.obj SphereSpectrum) 6).sequence.ssData (12,123+12,130)).eInfty) :=
    e.injective.subsingleton
  let hn := ModuleCat.isZero_of_subsingleton
    (((background.family.quotient (background.nu.functor.obj SphereSpectrum) 6).sequence.ssData
      (12,123+12,130)).eInfty)
  let f := (background.family.functor.map
    (XModLambdaN.map background.nu.unitIso.hom 6)).eInftyMap (12,123+12,130)
  let g := (background.family.functor.map
    (XModLambdaN.map background.nu.unitIso.inv 6)).eInftyMap (12,123+12,130)
  have hfg : g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
      ←background.quotients.functoriality.map_comp,background.nu.unitIso.inv_hom_id,
      background.quotients.functoriality.map_id,CategoryTheory.Functor.map_id,
      SpectralSequenceMorphism.eInftyMap_id]
  apply (IsZero.iff_id_eq_zero _).mpr
  exact hfg.symm.trans (by rw [hn.eq_of_src f 0,comp_zero])

/-- Multiplication by h₀ kills every sixth-quotient source of filtration ten. -/
private theorem sixth_h0_zero_of_filtration_ten
    (a : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 6))
    (ha : FiltrationAtLeast background.syntheticTower 10 a) :
    sphereAction KIP126.Literature.Standard.syntheticH0 a=0 := by
  have ha11 := (SixthQuotient.six_source_filtration_gap a).mp ha
  have hh0 := background.sphereDetectionCompatible.homotopy_lambda 1 1 0
    KIP126.Literature.Standard.syntheticH0
  rw [sphere_lambda_zero_h0] at hh0
  have hf0 := detects_implies_filtration (background.convergence .sphere)
    (1,1,1) _ _ hh0
  exact sixth_h0_target_filtration_twelve_zero _
    (KIP126.Literature.Standard.action_filtration (.quotient 6 .sphere)
      0 1 123 129 1 11 KIP126.Literature.Standard.syntheticH0 a hf0 ha11)

/-- Equal leading labels give equal h₀ products. -/
private theorem sixth_h0_eq_of_difference_filtration_ten
    (a b : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 6))
    (hab : FiltrationAtLeast background.syntheticTower 10 (a-b)) :
    sphereAction KIP126.Literature.Standard.syntheticH0 a=
      sphereAction KIP126.Literature.Standard.syntheticH0 b := by
  apply sub_eq_zero.mp
  have h := sixth_h0_zero_of_filtration_ten (a-b) hab
  simpa only [sphereAction,Preadditive.comp_sub] using h

private theorem sixth_h0_eq_of_same_detection
    (x : background.classical.sphere.Page 2 (9,132))
    (a b : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 6))
    (ha : Detects (background.convergence (.quotient 6 .sphere)) (9,132,129)
      (quotientLabel 6 9 132 3 x) a)
    (hb : Detects (background.convergence (.quotient 6 .sphere)) (9,132,129)
      (quotientLabel 6 9 132 3 x) b) :
    sphereAction KIP126.Literature.Standard.syntheticH0 a=
      sphereAction KIP126.Literature.Standard.syntheticH0 b :=
  sixth_h0_eq_of_difference_filtration_ten a b
    (detects_sub_filtration (background.convergence (.quotient 6 .sphere))
      (9,132,129) ha hb)

end
end KIP126.Main.Internal.Moore
end
