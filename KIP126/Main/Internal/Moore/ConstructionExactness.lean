module

import all KIP126.Main.Internal.Moore.ConstructionAnnihilation
import all KIP126.Main.Internal.Moore.ConstructionCrossing
import all KIP126.Main.Internal.Moore.ConstructionSourceDetection

/-! The short exactness route to the Moore top image.  Vanishing of the
actual second-quotient top image forces the source into filtration nine.
The source calculation and the normalized quotient row are kept explicit. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.Main.Internal KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

private theorem moore_sphere_second_source_filtration
    (hZ : cycles background .sphere 2 (8,132)=⊥)
    (a : BiHom 124 132 (XModLambdaN (background.nu.functor.obj SphereSpectrum) 2)) :
    FiltrationAtLeast background.syntheticTower 9 a := by
  let f := XModLambdaN.map background.nu.unitIso.hom 2
  let g := XModLambdaN.map background.nu.unitIso.inv 2
  have hfg : f ≫ g=𝟙 _ := by
    dsimp only [f,g]
    rw [←background.quotients.functoriality.map_comp,Iso.hom_inv_id,
      background.quotients.functoriality.map_id]
  have haf : FiltrationAtLeast background.syntheticTower 8 a :=
    finite_bottom_filtration .sphere 2 (by decide) 8 132 a
  have hs := map_preserves_filtration (background.convergentMap
    (.quotient 2 (.nu .sphere)) (.quotient 2 .sphere) f) (124,132) 8 a haf
  obtain ⟨x,hx,hd⟩ := finite_sphere_filtration_has_cycle_label
    2 0 (by decide) (by decide) 8 132 (a≫f) hs
  have hx0 : x=0 := by
    change x∈cycles background .sphere 2 (8,132) at hx
    rw [hZ,Submodule.mem_bot] at hx
    exact hx
  have hl : quotientLabel 2 8 132 0 x=0 := by
    rw [hx0]
    simp only [quotientLabel,sphereLabel,map_zero]
  rw [hl] at hd
  have hs9 := detects_zero_filtration (background.convergence (.quotient 2 .sphere))
    (8,132,132) hd
  have hm := map_preserves_filtration (background.convergentMap
    (.quotient 2 .sphere) (.quotient 2 (.nu .sphere)) g) (124,132) 9 (a≫f) hs9
  change FiltrationAtLeast background.syntheticTower 9 ((a≫f)≫g) at hm
  simpa only [Category.assoc,hfg,Category.comp_id] using hm

/-- Exactness uses the actual normalized quotient maps.  Its lift is a
sphere source whose entire filtration-eight grade vanishes. -/
private theorem moore_second_top_zero_source_filtration
    (hZ : cycles background .sphere 2 (8,132)=⊥)
    (a : BiHom 124 132
      (XModLambdaN (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 2))
    (ha : a ≫ XModLambdaN.map
      (background.nu.functor.map KIP126.AdamsComputation.Moore.top) 2 = 0) :
    FiltrationAtLeast background.syntheticTower 9 a := by
  let Q := background.quotients.functoriality.functor 2
  let eC := Q.mapIso mooreNormalizedSourceIso
  let eS := Q.mapIso ((shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso mooreNormalizedFirstIso)
  let an := a ≫ eC.inv
  have htop : an ≫ XModLambdaN.map mooreNormalizedTriangle.mor₃ 2 = 0 := by
    apply (cancel_mono eS.hom).mp
    have hsq := congrArg (fun f => Q.map f) moore_normalized_connecting_square
    simp only [Q.map_comp] at hsq
    change XModLambdaN.map mooreNormalizedTriangle.mor₃ 2 ≫ eS.hom =
      eC.hom ≫ XModLambdaN.map (background.nu.functor.map KIP126.AdamsComputation.Moore.top) 2 ≫
        XModLambdaN.map mooreTopLandingIso.hom 2 at hsq
    dsimp only [an]
    rw [Category.assoc,hsq]
    simp only [Category.assoc,Iso.inv_hom_id_assoc,zero_comp]
    rw [←Category.assoc,ha,zero_comp]
  obtain ⟨es,hes,hrow⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    KIP126.AdamsComputation.Moore.triangle moore_exponent_sum 2 (by decide)
  obtain ⟨b,hb⟩ := (Triangle.mk (XModLambdaN.map mooreNormalizedTriangle.mor₂ 2)
    (XModLambdaN.map mooreNormalizedTriangle.mor₃ 2)
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      mooreNormalizedTriangle.mor₁) 2 ≫ es.hom))).coyoneda_exact₂ hrow an htop
  have hf : FiltrationAtLeast background.syntheticTower 9 b :=
    moore_sphere_second_source_filtration hZ b
  let f := XModLambdaN.map mooreNormalizedTriangle.mor₂ 2 ≫ eC.hom
  have hm := map_preserves_filtration (background.convergentMap (.quotient 2 (.nu .sphere))
    (.quotient 2 (.nu KIP126.AdamsComputation.Moore.adamsObject)) f) (124,132) 9 b hf
  have hba : b ≫ f = a := by
    change an = b ≫ XModLambdaN.map mooreNormalizedTriangle.mor₂ 2 at hb
    dsimp only [f]
    rw [←Category.assoc,←hb]
    simp only [an,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  change FiltrationAtLeast background.syntheticTower 9 (b≫f) at hm
  rwa [hba] at hm

private theorem moore_second_top_zero_source_filtration_actual
    (a : BiHom 124 132
      (XModLambdaN (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 2))
    (ha : a ≫ XModLambdaN.map
      (background.nu.functor.map KIP126.AdamsComputation.Moore.top) 2 = 0) :
    FiltrationAtLeast background.syntheticTower 9 a :=
  moore_second_top_zero_source_filtration SphereCrossing.cycles_two_source_eq_bot a ha

private theorem moore_actual_fourth_detection_of_not_high
    (a : BiHom 123 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 4))
    (ha : FiltrationAtLeast background.syntheticTower 9 a)
    (hn : ¬ FiltrationAtLeast background.syntheticTower 10 a) :
    Detects (background.convergence (.quotient 4 .sphere)) (9,132,131)
      (quotientLabel 4 9 132 1 KIP126.Computation.Standard.V) a := by
  obtain ⟨x,hx,hd⟩ := finite_sphere_filtration_has_cycle_label
    4 1 (by decide) (by decide) 9 132 a ha
  rcases SphereCrossing.cycles_three_cases x hx with hz | he
  · exfalso
    apply hn
    have hl : quotientLabel 4 9 132 1 x = 0 := by
      rw [hz]
      simp only [quotientLabel,sphereLabel,map_zero]
    rw [hl] at hd
    exact detects_zero_filtration (background.convergence (.quotient 4 .sphere))
      (9,132,131) hd
  · rwa [he] at hd

private theorem moore_suspension_preserves_filtration
    (X : SyntheticObject (coefficients := background.coefficients))
    (s m w k l : ℤ) (a : BiHom m w (X.obj background.nu background.auxiliary))
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    FiltrationAtLeast background.syntheticTower s
      (susp_invariance m w k l (X.obj background.nu background.auxiliary) a) := by
  let E := (essShift (k,l)).filtered X (m,w)
  have ham : a ∈ ModuleCat.subobjectModule _
      ((background.convergence X).filtration.F s (m,w)) := by
    simpa only [SyntheticTowerConvergence.filtration,SyntheticTowerPresentation.filtration,
      OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
  obtain ⟨aa,haa⟩ := ham
  have hb : shiftHomotopyClass (k,l) (m,w) a ∈ ModuleCat.subobjectModule _
      ((background.convergence (.shift (k,l) X)).filtration.F s ((m,w)+(k,l))) := by
    refine ⟨(E.level s).hom aa,?_⟩
    exact (ConcreteCategory.congr_hom (E.level_arrow s) aa).trans
      (((essShift (k,l)).ambient_eq X (m,w) _).trans (congrArg _ haa))
  have hb' : FiltrationAtLeast background.syntheticTower s
      (shiftHomotopyClass (k,l) (m,w) a) := by
    simpa only [SyntheticTowerConvergence.filtration,SyntheticTowerPresentation.filtration,
      OrderIso.apply_symm_apply,FiltrationAtLeast,SyntheticObject.obj,syntheticHomotopy,
      Prod.mk_add_mk] using hb
  have he : susp_invariance m w k l (X.obj background.nu background.auxiliary) a =
      shiftHomotopyClass (k,l) (m,w) a := by
    change (SyntheticCategory.biShift_comp (m,w) (k,l)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (k,l)).map a ≫ 𝟙 _ = _
    rw [Category.comp_id]
    rfl
  rwa [he]

/-- A high fourth-quotient top image would vanish after restricting the
literal ν(top) image to the second quotient.  Only the same-quotient
suspension comparison is used. -/
private theorem moore_top_high_second_zero
    (c4 : BiHom 124 132 (XModLambdaN
      (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 4))
    (ha : FiltrationAtLeast background.syntheticTower 10 (mooreTopImage c4)) :
    (c4 ≫ (background.quotients.tower
      (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum)).rho 2 4 (by decide)) ≫
      XModLambdaN.map (background.nu.functor.map KIP126.AdamsComputation.Moore.top) 2 = 0 := by
  have hs := moore_suspension_preserves_filtration (.quotient 4 .sphere)
    10 123 131 1 1 (mooreTopImage c4) ha
  change FiltrationAtLeast background.syntheticTower 10
    (susp_invariance 123 131 1 1 (XModLambdaN (S_0_0 : SyntheticSpectrum) 4)
      (mooreTopImage c4)) at hs
  have he : susp_invariance 123 131 1 1 _ (mooreTopImage c4) =
      c4 ≫ XModLambdaN.map (background.nu.functor.map KIP126.AdamsComputation.Moore.top) 4 ≫
        (mooreNuSuspensionQuotientIso 4).hom := by
    exact (susp_invariance 123 131 1 1 _).apply_symm_apply _
  rw [he] at hs
  have hm := map_preserves_filtration (background.convergentMap
    (.shift (1,1) (.quotient 4 .sphere)) (.quotient 4 (.nu (.shift 1 .sphere)))
    (mooreNuSuspensionQuotientIso 4).inv) (124,132) 10 _ hs
  have hr : FiltrationAtLeast background.syntheticTower 10
      (c4 ≫ XModLambdaN.map (background.nu.functor.map KIP126.AdamsComputation.Moore.top) 4) := by
    change FiltrationAtLeast background.syntheticTower 10
      ((c4 ≫ XModLambdaN.map (background.nu.functor.map KIP126.AdamsComputation.Moore.top) 4 ≫
        (mooreNuSuspensionQuotientIso 4).hom) ≫ (mooreNuSuspensionQuotientIso 4).inv) at hm
    simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id] using hm
  have ht := map_preserves_filtration (background.convergentMap
    (.quotient 4 (.nu (.shift 1 .sphere))) (.quotient 2 (.nu (.shift 1 .sphere)))
    ((background.quotients.tower (background.nu.functor.obj (Sphere 1))).rho 2 4
      (by decide))) (124,132) 10 _ hr
  have hz := finite_high_filtration_zero (.shift 1 .sphere) 2 (by decide)
    124 132 10 (by decide) _ ht
  have hn := (background.quotients.natural
    (background.nu.functor.map KIP126.AdamsComputation.Moore.top)).rho_naturality
      (by decide : 2 ≤ 4)
  change (background.quotients.tower
      (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum)).rho 2 4 (by decide) ≫
      XModLambdaN.map (background.nu.functor.map KIP126.AdamsComputation.Moore.top) 2 =
    XModLambdaN.map (background.nu.functor.map KIP126.AdamsComputation.Moore.top) 4 ≫
      (background.quotients.tower (background.nu.functor.obj (Sphere 1))).rho 2 4 (by decide) at hn
  simpa only [Category.assoc,←hn] using hz

private theorem moore_top_not_high
    (x : KIP126.AdamsComputation.Moore.Page 8 132) (hx : x ≠ 0)
    (c4 : BiHom 124 132 (XModLambdaN
      (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 4))
    (hc4 : Detects (background.convergence
      (.quotient 4 (.nu KIP126.AdamsComputation.Moore.adamsObject))) (8,132,132)
      (finiteTargetLabel background KIP126.AdamsComputation.Moore.adamsObject 4 8 132 0 x) c4) :
    ¬ FiltrationAtLeast background.syntheticTower 10 (mooreTopImage c4) := by
  intro hhigh
  exact moore_source_second_restriction_not_high x hx c4 hc4
    (moore_second_top_zero_source_filtration_actual _ (moore_top_high_second_zero c4 hhigh))

end
end KIP126.Main.Internal.Moore
