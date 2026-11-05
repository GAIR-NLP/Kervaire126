module

public import KIP126.ProofTools.Operations
import all KIP126.Main.Internal.NuNinth.Shift
import all KIP126.Main.Internal.DetectionLabels

/-! The two-coefficient inclusion from the fourth to the sixth quotient.
For a specified fourth-quotient representative, it preserves the detecting
label and the vanishing h₀ product of that same representative. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.Main.Internal KIP126.Main.Internal.NuNinth
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

private theorem nu_sixth_detected
    (x : background.classical.sphere.Page 2 (9,132))
    (hx : x∈cycles background .sphere 3 (9,132))
    (a : BiHom 123 131 (XModLambdaN (background.nu.functor.obj SphereSpectrum) 4))
    (ha : Detects (background.convergence (.quotient 4 (.nu .sphere))) (9,132,131)
      (finiteTargetLabel background .sphere 4 9 132 1 x) a) :
    Detects (background.convergence (.quotient 6 (.nu .sphere))) (9,132,129)
      (finiteTargetLabel background .sphere 6 9 132 3 x)
      (weightShiftHom (-2) a ≫ ((background.quotients.tower (background.nu.functor.obj SphereSpectrum)).triangle (i:=2) (j:=6) (by decide) (by decide)).lambdaMap) := by
  obtain ⟨e,he,aa,haa,hgr⟩ := ha
  let f := ((background.quotients.tower (background.nu.functor.obj SphereSpectrum)).triangle (i:=2) (j:=6) (by decide) (by decide)).lambdaMap
  let e' := KIP126.Literature.Standard.infinityFiniteLambda .sphere 6 2 (by decide) (9,132) 131 e
  let c : cycles background .sphere ((4:ℤ)-132+(132-(1:ℕ))) (9,132) := ⟨x,hx⟩
  have hs := (finite_target_label_iff .sphere 4 (by decide) 9 132 1 (by decide) c e).mp he
  have hh := KIP126.Literature.Standard.eInfinity_lambda_finite .sphere 6 2 (by decide) (9,132) 131 (by norm_num) e
  erw [hs] at hh
  have hre : HasInfinityRepresentative (background.family.quotient (background.nu.functor.obj SphereSpectrum) 6) 2 (9,132,129)
      (finiteTargetLabel background .sphere 6 9 132 3 x) e' := by
    apply (finite_target_label_iff .sphere 6 (by decide) 9 132 3 (by decide) ⟨x,hx⟩ e').mpr
    exact hh
  let S := KIP126.Literature.Standard.infinityShift_comparison 2
  obtain ⟨bb,hbb,hbg⟩ := shift_graded (.quotient 4 (.nu .sphere)) (0,-2) (123,131) 9 S e aa (by
    simpa only [SyntheticTowerConvergence.filtration,Int.reduceAdd,Int.reduceSub,towerGradedIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] using hgr)
  let ee := (infinityShift background KIP126.Literature.Standard.infinityShift_comparison
    (.quotient 4 (.nu .sphere)) 2 (9,132) 131).hom e
  have hgg : ((background.convergence (.shift (0,-2) (.quotient 4 (.nu .sphere)))).identification (9,132,129)).hom ee =
      (background.convergence (.shift (0,-2) (.quotient 4 (.nu .sphere)))).filtration.toAssociatedGraded 9 (123,129) bb := by
    simpa only [SyntheticTowerConvergence.filtration,Prod.mk_add_mk,Prod.fst_add,Prod.snd_add,Int.reduceAdd,Int.reduceSub,Int.reduceNeg,Nat.cast_ofNat,ee,infinityShift,S,towerGradedIso,Iso.trans_hom,eqToIso.hom,
      eqToHom_refl,Category.id_comp,Category.comp_id] using hbg
  obtain ⟨cc,hcc,hcg⟩ := map_graded (.shift (0,-2) (.quotient 4 (.nu .sphere)))
    (.quotient 6 (.nu .sphere)) f (9,132,129) ee bb hgg
  refine ⟨e',hre,cc,?_,?_⟩
  · refine hcc.trans ?_
    have ht := hbb.trans (congrArg (shiftHomotopyClass (0,-2) _) haa)
    simpa only [f,syntheticHomotopy,SyntheticTowerConvergence.filtration,SyntheticObject.obj,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub,shiftHomotopyClass,weightShiftHom,biShiftAddIso,Iso.trans_inv,eqToIso.inv,
      NatTrans.comp_app,eqToHom_app,eqToHom_refl,Category.id_comp] using congrArg (fun z => z ≫ f) ht
  · exact hcg

private theorem sixth_sphere_transport (a : BiHom 123 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 4)) :
    (weightShiftHom (-2) (a≫XModLambdaN.map background.nu.unitIso.inv 4) ≫
      ((background.quotients.tower (background.nu.functor.obj SphereSpectrum)).triangle (i:=2) (j:=6) (by decide) (by decide)).lambdaMap) ≫
      XModLambdaN.map background.nu.unitIso.hom 6 =
    weightShiftHom (-2) a ≫ ((background.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle (i:=2) (j:=6) (by decide) (by decide)).lambdaMap := by
  have hn := (background.quotients.natural background.nu.unitIso.inv).lambda_naturality
    (i:=2) (j:=6) (by decide) (by decide)
  have hg : XModLambdaN.map background.nu.unitIso.inv 6 ≫ XModLambdaN.map background.nu.unitIso.hom 6 = 𝟙 _ := by
    rw [←background.quotients.functoriality.map_comp,Iso.inv_hom_id,background.quotients.functoriality.map_id]
  change (SyntheticCategory.biShift (0,-2)).map (XModLambdaN.map background.nu.unitIso.inv 4) ≫
    ((background.quotients.tower (background.nu.functor.obj SphereSpectrum)).triangle (i:=2) (j:=6) (by decide) (by decide)).lambdaMap =
    ((background.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle (i:=2) (j:=6) (by decide) (by decide)).lambdaMap ≫
      XModLambdaN.map background.nu.unitIso.inv 6 at hn
  dsimp only [weightShiftHom]
  simp only [Functor.map_comp,Category.assoc]
  erw [reassoc_of% hn,hg,Category.comp_id]

private theorem sphere_sixth_detected
    (x : background.classical.sphere.Page 2 (9,132))
    (hx : x∈cycles background .sphere 3 (9,132))
    (a : BiHom 123 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 4))
    (ha : Detects (background.convergence (.quotient 4 .sphere)) (9,132,131)
      (quotientLabel 4 9 132 1 x) a) :
    Detects (background.convergence (.quotient 6 .sphere)) (9,132,129)
      (quotientLabel 6 9 132 3 x)
      (weightShiftHom (-2) a ≫ ((background.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle (i:=2) (j:=6) (by decide) (by decide)).lambdaMap) := by
  have hn := detects_map (.quotient 4 .sphere) (.quotient 4 (.nu .sphere))
    (XModLambdaN.map background.nu.unitIso.inv 4) (9,132,131) _ a ha
  erw [sphere_quotient_label_to_nu 4 1 9 132 x] at hn
  have hp := nu_sixth_detected x hx (a≫XModLambdaN.map background.nu.unitIso.inv 4) hn
  have hs := detects_map (.quotient 6 (.nu .sphere)) (.quotient 6 .sphere)
    (XModLambdaN.map background.nu.unitIso.hom 6) (9,132,129) _ _ hp
  erw [sphere_quotient_label_from_nu 6 3 9 132 x,sixth_sphere_transport] at hs
  exact hs

private def insertTwoCoefficients {m w : ℤ} {X Y : SyntheticSpectrum}
    (f : (SyntheticCategory.biShift (0,-2)).obj X ⟶ Y) (a : BiHom m w X) :
    BiHom m (w-2) Y :=
  eqToHom (by congr 1; simp) ≫
    (SyntheticCategory.biShift_comp (m,w) (0,-2)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (0,-2)).map a ≫ f

private theorem h0_insert_two_coefficients {X Y : SyntheticSpectrum}
    (f : (SyntheticCategory.biShift (0,-2)).obj X ⟶ Y)
    (h : BiHom 0 1 (S_0_0 : SyntheticSpectrum)) (a : BiHom 123 131 X) :
    sphereAction h (insertTwoCoefficients f a) = insertTwoCoefficients f (sphereAction h a) := by
  classical
  have he := Selected.shift_assoc_inv background.quotients.coherence (0,1) (123,131) (0,-2)
    (123,132) (123,129) (123,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp] at he
  simp only [insertTwoCoefficients,eqToHom_refl,Category.id_comp]
  change
    (SyntheticCategory.biShift_comp (0,1) (123,129)).inv.app (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift (123,129)).map h ≫
      ((SyntheticCategory.biShift_comp (123,131) (0,-2)).inv.app (S_0_0 : SyntheticSpectrum) ≫
        (SyntheticCategory.biShift (0,-2)).map a ≫ f) =
    (SyntheticCategory.biShift_comp (123,132) (0,-2)).inv.app (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift (0,-2)).map
        ((SyntheticCategory.biShift_comp (0,1) (123,131)).inv.app (S_0_0 : SyntheticSpectrum) ≫
          (SyntheticCategory.biShift (123,131)).map h ≫ a) ≫ f
  simp only [Functor.map_comp,Category.assoc]
  erw [reassoc_of% ((SyntheticCategory.biShift_comp (123,131) (0,-2)).inv.naturality h)]
  erw [←reassoc_of% he]

private theorem sixth_representative_of_fourth
    (x : background.classical.sphere.Page 2 (9,132))
    (hx : x∈cycles background .sphere 3 (9,132))
    (a : BiHom 123 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 4))
    (ha : Detects (background.convergence (.quotient 4 .sphere)) (9,132,131)
      (quotientLabel 4 9 132 1 x) a)
    (hz : sphereAction KIP126.Literature.Standard.syntheticH0 a = 0) :
    ∃ b : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 6),
      Detects (background.convergence (.quotient 6 .sphere)) (9,132,129)
        (quotientLabel 6 9 132 3 x) b ∧
      sphereAction KIP126.Literature.Standard.syntheticH0 b = 0 := by
  let f := ((background.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle
    (i:=2) (j:=6) (by decide) (by decide)).lambdaMap
  refine ⟨insertTwoCoefficients f a,?_,?_⟩
  · simpa only [insertTwoCoefficients,weightShiftHom,biShiftAddIso,Iso.trans_inv,
      eqToIso.inv,NatTrans.comp_app,eqToHom_app,eqToHom_refl,Category.id_comp,
      Category.assoc,f] using sphere_sixth_detected x hx a ha
  · rw [h0_insert_two_coefficients, hz]
    letI := KIP126.AdamsSynthetic.Completed.graded_shiftAdditive (0,-2)
    simp only [insertTwoCoefficients,Functor.map_zero,comp_zero,zero_comp]

end
end KIP126.Main.Internal.Moore
