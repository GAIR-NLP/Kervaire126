module

import all KIP126.ProofTools.GeneralizedMahowald.CofiberIdentification

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

private theorem shift_negativeLift_cancel (k : ℕ) {A B : SyntheticSpectrum}
    (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B) :
    (SyntheticCategory.biShift (0,(k:ℤ))).map (negativeLift k f) ≫
      (biShiftAddIso (0,-(k:ℤ)) (0,(k:ℤ)) 0 (by ext <;> simp)).hom.app B ≫
        SyntheticCategory.biShift_zero.hom.app B = f := by
  let h : ℤ×ℤ := (0,(k:ℤ))
  let nh : ℤ×ℤ := (0,-(k:ℤ))
  let e : (SyntheticCategory.biShift nh).obj ((SyntheticCategory.biShift h).obj A) ≅ A :=
    (biShiftAddIso h nh 0 (by ext <;> simp [h,nh])).app A ≪≫
      SyntheticCategory.biShift_zero.app A
  have hs : e.hom ≫ negativeLift k f = (SyntheticCategory.biShift nh).map f := by
    simp only [e,h,nh,biShiftAddIso,Iso.trans_hom,Iso.app_hom,NatTrans.comp_app,
      eqToIso.hom,eqToHom_app,negativeLift,Category.assoc,
      Iso.hom_inv_id_app_assoc,eqToHom_trans_assoc]
    simp
  have hu : (SyntheticCategory.biShift h).map e.hom =
      (biShiftAddIso nh h 0 (by ext <;> simp [h,nh])).hom.app
        ((SyntheticCategory.biShift h).obj A) ≫
      SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift h).obj A) := by
    have H := background.quotients.coherence.associativity h nh h 0 0 h
      (by ext <;> simp [h,nh]) (by ext <;> simp [h,nh])
      (zero_add h) (add_zero h) A
    rw [background.quotients.coherence.left_unit,background.quotients.coherence.right_unit] at H
    simpa only [e,Iso.trans_hom,Iso.app_hom,Functor.map_comp] using H
  apply (cancel_epi ((SyntheticCategory.biShift h).mapIso e).hom).mp
  change (SyntheticCategory.biShift h).map e.hom ≫ _ = _
  rw [←Category.assoc,←Functor.map_comp,hs]
  erw [(biShiftAddIso nh h 0 (by ext <;> simp [h,nh])).hom.naturality_assoc]
  erw [SyntheticCategory.biShift_zero.hom.naturality]
  change _ = (SyntheticCategory.biShift h).map e.hom ≫ f
  rw [hu]
  simp only [Category.assoc,Functor.id_map]
  rfl

private theorem shift_negativeLift_target (k : ℕ) {A B X : SyntheticSpectrum}
    (σ δ : ℤ×ℤ) (hσ : σ+(0,-(k:ℤ))=δ) (hδ : δ+(0,(k:ℤ))=σ)
    (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B)
    (u : B ⟶ (SyntheticCategory.biShift σ).obj X) :
    (SyntheticCategory.biShift (0,(k:ℤ))).map
      (negativeLift k f ≫ (SyntheticCategory.biShift (0,-(k:ℤ))).map u ≫
        (biShiftAddIso σ (0,-(k:ℤ)) δ hσ).hom.app X) ≫
      (biShiftAddIso δ (0,(k:ℤ)) σ hδ).hom.app X = f≫u := by
  let h : ℤ×ℤ := (0,(k:ℤ))
  let nh : ℤ×ℤ := (0,-(k:ℤ))
  have H := background.quotients.coherence.associativity σ nh h δ 0 σ
    hσ (by ext <;> simp [h,nh]) hδ (add_zero σ) X
  rw [background.quotients.coherence.right_unit] at H
  simp only [Functor.map_comp,Category.assoc]
  rw [H]
  erw [(biShiftAddIso nh h 0 (by ext <;> simp [h,nh])).hom.naturality_assoc]
  erw [SyntheticCategory.biShift_zero.hom.naturality]
  simpa only [Category.assoc,Functor.id_map] using
    congrArg (fun z => z≫u) (shift_negativeLift_cancel k f)

private theorem normalized_g_cofiber_inclusion_shifted (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he) :
    (SyntheticCategory.biShift (0,(normalizedExponent background.classicalTower T.h : ℤ))).map
      (HasFunctorialCofiber.cofibι (background.normalizedMap T.Y T.Z T.g).map ≫
        (normalized_g_cofiber_iso T he hT).hom) ≫
      (biShiftAddIso
        (1,(normalizedExponent background.classicalTower T.f : ℤ) + normalizedExponent background.classicalTower T.g)
        (0,(normalizedExponent background.classicalTower T.h : ℤ)) (1,1)
        (by ext <;> simp only [Prod.fst_add,Prod.snd_add] <;> omega)).hom.app _ =
      (background.normalizedMap T.Z (.shift 1 T.X) T.h).map ≫
        (background.nu.suspensionIso (T.X.obj background.auxiliary)).hom := by
  rw [normalized_g_cofiber_inclusion]
  exact shift_negativeLift_target _ _ _ _ _ _ _

end
end KIP126.ProofTools.Internal.Mahowald
