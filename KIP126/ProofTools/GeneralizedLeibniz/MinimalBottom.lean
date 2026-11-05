module
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingFinite

/-! Minimal-length bottom crossing for the normalized map. Vanishing
of high filtration in the smaller lambda quotient gives source division
by exactness; its image has the bottom filtration of a shifted nu object. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private def bottomTranslate (A : SyntheticSpectrum) (δ : ℤ × ℤ) (m w : ℤ) :
    BiHom (m-δ.1) (w-δ.2) A ≃+
      BiHom m w ((SyntheticCategory.biShift δ).obj A) :=
  (suspInvarianceAddEquiv (m-δ.1) (w-δ.2) δ.1 δ.2 A).trans
    (regradeAddEquiv (sub_add_cancel m δ.1) (sub_add_cancel w δ.2))

private theorem bottom_translate_filtration_iff (A : SyntheticObject (coefficients := background.coefficients))
    (δ : ℤ × ℤ) (m w u : ℤ)
    (a : BiHom (m-δ.1) (w-δ.2) (A.obj background.nu background.auxiliary)) :
    FiltrationAtLeast background.syntheticTower u (bottomTranslate _ δ m w a) ↔
      FiltrationAtLeast background.syntheticTower u a := by
  change FiltrationAtLeast background.syntheticTower u
    (homotopyRegrade (sub_add_cancel m δ.1) (sub_add_cancel w δ.2)
      (susp_invariance (m-δ.1) (w-δ.2) δ.1 δ.2 _ a)) ↔ _
  rw [regrade_filtration_iff]
  have he : susp_invariance (m-δ.1) (w-δ.2) δ.1 δ.2 _ a =
      shiftHomotopyClass δ (m-δ.1,w-δ.2) a := by
    simp [susp_invariance,shiftHomotopyClass,Iso.homCongr]
  rw [he]
  exact shift_filtration_iff A δ (m-δ.1,w-δ.2) u a

private theorem bottom_translate_comp (A B : SyntheticSpectrum) (g : A ⟶ B)
    (δ : ℤ × ℤ) (m w : ℤ) (a : BiHom (m-δ.1) (w-δ.2) A) :
    bottomTranslate A δ m w a ≫ (SyntheticCategory.biShift δ).map g =
      bottomTranslate B δ m w (a≫g) := by
  simp [bottomTranslate,AddEquiv.trans_apply,regradeAddEquiv,
    suspInvarianceAddEquiv,susp_invariance,Iso.homCongr,regrade_precomp,Functor.map_comp]

private theorem shifted_nu_bottom_filtration (X : AdamsObject (coefficients := background.coefficients))
    (δ : ℤ × ℤ) (m w : ℤ)
    (a : BiHom m w ((SyntheticCategory.biShift δ).obj
      (background.nu.functor.obj (X.obj background.auxiliary)))) :
    FiltrationAtLeast background.syntheticTower (w-δ.2-(m-δ.1)) a := by
  let E := bottomTranslate (background.nu.functor.obj (X.obj background.auxiliary)) δ m w
  let b := E.symm a
  have hb : FiltrationAtLeast background.syntheticTower (w-δ.2-(m-δ.1)) b := by
    have h := nu_bottom_filtration X (w-δ.2-(m-δ.1)) (w-δ.2)
    have he : w-δ.2-(w-δ.2-(m-δ.1)) = m-δ.1 := by omega
    rw [he] at h
    exact h b
  have h := (bottom_translate_filtration_iff (.nu X) δ m w
    (w-δ.2-(m-δ.1)) b).mpr hb
  change FiltrationAtLeast background.syntheticTower _ (E (E.symm a)) at h
  simpa only [AddEquiv.apply_symm_apply] using h

private theorem normalized_nu_source_division (X : AdamsObject (coefficients := background.coefficients))
    (e : ℤ) (i : ℕ) (hi : 0 < i) (m w u : ℤ)
    (hu : (i:ℤ) ≤ m+u-(w-e))
    (a : BiHom m w ((SyntheticCategory.biShift (0,e)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))))
    (ha : FiltrationAtLeast background.syntheticTower u a) :
    ∃ b : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
        ((SyntheticCategory.biShift (0,e)).obj
          (background.nu.functor.obj (X.obj background.auxiliary)))),
      b ≫ lambdaPow i _ = a := by
  let A : SyntheticObject (coefficients := background.coefficients) := .shift (0,e) (.nu X)
  let V := A.obj background.nu background.auxiliary
  letI := background.exactness.shiftCommShift (0,e)
  letI := background.exactness.shiftExact (0,e)
  obtain ⟨Q,_,_⟩ := quotient_shift_exists background.quotients.coherence (0,e) i
    (background.nu.functor.obj (X.obj background.auxiliary))
  have hproj : FiltrationAtLeast background.syntheticTower u
      (a≫XModLambdaN.incl V i) :=
    map_preserves_filtration (background.convergentMap A (.quotient i A)
      (XModLambdaN.incl V i)) (m,w) u a ha
  have hQ : FiltrationAtLeast background.syntheticTower u (a≫XModLambdaN.incl V i≫Q.hom) := by
    change (a≫XModLambdaN.incl V i≫Q.hom) ∈ background.syntheticTower.filtrationSubmodule
      ((SyntheticObject.shift (0,e) (.quotient i (.nu X))).obj background.nu background.auxiliary) u (m,w)
    simpa only [Category.assoc] using map_preserves_filtration
      (background.convergentMap (.quotient i A) (.shift (0,e) (.quotient i (.nu X))) Q.hom)
      (m,w) u _ hproj
  have hz := shifted_finite_high_filtration_zero X i hi e m w u hu _ hQ
  have hrho : a≫XModLambdaN.incl V i=0 := by
    have he := congrArg (fun z => z≫Q.inv) hz
    simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id,zero_comp] using he
  obtain ⟨b,hb⟩ := (XModLambdaN.cofiberTriangle V i).coyoneda_exact₂
    (XModLambdaN.cofiberTriangle_distinguished V i) a hrho
  exact ⟨b,hb.symm⟩

private theorem normalized_nu_image_filtration (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (m w u : ℤ)
    (a : BiHom m w ((extensionSourceObject background X Y f).obj background.nu background.auxiliary))
    (ha : FiltrationAtLeast background.syntheticTower u a) :
    FiltrationAtLeast background.syntheticTower (u+normalizedExponent background.classicalTower f)
      (a≫(background.normalizedMap X Y f).map) := by
  let e : ℤ := normalizedExponent background.classicalTower f
  let A := (extensionSourceObject background X Y f).obj background.nu background.auxiliary
  let B := background.nu.functor.obj (Y.obj background.auxiliary)
  by_cases hu : u ≤ w-m-e
  · have hbottom : FiltrationAtLeast background.syntheticTower (w-m)
        (a≫(background.normalizedMap X Y f).map) := by
      have h := nu_bottom_filtration Y (w-m) w
      have he : w-(w-m)=m := by omega
      rw [he] at h
      exact h _
    exact background.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by dsimp [e] at hu; omega) hbottom
  · let i := (u-(w-m-e)).toNat
    have hi : 0 < i := by dsimp only [i]; omega
    have hiz : (i:ℤ)=u-(w-m-e) := Int.toNat_of_nonneg (by omega)
    obtain ⟨b,hb⟩ := normalized_nu_source_division X e i hi m w u (by omega) a ha
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
    let c := b≫F.map (background.normalizedMap X Y f).map
    have hc : FiltrationAtLeast background.syntheticTower (u+e) c := by
      have h := shifted_nu_bottom_filtration Y (0,-(i:ℤ)) m w c
      convert h using 1
      dsimp at *
      omega
    have heq : c≫lambdaPow i B = a≫(background.normalizedMap X Y f).map := by
      dsimp only [c]
      rw [Category.assoc,lambdaPow_naturality,←Category.assoc,hb]
    rw [←heq]
    exact map_preserves_filtration (background.convergentMap (.shift (0,-(i:ℤ)) (.nu Y)) (.nu Y)
      (lambdaPow i B)) (m,w) (u+e) c hc

private theorem shifted_normalized_nu_image_filtration (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (δ : ℤ × ℤ) (m w u : ℤ)
    (a : BiHom m w ((SyntheticCategory.biShift δ).obj
      ((extensionSourceObject background X Y f).obj background.nu background.auxiliary)))
    (ha : FiltrationAtLeast background.syntheticTower u a) :
    FiltrationAtLeast background.syntheticTower (u+normalizedExponent background.classicalTower f)
      (a≫(SyntheticCategory.biShift δ).map (background.normalizedMap X Y f).map) := by
  let A := (extensionSourceObject background X Y f).obj background.nu background.auxiliary
  let E := bottomTranslate A δ m w
  let b := E.symm a
  have hb : FiltrationAtLeast background.syntheticTower u b :=
    (bottom_translate_filtration_iff (extensionSourceObject background X Y f) δ m w u b).mp
      (by
        change FiltrationAtLeast background.syntheticTower u (E (E.symm a))
        simpa only [AddEquiv.apply_symm_apply] using ha)
  have himage := normalized_nu_image_filtration X Y f (m-δ.1) (w-δ.2) u b hb
  have h := (bottom_translate_filtration_iff (.nu Y) δ m w
    (u+normalizedExponent background.classicalTower f) (b≫(background.normalizedMap X Y f).map)).mpr himage
  rw [←bottom_translate_comp] at h
  change FiltrationAtLeast background.syntheticTower _
    (E (E.symm a)≫(SyntheticCategory.biShift δ).map (background.normalizedMap X Y f).map) at h
  simpa only [AddEquiv.apply_symm_apply] using h

private theorem minimal_length_shifted_nu_tower_no_crossing (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (δ p : ℤ × ℤ) (s l : ℤ)
    (hl : l ≤ normalizedExponent background.classicalTower f) :
    TowerNoCrossing (background.convergentMap (.shift δ (extensionSourceObject background X Y f))
      (.shift δ (.nu Y)) ((SyntheticCategory.biShift δ).map (background.normalizedMap X Y f).map))
      p s l := by
  apply tower_no_crossing_of_correction
  intro u v hsu huv hvs a ha hfa
  refine ⟨a,ha,?_,?_⟩
  · simp only [sub_self]
    exact (background.syntheticTower.filtrationSubmodule _ _ _).zero_mem
  · have h := shifted_normalized_nu_image_filtration X Y f δ p.1 p.2 u a ha
    exact background.syntheticTower.filtrationSubmodule_antitone _ p (by omega) h

private theorem minimal_length_bottom_tower_no_crossing (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (page : ℕ) (r l s t : ℤ)
    (hl : l ≤ normalizedExponent background.classicalTower f) :
    TowerNoCrossing (background.convergentMap
      (.shift (1,-((page-1:ℕ):ℤ)) (extensionSourceObject background X Y f))
      (.shift (1,-((page-1:ℕ):ℤ)) (.nu Y))
      ((SyntheticCategory.biShift (1,-((page-1:ℕ):ℤ))).map (background.normalizedMap X Y f).map))
      (t-s,t+normalizedExponent background.classicalTower f) (s+r) l :=
  minimal_length_shifted_nu_tower_no_crossing X Y f _ _ _ _ hl

end
end KIP126.ProofTools.Internal.Leibniz
