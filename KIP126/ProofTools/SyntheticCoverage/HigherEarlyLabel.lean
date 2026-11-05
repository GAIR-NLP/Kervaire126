module

import all KIP126.ProofTools.SyntheticCoverage.HigherRotatedLift
import all KIP126.ProofTools.SyntheticCoverage.EarlyRotatedLabel
import all KIP126.ProofTools.SyntheticCoverage.BoundaryPermanence
import all KIP126.ProofTools.SyntheticCoverage.RawImageComparison
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLambdaShift

/-! Labels of the actual coefficient inclusion in the inverse-rotated
finite lift. The selected shift commutation is retained on full objects;
the induced sphere automorphism is removed only on the first quotient. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

private def higherStandardShiftEquiv (i : ℕ) (A : SyntheticSpectrum) (m w : ℤ) :
    BiHom (m-1) (w+(i:ℤ)-1) A ≃+ BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      ((SyntheticCategory.biShift (1,1)).obj A)) :=
  (suspInvarianceAddEquiv (m-1) (w+(i:ℤ)-1) 1 1 A) |>.trans
    (regradeAddEquiv (by omega) (by omega)) |>.trans
    (verticalTranslate _ (-(i:ℤ)) m (w+(i:ℤ))) |>.trans
    (regradeAddEquiv rfl (by omega))

private def higherActualShiftEquiv (i : ℕ) (A : SyntheticSpectrum) (m w : ℤ) :
    BiHom (m-1) (w+(i:ℤ)-1) A ≃+ BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      ((SyntheticCategory.biShift (1,1)).obj A)) := by
  letI := background.exactness.shiftCommShift (0,-(i:ℤ))
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,1)
  exact (verticalTranslate A 1 (m-1) (w+(i:ℤ)-1)) |>.trans
    (regradeAddEquiv rfl (by omega)) |>.trans
    (biSuspensionHomEquiv m w i (G.obj A)).symm |>.trans
    (homPostcompAddEquiv ((F.commShiftIso (1:ℤ)).symm.app (G.obj A))) |>.trans
    (homPostcompAddEquiv (F.mapIso (positiveOrdinaryIso.app A)))

private theorem higher_standard_shift_eq (i : ℕ) (A : SyntheticSpectrum) (m w : ℤ)
    (a : BiHom (m-1) (w+(i:ℤ)-1) A) :
    higherStandardShiftEquiv i A m w a =
      homotopyRegrade (show ((m,w+(i:ℤ))+(0,-(i:ℤ))).1=m by dsimp; omega)
        (show ((m,w+(i:ℤ))+(0,-(i:ℤ))).2=w by dsimp; omega)
        (shiftHomotopyClass (0,-(i:ℤ)) (m,w+(i:ℤ))
          (homotopyRegrade (show ((m-1,w+(i:ℤ)-1)+(1,1)).1=m by dsimp; omega) (show (w+(i:ℤ)-1)+1=w+(i:ℤ) by omega)
            (shiftHomotopyClass (1,1) (m-1,w+(i:ℤ)-1) a))) := by
  simp [higherStandardShiftEquiv,verticalTranslate,suspInvarianceAddEquiv,
    regradeAddEquiv,susp_invariance,Iso.homCongr,shiftHomotopyClass,
    normalized_homotopy_regrade_trans]

private theorem higher_standard_shift_natural (i : ℕ) {A B : SyntheticSpectrum}
    (f : A ⟶ B) (m w : ℤ) (a : BiHom (m-1) (w+(i:ℤ)-1) A) :
    higherStandardShiftEquiv i B m w (a ≫ f) =
      higherStandardShiftEquiv i A m w a ≫
        (SyntheticCategory.biShift (0,-(i:ℤ))).map ((SyntheticCategory.biShift (1,1)).map f) := by
  simp only [higherStandardShiftEquiv,AddEquiv.trans_apply,regradeAddEquiv,
    suspInvarianceAddEquiv,AddEquiv.coe_mk,Equiv.coe_fn_mk]
  have hs : susp_invariance (m-1) (w+(i:ℤ)-1) 1 1 B (a ≫ f) =
      susp_invariance (m-1) (w+(i:ℤ)-1) 1 1 A a ≫ (SyntheticCategory.biShift (1,1)).map f := by
    simp [susp_invariance,Functor.map_comp,Category.assoc]
  rw [hs,regrade_comp,←vertical_translate_comp,regrade_comp]

private theorem higher_actual_shift_natural (i : ℕ) {A B : SyntheticSpectrum}
    (f : A ⟶ B) (m w : ℤ) (a : BiHom (m-1) (w+(i:ℤ)-1) A) :
    higherActualShiftEquiv i B m w (a ≫ f) =
      higherActualShiftEquiv i A m w a ≫
        (SyntheticCategory.biShift (0,-(i:ℤ))).map ((SyntheticCategory.biShift (1,1)).map f) := by
  letI := background.exactness.shiftCommShift (0,-(i:ℤ))
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,1)
  let D := shiftFunctor SyntheticSpectrum (1:ℤ)
  let κ := F.commShiftIso (1:ℤ)
  simp only [higherActualShiftEquiv,AddEquiv.trans_apply,homPostcompAddEquiv,regradeAddEquiv,
    AddEquiv.coe_mk,Equiv.coe_fn_mk,Iso.app_hom,Iso.symm_hom,Functor.mapIso_hom]
  rw [←vertical_translate_comp,regrade_comp,bi_susp_symm_natural]
  simp only [Category.assoc]
  have hn : D.map (F.map (G.map f)) ≫ κ.inv.app (G.obj B) =
      κ.inv.app (G.obj A) ≫ F.map (D.map (G.map f)) := κ.inv.naturality (G.map f)
  rw [←Category.assoc (D.map (F.map (G.map f))),hn]
  simp only [Category.assoc]
  have hn' : D.map (G.map f) ≫ positiveOrdinaryIso.hom.app B =
      positiveOrdinaryIso.hom.app A ≫ (SyntheticCategory.biShift (1,1)).map f :=
    positiveOrdinaryIso.hom.naturality f
  rw [←Functor.map_comp,hn',Functor.map_comp]

private theorem higher_standard_shift_symm_natural (i : ℕ) {A B : SyntheticSpectrum}
    (f : A ⟶ B) (m w : ℤ)
    (a : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      ((SyntheticCategory.biShift (1,1)).obj A))) :
    (higherStandardShiftEquiv i B m w).symm
        (a ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map ((SyntheticCategory.biShift (1,1)).map f)) =
      (higherStandardShiftEquiv i A m w).symm a ≫ f := by
  apply (higherStandardShiftEquiv i B m w).injective
  rw [AddEquiv.apply_symm_apply,higher_standard_shift_natural i,AddEquiv.apply_symm_apply]

private def higherShiftReindex (i : ℕ) (A : SyntheticSpectrum) (m w : ℤ) :
    BiHom (m-1) (w+(i:ℤ)-1) A ≃+ BiHom (m-1) (w+(i:ℤ)-1) A :=
  (higherActualShiftEquiv i A m w).trans (higherStandardShiftEquiv i A m w).symm

private theorem higher_shift_reindex_natural (i : ℕ) {A B : SyntheticSpectrum}
    (f : A ⟶ B) (m w : ℤ) (a : BiHom (m-1) (w+(i:ℤ)-1) A) :
    higherShiftReindex i B m w (a ≫ f) = higherShiftReindex i A m w a ≫ f := by
  simp only [higherShiftReindex,AddEquiv.trans_apply]
  rw [higher_actual_shift_natural i,higher_standard_shift_symm_natural i]

private def higherShiftSourceIso (i : ℕ) (m w : ℤ) :
    Smn (Syn:=SyntheticSpectrum) (m-1) (w+(i:ℤ)-1) ≅ Smn (m-1) (w+(i:ℤ)-1) where
  hom := higherShiftReindex i _ m w (𝟙 _)
  inv := (higherShiftReindex i _ m w).symm (𝟙 _)
  hom_inv_id := by
    rw [←higher_shift_reindex_natural i,Category.id_comp,AddEquiv.apply_symm_apply]
  inv_hom_id := by
    apply (higherShiftReindex i _ m w).injective
    rw [higher_shift_reindex_natural i,AddEquiv.apply_symm_apply,Category.id_comp]

private theorem higher_actual_shift_first_quotient (i : ℕ)
    (X : (AdamsObject (coefficients := background.coefficients))) (m w : ℤ)
    (a : BiHom (m-1) (w+(i:ℤ)-1) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1)) :
    higherActualShiftEquiv i _ m w a = higherStandardShiftEquiv i _ m w a := by
  have h : higherShiftReindex i _ m w a = (higherShiftSourceIso i m w).hom ≫ a := by
    simpa only [Category.id_comp,higherShiftSourceIso] using
      higher_shift_reindex_natural i a m w (𝟙 _)
  rw [sphere_automorphism_first_finite] at h
  apply (higherStandardShiftEquiv i _ m w).symm.injective
  simpa only [higherShiftReindex,AddEquiv.trans_apply,AddEquiv.symm_apply_apply] using h


private def higherPositiveBoundaryInput
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (i : ℕ) (s t : ℤ) (u : Ambient background T.X (s+i,t+i-1)) :
    BiHom (t-s) t (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (normalizedTriangle background T he).obj₁ (i+1-i)))⟦(1:ℤ)⟧) := by
  simpa only [Nat.add_sub_cancel_left] using
    (biSuspensionHomEquiv (t-s) t i (XModLambdaN (normalizedTriangle background T he).obj₁ 1)).symm
      (homotopyRegrade (show (t+i-1)-(s+i)=(t-s)-1 by omega)
        (show (t+i-1)+1=t+i by omega) (earlyNormalizedSourceLabel T he hf (s+i) (t+i-1) u))


private theorem higher_rotated_input_native_first_one
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (i : ℕ)
    (ex : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ 1)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ 1 ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ 1))
    (ε₁ : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 1))
    (hε₁ : XModLambdaN.incl _ 1 ≫ ε₁.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 1))
    (s t : ℤ) (u : Ambient background T.X (s+i,t+i-1)) :
    letI := background.exactness.shiftCommShift (0,-(i:ℤ))
    (((biSuspensionHomEquiv (t-s) t i
        (XModLambdaN (normalizedTriangle background T he).obj₁ 1)).symm
      (homotopyRegrade (show (t+i-1)-(s+i)=(t-s)-1 by omega)
        (show (t+i-1)+1=t+i by omega)
        (earlyNormalizedSourceLabel T he hf (s+i) (t+i-1) u))) ≫
      (Functor.commShiftIso (SyntheticCategory.biShift (Syn:=SyntheticSpectrum)
        (0,-(i:ℤ))) (1:ℤ)).inv.app _ ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map ex.inv) ≫
        (SyntheticCategory.biShift (0,-(i:ℤ))).map
          (XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
            (normalizedPositiveSourceIso T hf).hom ≫ positiveOrdinaryIso.hom.app _) 1) ≫
        (SyntheticCategory.biShift (0,-(i:ℤ))).map ε₁.hom =
      higherStandardShiftEquiv i _ (t-s) t
        (homotopyRegrade (show (t+i-1)-(s+i)=(t-s)-1 by omega) rfl (nativeFirstLabel T.X (s+i) (t+i-1) u)) := by
  letI := background.exactness.shiftCommShift (0,-(i:ℤ))
  let A := background.nu.functor.obj (T.X.obj background.auxiliary)
  let N := (normalizedTriangle background T he).obj₁
  let E := normalizedPositiveSourceIso T hf
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,1)
  let D := shiftFunctor SyntheticSpectrum (1:ℤ)
  let κ := F.commShiftIso (1:ℤ)
  let εp := levelQuotientShiftIso T.X 1 1
  let exG := positiveOrdinaryQuotientIso T.X 1 ε₁ εp
  let ex0 := transportedSuspensionQuotientIso E.symm 1 exG
  have hexG := positiveOrdinaryQuotientIso_incl T.X 1 ε₁ εp hε₁
    (level_quotient_shift_incl T.X 1 1)
  have hex0 := transported_suspension_quotient_incl E.symm 1 exG hexG
  have hinv (m w : ℤ) (c : BiHom m w ((XModLambdaN N 1)⟦(1:ℤ)⟧)) :
      c ≫ ex.inv = c ≫ ex0.inv := by
    have h := transported_suspension_comparisons_equal T.X E ex ex0 hex hex0 m w (c ≫ ex.inv)
    have h' := congrArg (fun z => z ≫ ex0.inv) h
    simpa only [Category.assoc,Iso.inv_hom_id_assoc,Iso.hom_inv_id,Category.comp_id] using h'.symm
  let b := (biSuspensionHomEquiv (t-s) t i (XModLambdaN N 1)).symm
    (homotopyRegrade (show (t+i-1)-(s+i)=(t-s)-1 by omega)
      (show (t+i-1)+1=t+i by omega) (earlyNormalizedSourceLabel T he hf (s+i) (t+i-1) u))
  have hd := shift_preserves_sphere_congruence _ _ (0,-(i:ℤ)) ex.inv ex0.inv hinv
    (t-s) t (b ≫ κ.inv.app (XModLambdaN N 1))
  have hcomp : ex0.inv ≫ XModLambdaN.map (D.map E.hom ≫ positiveOrdinaryIso.hom.app A) 1 ≫ ε₁.hom =
      D.map (XModLambdaN.map E.hom 1 ≫ εp.hom) ≫ positiveOrdinaryIso.hom.app (XModLambdaN A 1) := by
    simp only [ex0,transportedSuspensionQuotientIso,exG,positiveOrdinaryQuotientIso,
      Iso.trans_inv,Iso.symm_inv,Functor.mapIso_inv,Iso.app_inv,Category.assoc]
    change D.map (XModLambdaN.map E.hom 1) ≫ D.map εp.hom ≫
      positiveOrdinaryIso.hom.app (XModLambdaN A 1) ≫ ε₁.inv ≫
      XModLambdaN.map (positiveOrdinaryIso.inv.app A) 1 ≫
      XModLambdaN.map (D.map E.inv) 1 ≫
        XModLambdaN.map (D.map E.hom ≫ positiveOrdinaryIso.hom.app A) 1 ≫ ε₁.hom = _
    rw [background.quotients.functoriality.map_comp,Functor.map_comp]
    simp only [Category.assoc]
    rw [←Category.assoc (XModLambdaN.map (D.map E.inv) 1),
      ←background.quotients.functoriality.map_comp,←Functor.map_comp,E.inv_hom_id,
      CategoryTheory.Functor.map_id,background.quotients.functoriality.map_id,Category.id_comp]
    rw [←Category.assoc (XModLambdaN.map (positiveOrdinaryIso.inv.app A) 1),
      ←background.quotients.functoriality.map_comp,Iso.inv_hom_id_app,
      background.quotients.functoriality.map_id,Category.id_comp,ε₁.inv_hom_id,Category.comp_id]
  let a := homotopyRegrade (show (t+i-1)-(s+i)=(t-s)-1 by omega) rfl
    (nativeFirstLabel T.X (s+i) (t+i-1) u)
  have hfirst : homotopyRegrade (show (t+i-1)-(s+i)=(t-s)-1 by omega)
      (show (t+i-1)+1=t+i by omega)
      (earlyNormalizedSourceLabel T he hf (s+i) (t+i-1) u) ≫
        (XModLambdaN.map E.hom 1 ≫ εp.hom) = homotopyRegrade rfl (show (t+i-1)+1=t+i by omega)
          (verticalTranslate _ 1 ((t-s)-1) (t+i-1) a) := by
    dsimp only [earlyNormalizedSourceLabel,a,E]
    rw [←regrade_comp,Category.assoc,←Category.assoc (XModLambdaN.map _ 1),
      ←background.quotients.functoriality.map_comp,Iso.inv_hom_id,
      background.quotients.functoriality.map_id,Category.id_comp]
    have hregrade {m m' w w' : ℤ} (hm : m=m') (hw : w=w')
        (a : BiHom m w (XModLambdaN A 1)) :
        verticalTranslate _ 1 m' w' (homotopyRegrade hm hw a) =
          homotopyRegrade hm (congrArg (fun z : ℤ => z+1) hw) (verticalTranslate _ 1 m w a) := by
      subst m'; subst w'; rfl
    rw [hregrade,←positive_first_label_shift,normalized_homotopy_regrade_trans]
    simp only [εp,Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rfl
  have ha : (b ≫ κ.inv.app _ ≫ F.map ex.inv) ≫
        F.map (XModLambdaN.map (D.map E.hom ≫ positiveOrdinaryIso.hom.app A) 1) ≫ F.map ε₁.hom =
      higherActualShiftEquiv i _ (t-s) t a := by
    rw [←Category.assoc b (κ.inv.app _),hd]
    simp only [Category.assoc]
    rw [←Functor.map_comp,←Functor.map_comp,hcomp,Functor.map_comp]
    have hn := κ.inv.naturality (XModLambdaN.map E.hom 1 ≫ εp.hom)
    have hn' : D.map (F.map (XModLambdaN.map E.hom 1 ≫ εp.hom)) ≫
        κ.inv.app (G.obj (XModLambdaN A 1)) =
      κ.inv.app (XModLambdaN N 1) ≫ F.map (D.map (XModLambdaN.map E.hom 1 ≫ εp.hom)) := hn
    rw [←Category.assoc (κ.inv.app _),←hn',←Category.assoc b]
    dsimp only [b]
    rw [←Category.assoc _ (D.map (F.map (XModLambdaN.map E.hom 1 ≫ εp.hom)))]
    have hb := bi_susp_symm_natural (t-s) t i (XModLambdaN.map E.hom 1 ≫ εp.hom)
      (homotopyRegrade (show (t+i-1)-(s+i)=(t-s)-1 by omega)
        (show (t+i-1)+1=t+i by omega)
        (earlyNormalizedSourceLabel T he hf (s+i) (t+i-1) u))
    erw [←hb,hfirst]
    rfl
  exact ha.trans (higher_actual_shift_first_quotient i T.X (t-s) t a)

private theorem higher_rotated_input_native_first
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1) (i : ℕ)
    (ex : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (i+1-i) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ (i+1-i))⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ (i+1-i) ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (i+1-i)))
    (ε₁ : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (i+1-i) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (i+1-i)))
    (hε₁ : XModLambdaN.incl _ (i+1-i) ≫ ε₁.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (i+1-i)))
    (s t : ℤ) (u : Ambient background T.X (s+i,t+i-1)) :
    higherRotatedInput T he i ex (t-s) t (higherPositiveBoundaryInput T he hf i s t u) ≫
      (SyntheticCategory.biShift (0,-(i:ℤ))).map
        (XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (normalizedPositiveSourceIso T hf).hom ≫ positiveOrdinaryIso.hom.app _) (i+1-i)) ≫
      (SyntheticCategory.biShift (0,-(i:ℤ))).map ε₁.hom =
      higherStandardShiftEquiv i _ (t-s) t
        (homotopyRegrade (show (t+i-1)-(s+i)=(t-s)-1 by omega) rfl
          (oneQuotientCast _ (i+1-i) (by omega) ((t+i-1)-(s+i)) (t+i-1)
            (nativeFirstLabel T.X (s+i) (t+i-1) u))) := by
  letI := background.exactness.shiftCommShift (0,-(i:ℤ))
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let κ := F.commShiftIso (1:ℤ)
  let N := (normalizedTriangle background T he).obj₁
  let A := background.nu.functor.obj (T.X.obj background.auxiliary)
  let E := (shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalizedPositiveSourceIso T hf).hom ≫
    positiveOrdinaryIso.hom.app A
  let b₁ := (biSuspensionHomEquiv (t-s) t i (XModLambdaN N 1)).symm
    (homotopyRegrade (show (t+i-1)-(s+i)=(t-s)-1 by omega)
      (show (t+i-1)+1=t+i by omega) (earlyNormalizedSourceLabel T he hf (s+i) (t+i-1) u))
  have one (q : ℕ) (hq : q=1)
      (ex' : XModLambdaN (N⟦(1:ℤ)⟧) q ≅ (XModLambdaN N q)⟦(1:ℤ)⟧)
      (hex' : XModLambdaN.incl _ q ≫ ex'.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q))
      (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj A) q ≅
        (SyntheticCategory.biShift (1,1)).obj (XModLambdaN A q))
      (hε : XModLambdaN.incl _ q ≫ ε.hom =
        (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q))
      (b : BiHom (t-s) t ((F.obj (XModLambdaN N q))⟦(1:ℤ)⟧))
      (hb : HEq b b₁) :
      (b ≫ κ.inv.app _ ≫ F.map ex'.inv) ≫ F.map (XModLambdaN.map E q) ≫ F.map ε.hom =
        higherStandardShiftEquiv i _ (t-s) t
          (homotopyRegrade (show (t+i-1)-(s+i)=(t-s)-1 by omega) rfl
            (oneQuotientCast _ q hq ((t+i-1)-(s+i)) (t+i-1)
              (nativeFirstLabel T.X (s+i) (t+i-1) u))) := by
    subst q
    cases hb
    simpa only [oneQuotientCast] using
      higher_rotated_input_native_first_one T he hf i ex' hex' ε hε s t u
  apply one (i+1-i) (by omega) ex hex ε₁ hε₁ (higherPositiveBoundaryInput T he hf i s t u)
  simp only [higherPositiveBoundaryInput,b₁]
  exact cast_heq _ _

private theorem higher_standard_shift_regraded (i : ℕ) (A : SyntheticSpectrum)
    (m n k w v w' : ℤ) (hn : n=m-1) (hv : v=w+i-1) (hk : m=k) (hw : w=w')
    (a : BiHom n v A) :
    homotopyRegrade hk hw
        (higherStandardShiftEquiv i A m w (homotopyRegrade hn hv a)) =
      homotopyRegrade (show ((k,v+1)+(0,-(i:ℤ))).1=k by simp)
        (show ((k,v+1)+(0,-(i:ℤ))).2=w' by dsimp; omega)
        (shiftHomotopyClass (0,-(i:ℤ)) (k,v+1)
          (homotopyRegrade (show ((n,v)+(1,1)).1=k by dsimp; omega) rfl
            (shiftHomotopyClass (1,1) (n,v) a))) := by
  subst n; subst k; subst w'; subst v
  have h := higher_standard_shift_eq i A m w a
  simpa only [top_target_regrade_self,shift_class_input_regrade,
    normalized_homotopy_regrade_trans] using h

/-- The actual highest coefficient inclusion of the inverse-rotated input
has exactly the specified native top label, for every positive early page. -/
private theorem higher_rotated_input_top_label
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1) (i : ℕ) (hi : 0 < i)
    (ex : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (i+1-i) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ (i+1-i))⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ (i+1-i) ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (i+1-i)))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (i+1) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (i+1)))
    (hε : XModLambdaN.incl _ (i+1) ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (i+1)))
    (s t : ℤ) (u : Ambient background T.X (s+i,t+i-1)) :
    rawMaySourceDesuspend T he hf (i+1) i (s+i) (t+i-1) ε
      (homotopyRegrade (show t-s=(t+i-1)-(s+i)+1 by omega)
        (show t=(t+i-1)-i+1 by omega)
        (higherRotatedInput T he i ex (t-s) t (higherPositiveBoundaryInput T he hf i s t u) ≫
          ((background.quotients.tower ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧)).triangle
            hi (Nat.lt_succ_self i)).lambdaMap)) =
      finiteTopLabel T.X i hi (s+i) (t+i-1) u := by
  letI := background.exactness.shiftCommShift (1,1)
  letI := background.exactness.shiftExact (1,1)
  let A := background.nu.functor.obj (T.X.obj background.auxiliary)
  let S := s+(i:ℤ)
  let V := t+(i:ℤ)-1
  obtain ⟨ε₁,hε₁,_⟩ := quotient_shift_exists background.quotients.coherence (1,1) (i+1-i) A
  let E := (shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalizedPositiveSourceIso T hf).hom ≫
    positiveOrdinaryIso.hom.app A
  let d := higherRotatedInput T he i ex (t-s) t (higherPositiveBoundaryInput T he hf i s t u)
  let z := oneQuotientCast A (i+1-i) (by omega) (V-S) V (nativeFirstLabel T.X S V u)
  let zH := homotopyRegrade (show ((V-S,V)+(1,1)).1=V+1-S by dsimp; omega) rfl
    (shiftHomotopyClass (1,1) (V-S,V) z) ≫ ε₁.inv
  have hfirst := higher_rotated_input_native_first T he hf i ex hex ε₁ hε₁ s t u
  have hfirst' := congrArg (fun a => a ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map ε₁.inv) hfirst
  simp only [Category.assoc,←Functor.map_comp,ε₁.hom_inv_id] at hfirst'
  erw [Category.comp_id] at hfirst'
  have hstd : homotopyRegrade (show t-s=V+1-S by dsimp [V,S]; omega)
      (show t=V+1-i by dsimp [V]; omega)
      (d ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.map E (i+1-i))) =
      homotopyRegrade (show ((V+1-S,V+1)+(0,-(i:ℤ))).1=V+1-S by simp)
        (show ((V+1-S,V+1)+(0,-(i:ℤ))).2=V+1-i by dsimp; omega)
        (shiftHomotopyClass (0,-(i:ℤ)) (V+1-S,V+1) zH) := by
    have h := congrArg (homotopyRegrade (show t-s=V+1-S by dsimp [V,S]; omega)
      (show t=V+1-i by dsimp [V]; omega)) hfirst'
    simp only [regrade_comp] at h
    rw [higher_standard_shift_regraded] at h
    simpa only [d,E,z,zH,S,V,shift_hom_comp,regrade_comp] using h
  have hlambda := shifted_finite_lambda_class T.X (i+1) i hi (Nat.lt_succ_self i)
    S V ε₁ ε hε₁ hε z
  have heq : homotopyRegrade (show t-s=V+1-S by dsimp [V,S]; omega)
      (show t=V+1-i by dsimp [V]; omega)
      ((d ≫ ((background.quotients.tower ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧)).triangle
        hi (Nat.lt_succ_self i)).lambdaMap) ≫ XModLambdaN.map E (i+1)) =
      homotopyRegrade (m':=V+1-S) (w':=V+1-i) (by dsimp; omega) (by dsimp; omega)
        (shiftHomotopyClass (1,1) (V-S,V-i)
          (finiteLambdaClass T.X (i+1) i hi (Nat.lt_succ_self i) S V z)) ≫ ε.inv := by
    rw [Category.assoc]
    erw [←(background.quotients.natural E).lambda_naturality hi (Nat.lt_succ_self i)]
    rw [←Category.assoc,regrade_comp]
    erw [hstd]
    exact hlambda.symm
  have heq' := congrArg (fun a => quotientUnshift T.X (1,1) (V-S,V-i) (i+1) ε
    (homotopyRegrade (show V+1-S=((V-S,V-i)+(1,1)).1 by dsimp; omega)
      (show V+1-i=((V-S,V-i)+(1,1)).2 by dsimp; omega) a)) heq
  have hE : E = (normalizedSuspensionNativeIso T he hf).hom ≫
      (background.nu.suspensionIso (T.X.obj background.auxiliary)).hom :=
    normalizedPositiveSourceIso_suspension T he hf
  rw [hE,background.quotients.functoriality.map_comp] at heq'
  have htop : finiteLambdaClass T.X (i+1) i hi (Nat.lt_succ_self i) S V z =
      finiteTopLabel T.X i hi S V u :=
    (finiteTopOfFirst_eq_raw A i hi (V-S) V (nativeFirstLabel T.X S V u)).symm
  simpa only [rawMaySourceDesuspend,regrade_comp,normalized_homotopy_regrade_trans,
    top_target_regrade_self,quotient_unshift_shift,htop,d,S,V] using heq'

end
end KIP126.ProofTools.Internal.SyntheticCoverage
