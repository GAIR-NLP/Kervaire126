module

import all KIP126.ProofTools.SyntheticCoverage.EarlyRotatedLift
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

private def earlyStandardShiftEquiv (A : SyntheticSpectrum) (m w : ℤ) :
    BiHom (m-1) w A ≃+ BiHom m w ((SyntheticCategory.biShift (0,-1)).obj
      ((SyntheticCategory.biShift (1,1)).obj A)) :=
  (suspInvarianceAddEquiv (m-1) w 1 1 A) |>.trans
    (regradeAddEquiv (by omega) rfl) |>.trans
    (verticalTranslate _ (-1) m (w+1)) |>.trans
    (regradeAddEquiv rfl (by omega))

private def earlyActualShiftEquiv (A : SyntheticSpectrum) (m w : ℤ) :
    BiHom (m-1) w A ≃+ BiHom m w ((SyntheticCategory.biShift (0,-1)).obj
      ((SyntheticCategory.biShift (1,1)).obj A)) := by
  letI := background.exactness.shiftCommShift (0,-1)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,1)
  exact (verticalTranslate A 1 (m-1) w) |>.trans
    (biSuspensionHomEquiv m w 1 (G.obj A)).symm |>.trans
    (homPostcompAddEquiv ((F.commShiftIso (1:ℤ)).symm.app (G.obj A))) |>.trans
    (homPostcompAddEquiv (F.mapIso (positiveOrdinaryIso.app A)))

private theorem early_standard_shift_eq (A : SyntheticSpectrum) (m w : ℤ)
    (a : BiHom (m-1) w A) :
    earlyStandardShiftEquiv A m w a =
      homotopyRegrade (show ((m,w+1)+(0,-1)).1=m by simp)
        (show ((m,w+1)+(0,-1)).2=w by dsimp; omega)
        (shiftHomotopyClass (0,-1) (m,w+1)
          (homotopyRegrade (show ((m-1,w)+(1,1)).1=m by dsimp; omega) rfl
            (shiftHomotopyClass (1,1) (m-1,w) a))) := by
  simp [earlyStandardShiftEquiv,verticalTranslate,suspInvarianceAddEquiv,
    regradeAddEquiv,susp_invariance,Iso.homCongr,shiftHomotopyClass,
    normalized_homotopy_regrade_trans]

private theorem early_standard_shift_regraded (A : SyntheticSpectrum)
    (m n k w w' : ℤ) (hn : n=m-1) (hk : m=k) (hw : w=w')
    (a : BiHom n w A) :
    homotopyRegrade hk hw (earlyStandardShiftEquiv A m w (homotopyRegrade hn rfl a)) =
      homotopyRegrade (show ((k,w+1)+(0,-1)).1=k by simp)
        (show ((k,w+1)+(0,-1)).2=w' by dsimp; omega)
        (shiftHomotopyClass (0,-1) (k,w+1)
          (homotopyRegrade (show ((n,w)+(1,1)).1=k by dsimp; omega) rfl
            (shiftHomotopyClass (1,1) (n,w) a))) := by
  subst n; subst k; subst w'
  simpa only [top_target_regrade_self] using early_standard_shift_eq A m w a

private theorem early_standard_shift_natural {A B : SyntheticSpectrum}
    (f : A ⟶ B) (m w : ℤ) (a : BiHom (m-1) w A) :
    earlyStandardShiftEquiv B m w (a ≫ f) =
      earlyStandardShiftEquiv A m w a ≫
        (SyntheticCategory.biShift (0,-1)).map ((SyntheticCategory.biShift (1,1)).map f) := by
  simp only [earlyStandardShiftEquiv,AddEquiv.trans_apply,regradeAddEquiv,
    suspInvarianceAddEquiv,AddEquiv.coe_mk,Equiv.coe_fn_mk]
  have hs : susp_invariance (m-1) w 1 1 B (a ≫ f) =
      susp_invariance (m-1) w 1 1 A a ≫ (SyntheticCategory.biShift (1,1)).map f := by
    simp [susp_invariance,Functor.map_comp,Category.assoc]
  rw [hs,regrade_comp,←vertical_translate_comp,regrade_comp]

private theorem early_actual_shift_natural {A B : SyntheticSpectrum}
    (f : A ⟶ B) (m w : ℤ) (a : BiHom (m-1) w A) :
    earlyActualShiftEquiv B m w (a ≫ f) =
      earlyActualShiftEquiv A m w a ≫
        (SyntheticCategory.biShift (0,-1)).map ((SyntheticCategory.biShift (1,1)).map f) := by
  letI := background.exactness.shiftCommShift (0,-1)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,1)
  let D := shiftFunctor SyntheticSpectrum (1:ℤ)
  let κ := F.commShiftIso (1:ℤ)
  simp only [earlyActualShiftEquiv,AddEquiv.trans_apply,homPostcompAddEquiv,
    AddEquiv.coe_mk,Equiv.coe_fn_mk,Iso.app_hom,Iso.symm_hom,Functor.mapIso_hom]
  rw [←vertical_translate_comp,bi_susp_symm_natural]
  simp only [Category.assoc]
  have hn : D.map (F.map (G.map f)) ≫ κ.inv.app (G.obj B) =
      κ.inv.app (G.obj A) ≫ F.map (D.map (G.map f)) := κ.inv.naturality (G.map f)
  rw [←Category.assoc (D.map (F.map (G.map f))),hn]
  simp only [Category.assoc]
  have hn' : D.map (G.map f) ≫ positiveOrdinaryIso.hom.app B =
      positiveOrdinaryIso.hom.app A ≫ (SyntheticCategory.biShift (1,1)).map f :=
    positiveOrdinaryIso.hom.naturality f
  rw [←Functor.map_comp,hn',Functor.map_comp]

private theorem early_standard_shift_symm_natural {A B : SyntheticSpectrum}
    (f : A ⟶ B) (m w : ℤ)
    (a : BiHom m w ((SyntheticCategory.biShift (0,-1)).obj
      ((SyntheticCategory.biShift (1,1)).obj A))) :
    (earlyStandardShiftEquiv B m w).symm
        (a ≫ (SyntheticCategory.biShift (0,-1)).map ((SyntheticCategory.biShift (1,1)).map f)) =
      (earlyStandardShiftEquiv A m w).symm a ≫ f := by
  apply (earlyStandardShiftEquiv B m w).injective
  rw [AddEquiv.apply_symm_apply,early_standard_shift_natural,AddEquiv.apply_symm_apply]

private def earlyShiftReindex (A : SyntheticSpectrum) (m w : ℤ) :
    BiHom (m-1) w A ≃+ BiHom (m-1) w A :=
  (earlyActualShiftEquiv A m w).trans (earlyStandardShiftEquiv A m w).symm

private theorem early_shift_reindex_natural {A B : SyntheticSpectrum}
    (f : A ⟶ B) (m w : ℤ) (a : BiHom (m-1) w A) :
    earlyShiftReindex B m w (a ≫ f) = earlyShiftReindex A m w a ≫ f := by
  simp only [earlyShiftReindex,AddEquiv.trans_apply]
  rw [early_actual_shift_natural,early_standard_shift_symm_natural]

private def earlyShiftSourceIso (m w : ℤ) :
    Smn (Syn:=SyntheticSpectrum) (m-1) w ≅ Smn (m-1) w where
  hom := earlyShiftReindex _ m w (𝟙 _)
  inv := (earlyShiftReindex _ m w).symm (𝟙 _)
  hom_inv_id := by
    rw [←early_shift_reindex_natural,Category.id_comp,AddEquiv.apply_symm_apply]
  inv_hom_id := by
    apply (earlyShiftReindex _ m w).injective
    rw [early_shift_reindex_natural,AddEquiv.apply_symm_apply,Category.id_comp]

private theorem early_actual_shift_first_quotient
    (X : (AdamsObject (coefficients := background.coefficients))) (m w : ℤ)
    (a : BiHom (m-1) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1)) :
    earlyActualShiftEquiv _ m w a = earlyStandardShiftEquiv _ m w a := by
  have h : earlyShiftReindex _ m w a = (earlyShiftSourceIso m w).hom ≫ a := by
    simpa only [Category.id_comp,earlyShiftSourceIso] using
      early_shift_reindex_natural a m w (𝟙 _)
  rw [sphere_automorphism_first_finite] at h
  apply (earlyStandardShiftEquiv _ m w).symm.injective
  simpa only [earlyShiftReindex,AddEquiv.trans_apply,AddEquiv.symm_apply_apply] using h

private def transportedSuspensionQuotientIso {A B : SyntheticSpectrum}
    (E : A ≅ B) (q : ℕ)
    (e : XModLambdaN (A⟦(1:ℤ)⟧) q ≅ (XModLambdaN A q)⟦(1:ℤ)⟧) :
    XModLambdaN (B⟦(1:ℤ)⟧) q ≅ (XModLambdaN B q)⟦(1:ℤ)⟧ :=
  (background.quotients.functoriality.functor q).mapIso
      ((shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso E.symm) ≪≫ e ≪≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso ((background.quotients.functoriality.functor q).mapIso E)

private theorem transported_suspension_quotient_incl {A B : SyntheticSpectrum}
    (E : A ≅ B) (q : ℕ)
    (e : XModLambdaN (A⟦(1:ℤ)⟧) q ≅ (XModLambdaN A q)⟦(1:ℤ)⟧)
    (he : XModLambdaN.incl _ q ≫ e.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q)) :
    XModLambdaN.incl _ q ≫ (transportedSuspensionQuotientIso E q e).hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q) := by
  change XModLambdaN.incl _ q ≫ XModLambdaN.map
    ((shiftFunctor SyntheticSpectrum (1:ℤ)).map E.inv) q ≫ e.hom ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map E.hom q) = _
  rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,
    ←Category.assoc _ e.hom,he,←Functor.map_comp,
    ←XModLambdaN.incl_naturality,←Functor.map_comp]
  simp only [←Category.assoc,E.inv_hom_id,Category.id_comp]

private theorem transported_suspension_comparisons_equal
    (X : (AdamsObject (coefficients := background.coefficients))) {A : SyntheticSpectrum}
    (E : A ≅ (SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (X.obj background.auxiliary)))
    (e₁ e₂ : XModLambdaN (A⟦(1:ℤ)⟧) 1 ≅ (XModLambdaN A 1)⟦(1:ℤ)⟧)
    (h₁ : XModLambdaN.incl _ 1 ≫ e₁.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ 1))
    (h₂ : XModLambdaN.incl _ 1 ≫ e₂.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ 1))
    (m w : ℤ) (a : BiHom m w (XModLambdaN (A⟦(1:ℤ)⟧) 1)) :
    a ≫ e₁.hom = a ≫ e₂.hom := by
  let P := (background.quotients.functoriality.functor 1).mapIso
    ((shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso E)
  let Q := (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
    ((background.quotients.functoriality.functor 1).mapIso E)
  have h := finite_suspension_comparisons_equal_on_spheres X 1 1 (by decide)
    (transportedSuspensionQuotientIso E 1 e₁) (transportedSuspensionQuotientIso E 1 e₂)
    (transported_suspension_quotient_incl E 1 e₁ h₁)
    (transported_suspension_quotient_incl E 1 e₂ h₂) m w (a ≫ P.hom)
  change (a ≫ P.hom) ≫ (P.inv ≫ e₁.hom ≫ Q.hom) =
    (a ≫ P.hom) ≫ (P.inv ≫ e₂.hom ≫ Q.hom) at h
  simp only [Category.assoc,P.hom_inv_id_assoc] at h
  exact (cancel_mono Q.hom).mp (by simpa only [Category.assoc] using h)

private theorem early_rotated_input_native_first
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
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
    (s t : ℤ) (u : Ambient background T.X (s+1,t)) :
    earlyRotatedInput T he ex (t-s) t (earlyPositiveBoundaryInput T he hf s t u) ≫
        (SyntheticCategory.biShift (0,-1)).map
          (XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
            (normalizedPositiveSourceIso T hf).hom ≫ positiveOrdinaryIso.hom.app _) 1) ≫
        (SyntheticCategory.biShift (0,-1)).map ε₁.hom =
      earlyStandardShiftEquiv _ (t-s) t
        (homotopyRegrade (show t-(s+1)=(t-s)-1 by omega) rfl (nativeFirstLabel T.X (s+1) t u)) := by
  letI := background.exactness.shiftCommShift (0,-1)
  let A := background.nu.functor.obj (T.X.obj background.auxiliary)
  let N := (normalizedTriangle background T he).obj₁
  let E := normalizedPositiveSourceIso T hf
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
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
  let b := earlyPositiveBoundaryInput T he hf s t u
  have hd := shift_preserves_sphere_congruence _ _ (0,-1) ex.inv ex0.inv hinv
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
  let a := homotopyRegrade (show t-(s+1)=(t-s)-1 by omega) rfl
    (nativeFirstLabel T.X (s+1) t u)
  have hfirst : homotopyRegrade (show t-(s+1)=(t-s)-1 by omega) rfl
      (earlyNormalizedSourceLabel T he hf (s+1) t u) ≫
        (XModLambdaN.map E.hom 1 ≫ εp.hom) = verticalTranslate _ 1 ((t-s)-1) t a := by
    dsimp only [earlyNormalizedSourceLabel,a,E]
    rw [←regrade_comp,Category.assoc,←Category.assoc (XModLambdaN.map _ 1),
      ←background.quotients.functoriality.map_comp,Iso.inv_hom_id,
      background.quotients.functoriality.map_id,Category.id_comp]
    have hregrade {m m' w w' : ℤ} (hm : m=m') (hw : w=w')
        (a : BiHom m w (XModLambdaN A 1)) :
        verticalTranslate _ 1 m' w' (homotopyRegrade hm hw a) =
          homotopyRegrade hm (congrArg (fun z : ℤ => z+1) hw) (verticalTranslate _ 1 m w a) := by
      subst m'; subst w'; rfl
    rw [hregrade,←positive_first_label_shift]
    simp only [εp,Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rfl
  have ha : earlyRotatedInput T he ex (t-s) t b ≫
        F.map (XModLambdaN.map (D.map E.hom ≫ positiveOrdinaryIso.hom.app A) 1) ≫ F.map ε₁.hom =
      earlyActualShiftEquiv _ (t-s) t a := by
    change (b ≫ κ.inv.app _ ≫ F.map ex.inv) ≫ _ ≫ _ = _
    rw [←Category.assoc b (κ.inv.app _),hd]
    simp only [Category.assoc]
    rw [←Functor.map_comp,←Functor.map_comp,hcomp,Functor.map_comp]
    have hn := κ.inv.naturality (XModLambdaN.map E.hom 1 ≫ εp.hom)
    have hn' : D.map (F.map (XModLambdaN.map E.hom 1 ≫ εp.hom)) ≫
        κ.inv.app (G.obj (XModLambdaN A 1)) =
      κ.inv.app (XModLambdaN N 1) ≫ F.map (D.map (XModLambdaN.map E.hom 1 ≫ εp.hom)) := hn
    rw [←Category.assoc (κ.inv.app _),←hn',←Category.assoc b]
    dsimp only [b,earlyPositiveBoundaryInput]
    rw [←Category.assoc _ (D.map (F.map (XModLambdaN.map E.hom 1 ≫ εp.hom)))]
    have hb := bi_susp_symm_natural (t-s) t 1 (XModLambdaN.map E.hom 1 ≫ εp.hom)
      (homotopyRegrade (show t-(s+1)=(t-s)-1 by omega) rfl
        (earlyNormalizedSourceLabel T he hf (s+1) t u))
    erw [←hb,hfirst]
    rfl
  exact ha.trans (early_actual_shift_first_quotient T.X (t-s) t a)

/-- The selected coefficient inclusion of the inverse-rotated input is
exactly the prescribed native top label after the fixed May desuspension. -/
private theorem early_rotated_input_top_label
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (ex : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ 1)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ 1 ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ 1))
    (ε₂ : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) 2 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2))
    (hε₂ : XModLambdaN.incl _ 2 ≫ ε₂.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 2))
    (s t : ℤ) (u : Ambient background T.X (s+1,t)) :
    rawMaySourceDesuspend T he hf 2 1 (s+1) t ε₂
      (homotopyRegrade (show t-s=t-(s+1)+1 by omega) (show t=t-(1:ℕ)+1 by omega)
        (earlyRotatedInput T he ex (t-s) t (earlyPositiveBoundaryInput T he hf s t u) ≫
          ((background.quotients.tower ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧)).triangle
            (show 0<1 by decide) (show 1<2 by decide)).lambdaMap)) =
      finiteTopLabel T.X 1 (by decide) (s+1) t u := by
  letI := background.exactness.shiftCommShift (1,1)
  letI := background.exactness.shiftExact (1,1)
  let A := background.nu.functor.obj (T.X.obj background.auxiliary)
  obtain ⟨ε₁,hε₁,_⟩ := quotient_shift_exists background.quotients.coherence (1,1) 1 A
  let E := (shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalizedPositiveSourceIso T hf).hom ≫
    positiveOrdinaryIso.hom.app A
  let d := earlyRotatedInput T he ex (t-s) t (earlyPositiveBoundaryInput T he hf s t u)
  let z := nativeFirstLabel T.X (s+1) t u
  let zH := homotopyRegrade (show ((t-(s+1),t)+(1,1)).1=t+1-(s+1) by dsimp; omega) rfl
    (shiftHomotopyClass (1,1) (t-(s+1),t) z) ≫ ε₁.inv
  have hfirst := early_rotated_input_native_first T he hf ex hex ε₁ hε₁ s t u
  have hfirst' := congrArg (fun a => a ≫ (SyntheticCategory.biShift (0,-1)).map ε₁.inv) hfirst
  simp only [Category.assoc,←Functor.map_comp,ε₁.hom_inv_id,
    ] at hfirst'
  erw [Category.comp_id] at hfirst'
  have hstd : homotopyRegrade (show t-s=t+1-(s+1) by omega)
      (show t=t+1-(1:ℕ) by omega)
      (d ≫ (SyntheticCategory.biShift (0,-1)).map (XModLambdaN.map E 1)) =
      homotopyRegrade (show ((t+1-(s+1),t+1)+(0,-(1:ℤ))).1=t+1-(s+1) by simp)
        (show ((t+1-(s+1),t+1)+(0,-(1:ℤ))).2=t+1-(1:ℕ) by dsimp; omega)
        (shiftHomotopyClass (0,-(1:ℤ)) (t+1-(s+1),t+1) zH) := by
    have h := congrArg (homotopyRegrade (show t-s=t+1-(s+1) by omega)
      (show t=t+1-(1:ℕ) by omega)) hfirst'
    simp only [regrade_comp] at h
    rw [early_standard_shift_regraded] at h
    simpa only [d,E,z,zH,shift_hom_comp,regrade_comp] using h
  have hlambda := shifted_finite_lambda_class T.X 2 1 (by decide) (by decide)
    (s+1) t ε₁ ε₂ hε₁ hε₂ z
  have heq : homotopyRegrade (show t-s=t+1-(s+1) by omega)
      (show t=t+1-(1:ℕ) by omega)
      ((d ≫ ((background.quotients.tower ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧)).triangle
        (show 0<1 by decide) (show 1<2 by decide)).lambdaMap) ≫ XModLambdaN.map E 2) =
      homotopyRegrade (m':=t+1-(s+1)) (w':=t+1-(1:ℕ)) (by dsimp; omega) (by dsimp; omega)
        (shiftHomotopyClass (1,1) (t-(s+1),t-(1:ℕ))
          (finiteLambdaClass T.X 2 1 (by decide) (by decide) (s+1) t z)) ≫ ε₂.inv := by
    rw [Category.assoc]
    erw [←(background.quotients.natural E).lambda_naturality
      (show 0<1 by decide) (show 1<2 by decide)]
    rw [←Category.assoc,regrade_comp]
    erw [hstd]
    exact hlambda.symm
  have heq' := congrArg (fun a => quotientUnshift T.X (1,1) (t-(s+1),t-(1:ℕ)) 2 ε₂
    (homotopyRegrade (show t+1-(s+1)=((t-(s+1),t-(1:ℕ))+(1,1)).1 by dsimp; omega)
      (show t+1-(1:ℕ)=((t-(s+1),t-(1:ℕ))+(1,1)).2 by dsimp; omega) a)) heq
  have hE : E = (normalizedSuspensionNativeIso T he hf).hom ≫
      (background.nu.suspensionIso (T.X.obj background.auxiliary)).hom :=
    normalizedPositiveSourceIso_suspension T he hf
  rw [hE,background.quotients.functoriality.map_comp] at heq'
  simpa only [rawMaySourceDesuspend,regrade_comp,normalized_homotopy_regrade_trans,
    top_target_regrade_self,quotient_unshift_shift,d,z,finiteTopLabel,finiteTopOfFirst,
    finiteTopInclusion,oneInclusionCast,finiteLambdaClass,Category.assoc] using heq'

/-- The original early differential produces one Q₂ root with both the
prescribed G₂ first label and the exact native highest-layer H image. -/
private theorem early_positive_rotated_first_and_top
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (ε₂ : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) 2 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2))
    (hε₂ : XModLambdaN.incl _ 2 ≫ ε₂.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 2))
    (s t : ℤ) (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (s+1,t))
    (hd : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      2 (s,t) (s+1+1,t+1) c
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+1) t u)) :
    ∃ R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ 2),
      R ≫ (background.quotients.tower _).rho 1 2 (by decide) =
        nativeFirstLabel T.Z s t ((background.classical.map T.g).pageMap 2 (s,t) c) ≫
          XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1 ∧
      rawMaySourceDesuspend T he hf 2 1 (s+1) t ε₂
        (homotopyRegrade (show t-s=t-(s+1)+1 by omega) (show t=t-(1:ℕ)+1 by omega)
          (R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ 2)) =
        finiteTopLabel T.X 1 (by decide) (s+1) t u := by
  obtain ⟨ex,hex,R,hR,hRh⟩ := early_positive_rotated_of_d2 T he hT hf hg s t c u hd
  refine ⟨R,hR,?_⟩
  rw [hRh]
  exact early_rotated_input_top_label T he hf ex hex ε₂ hε₂ s t u

end
end KIP126.ProofTools.Internal.SyntheticCoverage
