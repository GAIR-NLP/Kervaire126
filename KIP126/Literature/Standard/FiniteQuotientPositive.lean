module

import all KIP126.Literature.Standard.FiniteQuotientNaturality
import KIP126.AdamsSynthetic.Completed.ClassicalSupport

/-! Actual positive lambda lifts: exact ambiguity and strict spherical
uniqueness in the negative-Adams-filtration range. All statements retain
existing lambda powers, selected quotient objects, and actual maps.
-/

@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

section Generic
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [hCof : HasFunctorialCofiber (C := Syn)]

private def positive_lambda_source_iso (k : ℕ) :
    (𝟭 Syn) ≅ SyntheticCategory.biShift (0,(k:ℤ)) ⋙
      SyntheticCategory.biShift (0,-(k:ℤ)) :=
  SyntheticCategory.biShift_zero.symm ≪≫
    eqToIso (congrArg SyntheticCategory.biShift
      (show ((0:ℤ),(0:ℤ)) = (0,(k:ℤ))+(0,-(k:ℤ)) by ext <;> simp)) ≪≫
    (SyntheticCategory.biShift_comp (0,(k:ℤ)) (0,-(k:ℤ))).symm

omit hCof in
private theorem positive_lambda_factorization (k : ℕ) (A : Syn) :
    lambdaToPositivePow k A = (positive_lambda_source_iso k).hom.app A ≫
      lambdaPow k ((SyntheticCategory.biShift (0,(k:ℤ))).obj A) := by
  simp only [positive_lambda_source_iso,lambdaToPositivePow,Iso.trans_hom,
    Iso.symm_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app]
  simp only [Category.assoc]

omit hCof in
private theorem positive_lambda_naturality (k : ℕ) {A B : Syn} (f : A ⟶ B) :
    lambdaToPositivePow k A ≫ (SyntheticCategory.biShift (0,(k:ℤ))).map f =
      f ≫ lambdaToPositivePow k B := by
  rw [positive_lambda_factorization,positive_lambda_factorization,Category.assoc,
    ←lambdaPow_naturality]
  have hn := (positive_lambda_source_iso k).hom.naturality f
  dsimp only [Functor.id_map,Functor.comp_map] at hn
  simpa only [Category.assoc] using
    (congrArg (fun z => z ≫ lambdaPow k
      ((SyntheticCategory.biShift (0,(k:ℤ))).obj B)) hn).symm

/-- The full ambiguity is through this actual Q_k(F_k A), with the same
specified pair of maps and their actual difference. -/
private theorem positive_lambda_lifts_same_iff_quotient_factor
    (k : ℕ) {A B : Syn}
    (M N : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B) :
    lambdaToPositivePow k A ≫ M = lambdaToPositivePow k A ≫ N ↔
      ∃ z : XModLambdaN ((SyntheticCategory.biShift (0,(k:ℤ))).obj A) k ⟶ B,
        M-N = XModLambdaN.incl ((SyntheticCategory.biShift (0,(k:ℤ))).obj A) k ≫ z := by
  constructor
  · intro hMN
    have hzero : lambdaToPositivePow k A ≫ (M-N) = 0 := by
      rw [Preadditive.comp_sub,hMN,sub_self]
    rw [positive_lambda_factorization,Category.assoc] at hzero
    have hkernel : lambdaPow k ((SyntheticCategory.biShift (0,(k:ℤ))).obj A) ≫ (M-N) = 0 :=
      (cancel_epi ((positive_lambda_source_iso k).hom.app A)).mp (by simpa using hzero)
    exact (XModLambdaN.cofiberTriangle _ k).yoneda_exact₂
      (XModLambdaN.cofiberTriangle_distinguished _ k) (M-N) hkernel
  · rintro ⟨z,hz⟩
    apply sub_eq_zero.mp
    rw [←Preadditive.comp_sub,hz,positive_lambda_factorization]
    calc
      _ = (positive_lambda_source_iso k).hom.app A ≫
          ((lambdaPow k ((SyntheticCategory.biShift (0,(k:ℤ))).obj A) ≫
            XModLambdaN.incl ((SyntheticCategory.biShift (0,(k:ℤ))).obj A) k) ≫ z) := by
        simp only [Category.assoc]
      _ = 0 := by rw [XModLambdaN.lambdaPow_comp_incl,zero_comp,comp_zero]

omit hCof in
private theorem positive_negative_lift_factorization (k : ℕ) {A B : Syn}
    (M : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B) :
    negativeLift k M ≫ lambdaPow k B = lambdaToPositivePow k A ≫ M := by
  simp only [negativeLift,lambdaToPositivePow,Category.assoc]
  rw [lambdaPow_naturality]

omit hCof in
private theorem positive_negative_lift_reflects_zero (k : ℕ) {A B : Syn}
    (M : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B)
    (hM : negativeLift k M = 0) : M=0 := by
  have hsource : negativeLift k M = (positive_lambda_source_iso k).hom.app A ≫
      (SyntheticCategory.biShift (0,-(k:ℤ))).map M := by
    simp only [positive_lambda_source_iso,negativeLift,Iso.trans_hom,Iso.symm_hom,
      NatTrans.comp_app,eqToIso.hom,eqToHom_app]
    simp only [Category.assoc]
  rw [hsource] at hM
  letI : (SyntheticCategory.biShift (Syn:=Syn) (0,-(k:ℤ))).Additive := by
    let p : ℤ×ℤ := (0,-(k:ℤ))
    letI : (SyntheticCategory.biShift (Syn:=Syn) p).IsEquivalence :=
      Functor.IsEquivalence.mk' (SyntheticCategory.biShift (-p))
        (SyntheticCategory.biShift_zero.symm ≪≫
          eqToIso (congrArg SyntheticCategory.biShift
            (by simp : (0:ℤ×ℤ)=p + -p)) ≪≫
          (SyntheticCategory.biShift_comp p (-p)).symm)
        (SyntheticCategory.biShift_comp (-p) p ≪≫
          eqToIso (congrArg SyntheticCategory.biShift
            (by simp : -p+p=(0:ℤ×ℤ))) ≪≫ SyntheticCategory.biShift_zero)
    exact Functor.additive_of_preserves_binary_products _
  have hmap : (SyntheticCategory.biShift (0,-(k:ℤ))).map M = 0 :=
    (cancel_epi ((positive_lambda_source_iso k).hom.app A)).mp (by simpa using hM)
  exact (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-(k:ℤ))).map_injective
    (by simpa only [Functor.map_zero] using hmap)


omit hCof in
private theorem positive_negative_lift_surjective (k : ℕ) {A B : Syn}
    (a : A ⟶ (SyntheticCategory.biShift (0,-(k:ℤ))).obj B) :
    ∃ M : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B, negativeLift k M = a := by
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-(k:ℤ))
  let M := ff.preimage ((positive_lambda_source_iso k).inv.app A ≫ a)
  refine ⟨M,?_⟩
  have hsource : negativeLift k M = (positive_lambda_source_iso k).hom.app A ≫
      (SyntheticCategory.biShift (0,-(k:ℤ))).map M := by
    simp only [positive_lambda_source_iso,negativeLift,Iso.trans_hom,Iso.symm_hom,
      NatTrans.comp_app,eqToIso.hom,eqToHom_app,Category.assoc]
  rw [hsource]
  change (positive_lambda_source_iso k).hom.app A ≫
    (SyntheticCategory.biShift (0,-(k:ℤ))).map (ff.preimage _) = _
  rw [ff.map_preimage]
  simp only [←Category.assoc,Iso.hom_inv_id_app,Category.id_comp]

end Generic

private theorem positive_quotient_one_negative (X : AdamsObject (coefficients := background.coefficients)) (m w : ℤ)
    (h : w < m)
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1)) :
    a = 0 := by
  let e := (background.quotients.functoriality.functor 1).mapIso
    ((SyntheticCategory.biShift_zero (Syn:=SyntheticSpectrum)).symm.app
      (background.nu.functor.obj (X.obj background.auxiliary)))
  haveI := classical_page_negative X 2 (w-m) w (by omega)
  have he : a ≫ e.hom = 0 := by
    let e0 := background.firstQuotient X 0 (w-m) w
    have hz : (e0 (homotopyRegrade (by omega) (by simp) (a≫e.hom))) = 0 :=
      Subsingleton.elim _ _
    have hz' : homotopyRegrade (m':=w-(w-m)) (w':=w+0) (by omega) (by simp) (a≫e.hom) = 0 :=
      e0.injective (hz.trans (map_zero e0).symm)
    have hc {m' w' : ℤ} (hm : m=m') (hw : w=w')
        (c : BiHom m w (XModLambdaN (KIP126.Literature.nuZero background X) 1)) :
        homotopyRegrade hm hw c=0 ↔ c=0 := by
      subst m'; subst w'; rfl
    exact (hc _ _ _).mp hz'

  exact (cancel_mono e.hom).mp (by simpa only [zero_comp] using he)

private theorem positive_lambda_one_injective_of_quotient_vanishing
    (D Y : SyntheticSpectrum)
    (hz : ∀ b : D⟦(1:ℤ)⟧ ⟶ XModLambdaN Y 1, b=0)
    (a : D ⟶ (SyntheticCategory.biShift (0,-1)).obj Y)
    (ha : a≫SyntheticCategory.lam.app Y=0) : a=0 := by
  let F := shiftFunctor SyntheticSpectrum (1:ℤ)
  have hshift : F.map a≫F.map (lambdaPow 1 Y)=0 := by
    rw [←Functor.map_comp,lambdaPow_one background.quotients.coherence,ha,Functor.map_zero]
  obtain ⟨b,hb⟩ := (XModLambdaN.cofiberTriangle Y 1).coyoneda_exact₁
    (XModLambdaN.cofiberTriangle_distinguished Y 1) (F.map a) hshift
  have hf : F.map a=0 := by rw [hb,hz b,zero_comp]
  exact F.map_injective (by simpa only [Functor.map_zero] using hf)

private theorem positive_lambda_one_injective_at_diagonal (X : AdamsObject (coefficients := background.coefficients)) (m w : ℤ)
    (h : w ≤ m)
    (a : Smn (Syn:=SyntheticSpectrum) m w ⟶
      (SyntheticCategory.biShift (0,-1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary)))
    (ha : a≫SyntheticCategory.lam.app _ = 0) : a = 0 := by
  let Y := background.nu.functor.obj (X.obj background.auxiliary)
  let F := shiftFunctor SyntheticSpectrum (1:ℤ)
  have hshift : F.map a ≫ F.map (lambdaPow 1 Y) = 0 := by
    rw [←Functor.map_comp]
    have hpow : lambdaPow 1 Y = SyntheticCategory.lam.app Y :=
      lambdaPow_one background.quotients.coherence Y
    rw [hpow,ha,Functor.map_zero]
  obtain ⟨b,hb⟩ := (XModLambdaN.cofiberTriangle Y 1).coyoneda_exact₁
    (XModLambdaN.cofiberTriangle_distinguished Y 1) (F.map a) hshift
  let eS : Smn (Syn:=SyntheticSpectrum) (m+1) w ≅ F.obj (Smn m w) :=
    ((biShiftAddIso (m,w) (1,0) (m+1,w) (by ext <;> simp)).app S_0_0).symm ≪≫
      (SyntheticCategory.biShift_compat 1).app (Smn m w)
  have hz : eS.hom≫b=0 := positive_quotient_one_negative X (m+1) w (by omega) _
  have hb0 : b=0 := (cancel_epi eS.hom).mp (by simpa only [comp_zero] using hz)
  have hf : F.map a=0 := by rw [hb,hb0,zero_comp]
  exact F.map_injective (by simpa only [Functor.map_zero] using hf)


/-- Positive lambda division is unique as a sphere map in the stated range. -/
private theorem positive_lambda_lift_unique_sphere
    (Y : AdamsObject (coefficients := background.coefficients)) (m w : ℤ) (hw : w≤m)
    (M N : (SyntheticCategory.biShift (0,(1:ℤ))).obj
        (Smn (Syn:=SyntheticSpectrum) m w) ⟶
      background.nu.functor.obj (Y.obj background.auxiliary))
    (hMN : lambdaToPositivePow 1 (Smn m w) ≫ M =
      lambdaToPositivePow 1 (Smn m w) ≫ N) : M=N := by
  have hdiff : lambdaToPositivePow 1 (Smn m w) ≫ (M-N) = 0 := by
    rw [Preadditive.comp_sub,hMN,sub_self]
  have hnegative : negativeLift 1 (M-N) ≫ SyntheticCategory.lam.app _ = 0 := by
    have hp := (positive_negative_lift_factorization 1 (M-N)).trans hdiff
    simpa only [lambdaPow_one background.quotients.coherence] using hp
  have hzero := positive_lambda_one_injective_at_diagonal Y m w hw
    (negativeLift 1 (M-N)) hnegative
  exact sub_eq_zero.mp (positive_negative_lift_reflects_zero 1 (M-N) hzero)


/-- Positive lambda division below the diagonal from negative-filtration
vanishing in the first quotient. -/
private theorem positive_lambda_lift_surjective_sphere
    (Y : AdamsObject (coefficients := background.coefficients)) (m w : ℤ) (hw : w<m)
    (d : BiHom m w (background.nu.functor.obj (Y.obj background.auxiliary))) :
    ∃ M : (SyntheticCategory.biShift (0,(1:ℤ))).obj (Smn m w) ⟶
        background.nu.functor.obj (Y.obj background.auxiliary),
      lambdaToPositivePow 1 (Smn m w) ≫ M = d := by
  have hzero : d ≫ XModLambdaN.incl _ 1 = 0 :=
    positive_quotient_one_negative Y m w hw _
  obtain ⟨a,ha⟩ := (XModLambdaN.cofiberTriangle _ 1).coyoneda_exact₂
    (XModLambdaN.cofiberTriangle_distinguished _ 1) d hzero
  obtain ⟨M,hM⟩ := positive_negative_lift_surjective 1 a
  refine ⟨M,?_⟩
  rw [←positive_negative_lift_factorization,hM]
  exact ha.symm

private theorem positive_lambda_lift_unique_of_sphere_iso
    (Y : AdamsObject (coefficients := background.coefficients)) {A : SyntheticSpectrum} (m w : ℤ) (hw : w≤m)
    (e : A ≅ Smn m w)
    (M N : (SyntheticCategory.biShift (0,(1:ℤ))).obj A ⟶
      background.nu.functor.obj (Y.obj background.auxiliary))
    (hMN : lambdaToPositivePow 1 A ≫ M = lambdaToPositivePow 1 A ≫ N) : M=N := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,(1:ℤ))
  have hn := positive_lambda_naturality 1 e.inv
  change lambdaToPositivePow 1 (Smn m w) ≫ F.map e.inv = e.inv ≫ lambdaToPositivePow 1 A at hn
  have hcomp : lambdaToPositivePow 1 (Smn m w) ≫ (F.map e.inv ≫ M) =
      lambdaToPositivePow 1 (Smn m w) ≫ (F.map e.inv ≫ N) := by
    rw [←Category.assoc,hn,Category.assoc,hMN,←Category.assoc,←hn,Category.assoc]
  have heq := positive_lambda_lift_unique_sphere Y m w hw
    (F.map e.inv ≫ M) (F.map e.inv ≫ N) hcomp
  exact (cancel_epi (F.map e.inv)).mp heq

private theorem positive_lambda_lift_surjective_of_sphere_iso
    (Y : AdamsObject (coefficients := background.coefficients)) {A : SyntheticSpectrum} (m w : ℤ) (hw : w<m)
    (e : A ≅ Smn m w)
    (d : A ⟶ background.nu.functor.obj (Y.obj background.auxiliary)) :
    ∃ M : (SyntheticCategory.biShift (0,(1:ℤ))).obj A ⟶
        background.nu.functor.obj (Y.obj background.auxiliary),
      lambdaToPositivePow 1 A ≫ M = d := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,(1:ℤ))
  obtain ⟨M,hM⟩ := positive_lambda_lift_surjective_sphere Y m w hw (e.inv ≫ d)
  refine ⟨F.map e.hom ≫ M,?_⟩
  have hn := positive_lambda_naturality 1 e.hom
  change lambdaToPositivePow 1 A ≫ F.map e.hom = e.hom ≫ lambdaToPositivePow 1 (Smn m w) at hn
  rw [←Category.assoc,hn,Category.assoc,hM,←Category.assoc,Iso.hom_inv_id,Category.id_comp]

/-- Strict positive-lambda uniqueness extends across a distinguished
triangle through its first two shifted arrows. -/
private theorem positive_lambda_lift_unique_middle
    (Y : AdamsObject (coefficients := background.coefficients)) (T : Triangle SyntheticSpectrum)
    (hT : T ∈ distTriang SyntheticSpectrum)
    (hinjA : Function.Injective (fun M :
        (SyntheticCategory.biShift (0,(1:ℤ))).obj T.obj₁ ⟶
          background.nu.functor.obj (Y.obj background.auxiliary) => lambdaToPositivePow 1 T.obj₁ ≫ M))
    (hinjC : Function.Injective (fun M :
        (SyntheticCategory.biShift (0,(1:ℤ))).obj T.obj₃ ⟶
          background.nu.functor.obj (Y.obj background.auxiliary) => lambdaToPositivePow 1 T.obj₃ ≫ M))
    (hsurj : Function.Surjective (fun M :
        (SyntheticCategory.biShift (0,(1:ℤ))).obj (T.obj₁⟦(1:ℤ)⟧) ⟶
          background.nu.functor.obj (Y.obj background.auxiliary) =>
            lambdaToPositivePow 1 (T.obj₁⟦(1:ℤ)⟧) ≫ M)) :
    Function.Injective (fun M :
      (SyntheticCategory.biShift (0,(1:ℤ))).obj T.obj₂ ⟶
        background.nu.functor.obj (Y.obj background.auxiliary) => lambdaToPositivePow 1 T.obj₂ ≫ M) := by
  letI := background.exactness.shiftAdditive (0,(1:ℤ))
  letI := background.exactness.shiftCommShift (0,(1:ℤ))
  letI := background.exactness.shiftExact (0,(1:ℤ))
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,(1:ℤ))
  intro M N hMN
  dsimp only at hMN
  have hnatf := positive_lambda_naturality 1 T.mor₁
  change lambdaToPositivePow 1 T.obj₁ ≫ F.map T.mor₁ = T.mor₁ ≫ lambdaToPositivePow 1 T.obj₂ at hnatf
  have hnatg := positive_lambda_naturality 1 T.mor₂
  change lambdaToPositivePow 1 T.obj₂ ≫ F.map T.mor₂ = T.mor₂ ≫ lambdaToPositivePow 1 T.obj₃ at hnatg
  have hnath := positive_lambda_naturality 1 T.mor₃
  change lambdaToPositivePow 1 T.obj₃ ≫ F.map T.mor₃ = T.mor₃ ≫ lambdaToPositivePow 1 (T.obj₁⟦(1:ℤ)⟧) at hnath
  have hd : lambdaToPositivePow 1 T.obj₂ ≫ (M-N) = 0 := by
    rw [Preadditive.comp_sub,hMN,sub_self]
  have hf : F.map T.mor₁ ≫ (M-N) = 0 := by
    apply hinjA
    change lambdaToPositivePow 1 T.obj₁ ≫ (F.map T.mor₁ ≫ (M-N)) = lambdaToPositivePow 1 T.obj₁ ≫ 0
    rw [comp_zero,←Category.assoc,hnatf,Category.assoc,hd,comp_zero]
  obtain ⟨b,hb⟩ := (F.mapTriangle.obj T).yoneda_exact₂
    (F.map_distinguished T hT) (M-N) hf
  change F.obj T.obj₃ ⟶ background.nu.functor.obj (Y.obj background.auxiliary) at b
  change M-N = F.map T.mor₂ ≫ b at hb
  have hgb : T.mor₂ ≫ (lambdaToPositivePow 1 T.obj₃ ≫ b) = 0 := by
    calc
      _ = (lambdaToPositivePow 1 T.obj₂ ≫ F.map T.mor₂) ≫ b := by
        rw [←Category.assoc,←hnatg]
      _ = lambdaToPositivePow 1 T.obj₂ ≫ (M-N) := by rw [Category.assoc,←hb]
      _ = 0 := hd
  obtain ⟨d,hd'⟩ := T.yoneda_exact₃ hT (lambdaToPositivePow 1 T.obj₃ ≫ b) hgb
  obtain ⟨v,hv⟩ := hsurj d
  change lambdaToPositivePow 1 (T.obj₁⟦(1:ℤ)⟧) ≫ v = d at hv
  have hb' : b = F.map T.mor₃ ≫ v := by
    apply hinjC
    change lambdaToPositivePow 1 T.obj₃ ≫ b = lambdaToPositivePow 1 T.obj₃ ≫ (F.map T.mor₃ ≫ v)
    calc
      _ = T.mor₃ ≫ d := hd'
      _ = T.mor₃ ≫ (lambdaToPositivePow 1 (T.obj₁⟦(1:ℤ)⟧) ≫ v) := by rw [hv]
      _ = _ := by rw [←Category.assoc,←hnath,Category.assoc]
  apply sub_eq_zero.mp
  rw [hb,hb',←Category.assoc,←Functor.map_comp,
    comp_distTriang_mor_zero₂₃ T hT,Functor.map_zero,zero_comp]

private def positive_sphere_suspension_iso (m w : ℤ) :
    (Smn (Syn:=SyntheticSpectrum) m w)⟦(1:ℤ)⟧ ≅ Smn (m+1) w :=
  (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app (Smn m w) ≪≫
    (biShiftAddIso (m,w) (1,0) (m+1,w) (by ext <;> simp)).app S_0_0

/-- The normalized nu-cofiber triangle gives strict uniqueness on
nu Cnu, with selected nu Y as target, through its two diagonal sphere cells. -/
private theorem positive_lambda_lift_unique_nu_cofiber
    (Y : AdamsObject (coefficients := background.coefficients))
    (M N : (SyntheticCategory.biShift (0,(1:ℤ))).obj
        (background.nu.functor.obj (AdamsObject.nuCofiber.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Y.obj background.auxiliary))
    (hMN : lambdaToPositivePow 1
        (background.nu.functor.obj (AdamsObject.nuCofiber.obj background.auxiliary)) ≫ M =
      lambdaToPositivePow 1
        (background.nu.functor.obj (AdamsObject.nuCofiber.obj background.auxiliary)) ≫ N) : M=N := by
  let T := (KIP126.Literature.normalizedTriangle background background.auxiliary.nuRouteTriangle
    nuCofiber_exponent_sum).rotate
  have hT : T ∈ distTriang SyntheticSpectrum :=
    rot_of_distTriang _ nuCofiber_distinguished
  let eA : T.obj₁ ≅ Smn (Syn:=SyntheticSpectrum) 0 0 :=
    background.nu.unitIso ≪≫ SyntheticCategory.biShift_zero.symm.app S_0_0
  let eC : T.obj₃ ≅ Smn (Syn:=SyntheticSpectrum) 4 4 := by
    change ((SyntheticCategory.biShift
      (0,(normalizedExponent background.classicalTower background.auxiliary.nuMap:ℤ))).obj
      (background.nu.functor.obj (Sphere (C:=Spectrum) 3)))⟦(1:ℤ)⟧ ≅ _
    rw [nuCofiber_nu_exponent]
    exact (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
        ((SyntheticCategory.biShift (0,(1:ℤ))).mapIso (KIP126.Literature.nuSphereThree background) ≪≫
          (biShiftAddIso (3,3) (0,1) (3,4) (by decide)).app S_0_0) ≪≫
      positive_sphere_suspension_iso 3 4
  let eSA : T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 1 0 :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso eA ≪≫ positive_sphere_suspension_iso 0 0
  let eB : T.obj₂ ≅ background.nu.functor.obj (AdamsObject.nuCofiber.obj background.auxiliary) := by
    change (SyntheticCategory.biShift
      (0,-(normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g:ℤ))).obj
      (background.nu.functor.obj (AdamsObject.nuCofiber.obj background.auxiliary)) ≅ _
    rw [nuCofiber_bottom_exponent]
    exact SyntheticCategory.biShift_zero.app _
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,(1:ℤ))
  have hn := positive_lambda_naturality 1 eB.hom
  change lambdaToPositivePow 1 T.obj₂ ≫ F.map eB.hom =
    eB.hom ≫ lambdaToPositivePow 1
      (background.nu.functor.obj (AdamsObject.nuCofiber.obj background.auxiliary)) at hn
  have hcomp : lambdaToPositivePow 1 T.obj₂ ≫ (F.map eB.hom ≫ M) =
      lambdaToPositivePow 1 T.obj₂ ≫ (F.map eB.hom ≫ N) := by
    rw [←Category.assoc,hn,Category.assoc,hMN,←Category.assoc,←hn,Category.assoc]
  have heq := positive_lambda_lift_unique_middle Y T hT
    (fun a b hab => positive_lambda_lift_unique_of_sphere_iso Y 0 0 (by omega) eA a b hab)
    (fun a b hab => positive_lambda_lift_unique_of_sphere_iso Y 4 4 (by omega) eC a b hab)
    (fun d => positive_lambda_lift_surjective_of_sphere_iso Y 1 0 (by omega) eSA d) hcomp
  exact (cancel_epi (F.map eB.hom)).mp heq


/-- The actual selected positive normalized map, with only its source index
transported by the supplied equality e(f)=1. -/
private def positive_normalized_map_at_one (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (h1 : normalizedExponent background.classicalTower f = 1) :
    (SyntheticCategory.biShift (0,(1:ℤ))).obj
        (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Y.obj background.auxiliary) :=
  eqToHom (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
    (background.nu.functor.obj (X.obj background.auxiliary))) h1).symm ≫ (background.normalizedMap X Y f).map

private theorem positive_normalized_map_at_one_factorization (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (h1 : normalizedExponent background.classicalTower f = 1) :
    lambdaToPositivePow 1 (background.nu.functor.obj (X.obj background.auxiliary)) ≫
      positive_normalized_map_at_one X Y f h1 = background.nu.functor.map f := by
  have transport {A B : SyntheticSpectrum} (k : ℕ) (hk : k=1)
      (M : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B)
      (g : A ⟶ B) (hM : lambdaToPositivePow k A ≫ M = g) :
      lambdaToPositivePow 1 A ≫
        (eqToHom (congrArg (fun j : ℕ =>
          (SyntheticCategory.biShift (0,(j:ℤ))).obj A) hk).symm ≫ M) = g := by
    subst k
    simpa only [eqToHom_refl,Category.id_comp] using hM
  exact transport _ h1 _ _ (background.normalizedMap X Y f).factorization

/-- Exact lambda-kernel ambiguity for the actual exponent-one normalized
map. This retains the same comparison lift and actual quotient factor. -/
private theorem positive_normalized_one_ambiguity (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (h1 : normalizedExponent background.classicalTower f = 1)
    (N : (SyntheticCategory.biShift (0,(1:ℤ))).obj
        (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Y.obj background.auxiliary))
    (hN : lambdaToPositivePow 1 (background.nu.functor.obj (X.obj background.auxiliary)) ≫ N =
      background.nu.functor.map f) :
    ∃ z : XModLambdaN ((SyntheticCategory.biShift (0,(1:ℤ))).obj
          (background.nu.functor.obj (X.obj background.auxiliary))) 1 ⟶
        background.nu.functor.obj (Y.obj background.auxiliary),
      positive_normalized_map_at_one X Y f h1 - N = XModLambdaN.incl _ 1 ≫ z := by
  apply (positive_lambda_lifts_same_iff_quotient_factor 1 _ N).mp
  exact (positive_normalized_map_at_one_factorization X Y f h1).trans hN.symm

/-- The exponent-one normalized lift on the nu-sphere has zero lambda-kernel
ambiguity, with any selected nu Y as target. -/
private theorem positive_normalized_one_unique_sphere (Y : AdamsObject (coefficients := background.coefficients))
    (f : AdamsObject.sphere.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (h1 : normalizedExponent background.classicalTower f = 1)
    (N : (SyntheticCategory.biShift (0,(1:ℤ))).obj
        (background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Y.obj background.auxiliary))
    (hN : lambdaToPositivePow 1 (background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)) ≫ N =
      background.nu.functor.map f) : positive_normalized_map_at_one .sphere Y f h1 = N := by
  let e : background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary) ≅
      Smn (Syn:=SyntheticSpectrum) 0 0 :=
    background.nu.unitIso ≪≫ SyntheticCategory.biShift_zero.symm.app S_0_0
  apply positive_lambda_lift_unique_of_sphere_iso Y 0 0 (by omega) e
  exact (positive_normalized_map_at_one_factorization .sphere Y f h1).trans hN.symm

/-- The actual exponent-one normalized lift on nu Cnu is likewise strictly
unique, by the existing actual normalized nu-cofiber distinguished triangle. -/
private theorem positive_normalized_one_unique_nu_cofiber (Y : AdamsObject (coefficients := background.coefficients))
    (f : AdamsObject.nuCofiber.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (h1 : normalizedExponent background.classicalTower f = 1)
    (N : (SyntheticCategory.biShift (0,(1:ℤ))).obj
        (background.nu.functor.obj (AdamsObject.nuCofiber.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Y.obj background.auxiliary))
    (hN : lambdaToPositivePow 1 (background.nu.functor.obj (AdamsObject.nuCofiber.obj background.auxiliary)) ≫ N =
      background.nu.functor.map f) : positive_normalized_map_at_one .nuCofiber Y f h1 = N := by
  apply positive_lambda_lift_unique_nu_cofiber Y
  exact (positive_normalized_map_at_one_factorization .nuCofiber Y f h1).trans hN.symm

private theorem negative_hom_middle
    (T : Triangle SyntheticSpectrum) (hT : T ∈ distTriang SyntheticSpectrum)
    (D : SyntheticSpectrum)
    (hA : ∀ a : T.obj₁ ⟶ D, a=0)
    (hC : ∀ c : T.obj₃ ⟶ D, c=0)
    (b : T.obj₂ ⟶ D) : b=0 := by
  have hab : T.mor₁ ≫ b=0 := hA _
  obtain ⟨c,hc⟩ := T.yoneda_exact₂ hT b hab
  rw [hc,hC c,comp_zero]

private theorem negative_hom_shifted_first_sphere
    (Y : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (m w : ℤ) (hw : w+(q:ℤ)<m)
    (a : BiHom m w ((SyntheticCategory.biShift (0,-(q:ℤ))).obj
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) 1))) : a=0 := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,(q:ℤ))
  letI : F.Additive := background.exactness.shiftAdditive (0,(q:ℤ))
  let eS : F.obj (Smn (Syn:=SyntheticSpectrum) m w) ≅ Smn m (w+(q:ℤ)) :=
    (biShiftAddIso (m,w) (0,(q:ℤ)) (m,w+(q:ℤ)) (by ext <;> simp)).app S_0_0
  let eT : F.obj ((SyntheticCategory.biShift (0,-(q:ℤ))).obj
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) 1)) ≅
      XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) 1 :=
    (biShiftAddIso (0,-(q:ℤ)) (0,(q:ℤ)) (0,0) (by ext <;> simp)).app _ ≪≫
      SyntheticCategory.biShift_zero.app _
  have hz : eS.inv ≫ F.map a ≫ eT.hom=0 := positive_quotient_one_negative Y m (w+q) hw _
  have hmap : F.map a=0 := (cancel_mono eT.hom).mp
    ((cancel_epi eS.inv).mp (by simpa only [Category.assoc,comp_zero,zero_comp] using hz))
  exact (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,(q:ℤ))).map_injective
    (by simpa only [Functor.map_zero] using hmap)

/-- Actual finite-quotient negative window on sphere Hom, obtained only
from Q1 and the existing finite lambda-rho-delta triangles. -/
private theorem negative_hom_finite_sphere
    (Y : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0<q) (m w : ℤ)
    (hw : w+(q:ℤ)-1<m)
    (b : BiHom m w (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)) : b=0 := by
  induction q with
  | zero => omega
  | succ q ih =>
    by_cases hq0 : q=0
    · subst q
      exact positive_quotient_one_negative Y m w (by omega) b
    · have hqp : 0<q := by omega
      let L := (background.quotients.tower
        (background.nu.functor.obj (Y.obj background.auxiliary))).triangle hqp (Nat.lt_succ_self q)
      have hrho : b ≫ L.rho=0 := ih hqp (by omega) _
      obtain ⟨a,ha⟩ := (Triangle.mk L.lambdaMap L.rho L.delta).coyoneda_exact₂
        L.distinguished b hrho
      have ha0 : a=0 := by
        change BiHom m w ((SyntheticCategory.biShift (0,-(q:ℤ))).obj
          (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) ((q+1)-q))) at a
        have hzero (j : ℕ) (hj : j=1)
            (a' : BiHom m w ((SyntheticCategory.biShift (0,-(q:ℤ))).obj
              (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) j))) : a'=0 := by
          subst j
          exact negative_hom_shifted_first_sphere Y q m w (by omega) a'
        exact hzero _ (by omega) a
      rw [ha,ha0,zero_comp]

private theorem negative_hom_finite_sphere_iso
    (Y : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0<q) {D : SyntheticSpectrum} (m w : ℤ)
    (hw : w+(q:ℤ)-1<m) (e : D ≅ Smn m w)
    (b : D ⟶ XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q) : b=0 := by
  have hz : e.inv ≫ b=0 := negative_hom_finite_sphere Y q hq m w hw _
  exact (cancel_epi e.inv).mp (by simpa using hz)

private theorem negative_hom_shifted_nu_cofiber_finite
    (Y : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0<q) (m w : ℤ) (hw : w+(q:ℤ)≤m+1)
    (b : ((SyntheticCategory.biShift (m,w)).obj
      (background.nu.functor.obj (AdamsObject.nuCofiber.obj background.auxiliary)))⟦(1:ℤ)⟧ ⟶
      XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q) : b=0 := by
  let T := (KIP126.Literature.normalizedTriangle background background.auxiliary.nuRouteTriangle
    nuCofiber_exponent_sum).rotate
  have hT : T ∈ distTriang SyntheticSpectrum := rot_of_distTriang _ nuCofiber_distinguished
  let eA : T.obj₁ ≅ Smn (Syn:=SyntheticSpectrum) 0 0 :=
    background.nu.unitIso ≪≫ SyntheticCategory.biShift_zero.symm.app S_0_0
  let eC : T.obj₃ ≅ Smn (Syn:=SyntheticSpectrum) 4 4 := by
    change ((SyntheticCategory.biShift
      (0,(normalizedExponent background.classicalTower background.auxiliary.nuMap:ℤ))).obj
      (background.nu.functor.obj (Sphere (C:=Spectrum) 3)))⟦(1:ℤ)⟧ ≅ _
    rw [nuCofiber_nu_exponent]
    exact (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
        ((SyntheticCategory.biShift (0,(1:ℤ))).mapIso (KIP126.Literature.nuSphereThree background) ≪≫
          (biShiftAddIso (3,3) (0,1) (3,4) (by decide)).app S_0_0) ≪≫
      positive_sphere_suspension_iso 3 4
  let eB : T.obj₂ ≅ background.nu.functor.obj (AdamsObject.nuCofiber.obj background.auxiliary) := by
    change (SyntheticCategory.biShift
      (0,-(normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g:ℤ))).obj
      (background.nu.functor.obj (AdamsObject.nuCofiber.obj background.auxiliary)) ≅ _
    rw [nuCofiber_bottom_exponent]
    exact SyntheticCategory.biShift_zero.app _
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (m,w)
  letI : F.Additive := background.exactness.shiftAdditive (m,w)
  letI : F.CommShift ℤ := background.exactness.shiftCommShift (m,w)
  letI : F.IsTriangulated := background.exactness.shiftExact (m,w)
  let U := (F.mapTriangle.obj T)⟦(1:ℤ)⟧
  have hU : U ∈ distTriang SyntheticSpectrum :=
    Triangle.shift_distinguished _ (F.map_distinguished T hT) 1
  let eUA : U.obj₁ ≅ Smn (Syn:=SyntheticSpectrum) (m+1) w :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      (F.mapIso eA ≪≫
        (biShiftAddIso (0,0) (m,w) (m,w) (by ext <;> simp)).app S_0_0) ≪≫
      positive_sphere_suspension_iso m w
  let eUC : U.obj₃ ≅ Smn (Syn:=SyntheticSpectrum) (m+5) (w+4) :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      (F.mapIso eC ≪≫
        (biShiftAddIso (4,4) (m,w) (m+4,w+4) (by ext <;> simp [add_comm])).app S_0_0) ≪≫
      positive_sphere_suspension_iso (m+4) (w+4) ≪≫
      eqToIso (by congr 1; omega)
  let eUB : U.obj₂ ≅ ((SyntheticCategory.biShift (m,w)).obj
      (background.nu.functor.obj (AdamsObject.nuCofiber.obj background.auxiliary)))⟦(1:ℤ)⟧ :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso (F.mapIso eB)
  have hb : eUB.hom ≫ b=0 := negative_hom_middle U hU _
    (fun a => negative_hom_finite_sphere_iso Y q hq (m+1) w (by omega) eUA a)
    (fun c => negative_hom_finite_sphere_iso Y q hq (m+5) (w+4) (by omega) eUC c) _
  exact (cancel_epi eUB.hom).mp (by simpa using hb)


/-- Actual postcomposition by lambda^q is injective whenever this same
lambda cofiber has no Hom from the suspended source. -/
private theorem positive_lambda_power_injective_of_quotient_vanishing
    (D Y : SyntheticSpectrum) (q : ℕ)
    (hz : ∀ b : D⟦(1:ℤ)⟧ ⟶ XModLambdaN Y q, b=0)
    (a : D ⟶ (SyntheticCategory.biShift (0,-(q:ℤ))).obj Y)
    (ha : a≫lambdaPow q Y=0) : a=0 := by
  let F := shiftFunctor SyntheticSpectrum (1:ℤ)
  have hshift : F.map a≫F.map (lambdaPow q Y)=0 := by
    rw [←Functor.map_comp,ha,Functor.map_zero]
  obtain ⟨b,hb⟩ := (XModLambdaN.cofiberTriangle Y q).coyoneda_exact₁
    (XModLambdaN.cofiberTriangle_distinguished Y q) (F.map a) hshift
  have hf : F.map a=0 := by rw [hb,hz b,zero_comp]
  exact F.map_injective (by simpa only [Functor.map_zero] using hf)

/-- Strict global lambda^q-kernel vanishing on the actual shifted nu Cnu
source, retaining the exact finite window established above. -/
private theorem positive_lambda_power_injective_shifted_nu_cofiber
    (Y : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0<q) (m w : ℤ) (hw : w+(q:ℤ)≤m+1)
    (a : (SyntheticCategory.biShift (m,w)).obj
        (background.nu.functor.obj (AdamsObject.nuCofiber.obj background.auxiliary)) ⟶
      (SyntheticCategory.biShift (0,-(q:ℤ))).obj
        (background.nu.functor.obj (Y.obj background.auxiliary)))
    (ha : a≫lambdaPow q (background.nu.functor.obj (Y.obj background.auxiliary))=0) : a=0 := by
  exact positive_lambda_power_injective_of_quotient_vanishing _ _ q
    (fun b => negative_hom_shifted_nu_cofiber_finite Y q hq m w hw b) a ha

end
end KIP126.Literature.Standard
