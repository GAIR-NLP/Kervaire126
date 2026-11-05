module

import all KIP126.ProofTools.GeneralizedMahowald.FiniteMayAtTriangle
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelSourceLabel
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingDelta
import all KIP126.ProofTools.GeneralizedMahowald.RotatedNuTriangle
import all KIP126.ProofTools.MahowaldLeibniz.Filtration
import all KIP126.ProofTools.MahowaldLeibniz.Bockstein

/-! Finite-quotient Mahowald–Leibniz comparison. The normalized triangle
constructs the finite May representative. Under the stated detection and
higher-filtration annihilation hypotheses, a prescribed representative
with the same detected source has the same image. -/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/-- The unit comparison removes exponent-zero negative-target normalization
as an equality of maps. -/
private theorem negative_lift_zero_comparison {A B : SyntheticSpectrum} {k : ℕ}
    (hk : k=0) (M : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B)
    (g : A ⟶ B) (hM : lambdaToPositivePow k A ≫ M = g) :
    negativeLift k M ≫
      eqToHom (congrArg (fun j : ℕ =>
        (SyntheticCategory.biShift (0,-(j:ℤ))).obj B) hk) ≫
      SyntheticCategory.biShift_zero.hom.app B = g := by
  subst k
  simp only [eqToHom_refl,Category.id_comp]
  have hf := negative_lift_factorization 0 M
  simpa only [lambdaPow] using hf.trans hM

/-- The comparison from the normalized third vertex to the native νZ when
the actual exponent of g is zero. -/
private def normalizedThirdZeroIso
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0) :
    (normalizedTriangle background T he).obj₃ ≅
      background.nu.functor.obj (T.Z.obj background.auxiliary) :=
  eqToIso (congrArg (fun j : ℕ =>
    (SyntheticCategory.biShift (0,-(j:ℤ))).obj
      (background.nu.functor.obj (T.Z.obj background.auxiliary))) hg) ≪≫
    SyntheticCategory.biShift_zero.app _

/-- The literal second normalized arrow is νg after this comparison.
Consequently the ordinary E₂ map is appropriate exactly in this branch. -/
private theorem normalized_second_arrow_zero
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0) :
    (normalizedTriangle background T he).mor₂ ≫
      (normalizedThirdZeroIso T he hg).hom = background.nu.functor.map T.g := by
  exact negative_lift_zero_comparison hg (background.normalizedMap T.Y T.Z T.g).map
    (background.nu.functor.map T.g) (background.normalizedMap T.Y T.Z T.g).factorization

private theorem raw_connecting_one_zero_zero {A C D : SyntheticSpectrum}
    (ef eg eh : ℕ) (he : (ef:ℤ)+eg+eh=1)
    (hf : ef=1) (hg : eg=0) (hh : eh=0)
    (h : (SyntheticCategory.biShift (0,(eh:ℤ))).obj C ⟶ D)
    (σ : D ≅ (SyntheticCategory.biShift (1,1)).obj A)
    (g : C ⟶ D) (hfg : lambdaToPositivePow eh C ≫ h=g) :
    raw_normalized_connecting ef eg eh he h σ ≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _ ≫
      (SyntheticCategory.biShift_comp (0,(ef:ℤ)) (1,0)).hom.app A ≫
      eqToHom (congrArg (fun p : ℤ×ℤ => (SyntheticCategory.biShift p).obj A)
        (show (0,(ef:ℤ))+(1,0)=(1,1) by ext <;> dsimp <;> omega)) =
      (zero_negative_iso C eg hg).hom ≫ g ≫ σ.hom := by
  subst ef
  subst eg
  subst eh
  have hh := negative_lift_zero_map_form 0 rfl h g hfg
  dsimp only [raw_normalized_connecting,zero_negative_iso] at hh ⊢
  simp only [eqToHom_refl,eqToIso_refl,Iso.trans_hom,Iso.refl_hom,
    Category.id_comp,Category.comp_id] at hh ⊢
  simp only [Category.assoc,Iso.hom_inv_id_app_assoc]
  have hr := background.quotients.coherence.right_unit (1,1) A
  dsimp only [biShiftAddIso] at hr
  simp only [eqToIso_refl,Iso.trans_refl] at hr
  erw [hr]
  erw [SyntheticCategory.biShift_zero.hom.naturality_assoc]
  erw [SyntheticCategory.biShift_zero.hom.naturality_assoc]
  erw [SyntheticCategory.biShift_zero.hom.naturality_assoc]
  simp only [Functor.id_map,Iso.inv_hom_id_app]
  erw [Category.comp_id]
  erw [SyntheticCategory.biShift_zero.hom.naturality]
  simp only [Functor.id_map,←Category.assoc]
  rw [Category.assoc _ (negativeLift 0 h)]
  erw [hh]
  rfl

/-- The actual suspension comparison used when e_f=1.  Both the ordinary
suspension and the positive weight shift are retained in the definition. -/
private def normalizedSuspensionNativeIso
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1) :
    ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) ≅
      background.nu.functor.obj ((AdamsObject.shift 1 T.X).obj background.auxiliary) :=
  (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
    (SyntheticCategory.biShift_comp
      (0,(normalizedExponent background.classicalTower T.f:ℤ)) (1,0)).app _ ≪≫
    eqToIso (congrArg (fun p : ℤ×ℤ => (SyntheticCategory.biShift p).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary)))
      (show (0,(normalizedExponent background.classicalTower T.f:ℤ))+(1,0)=(1,1)
        by ext <;> dsimp <;> omega)) ≪≫
    (background.nu.suspensionIso (T.X.obj background.auxiliary)).symm

/-- Comparison of the normalized connecting arrow with νh. The branch
`e_f=1,e_g=e_h=0` uses the specified suspension isomorphism. -/
private theorem normalized_third_arrow_zero
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0) :
    (normalizedTriangle background T he).mor₃ ≫
      (normalizedSuspensionNativeIso T he hf).hom =
      (normalizedThirdZeroIso T he hg).hom ≫ background.nu.functor.map T.h := by
  have h := raw_connecting_one_zero_zero _ _ _ he hf hg hh
    (background.normalizedMap T.Z (.shift 1 T.X) T.h).map
    (background.nu.suspensionIso (T.X.obj background.auxiliary))
    (background.nu.functor.map T.h)
    (background.normalizedMap T.Z (.shift 1 T.X) T.h).factorization
  have h' := congrArg (fun z => z ≫ (background.nu.suspensionIso
    (T.X.obj background.auxiliary)).inv) h
  simpa only [normalizedTriangle,Triangle.mk,normalizedConnecting,
    raw_normalized_connecting,normalizedSuspensionNativeIso,
    normalizedThirdZeroIso,zero_negative_iso,Iso.trans_hom,Iso.symm_hom,
    Iso.app_hom,Iso.app_inv,eqToIso.hom,Category.assoc,Iso.hom_inv_id,
    Category.comp_id] using h'

/-- The actual first quotient coordinates commute strictly with ν of a
classical map.  Detection naturality gives equality modulo the next
filtration, and the one-layer window makes that ambiguity zero. -/
private theorem native_first_label_natural
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t : ℤ) (x : Ambient background X (s,t)) :
    nativeFirstLabel X s t x ≫ XModLambdaN.map (background.nu.functor.map f) 1 =
      nativeFirstLabel Y s t ((background.classical.map f).pageMap 2 (s,t) x) := by
  have ha := first_label_detects_unshifted X 1 (by omega) s t x
    (nativeFirstLabel X s t x) (by
      rw [(background.quotients.tower _).rho_id,Category.comp_id]
      rfl)
  have hb := first_label_detects_unshifted Y 1 (by omega) s t
    ((background.classical.map f).pageMap 2 (s,t) x)
    (nativeFirstLabel Y s t ((background.classical.map f).pageMap 2 (s,t) x)) (by
      rw [(background.quotients.tower _).rho_id,Category.comp_id]
      rfl)
  have hm := detects_map (.quotient 1 (.nu X)) (.quotient 1 (.nu Y))
    (XModLambdaN.map (background.nu.functor.map f) 1) (s,t,t) _ _ ha
  rw [←zero_weight_label X 1 s t x] at hm
  erw [finite_weight_label_natural X Y f 1 s t t (by omega) x] at hm
  rw [zero_weight_label Y 1 s t] at hm
  exact finite_top_detection_unique Y 1 (by omega) s t t (by omega) _ _ _ hm hb

private def adjacentDelta (A : SyntheticSpectrum) (q : ℕ) (hq : 0<q) :
    XModLambdaN A q ⟶
      ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧ := by
  simpa only [show q.succ-q=1 by omega] using
    ((background.quotients.tower A).triangle hq (Nat.lt_succ_self q)).delta

private theorem adjacent_delta_natural {A B : SyntheticSpectrum}
    (f : A ⟶ B) (q : ℕ) (hq : 0<q) :
    XModLambdaN.map f q ≫ adjacentDelta B q hq =
      adjacentDelta A q hq ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(q:ℤ))).map (XModLambdaN.map f 1)) := by
  have h := (background.quotients.natural f).delta_naturality hq (Nat.lt_succ_self q)
  have transport (n : ℕ) (hn : n=1)
      (da : XModLambdaN A q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧)
      (db : XModLambdaN B q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN B n))⟦(1:ℤ)⟧)
      (h : XModLambdaN.map f q ≫ db = da ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(q:ℤ))).map (XModLambdaN.map f n))) :
      XModLambdaN.map f q ≫
        (Eq.mp (congrArg (fun j => XModLambdaN B q ⟶
          ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN B j))⟦(1:ℤ)⟧) hn) db) =
      (Eq.mp (congrArg (fun j => XModLambdaN A q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A j))⟦(1:ℤ)⟧) hn) da) ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(q:ℤ))).map (XModLambdaN.map f 1)) := by
    subst n
    exact h
  exact transport (q.succ-q) (by omega) _ _ h

private theorem homotopy_regrade_injective {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') :
    Function.Injective (homotopyRegrade hm hw (X:=A)) := by
  subst m'
  subst w'
  exact fun _ _ h => h

/-- A prescribed second classical differential produces the exact finite
delta--g square.  In particular its target is the supplied v, including
when its first-quotient image is an earlier classical boundary. -/
private theorem classical_differential_finite_square
    (Y Z : AdamsObject (coefficients := background.coefficients)) (g : Y.obj background.auxiliary ⟶ Z.obj background.auxiliary)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient background Z (s,t)) (v : Ambient background Y (s+q+1,t+q))
    (hd : HasDifferential (background.classical.obj (Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z
      ((background.classical.map g).pageMap 2 (s+q+1,t+q) v)) :
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel Y (s+q+1) (t+q) v))
    ∃ a : BiHom (t-s) t
        (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) q),
      a ≫ (background.quotients.tower _).rho 1 q hq = nativeFirstLabel Z s t z ∧
      a ≫ adjacentDelta _ q hq =
        b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(q:ℤ))).map
            (XModLambdaN.map (background.nu.functor.map g) 1)) := by
  dsimp only
  obtain ⟨a,ha,hd⟩ := (differential_iff_specified_finite_lift Z q hq s t z
    ((background.classical.map g).pageMap 2 (s+q+1,t+q) v)).mp hd
  refine ⟨a,ha,?_⟩
  apply (biSuspensionHomEquiv (t-s) t (q:ℤ)
    (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) 1)).injective
  rw [bi_susp_natural background.quotients.coherence,AddEquiv.apply_symm_apply]
  apply homotopy_regrade_injective
    (show (t-s)-1=(t+q)-(s+q+1) by omega) rfl
  rw [regrade_comp,homotopy_regrade_inverse,
    native_first_label_natural Y Z g (s+q+1) (t+q) v]
  simpa only [adjacentFiniteBoundary,adjacentDelta] using hd

/-- The second classical differential supplies a finite May representative.
The Bockstein lift and TR3/TR4 give its source and signed target image. -/
private theorem classical_second_differential_may
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient background T.Z (s,t)) (v : Ambient background T.Y (s+q+1,t+q))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z
      ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
    (ey : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ (q+1))⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1))) :
    let V := normalizedTriangle background T he
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel T.Y (s+q+1) (t+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN V.obj₂ 1) ⟶
        XModLambdaN V.obj₂ (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((background.quotients.tower V.obj₂).triangle hq (Nat.lt_succ_self q)).lambdaMap
    ∃ (a : BiHom (t-s) t (XModLambdaN V.obj₃ q))
      (c : BiHom (t-s) t (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (q+1))),
      a ≫ (background.quotients.tower _).rho 1 q hq =
        nativeFirstLabel T.Z s t z ≫ XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1 ∧
      a ≫ adjacentDelta V.obj₃ q hq =
        b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(q:ℤ))).map (XModLambdaN.map V.mor₂ 1)) ∧
      c ≫ (background.quotients.tower _).rho q (q+1) (by omega) =
        a ≫ XModLambdaN.map V.mor₃ q ∧
      c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (q+1) ≫
        ey.hom = -(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly) := by
  dsimp only
  let V := normalizedTriangle background T he
  let E := normalizedThirdZeroIso T he hg
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
    (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1)).symm
      (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
        (nativeFirstLabel T.Y (s+q+1) (t+q) v))
  obtain ⟨a₀,ha₀,hab₀⟩ := classical_differential_finite_square T.Y T.Z T.g q hq s t z v hd
  let a := a₀ ≫ XModLambdaN.map E.inv q
  have hag : background.nu.functor.map T.g ≫ E.inv = V.mor₂ := by
    apply (cancel_mono E.hom).mp
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      (normalized_second_arrow_zero T he hg).symm
  have hab : a ≫ adjacentDelta V.obj₃ q hq =
      b ≫ S.map (F.map (XModLambdaN.map V.mor₂ 1)) := by
    dsimp only [a]
    rw [Category.assoc,adjacent_delta_natural E.inv q hq,←Category.assoc,hab₀]
    simp only [Category.assoc]
    rw [←Functor.map_comp,←Functor.map_comp,
      ←background.quotients.functoriality.map_comp,hag]
  obtain ⟨c,hcr,hcf⟩ := finite_may_at_normalized_triangle_explicit_lengths T he hT q 1 hq
    (by omega) (t-s) t ey hey a b hab
  refine ⟨a,c,?_,hab,hcr,hcf⟩
  dsimp only [a]
  rw [Category.assoc,←(background.quotients.natural E.inv).rho_naturality hq,
    ←Category.assoc,ha₀]

/-- At level zero the May representative has exactly the prescribed
ordinary h₂z first label after the fixed suspension comparison. -/
private theorem finite_may_source_first_label
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q N : ℕ) (hq : 0<q) (hqN : q≤N) (s t : ℤ)
    (z : Ambient background T.Z (s,t))
    (a : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ q))
    (c : BiHom (t-s) t
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N))
    (ha : a ≫ (background.quotients.tower _).rho 1 q hq =
      nativeFirstLabel T.Z s t z ≫ XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1)
    (hc : c ≫ (background.quotients.tower _).rho q N hqN =
      a ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ q) :
    (c ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N) ≫
      (background.quotients.tower _).rho 1 N (by omega) =
        nativeFirstLabel (.shift 1 T.X) s t
          ((background.classical.map T.h).pageMap 2 (s,t) z) := by
  let E := normalizedSuspensionNativeIso T he hf
  let EZ := normalizedThirdZeroIso T he hg
  let V := normalizedTriangle background T he
  have hfirst : c ≫ (background.quotients.tower _).rho 1 N (by omega) =
      (nativeFirstLabel T.Z s t z ≫ XModLambdaN.map EZ.inv 1) ≫
        XModLambdaN.map V.mor₃ 1 := by
    rw [←(background.quotients.tower _).rho_comp (show 1≤q by omega) hqN,
      ←Category.assoc,hc,Category.assoc,
      ←(background.quotients.natural V.mor₃).rho_naturality hq,
      ←Category.assoc,ha]
  rw [Category.assoc,←(background.quotients.natural E.hom).rho_naturality (show 1≤N by omega),
    ←Category.assoc,hfirst]
  simp only [Category.assoc]
  rw [←background.quotients.functoriality.map_comp,normalized_third_arrow_zero T he hf hg hh,
    ←background.quotients.functoriality.map_comp]
  simp only [EZ,Category.assoc,Iso.inv_hom_id_assoc]
  exact native_first_label_natural T.Z (.shift 1 T.X) T.h s t z

/-- The actual May source therefore detects h₂z at the bottom finite
layer, and its cycle qualification follows from that same actual lift. -/
private theorem finite_may_source_detects
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q N : ℕ) (hq : 0<q) (hqN : q≤N) (s t : ℤ)
    (z : Ambient background T.Z (s,t))
    (a : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ q))
    (c : BiHom (t-s) t
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N))
    (ha : a ≫ (background.quotients.tower _).rho 1 q hq =
      nativeFirstLabel T.Z s t z ≫ XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1)
    (hc : c ≫ (background.quotients.tower _).rho q N hqN =
      a ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ q) :
    Detects (background.convergence (.quotient N (.nu (.shift 1 T.X)))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel background (.shift 1 T.X) N s t 0
        ((background.classical.map T.h).pageMap 2 (s,t) z)))
      (c ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N) ∧
      IsCycle background (.shift 1 T.X) N (s,t)
        ((background.classical.map T.h).pageMap 2 (s,t) z) := by
  have hfirst := finite_may_source_first_label T he hf hg hh q N hq hqN s t z a c ha hc
  exact ⟨first_label_detects_unshifted (.shift 1 T.X) N (by omega) s t _ _ hfirst,
    specified_adjacent_lift_cycles (.shift 1 T.X) N (by omega) s t _ _ hfirst⟩

/-- Finite May comparison at any visible source level K, using the fixed
triangle and quotient lengths. TR3/TR4 supplies the May representative.
-/
private theorem finite_may_image_of_same_source_and_annihilation
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (A B K : ℕ) (hA : 0 < A) (hB : 0 < B) (hKA : K < A)
    (s t : ℤ) (p : ℤ × ℤ)
    (hp : p.1 = t-s+1)
    (hw : p.2 = t+(normalizedExponent background.classicalTower T.f : ℤ)-K)
    (x : Ambient background T.X (s,t))
    (exA : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) A ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ A)⟦(1:ℤ)⟧)
    (exN : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (A+B) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ (A+B))⟦(1:ℤ)⟧)
    (eyN : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) (A+B) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ (A+B))⟦(1:ℤ)⟧)
    (hexA : XModLambdaN.incl _ A ≫ exA.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ A))
    (hexN : XModLambdaN.incl _ (A+B) ≫ exN.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (A+B)))
    (heyN : XModLambdaN.incl _ (A+B) ≫ eyN.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (A+B)))
    (a : BiHom p.1 p.2 (XModLambdaN (normalizedTriangle background T he).obj₃ A))
    (b : BiHom p.1 p.2
      (((SyntheticCategory.biShift (0,-(A:ℤ))).obj
        (XModLambdaN (normalizedTriangle background T he).obj₂ ((A+B)-A)))⟦(1:ℤ)⟧))
    (d : BiHom p.1 p.2
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (A+B)))
    (hab : a ≫ ((background.quotients.tower (normalizedTriangle background T he).obj₃).triangle
        hA (show A < A+B by omega)).delta =
      b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(A:ℤ))).map
          (XModLambdaN.map (normalizedTriangle background T he).mor₂ ((A+B)-A))))
    (ha : Detects (background.convergence (.shift (1,0) (.quotient A
        (.shift (0,(normalizedExponent background.classicalTower T.f : ℤ)) (.nu T.X)))))
      (s,p.1+s,p.2)
      (finiteConclusionSourceLabel T.X A K (normalizedExponent background.classicalTower T.f)
        s t p hp hw x)
      (homotopyRegrade (by dsimp; omega) rfl
        (a ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ A ≫ exA.hom ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)))
    (hd : Detects (background.convergence (.shift (1,0) (.quotient (A+B)
        (.shift (0,(normalizedExponent background.classicalTower T.f : ℤ)) (.nu T.X)))))
      (s,p.1+s,p.2)
      (finiteConclusionSourceLabel T.X (A+B) K (normalizedExponent background.classicalTower T.f)
        s t p hp hw x)
      (homotopyRegrade (by dsimp; omega) rfl
        (d ≫ exN.hom ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)))
    (hkill : ∀ e : BiHom p.1 p.2
        (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (A+B)),
      FiltrationAtLeast background.syntheticTower (s+1)
        (e ≫ exN.hom ≫ (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _) →
      e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (A+B) ≫ eyN.hom = 0) :
    x ∈ cycles background T.X ((A+B:ℕ)-K) (s,t) ∧
      d ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (normalizedTriangle background T he).mor₁) (A+B) ≫ eyN.hom =
        -(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((background.quotients.tower (normalizedTriangle background T he).obj₂).triangle
            hA (show A < A+B by omega)).lambdaMap) := by
  obtain ⟨c,hcr,hcf⟩ := finite_may_at_normalized_triangle T he hT A B hA hB
    p.1 p.2 eyN heyN a b hab
  obtain ⟨hc,hx⟩ := finite_suspended_source_label_reflection T.X
    (normalizedExponent background.classicalTower T.f) A (A+B) K (by omega) hKA
    s t p hp hw x exA exN hexA hexN
    (a ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ A) c hcr (by
      simpa only [Category.assoc,normalizedTriangle,Triangle.mk,SyntheticObject.obj] using ha)
  refine ⟨?_,?_⟩
  · simpa only [Nat.cast_sub (show K ≤ A+B by omega),Nat.cast_add] using hx
  · have hdiff := detects_sub_filtration
      (background.convergence (.shift (1,0) (.quotient (A+B)
        (.shift (0,(normalizedExponent background.classicalTower T.f : ℤ)) (.nu T.X)))))
      (s,p.1+s,p.2) hd hc
    have hdiff' : FiltrationAtLeast background.syntheticTower (s+1)
        ((d-c) ≫ exN.hom ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _) := by
      apply (regrade_filtration_iff (show p.1 = (p.1+s)-s by omega) rfl (s+1) _).mp
      simpa only [Preadditive.sub_comp,regrade_precomp,Preadditive.comp_sub,
        normalizedTriangle,Triangle.mk,SyntheticObject.obj,Category.assoc] using hdiff
    have hz := hkill (d-c) hdiff'
    simp only [Preadditive.sub_comp] at hz
    exact (sub_eq_zero.mp hz).trans hcf

/-- The existing classical finite-layer condition annihilates the actual
higher-filtration ambiguity of the normalized triangle.  The finite quotient
comparison is used as a map between the selected convergent objects. -/
private theorem finite_layer_surj_normalized_annihilation
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (hT : NormalizedTriangleCompatible background T he)
    (c K : ℕ) (hK : 2≤K) (S V : ℤ)
    (hsurj : KIP126.ProofTools.Standard.MahowaldLeibnizFiniteLayerSurjectivity
      T (c+2) K (S-(c+2:ℕ)) (V-(c+2:ℕ)+1))
    (exQ : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+K) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ (c+K))⟦(1:ℤ)⟧)
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+K)))
    (ha : FiltrationAtLeast background.syntheticTower (S+1)
      (a ≫ exQ.hom ≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) :
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) (c+K) = 0 := by
  let N := normalizedTriangle background T he
  let E := normalizedSuspensionNativeIso T he hf
  let EZ := normalizedThirdZeroIso T he hg
  let Source : SyntheticObject (coefficients := background.coefficients) := .shift (1,0)
    (.quotient (c+K) (extensionSourceObject background T.X T.Y T.f))
  let Target : SyntheticObject (coefficients := background.coefficients) := .quotient (c+K) (.nu (.shift 1 T.X))
  let j : Source.obj background.nu background.auxiliary ⟶ Target.obj background.nu background.auxiliary :=
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app _ ≫
      exQ.inv ≫ XModLambdaN.map E.hom (c+K)
  have hat : FiltrationAtLeast background.syntheticTower (S+1)
      (a ≫ XModLambdaN.map E.hom (c+K)) := by
    have h := map_preserves_filtration (background.convergentMap Source Target j)
      (V-S+1,V-c+1) (S+1)
      (a ≫ exQ.hom ≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _) ha
    change FiltrationAtLeast background.syntheticTower (S+1)
      ((a ≫ exQ.hom ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app
            (XModLambdaN N.obj₁ (c+K))) ≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app
          (XModLambdaN N.obj₁ (c+K)) ≫ exQ.inv ≫
          XModLambdaN.map E.hom (c+K)) at h
    simpa only [Category.assoc,Iso.inv_hom_id_app_assoc,Iso.hom_inv_id_assoc] using h
  obtain ⟨b,_,hb⟩ := finite_layer_surj_ordinary_h_filtered T c K hK S V hsurj
    (a ≫ XModLambdaN.map E.hom (c+K)) hat
  have hcomm : XModLambdaN.map N.mor₃ (c+K) ≫ XModLambdaN.map E.hom (c+K) =
      XModLambdaN.map EZ.hom (c+K) ≫
        XModLambdaN.map (background.nu.functor.map T.h) (c+K) := by
    rw [←background.quotients.functoriality.map_comp,←background.quotients.functoriality.map_comp]
    exact congrArg (fun f => XModLambdaN.map f (c+K))
      (normalized_third_arrow_zero T he hf hg hh)
  have haq : (b ≫ XModLambdaN.map EZ.inv (c+K)) ≫
      XModLambdaN.map N.mor₃ (c+K) = a := by
    let eQ := (background.quotients.functoriality.functor (c+K)).mapIso E
    apply (cancel_mono eQ.hom).mp
    change _ ≫ XModLambdaN.map E.hom (c+K) = _
    rw [Category.assoc,Category.assoc,hcomm]
    rw [←Category.assoc (XModLambdaN.map EZ.inv (c+K)),
      ←background.quotients.functoriality.map_comp,Iso.inv_hom_id,
      background.quotients.functoriality.map_id,Category.id_comp]
    exact hb
  obtain ⟨ey,_,hrow⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he (c+K) (by omega)
  have hzero := comp_distTriang_mor_zero₂₃ _ hrow
  change XModLambdaN.map N.mor₃ (c+K) ≫
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) (c+K) ≫
      ey.hom))=0 at hzero
  rw [Preadditive.comp_neg,neg_eq_zero] at hzero
  have hzero' : XModLambdaN.map N.mor₃ (c+K) ≫
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) (c+K)=0 := by
    apply (cancel_mono ey.hom).mp
    simpa only [Category.assoc,zero_comp] using hzero
  rw [←haq,Category.assoc,hzero',comp_zero]

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
