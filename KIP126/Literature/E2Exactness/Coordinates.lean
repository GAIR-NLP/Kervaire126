module
public import KIP126.Literature.Standard
import all KIP126.Literature.E2Exactness.ClassicalSuspension
import all KIP126.Literature.Standard.FiniteQuotientNaturality
import all KIP126.Literature.Standard.FiniteQuotientNoReturn
import KIP126.AdamsSynthetic.Completed.FirstQuotientCompatibility

/-! Fixed first-quotient coordinates for the E₂ exact sequence. -/
@[expose] section
namespace KIP126.Literature.Standard.E2Exactness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.Literature.Standard.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
public def e2Connecting
    (T : TriangleData background.auxiliary)
    (hef : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ) (x : (background.classical.obj (T.X.obj background.auxiliary)).Page 2 (s,t)) :
    (background.classical.obj (T.Y.obj background.auxiliary)).Page 2 (s+1,t+1) :=
  let F : (SyntheticCategory.biShift (Syn := SyntheticSpectrum) (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary)) ⟶
      background.nu.functor.obj (T.Y.obj background.auxiliary) := by
    simpa only [hef, Nat.cast_one] using (background.normalizedMap T.X T.Y T.f).map
  let a := (background.firstQuotient T.X 1 s t).symm x
  let b := a ≫ XModLambdaN.map F 1 ≫
    XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app
      (background.nu.functor.obj (T.Y.obj background.auxiliary))) 1
  background.firstQuotient T.Y 0 (s+1) (t+1)
    (homotopyRegrade (by omega) (by omega) b)

private def nativeFirstLabel (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (x : Ambient background X (s,t)) :
    BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1) :=
  KIP126.Literature.firstLabel background X s t x ≫
    XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1

private theorem negative_lift_factorization {A B : SyntheticSpectrum} (k : ℕ)
    (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B) :
    negativeLift k f ≫ lambdaPow k B = lambdaToPositivePow k A ≫ f := by
  simp only [negativeLift,lambdaToPositivePow,Category.assoc]
  rw [lambdaPow_naturality]


private def zero_negative_iso (A : SyntheticSpectrum) (k : ℕ) (hk : k=0) :
    (SyntheticCategory.biShift (0,-(k:ℤ))).obj A ≅ A :=
  eqToIso (congrArg (fun j : ℕ => (SyntheticCategory.biShift (0,-(j:ℤ))).obj A) hk) ≪≫
    SyntheticCategory.biShift_zero.app A

private theorem negative_lift_zero_map_form {A B : SyntheticSpectrum} (k : ℕ)
    (hk : k=0) (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B)
    (g : A ⟶ B) (hfg : lambdaToPositivePow k A≫f=g) :
    negativeLift k f≫(zero_negative_iso B k hk).hom=g := by
  subst k
  have h := (negative_lift_factorization 0 f).trans hfg
  simpa only [zero_negative_iso,lambdaPow,eqToIso_refl,Iso.trans_hom,Iso.refl_hom,Category.id_comp,Iso.app_hom] using h

private def raw_normalized_connecting {A C D : SyntheticSpectrum} (ef eg eh : ℕ)
    (he : (ef:ℤ)+eg+eh=1)
    (h : (SyntheticCategory.biShift (0,(eh:ℤ))).obj C ⟶ D)
    (σ : D ≅ (SyntheticCategory.biShift (1,1)).obj A) :
    (SyntheticCategory.biShift (0,-(eg:ℤ))).obj C ⟶
      ((SyntheticCategory.biShift (0,(ef:ℤ))).obj A)⟦(1:ℤ)⟧ :=
  (SyntheticCategory.biShift (0,-(eg:ℤ))).map (negativeLift eh h) ≫
  (SyntheticCategory.biShift (0,-(eg:ℤ))).map
      ((SyntheticCategory.biShift (0,-(eh:ℤ))).map σ.hom) ≫
  (SyntheticCategory.biShift (0,-(eg:ℤ))).map
      ((SyntheticCategory.biShift_comp (1,1) (0,-(eh:ℤ))).hom.app A) ≫
  (SyntheticCategory.biShift_comp ((1,1)+(0,-(eh:ℤ))) (0,-(eg:ℤ))).hom.app A ≫
  eqToHom (congrArg (fun p => (SyntheticCategory.biShift p).obj A)
    (show ((1,1)+(0,-(eh:ℤ)))+(0,-(eg:ℤ))=(0,(ef:ℤ))+(1,0) from by
      ext
      · rfl
      · dsimp; omega)) ≫
  (SyntheticCategory.biShift_comp (0,(ef:ℤ)) (1,0)).inv.app A ≫
  (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app _

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
    (KIP126.Literature.normalizedTriangle background T he).obj₃ ≅
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
    (KIP126.Literature.normalizedTriangle background T he).mor₂ ≫
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
    ((KIP126.Literature.normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) ≅
      background.nu.functor.obj ((AdamsObject.shift 1 T.X).obj background.auxiliary) :=
  (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
    (SyntheticCategory.biShift_comp
      (0,(normalizedExponent background.classicalTower T.f:ℤ)) (1,0)).app _ ≪≫
    eqToIso (congrArg (fun p : ℤ×ℤ => (SyntheticCategory.biShift p).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary)))
      (show (0,(normalizedExponent background.classicalTower T.f:ℤ))+(1,0)=(1,1)
        by ext <;> dsimp <;> omega)) ≪≫
    (background.nu.suspensionIso (T.X.obj background.auxiliary)).symm

/-- Comparison of the normalized connecting arrow with νh in the
e_f=1, e_g=e_h=0 case, through the specified suspension isomorphism. -/
private theorem normalized_third_arrow_zero
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0) :
    (KIP126.Literature.normalizedTriangle background T he).mor₃ ≫
      (normalizedSuspensionNativeIso T he hf).hom =
      (normalizedThirdZeroIso T he hg).hom ≫ background.nu.functor.map T.h := by
  have h := raw_connecting_one_zero_zero _ _ _ he hf hg hh
    (background.normalizedMap T.Z (.shift 1 T.X) T.h).map
    (background.nu.suspensionIso (T.X.obj background.auxiliary))
    (background.nu.functor.map T.h)
    (background.normalizedMap T.Z (.shift 1 T.X) T.h).factorization
  have h' := congrArg (fun z => z ≫ (background.nu.suspensionIso
    (T.X.obj background.auxiliary)).inv) h
  simpa only [KIP126.Literature.normalizedTriangle,Triangle.mk,normalizedConnecting,
    raw_normalized_connecting,normalizedSuspensionNativeIso,
    normalizedThirdZeroIso,zero_negative_iso,Iso.trans_hom,Iso.symm_hom,
    Iso.app_hom,Iso.app_inv,eqToIso.hom,Category.assoc,Iso.hom_inv_id,
    Category.comp_id] using h'

private theorem homotopy_regrade_injective {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') :
    Function.Injective (homotopyRegrade hm hw (X:=A)) := by
  subst m'
  subst w'
  exact fun _ _ h => h


private theorem regrade_composition {m m' w w' : ℤ} {A B : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w A) (f : A ⟶ B) :
    homotopyRegrade hm hw (a ≫ f) = homotopyRegrade hm hw a ≫ f := by
  subst m'; subst w'; rfl
private theorem regrade_precomp {m m' w w' : ℤ} {A : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w A) :
    homotopyRegrade hm hw a =
      eqToHom (congrArg (fun p : ℤ × ℤ => Smn p.1 p.2 (Syn := SyntheticSpectrum))
        (show (m',w')=(m,w) by rw [hm,hw])) ≫ a := by
  subst m'; subst w'
  simp only [homotopyRegrade,eqToHom_refl,Category.id_comp]


private theorem regrade_comp {m m' w w' : ℤ} {A B : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w A) (f : A ⟶ B) :
    homotopyRegrade hm hw (a ≫ f) = homotopyRegrade hm hw a ≫ f := by
  subst m'; subst w'; rfl
private theorem regrade_zero {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') :
    homotopyRegrade hm hw (0 : BiHom m w A) = 0 := by
  subst m'; subst w'; rfl
private def ordinarySuspendedRepresentative (A : SyntheticSpectrum) (m w : ℤ)
    (a : BiHom (m-1) w A) : BiHom m w (A⟦(1:ℤ)⟧) :=
  homotopyRegrade (by dsimp; omega) (by simp)
    (shiftHomotopyClass (1,0) (m-1,w) a) ≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app A

private theorem ordinarySuspendedRepresentative_natural {A B : SyntheticSpectrum}
    (f : A ⟶ B) (m w : ℤ) (a : BiHom (m-1) w A) :
    ordinarySuspendedRepresentative B m w (a ≫ f) =
      ordinarySuspendedRepresentative A m w a ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map f := by
  simp only [ordinarySuspendedRepresentative,shiftHomotopyClass,Functor.map_comp,
    regrade_precomp,Category.assoc]
  rw [←(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.naturality f]

private def normalizedFirstMap (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1) :
    (SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary)) ⟶
      background.nu.functor.obj (T.Y.obj background.auxiliary) := by
  simpa only [hf,Nat.cast_one] using (background.normalizedMap T.X T.Y T.f).map

private theorem cast_BiHom_regrade {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w')
    (h : BiHom m w A = BiHom m' w' A) (a : BiHom m w A) :
    h.mp a = homotopyRegrade hm hw a := by
  subst m'
  subst w'
  rfl

private theorem nativeFirstLabel_eq_regrade
    (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ) (x : Ambient background X (s,t)) :
    nativeFirstLabel X s t x =
      homotopyRegrade rfl (Int.add_zero t) ((background.firstQuotient X 0 s t).symm x) ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  dsimp only [nativeFirstLabel,KIP126.Literature.firstLabel]
  congr 1
  exact cast_BiHom_regrade rfl (Int.add_zero t) _ _

private theorem cofiberFirstQuotientBoundary_native_label
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ) (x : Ambient background T.X (s,t)) :
    nativeFirstLabel T.Y (s+1) (t+1)
      (e2Connecting T hf s t x) =
    homotopyRegrade (by omega) rfl
      ((background.firstQuotient T.X 1 s t).symm x ≫ XModLambdaN.map (normalizedFirstMap T hf) 1) := by
  rw [nativeFirstLabel_eq_regrade]
  simp only [
    e2Connecting,normalizedFirstMap]
  simp only [LinearEquiv.symm_apply_apply,regrade_precomp,Category.assoc,
    ←background.quotients.functoriality.map_comp,Iso.inv_hom_id_app]
  simp only [←Category.assoc,eqToHom_trans]
  erw [Category.comp_id]


private theorem native_first_label_natural
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t : ℤ) (x : Ambient background X (s,t)) :
    nativeFirstLabel X s t x ≫ XModLambdaN.map (background.nu.functor.map f) 1 =
      nativeFirstLabel Y s t ((background.classical.map f).pageMap 2 (s,t) x) := by
  rw [nativeFirstLabel_eq_regrade, nativeFirstLabel_eq_regrade]
  have h := first_quotient_nu_naturality X Y f 0 s t x
  have hn := SyntheticCategory.biShift_zero.hom.naturality (background.nu.functor.map f)
  change (SyntheticCategory.biShift (0,0)).map (background.nu.functor.map f) ≫
    SyntheticCategory.biShift_zero.hom.app _ =
    SyntheticCategory.biShift_zero.hom.app _ ≫ background.nu.functor.map f at hn
  rw [Category.assoc, ←background.quotients.functoriality.map_comp, ←hn,
    background.quotients.functoriality.map_comp, ←Category.assoc, ←regrade_composition, h]
  rfl
private theorem normalized_suspension_native_comparison
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1) :
    HEq ((normalizedSuspensionNativeIso T he hf).hom ≫
        (background.nu.suspensionIso (T.X.obj background.auxiliary)).hom)
      ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app
          ((SyntheticCategory.biShift (0,1)).obj
            (background.nu.functor.obj (T.X.obj background.auxiliary))) ≫
        (biShiftAddIso (0,1) (1,0) (1,1) (by ext <;> simp)).hom.app
          (background.nu.functor.obj (T.X.obj background.auxiliary))) := by
  simp only [normalizedSuspensionNativeIso,Iso.trans_hom,Iso.symm_hom,
    Category.assoc,Iso.inv_hom_id,Category.comp_id]
  dsimp only [biShiftAddIso,KIP126.Literature.normalizedTriangle,Triangle.mk]
  have general (A : SyntheticSpectrum) (k : ℕ) (hk : k=1)
      (hdeg : (0,(k:ℤ))+(1,0)=(1,1)) :
      HEq ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app
          ((SyntheticCategory.biShift (0,(k:ℤ))).obj A) ≫
        (SyntheticCategory.biShift_comp (0,(k:ℤ)) (1,0)).hom.app A ≫
        eqToHom (congrArg (fun j : ℤ×ℤ => (SyntheticCategory.biShift j).obj A) hdeg))
      ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app
          ((SyntheticCategory.biShift (0,1)).obj A) ≫
        (biShiftAddIso (0,1) (1,0) (1,1) (by ext <;> simp)).hom.app A) := by
    subst k
    rfl
  exact general _ _ hf (by ext <;> dsimp; omega)



private def regradeAddEquiv {A : SyntheticSpectrum} {m m' w w' : ℤ}
    (hm : m=m') (hw : w=w') : BiHom m w A ≃+ BiHom m' w' A where
  toFun := homotopyRegrade hm hw
  invFun := homotopyRegrade hm.symm hw.symm
  left_inv := by subst m'; subst w'; intro a; rfl
  right_inv := by subst m'; subst w'; intro a; rfl
  map_add' := by subst m'; subst w'; intro a b; rfl

private theorem susp_invariance_add (m n k l : ℤ) (X : SyntheticSpectrum)
    (f g : BiHom m n X) :
    susp_invariance m n k l X (f + g) =
      susp_invariance m n k l X f + susp_invariance m n k l X g := by
  letI := background.exactness.shiftAdditive (k,l)
  simp [susp_invariance, Functor.map_add, Preadditive.comp_add]

/-- The specified inverse reindexing map is additive. -/

private def suspInvarianceAddEquiv (m n k l : ℤ) (X : SyntheticSpectrum) :
    BiHom m n X ≃+ BiHom (m+k) (n+l) ((SyntheticCategory.biShift (k,l)).obj X) where
  toEquiv := susp_invariance m n k l X
  map_add' := susp_invariance_add m n k l X
private theorem inverse_associativity (coh : BiShiftCoherence SyntheticSpectrum)
    (a b c ab bc total : ℤ×ℤ) (hab : a+b=ab) (hbc : b+c=bc)
    (ht : ab+c=total) (ht' : a+bc=total) (X : SyntheticSpectrum) :
    (biShiftAddIso a bc total ht').inv.app X ≫
        (biShiftAddIso b c bc hbc).inv.app ((SyntheticCategory.biShift a).obj X) =
      (biShiftAddIso ab c total ht).inv.app X ≫
        (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).inv.app X) := by
  have he : (SyntheticCategory.biShift c).mapIso ((biShiftAddIso a b ab hab).app X) ≪≫
        (biShiftAddIso ab c total ht).app X =
      (biShiftAddIso b c bc hbc).app ((SyntheticCategory.biShift a).obj X) ≪≫
        (biShiftAddIso a bc total ht').app X := by
    apply Iso.ext
    exact coh.associativity a b c ab bc total hab hbc ht ht' X
  have h := congrArg Iso.inv he
  simpa only [Iso.trans_inv,Functor.mapIso_inv,Iso.app_inv] using h.symm

private theorem shift_hom_associativity (coh : BiShiftCoherence SyntheticSpectrum)
    (a b c ab bc total : ℤ×ℤ) (hab : a+b=ab) (hbc : b+c=bc)
    (ht : ab+c=total) (ht' : a+bc=total) {A : SyntheticSpectrum}
    (α : (SyntheticCategory.biShift a).obj (S_0_0 : SyntheticSpectrum) ⟶ A) :
    (biShiftAddIso a bc total ht').inv.app S_0_0 ≫
        (SyntheticCategory.biShift bc).map α ≫ (biShiftAddIso b c bc hbc).inv.app A =
      (biShiftAddIso ab c total ht).inv.app S_0_0 ≫
        (SyntheticCategory.biShift c).map
          ((biShiftAddIso a b ab hab).inv.app S_0_0 ≫ (SyntheticCategory.biShift b).map α) := by
  rw [(biShiftAddIso b c bc hbc).inv.naturality α]
  change _ ≫ _ ≫ (SyntheticCategory.biShift c).map ((SyntheticCategory.biShift b).map α) = _
  rw [←Category.assoc,inverse_associativity coh,Functor.map_comp,Category.assoc]


private def verticalTranslate (A : SyntheticSpectrum) (e m w : ℤ) :
    BiHom m w A ≃+ BiHom m (w+e) ((SyntheticCategory.biShift (0,e)).obj A) :=
  (suspInvarianceAddEquiv m w 0 e A).trans
    (regradeAddEquiv (add_zero m) rfl)


private def levelQuotientShiftIso (X : AdamsObject (coefficients := background.coefficients)) (e : ℤ) (q : ℕ) :
    XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,e)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q) := by
  letI := background.exactness.shiftCommShift (0,e)
  letI := background.exactness.shiftExact (0,e)
  exact (finite_quotient_shift_comparison background.quotients.coherence (0,e) q _).choose
private theorem level_quotient_shift_incl (X : AdamsObject (coefficients := background.coefficients)) (e : ℤ) (q : ℕ) :
    XModLambdaN.incl _ q ≫ (levelQuotientShiftIso X e q).hom =
      (SyntheticCategory.biShift (0,e)).map
        (XModLambdaN.incl (background.nu.functor.obj (X.obj background.auxiliary)) q) := by
  letI := background.exactness.shiftCommShift (0,e)
  letI := background.exactness.shiftExact (0,e)
  exact (finite_quotient_shift_comparison background.quotients.coherence (0,e) q _).choose_spec
private theorem positive_first_label_shift (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (x : Ambient background X (s,t)) :
    verticalTranslate _ 1 (t-s) t (nativeFirstLabel X s t x) ≫
      (levelQuotientShiftIso X 1 1).inv = (background.firstQuotient X 1 s t).symm x := by
  have h := KIP126.AdamsSynthetic.Completed.firstQuotient_positive_shift X s t x
    (levelQuotientShiftIso X 1 1) (level_quotient_shift_incl X 1 1)
  rw [nativeFirstLabel_eq_regrade]
  simpa [verticalTranslate,regradeAddEquiv,
    suspInvarianceAddEquiv,susp_invariance,shiftHomotopyClass,Iso.homCongr,
    regrade_precomp,Category.assoc] using h

private def positiveSuspensionIso (A : SyntheticSpectrum) :
    ((SyntheticCategory.biShift (0,1)).obj A)⟦(1:ℤ)⟧ ≅
      (SyntheticCategory.biShift (1,1)).obj A :=
  (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
    (biShiftAddIso (0,1) (1,0) (1,1) (by ext <;> simp)).app A

private theorem positive_ordinary_suspension_class
    (A : SyntheticSpectrum) (m w : ℤ) (a : BiHom (m-1) w A) :
    ordinarySuspendedRepresentative _ m (w+1)
        (verticalTranslate A 1 (m-1) w a) ≫ (positiveSuspensionIso A).hom =
      homotopyRegrade (by dsimp; omega) (by simp)
        (shiftHomotopyClass (1,1) (m-1,w) a) := by
  have h := shift_hom_associativity background.quotients.coherence
    (m-1,w) (0,1) (1,0) (m-1,w+1) (1,1) (m,w+1)
    (by ext <;> simp) (by ext <;> simp) (by ext <;> simp) (by ext <;> simp) a
  have hh := congrArg (fun z => z ≫
    (biShiftAddIso (0,1) (1,0) (1,1) (by ext <;> simp)).hom.app A) h.symm
  simp only [Category.assoc,Iso.inv_hom_id_app,Category.comp_id] at hh
  simpa [ordinarySuspendedRepresentative,verticalTranslate,regradeAddEquiv,
    suspInvarianceAddEquiv,susp_invariance,shiftHomotopyClass,Iso.homCongr,
    positiveSuspensionIso,Iso.trans_hom,Iso.symm_hom,Iso.app_inv,
    biShiftAddIso,regrade_precomp,Functor.map_comp,Category.assoc] using hh


private def positiveNormalizedSourceIso
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1) :
    (KIP126.Literature.normalizedTriangle background T he).obj₁ ≅
      (SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary)) :=
  eqToIso (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
    (background.nu.functor.obj (T.X.obj background.auxiliary))) hf)

private theorem positive_normalized_source_arrow
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1) :
    (positiveNormalizedSourceIso T he hf).hom ≫ normalizedFirstMap T hf =
      (KIP126.Literature.normalizedTriangle background T he).mor₁ := by
  have transport (A A' B : SyntheticSpectrum) (h : A=A')
      (ht : (A ⟶ B)=(A' ⟶ B)) (f : A ⟶ B) :
      eqToHom h ≫ ht.mp f = f := by
    subst A'
    simp
  dsimp only [positiveNormalizedSourceIso,normalizedFirstMap,KIP126.Literature.normalizedTriangle,Triangle.mk]
  exact transport _ _ _ (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
    (background.nu.functor.obj (T.X.obj background.auxiliary))) hf) _ _


private theorem positive_normalized_source_suspension
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1) :
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (positiveNormalizedSourceIso T he hf).inv ≫
      (normalizedSuspensionNativeIso T he hf).hom ≫
        (background.nu.suspensionIso (T.X.obj background.auxiliary)).hom =
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app
          ((SyntheticCategory.biShift (0,1)).obj
            (background.nu.functor.obj (T.X.obj background.auxiliary))) ≫
        (biShiftAddIso (0,1) (1,0) (1,1) (by ext <;> simp)).hom.app
          (background.nu.functor.obj (T.X.obj background.auxiliary)) := by
  have transport (A A' B : SyntheticSpectrum) (h : A=A')
      (f : A⟦(1:ℤ)⟧ ⟶ B) (g : A'⟦(1:ℤ)⟧ ⟶ B) (hfg : HEq f g) :
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (eqToIso h).inv ≫ f = g := by
    subst A'
    simpa using eq_of_heq hfg
  exact transport _ _ _ (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
    (background.nu.functor.obj (T.X.obj background.auxiliary))) hf) _ _
      (normalized_suspension_native_comparison T he hf)

private theorem positive_normalized_source_inv_arrow
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1) :
    (positiveNormalizedSourceIso T he hf).inv ≫ (KIP126.Literature.normalizedTriangle background T he).mor₁ =
      normalizedFirstMap T hf := by
  rw [←positive_normalized_source_arrow T he hf,←Category.assoc,Iso.inv_hom_id,Category.id_comp]

private theorem positive_normalized_source_raw_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (N : ℕ) (m w : ℤ)
    (a : BiHom m w (XModLambdaN (((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary)))⟦(1:ℤ)⟧) N)) :
    (a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (positiveNormalizedSourceIso T he hf).inv) N) ≫
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (KIP126.Literature.normalizedTriangle background T he).mor₁) N =
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedFirstMap T hf)) N := by
  rw [Category.assoc,←background.quotients.functoriality.map_comp,←Functor.map_comp,
    positive_normalized_source_inv_arrow]


private theorem ordinary_suspended_representative_injective
    (A : SyntheticSpectrum) (m w : ℤ) :
    Function.Injective (ordinarySuspendedRepresentative A m w) := by
  intro a b h
  have h₀ := (cancel_mono
    ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app A)).mp h
  have h₁ := homotopy_regrade_injective
    (show ((m-1,w)+(1,0)).1=m by dsimp; omega)
    (show ((m-1,w)+(1,0)).2=w by simp) h₀
  apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,0)).map_injective
  exact (cancel_epi ((SyntheticCategory.biShift_comp (m-1,w) (1,0)).inv.app S_0_0)).mp h₁

private theorem quotient_suspension_inclusion_exists
    (A : SyntheticSpectrum) (r : ℕ) :
    ∃ e : XModLambdaN (A⟦(1:ℤ)⟧) r ≅ (XModLambdaN A r)⟦(1:ℤ)⟧,
      XModLambdaN.incl (A⟦(1:ℤ)⟧) r ≫ e.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl A r) := by
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε⟩ := finite_quotient_shift_comparison background.quotients.coherence (1,0) r A
  let κ := (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).app A
  let κr := (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).app (XModLambdaN A r)
  let e : XModLambdaN (A⟦(1:ℤ)⟧) r ≅ (XModLambdaN A r)⟦(1:ℤ)⟧ :=
    (background.quotients.functoriality.functor r).mapIso κ.symm ≪≫ ε ≪≫ κr
  refine ⟨e,?_⟩
  change XModLambdaN.incl _ r ≫ XModLambdaN.map κ.inv r ≫ ε.hom ≫ κr.hom = _
  rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,←Category.assoc _ ε.hom,hε]
  have hn := (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.naturality
    (XModLambdaN.incl A r)
  change (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl A r) ≫ κr.hom =
    κ.hom ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl A r) at hn
  rw [hn,Iso.inv_hom_id_assoc]


end
end KIP126.Literature.Standard.E2Exactness
