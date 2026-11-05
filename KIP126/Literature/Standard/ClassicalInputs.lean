module
import all KIP126.Literature.BocksteinOriginalSuccessor
import all KIP126.Literature.BocksteinComparisonInput
import all KIP126.Literature.BocksteinBoundaryInput
public import KIP126.AdamsSynthetic.Completed.Background
import KIP126.AdamsSynthetic.Completed.Filtration
import KIP126.AdamsSynthetic.Completed.Separation
import KIP126.AdamsSynthetic.Completed.ClassicalSupport
public import KIP126.Literature.ModelResults
import all KIP126.Literature.ModelResults
import all KIP126.Literature.Classical
import all KIP126.Literature.ClassicalRange
import all KIP126.Literature.EInfinity
import all KIP126.Literature.Triangles
import all KIP126.Literature.May

public import KIP126.AdamsSynthetic.Completed.SpectrumScope

/-! Literature source objects, sphere normalizations and realization coordinates.
The related initial comparisons remain together to preserve their shared public proof terms. -/

@[expose] section
set_option autoImplicit false
noncomputable section
set_option backward.privateInPublic true
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)

/-- Connectivity follows from the sphere instance of the paper range. -/
public theorem sphere_connected :
  IsConnected (SphereSpectrum (C := Spectrum)) (-1) := by
  intro n hn
  exact KIP126.AdamsSynthetic.Completed.sphere_isPaperSpectrum.1 n (by omega)


public theorem connected_homology_vanishing :
  ∀ (X : Spectrum) (n : ℤ), IsConnected X n →
    ∀ i : ℤ, i ≤ n → Subsingleton (ModTwoHomology KIP126.AdamsSynthetic.Completed.coefficients i X) := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def universal_coefficient :
  ∀ (n : ℤ) (X : Spectrum),
    ((shiftFunctor Spectrum n).obj X ⟶ KIP126.AdamsSynthetic.Completed.coefficients.object) ≃+ (ModTwoHomology KIP126.AdamsSynthetic.Completed.coefficients (-n) X →+ ZMod 2) := by
  sorry

/-- The specified realization is additive by its actual adjunction. -/


public theorem realization_additive :
  background.recovery.realization.Additive := by
  letI := background.recovery.adjunction.isLeftAdjoint
  letI := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts
    background.recovery.realization
  exact Functor.additive_of_preservesBinaryBiproducts _

section RealizationConstruction
set_option backward.isDefEq.respectTransparency false

private theorem reflector_lambda_iso (X : SyntheticSpectrum) :
    IsIso (background.recovery.localization.reflector.map (SyntheticCategory.lam.app X)) := by
  let L := background.recovery.localization
  have hl (Z : SyntheticSpectrum) (hZ : IsLambdaInvertible Z) :
      Function.Bijective (fun f : X ⟶ Z => SyntheticCategory.lam.app X ≫ f) := by
    letI : IsIso (SyntheticCategory.lam.app Z) := hZ
    let hS := SyntheticCategory.biShift_fullyFaithful (Syn := SyntheticSpectrum) (0,-1)
    have hn (f : X ⟶ Z) :
        (SyntheticCategory.biShift (0,-1)).map f ≫ SyntheticCategory.lam.app Z =
          SyntheticCategory.lam.app X ≫ f := by
      exact SyntheticCategory.lam.naturality f
    constructor
    · intro f g h
      apply hS.map_injective
      apply (cancel_mono (SyntheticCategory.lam.app Z)).mp
      rw [hn, hn]
      exact h
    · intro g
      obtain ⟨f, hf⟩ := hS.map_surjective (g ≫ inv (SyntheticCategory.lam.app Z))
      refine ⟨f, ?_⟩
      change SyntheticCategory.lam.app X ≫ f = g
      rw [← hn, hf]
      simp
  apply isIso_of_coyoneda_map_bijective
  intro Z
  change Function.Bijective (fun g : L.reflector.obj X ⟶ Z =>
    L.reflector.map (SyntheticCategory.lam.app X) ≫ g)
  have h : (fun g : L.reflector.obj X ⟶ Z =>
      L.reflector.map (SyntheticCategory.lam.app X) ≫ g) =
      (fun g => (L.adjunction.homEquiv _ Z).symm
        (SyntheticCategory.lam.app X ≫ (L.adjunction.homEquiv X Z) g)) := by
    funext g
    apply (L.adjunction.homEquiv _ Z).injective
    rw [Equiv.apply_symm_apply, L.adjunction.homEquiv_naturality_left]
    rfl
  rw [h]
  exact (L.adjunction.homEquiv _ Z).symm.bijective.comp
    ((hl Z.obj Z.property).comp (L.adjunction.homEquiv X Z).bijective)

private theorem realization_lambda_iso (X : SyntheticSpectrum) :
    IsIso (background.recovery.realization.map (SyntheticCategory.lam.app X)) := by
  letI := reflector_lambda_iso X
  change IsIso (background.recovery.equivalence.functor.map
    (background.recovery.localization.reflector.map (SyntheticCategory.lam.app X)))
  infer_instance

set_option backward.privateInPublic true in
private def realizationZeroBase :
    Sphere (C := Spectrum) 0 ≅ background.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) 0 0) :=
  (shiftFunctorZero Spectrum ℤ).app SphereSpectrum ≪≫
    background.recovery.nuRealizationIso.symm.app SphereSpectrum ≪≫
    background.recovery.realization.mapIso background.nu.unitIso ≪≫
    (background.recovery.realization.mapIso
      (SyntheticCategory.biShift_zero.app (S_0_0 : SyntheticSpectrum))).symm

set_option backward.privateInPublic true in
private def realizationBase (m : ℤ) :
    Sphere (C := Spectrum) m ≅ background.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m 0) := by
  by_cases hm : m = 0
  · subst m
    exact realizationZeroBase
  · let R := background.recovery.realization
    letI := background.exactness.realizationShift
    let j : (SphereSpectrum : Spectrum) ≅ R.obj (S_0_0 : SyntheticSpectrum) :=
      background.recovery.nuRealizationIso.symm.app SphereSpectrum ≪≫ R.mapIso background.nu.unitIso
    exact (shiftFunctor Spectrum m).mapIso j ≪≫
      ((R.commShiftIso m).app (S_0_0 : SyntheticSpectrum)).symm ≪≫
      (R.mapIso ((SyntheticCategory.biShift_compat m).app (S_0_0 : SyntheticSpectrum))).symm

set_option backward.privateInPublic true in
private def realizationStep (m w : ℤ) :
    background.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m (w-1)) ≅
      background.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m w) := by
  let f := lambdaMultiply 1 (𝟙 (Smn (Syn := SyntheticSpectrum) m w))
  haveI : IsIso (background.recovery.realization.map f) := by
    dsimp only [f, lambdaMultiply]
    rw [lambdaPow_one background.quotients.coherence]
    letI := realization_lambda_iso (Smn (Syn := SyntheticSpectrum) m w)
    simp only [Functor.map_comp]
    infer_instance
  exact asIso (background.recovery.realization.map f)

set_option backward.privateInPublic true in
@[irreducible] private def realizationSphere (m w : ℤ) :
    Sphere (C := Spectrum) m ≅ background.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m w) :=
  w.inductionOn' 0 (realizationBase m)
    (fun w _ e => e ≪≫
      eqToIso (congrArg (fun q => background.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m q))
        (by omega : w = w+1-1)) ≪≫ realizationStep m (w+1))
    (fun w _ e => e ≪≫ (realizationStep m w).symm)

private theorem realizationSphere_zero : realizationSphere 0 0 = realizationZeroBase := by
  rw [realizationSphere, Int.inductionOn'_self]
  simp [realizationBase]

private theorem realizationUnit :
    (realizationSphere 0 0).hom ≫ background.recovery.realization.map
        (SyntheticCategory.biShift_zero.hom.app (S_0_0 : SyntheticSpectrum)) =
      (shiftFunctorZero Spectrum ℤ).hom.app SphereSpectrum ≫
        background.recovery.nuRealizationIso.inv.app SphereSpectrum ≫
        background.recovery.realization.map background.nu.unitIso.hom := by
  rw [realizationSphere_zero]
  simp only [realizationZeroBase, Iso.trans_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]


end RealizationConstruction

set_option backward.privateInPublic true in
/-- The fixed mathematical object on the project background. -/
public def realization_sphere :
  ∀ m w : ℤ, Sphere (C := Spectrum) m ≅ background.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m w) := realizationSphere

set_option backward.proofsInPublic true in
set_option backward.privateInPublic true in
/-- The sphere coordinates use the specified nu-realization unit comparison. -/
public theorem realization_unit :
  (realization_sphere 0 0).hom ≫ background.recovery.realization.map
      (SyntheticCategory.biShift_zero.hom.app (S_0_0 : SyntheticSpectrum)) =
    (shiftFunctorZero Spectrum ℤ).hom.app SphereSpectrum ≫
      background.recovery.nuRealizationIso.inv.app SphereSpectrum ≫
      background.recovery.realization.map background.nu.unitIso.hom := by
  change (realizationSphere 0 0).hom ≫ _ = _
  exact realizationUnit

section RealizationLambdaConstruction
set_option backward.isDefEq.respectTransparency false

private theorem realizationSphere_succ (m w : ℤ) (hw : 0 ≤ w) :
    realizationSphere m (w+1) = realizationSphere m w ≪≫
      eqToIso (congrArg (fun q => background.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m q))
        (by omega : w = w+1-1)) ≪≫ realizationStep m (w+1) := by
  unfold realizationSphere
  rw [Int.inductionOn'_add_one hw]

private theorem realizationSphere_pred (m w : ℤ) (hw : w ≤ 0) :
    realizationSphere m (w-1) = realizationSphere m w ≪≫ (realizationStep m w).symm := by
  unfold realizationSphere
  rw [Int.inductionOn'_sub_one hw]

private theorem realizationSphere_succ_to (m v w : ℤ) (hv : 0 ≤ v) (hvw : v+1=w) :
    realizationSphere m w = realizationSphere m v ≪≫
      eqToIso (congrArg (fun q => background.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m q))
        (by omega : v = w-1)) ≪≫ realizationStep m w := by
  subst w
  exact realizationSphere_succ m v hv

private theorem realizationSphere_adjacent (m w : ℤ) :
    (realizationSphere m (w-1)).hom ≫ background.recovery.realization.map
      (lambdaMultiply 1 (𝟙 (Smn (Syn := SyntheticSpectrum) m w))) =
        (realizationSphere m w).hom := by
  change (realizationSphere m (w-1)).hom ≫ (realizationStep m w).hom = _
  by_cases hw : w ≤ 0
  · rw [realizationSphere_pred m w hw]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · have hs := realizationSphere_succ_to m (w-1) w (by omega) (by omega)
    rw [hs]
    simp only [Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.id_comp]


-- Associativity of the inverse bidegree-shift comparisons.
private theorem shift_assoc_inv (coh : BiShiftCoherence SyntheticSpectrum)
    (a b c ab bc total : ℤ × ℤ) (hab : a+b=ab) (hbc : b+c=bc)
    (habc : ab+c=total) (habc' : a+bc=total) (A : SyntheticSpectrum) :
    (biShiftAddIso ab c total habc).inv.app A ≫
      (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).inv.app A) =
    (biShiftAddIso a bc total habc').inv.app A ≫
      (biShiftAddIso b c bc hbc).inv.app ((SyntheticCategory.biShift a).obj A) := by
  classical
  have he : ((SyntheticCategory.biShift c).mapIso ((biShiftAddIso a b ab hab).app A) ≪≫
      (biShiftAddIso ab c total habc).app A) =
    ((biShiftAddIso b c bc hbc).app ((SyntheticCategory.biShift a).obj A) ≪≫
      (biShiftAddIso a bc total habc').app A) :=
    Iso.ext (coh.associativity a b c ab bc total hab hbc habc habc' A)
  have hi := congrArg Iso.inv he
  exact hi


private def lambdaAt (m : ℤ) (n : ℕ) (w v : ℤ)
    (h : (m,w)+(0,-(n:ℤ))=(m,v))
    {X : SyntheticSpectrum} (a : BiHom m w X) : BiHom m v X :=
  (biShiftAddIso (m,w) (0,-(n:ℤ)) (m,v) h).inv.app S_0_0 ≫
    lambdaPow n (Smn m w) ≫ a

private theorem lambdaAt_heq (m : ℤ) (n : ℕ) (w v : ℤ)
    (h : (m,w)+(0,-(n:ℤ))=(m,v))
    {X : SyntheticSpectrum} (a : BiHom m w X) :
    HEq (lambdaAt m n w v h a) (lambdaMultiply n a) := by
  delta lambdaAt KIP126.Synthetic.Context.lambdaMultiply KIP126.Synthetic.Context.biShiftAddIso
  simp only [Iso.trans_inv,NatTrans.comp_app,eqToIso.inv,eqToHom_app,
    Category.assoc,eqToHom_comp_heq_iff,heq_eqToHom_comp_iff]
  rfl

private theorem multiply_heq {m w w' : ℤ} {X : SyntheticSpectrum} (n : ℕ)
    (h : w=w') {a : BiHom m w X} {b : BiHom m w' X} (hab : HEq a b) :
    HEq (lambdaMultiply n a) (lambdaMultiply n b) := by
  subst w'
  cases hab
  rfl

private theorem lambda_multiply_compose {m w : ℤ} {X : SyntheticSpectrum}
    (k n : ℕ) (a : BiHom m w X) :
    HEq (lambdaMultiply n (lambdaMultiply k a)) (lambdaMultiply (k+n) a) := by
  let v := w-(k:ℤ)
  let u := v-(n:ℤ)
  let hk : (m,w)+(0,-(k:ℤ))=(m,v) := by ext <;> dsimp [v] <;> omega
  let hn : (m,v)+(0,-(n:ℤ))=(m,u) := by ext <;> dsimp [u] <;> omega
  let hkn : (m,w)+(0,-((k+n:ℕ):ℤ))=(m,u) := by ext <;> (dsimp [u,v]; omega)
  have ha := shift_assoc_inv background.quotients.coherence (m,w) (0,-(k:ℤ)) (0,-(n:ℤ))
    (m,v) (0,-((k+n:ℕ):ℤ)) (m,u)
    hk (by ext <;> dsimp <;> omega) hn hkn (S_0_0 : SyntheticSpectrum)
  have heq : lambdaAt m n v u hn (lambdaAt m k w v hk a) =
      lambdaAt m (k+n) w u hkn a := by
    unfold lambdaAt
    have hnat₁ := congrArg (fun t => t ≫ (lambdaPow k (Smn m w) ≫ a))
      (lambdaPow_naturality n
        ((biShiftAddIso (m,w) (0,-(k:ℤ)) (m,v) hk).inv.app (S_0_0 : SyntheticSpectrum)))
    simp (config := { congrConsts := false }) only [Category.assoc] at hnat₁
    erw [← hnat₁]
    have hnat₂ := congrArg (fun t => t ≫ a)
      (lambdaPow_naturality n (lambdaPow k (Smn m w)))
    simp (config := { congrConsts := false }) only [Category.assoc] at hnat₂
    erw [← hnat₂]
    erw [←Category.assoc,ha]
    erw [lambdaPow_add background.quotients.coherence k n (k+n) rfl (Smn m w)]
    delta KIP126.Synthetic.Context.lambdaShiftAddIso KIP126.Synthetic.Context.lambdaDegree KIP126.Synthetic.Context.biShiftAddIso
    simp (config := { congrConsts := false }) only [Category.assoc]
    rfl
  have houter := lambdaAt_heq m n v u hn (lambdaAt m k w v hk a)
  have hinner := multiply_heq n (by rfl : v=w-(k:ℤ)) (lambdaAt_heq m k w v hk a)
  exact (houter.trans hinner).symm.trans ((heq_of_eq heq).trans (lambdaAt_heq m (k+n) _ _ hkn a))

private theorem realizationTransport {m w w' : ℤ} {X : SyntheticSpectrum}
    (hw : w = w') {a : BiHom m w X} {b : BiHom m w' X} (hab : HEq a b) :
    (realizationSphere m w).hom ≫ background.recovery.realization.map a =
      (realizationSphere m w').hom ≫ background.recovery.realization.map b := by
  subst w'
  cases hab
  rfl

private theorem realizationAdjacentMap {m w : ℤ} {X : SyntheticSpectrum} (a : BiHom m w X) :
    (realizationSphere m (w-1)).hom ≫ background.recovery.realization.map (lambdaMultiply 1 a) =
      (realizationSphere m w).hom ≫ background.recovery.realization.map a := by
  have hc : lambdaMultiply 1 a =
      lambdaMultiply 1 (𝟙 (Smn (Syn := SyntheticSpectrum) m w)) ≫ a := by
    delta KIP126.Synthetic.Context.lambdaMultiply
    simp only [Category.comp_id, Category.assoc]
  rw [hc, Functor.map_comp, ← Category.assoc, realizationSphere_adjacent]

private theorem lambdaMultiplyZero {m w : ℤ} {X : SyntheticSpectrum} (a : BiHom m w X) :
    HEq (lambdaMultiply 0 a) a := by
  let hz : (m,w)+(0,-((0:ℕ):ℤ))=(m,w) := by ext <;> simp
  have he : lambdaAt m 0 w w hz a = a := by
    unfold lambdaAt
    change (biShiftAddIso (m,w) 0 (m,w) (add_zero (m,w))).inv.app S_0_0 ≫
      SyntheticCategory.biShift_zero.hom.app (Smn (Syn := SyntheticSpectrum) m w) ≫ a = a
    erw [← background.quotients.coherence.right_unit (m,w) (S_0_0 : SyntheticSpectrum)]
    exact Iso.inv_hom_id_app_assoc (biShiftAddIso (m,w) 0 (m,w) (add_zero (m,w))) (S_0_0 : SyntheticSpectrum) a
  exact (lambdaAt_heq m 0 w w hz a).symm.trans (heq_of_eq he)

private theorem realizationLambdaMap {m w : ℤ} {X : SyntheticSpectrum}
    (a : BiHom m w X) (k : ℕ) :
    (realizationSphere m (w-k)).hom ≫ background.recovery.realization.map (lambdaMultiply k a) =
      (realizationSphere m w).hom ≫ background.recovery.realization.map a := by
  induction k with
  | zero =>
    exact realizationTransport (by omega : w-(0:ℕ)=w) (lambdaMultiplyZero a)
  | succ k ih =>
    have h := realizationTransport (by omega : w-(k:ℤ)-1=w-((k+1:ℕ):ℤ))
      (lambda_multiply_compose k 1 a)
    calc
      _ = (realizationSphere m (w-(k:ℤ)-1)).hom ≫
          background.recovery.realization.map (lambdaMultiply 1 (lambdaMultiply k a)) := h.symm
      _ = (realizationSphere m (w-(k:ℤ))).hom ≫
          background.recovery.realization.map (lambdaMultiply k a) := realizationAdjacentMap _
      _ = _ := ih

private theorem realizationLambda :
    ∀ (m w : ℤ) (k : ℕ),
      (realizationSphere m (w-k)).hom ≫ background.recovery.realization.map
        (lambdaMultiply k (𝟙 (Smn (Syn := SyntheticSpectrum) m w))) =
          (realizationSphere m w).hom := by
  intro m w k
  have h := realizationLambdaMap (𝟙 (Smn (Syn := SyntheticSpectrum) m w)) k
  erw [background.recovery.realization.map_id, Category.comp_id] at h
  exact h



end RealizationLambdaConstruction

set_option backward.proofsInPublic true in
set_option backward.privateInPublic true in
/-- Every realized lambda power agrees with the same sphere coordinates. -/
public theorem realization_lambda :
  ∀ (m w : ℤ) (k : ℕ),
    (realization_sphere m (w-k)).hom ≫
      background.recovery.realization.map (lambdaMultiply k (𝟙 (Smn (Syn := SyntheticSpectrum) m w))) =
        (realization_sphere m w).hom := by
  change ∀ (m w : ℤ) (k : ℕ), (realizationSphere m (w-k)).hom ≫ _ = (realizationSphere m w).hom
  exact realizationLambda

public def realizationData : RealizationCoordinates background where
  additive := realization_additive
  sphere := realization_sphere
  unit := realization_unit
  lambda := realization_lambda

public def realizeSphere := RealizationCoordinates.sphereMap background realizationData

private structure TmfObjectData where
  tmf : Spectrum
  tmfIso : tmf ≅ background.auxiliary.detector
  tmf_algebra : MonObj tmf
  tmfUnit_agrees : tmf_algebra.one ≫ tmfIso.hom = background.auxiliary.detectorUnit

private def tmfObjectConstruction : TmfObjectData where
  tmf := by sorry
  tmfIso := by sorry
  tmf_algebra := by sorry
  tmfUnit_agrees := by sorry

/-- The fixed mathematical object on the project background. -/
public def tmf :
  Spectrum :=
  tmfObjectConstruction.tmf

/-- The fixed mathematical object on the project background. -/
public def tmfIso :
  tmf ≅ background.auxiliary.detector :=
  tmfObjectConstruction.tmfIso

/-- The fixed mathematical object on the project background. -/
public def tmf_algebra :
  MonObj tmf :=
  tmfObjectConstruction.tmf_algebra

/-- The actual unit of the specified tmf algebra. -/

public def tmfUnit :
  SphereSpectrum ⟶ tmf := @MonObj.one _ _ _ tmf tmf_algebra


public theorem tmfUnit_agrees :
  tmfUnit ≫ tmfIso.hom = background.auxiliary.detectorUnit := by
  exact tmfObjectConstruction.tmfUnit_agrees

private structure SphereGData where
  g :
  background.classical.sphere.Page 2 (4,24)
  g_nonzero :
  g ≠ 0
  g_unique :
  ∀ x : background.classical.sphere.Page 2 (4,24), x ≠ 0 → x = g

private def gConstruction : SphereGData where
  g := by sorry
  g_nonzero := by sorry
  g_unique := by sorry

/-- The fixed mathematical object on the project background. -/
public def g :
  background.classical.sphere.Page 2 (4,24) :=
  gConstruction.g

private structure SphereDeltaH1gData where
  deltaH1g :
  background.classical.sphere.Page 2 (9,54)
  deltaH1g_nonzero :
  deltaH1g ≠ 0
  deltaH1g_unique :
  ∀ x : background.classical.sphere.Page 2 (9,54), x ≠ 0 → x = deltaH1g

private def deltaH1gConstruction : SphereDeltaH1gData where
  deltaH1g := by sorry
  deltaH1g_nonzero := by sorry
  deltaH1g_unique := by sorry

/-- The fixed mathematical object on the project background. -/
public def deltaH1g :
  background.classical.sphere.Page 2 (9,54) :=
  deltaH1gConstruction.deltaH1g

private def tmfBindingData : TmfBindings background where
  source := tmf
  sourceIso := tmfIso
  sourceUnit := tmfUnit
  unit_agrees := tmfUnit_agrees
  g := g
  deltaH1g := deltaH1g


public theorem eta_detection :
  ClassicalDetects (background.classicalConvergence .sphere) (1,2)
    (background.standardClasses.standardHi 1) background.auxiliary.etaMap := by
  sorry



public theorem eta_exponent :
  normalizedExponent background.classicalTower background.auxiliary.etaMap = 1 := by
  classical
  obtain ⟨_, _, b, hb, _⟩ := eta_detection
  have hmem : background.auxiliary.etaMap ∈ ModuleCat.subobjectModule _
      ((background.classicalTower.tower SphereSpectrum).filtration.F 1 1) := by
    change ∃ b, ((background.classicalTower.tower SphereSpectrum).filtration.F 1 1).arrow.hom b = _
    exact ⟨b, hb⟩
  simp only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] at hmem
  obtain ⟨lift, hlift⟩ := hmem
  have hF : MapFiltrationAtLeast background.classicalTower background.auxiliary.etaMap 1 :=
    ⟨lift, hlift⟩
  change (if MapFiltrationAtLeast background.classicalTower background.auxiliary.etaMap 1 then 1 else 0) = 1
  exact if_pos hF


public def eta :
  BiHom 1 2 (S_0_0 : SyntheticSpectrum) := (etaSourceIso background eta_exponent).hom ≫
    (background.normalizedMap (.shift 1 .sphere) .sphere background.auxiliary.etaMap).map ≫ background.nu.unitIso.hom


public theorem eta_normalized :
  eta = (etaSourceIso background eta_exponent).hom ≫
    (background.normalizedMap (.shift 1 .sphere) .sphere background.auxiliary.etaMap).map ≫ background.nu.unitIso.hom := rfl

/-- Choose the classical θ₅ together with its detection and doubling relation
on the same fixed sphere. The existence of this witness remains a source input. -/
private def theta5Construction :
    { θ : HomotopyGroup (C := Spectrum) 62 SphereSpectrum //
      ClassicalTheta5Detected background θ ∧ θ + θ = 0 } := by
  sorry

/-- The classical θ₅ selected by the common source witness. -/
public def theta5 :
  HomotopyGroup (C := Spectrum) 62 SphereSpectrum :=
  theta5Construction.val

/-- Detection of the classical θ₅ selected by the same witness. -/
public theorem theta5_detection :
  ClassicalTheta5Detected background theta5 :=
  theta5Construction.property.1

/-- The 2-primary subgroup of the ordinary 62-stem has exponent two. -/
public theorem stem62_exponent_two :
  ∀ a : HomotopyGroup (C := Spectrum) 62 SphereSpectrum,
    (∃ n : ℕ, (2 ^ n : ℕ) • a = 0) → a + a = 0 := by
  sorry


public theorem theta5_filtration_gap :
  ∀ a b, ClassicalTheta5Detected background a → ClassicalTheta5Detected background b →
    a-b ∈ (background.classicalTower.tower SphereSpectrum).filtrationSubmodule 6 62 := by
  sorry


public theorem nu_detection :
  ClassicalDetects (background.classicalConvergence .sphere) (1,4)
    (background.standardClasses.standardHi 2) background.auxiliary.nuMap := by
  sorry

section OneLinePermanenceConstruction
set_option backward.isDefEq.respectTransparency false

private theorem nonzeroSurvivalOfPermanentNoIncoming
    (p : ℤ × ℤ) (x : background.classical.sphere.Page 2 p)
    (hperm : IsPermanentCycle background.classical.sphere p x) (hx : x ≠ 0)
    (hin : ∀ r : ℤ, 2 ≤ r →
      background.classical.sphere.d r (p-background.classical.sphere.diffDeg r) = 0) :
    NonzeroSurvival background.classical.sphere p x := by
  let E := background.classical.sphere
  let D := E.ssData p
  let n : WithTop ℕ := ↑(2-E.r₀).toNat
  obtain ⟨z,hz⟩ := hperm
  refine ⟨z,hz,?_⟩
  intro hz0
  have hB : D.B ⊤ = D.B n := boundaries_top_eq_of_d_eq_zero E 2
    (le_of_eq (background.classical.firstPage SphereSpectrum)) p hin
  have hb := (subobject_cokernel_π_eq_zero_iff (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) z).mp hz0
  apply hx
  rw [←hz]
  change D.pageπ n (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) z) = 0
  apply (subobject_cokernel_π_eq_zero_iff (D.B n) (D.Z n) (D.B_le_Z n) _).mpr
  change (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ (D.Z n).arrow) z ∈ _
  rw [Subobject.ofLE_arrow]
  rwa [←hB]

private theorem oneLineNoIncoming (t : ℤ) (r : ℤ) (hr : 2 ≤ r) :
    background.classical.sphere.d r (((1:ℤ),t)-background.classical.sphere.diffDeg r) = 0 := by
  let q := ((1:ℤ),t)-background.classical.sphere.diffDeg r
  have hs : q.1 < 0 := by
    dsimp only [q]
    rw [background.classical.differentialDegree]
    change 1-r < 0
    omega
  letI : Subsingleton (background.classical.sphere.Page r q) :=
    KIP126.AdamsSynthetic.Completed.classical_page_negative .sphere r q.1 q.2 hs
  ext a
  have ha : a = 0 := Subsingleton.elim _ _
  simp only [ha, map_zero]


private theorem standardHiActualNonzero (i : ℕ) (hiBound : i ≤ 7 := by omega) :
    background.standardClasses.standardHi i ≠ 0 := by
  exact background.standardClasses.hi_ne_zero i hiBound

/-- The detected standard h₁ is nonzero, and every incoming source has negative filtration. -/
public theorem eta_permanent :
  NonzeroSurvival background.classical.sphere (1,2) (background.standardClasses.standardHi 1) := by
  have hperm : IsPermanentCycle background.classical.sphere (1,2)
      (background.standardClasses.standardHi 1) := by
    obtain ⟨z,hz,_,_,_⟩ := eta_detection
    exact ⟨z,hz⟩
  exact nonzeroSurvivalOfPermanentNoIncoming (1,2) _ hperm (standardHiActualNonzero 1) (oneLineNoIncoming 2)

/-- The detected standard h₂ is nonzero, and every incoming source has negative filtration. -/
public theorem nu_permanent :
  NonzeroSurvival background.classical.sphere (1,4) (background.standardClasses.standardHi 2) := by
  have hperm : IsPermanentCycle background.classical.sphere (1,4)
      (background.standardClasses.standardHi 2) := by
    obtain ⟨z,hz,_,_,_⟩ := nu_detection
    exact ⟨z,hz⟩
  exact nonzeroSurvivalOfPermanentNoIncoming (1,4) _ hperm (standardHiActualNonzero 2) (oneLineNoIncoming 4)

end OneLinePermanenceConstruction


public theorem eta_label :
  sphereFirstQuotient background 1 2 (quotientClass 1 eta) = background.standardClasses.standardHi 1 := by
  sorry


public theorem eta_realization :
  realizeSphere 1 2 eta = background.auxiliary.etaMap := by
  sorry

/-- The doubling relation for the common source witness of θ₅ and
its detection. -/
public theorem theta5_order_two :
  theta5 + theta5 = 0 :=
  theta5Construction.property.2


public theorem sphereVanishing :
  SphereVanishingLine background := by
  sorry


public theorem two_detection :
  ClassicalDetects (background.classicalConvergence .sphere) (1,1)
    (background.standardClasses.standardHi 0) (classicalTwo (C := Spectrum)) := by
  sorry


public theorem adamsOneLine_d2 :
  ∀ (j : ℕ), 4 ≤ j → (hjBound : j ≤ 7) →
    HasNonzeroDifferential background.classical.sphere 2
      (1,((2^j : ℕ) : ℤ)) (3,1+((2^(j-1+1) : ℕ) : ℤ))
      (background.standardClasses.standardHi j) (oneLineTarget background j) := by
  sorry

section H5SquarePermanenceConstruction
set_option backward.isDefEq.respectTransparency false

private theorem h5SquareActualNonzero : background.standardClasses.standardHiSquare 5 ≠ 0 := by
  obtain ⟨hdeg,xr,yr,_,hy,_,hne⟩ := adamsOneLine_d2 6 (by decide) (by decide)
  intro hz
  apply hne
  rw [←hy.eq_on_page_two]
  change background.sphereAlgebra.product (1,1) (2,64)
    (background.standardClasses.standardHi 0) (background.standardClasses.standardHiSquare 5) = 0
  rw [hz, map_zero]

private theorem h5SquareNoIncoming (r : ℤ) (hr : 2 ≤ r) :
    background.classical.sphere.d r (((2:ℤ),64)-background.classical.sphere.diffDeg r) = 0 := by
  by_cases h2 : r = 2
  · subst r
    have hq : ((2:ℤ),64)-background.classical.sphere.diffDeg 2 = (0,63) := by
      rw [background.classical.differentialDegree]
      decide
    rw [hq]
    letI := KIP126.AdamsSynthetic.Completed.sphere_page_filtration_zero 2 63 (by decide)
    ext a
    have ha : a = 0 := Subsingleton.elim _ _
    simp only [ha, map_zero]
  · let q := ((2:ℤ),64)-background.classical.sphere.diffDeg r
    have hs : q.1 < 0 := by
      dsimp only [q]
      rw [background.classical.differentialDegree]
      change 2-r < 0
      omega
    letI : Subsingleton (background.classical.sphere.Page r q) :=
      KIP126.AdamsSynthetic.Completed.classical_page_negative .sphere r q.1 q.2 hs
    ext a
    have ha : a = 0 := Subsingleton.elim _ _
    simp only [ha, map_zero]

private theorem h5SquarePermanentProof :
    NonzeroSurvival background.classical.sphere (2,64)
      (background.standardClasses.standardHiSquare 5) := by
  have hperm : IsPermanentCycle background.classical.sphere (2,64)
      (background.standardClasses.standardHiSquare 5) := by
    obtain ⟨z,hz,_,_,_⟩ := theta5_detection
    exact ⟨z,hz⟩
  exact nonzeroSurvivalOfPermanentNoIncoming _ _ hperm h5SquareActualNonzero h5SquareNoIncoming

/-- The detected square is nonzero at infinity: the independent Adams d2 target
forces E2 nonvanishing, and every possible incoming source is zero. -/
public theorem h5Square_permanent :
  NonzeroSurvival background.classical.sphere (2,64)
    (background.standardClasses.standardHiSquare 5) := by
  exact h5SquarePermanentProof

end H5SquarePermanenceConstruction

/-- The specified tmf unit is definitionally the same algebra unit. -/
public theorem tmf_algebra_unit :
  tmf_algebra.one = tmfUnit := rfl

section TmfConvergenceTransport
set_option backward.isDefEq.respectTransparency false

/-- Transport the specified detector convergence along the same fixed tmf
comparison, retaining the actual tower lifts and their cofiber images. -/
public def tmf_convergence :
  ClassicalTowerConvergence background.classicalTower tmf := by
  let e : tmf ≅ background.auxiliary.detector := tmfIso
  let c : ClassicalTowerConvergence background.classicalTower background.auxiliary.detector :=
    background.classicalConvergence .detector
  have tmf_filtration_map {X Y : Spectrum} (f : X ⟶ Y) (s m : ℤ) (x : HomotopyGroup m X)
      (hx : x ∈ (background.classicalTower.tower X).filtrationSubmodule s m) :
      x ≫ f ∈ (background.classicalTower.tower Y).filtrationSubmodule s m := by
    obtain ⟨a, rfl⟩ := hx
    refine ⟨a ≫ (background.classicalTower.map f).stage s.toNat, ?_⟩
    change (a ≫ (background.classicalTower.map f).stage s.toNat) ≫ (background.classicalTower.tower Y).projection s =
      (a ≫ (background.classicalTower.tower X).projection s) ≫ f
    rw [Category.assoc, (background.classicalTower.map f).projection s, ← Category.assoc]

  have tmf_filtration_iso_mem {X Y : Spectrum} (e : X ≅ Y) (s m : ℤ)
      (x : AbstractAdamsTower.homotopy X m) :
      x ≫ e.hom ∈
          ModuleCat.subobjectModule _ ((background.classicalTower.tower Y).filtration.F s m) ↔
        x ∈ ModuleCat.subobjectModule _ ((background.classicalTower.tower X).filtration.F s m) := by
    simp (config := { congrConsts := false }) only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply]
    change x ≫ e.hom ∈ (background.classicalTower.tower Y).filtrationSubmodule s m ↔
      x ∈ (background.classicalTower.tower X).filtrationSubmodule s m
    constructor
    · intro hx
      simpa (config := { congrConsts := false }) only [Category.assoc, e.hom_inv_id, Category.comp_id] using
        tmf_filtration_map e.inv s m (x ≫ e.hom) hx
    · exact tmf_filtration_map e.hom s m x

  have tmf_quotient_iso {R : Type} [Ring R] {M N : ModuleCat.{0} R}
      (B Z : Subobject M) (B' Z' : Subobject N) (h : B ≤ Z) (h' : B' ≤ Z')
      (e : M ≃ₗ[R] N)
      (hB : ∀ x, e x ∈ (ModuleCat.subobjectModule N) B' ↔ x ∈ (ModuleCat.subobjectModule M) B)
      (hZ : ∀ x, e x ∈ (ModuleCat.subobjectModule N) Z' ↔ x ∈ (ModuleCat.subobjectModule M) Z) :
      ∃ q : cokernel (Subobject.ofLE B Z h) ≅ cokernel (Subobject.ofLE B' Z' h'),
        ∀ a : (Subobject.underlying.obj Z : ModuleCat R),
          ∃ b : (Subobject.underlying.obj Z' : ModuleCat R),
            Z'.arrow b = e (Z.arrow a) ∧
            q.hom (cokernel.π (Subobject.ofLE B Z h) a) =
              cokernel.π (Subobject.ofLE B' Z' h') b := by
    have restrict (S : Subobject M) (T : Subobject N)
        (he : ∀ x, e x ∈ (ModuleCat.subobjectModule N) T ↔ x ∈ (ModuleCat.subobjectModule M) S) :
        ∃ w : Subobject.underlying.obj S ≅ Subobject.underlying.obj T,
          ∀ a, T.arrow (w.hom a) = e (S.arrow a) := by
      let a := LinearEquiv.ofInjective S.arrow.hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
      let b := LinearEquiv.ofInjective T.arrow.hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
      have hm : ((ModuleCat.subobjectModule M) S).map e.toLinearMap =
          (ModuleCat.subobjectModule N) T := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact (he x).2 hx
        · intro hy
          refine ⟨e.symm y, (he (e.symm y)).1 ?_, e.apply_symm_apply y⟩
          simpa (config := { congrConsts := false }) only [e.apply_symm_apply] using hy
      let c := e.ofSubmodules ((ModuleCat.subobjectModule M) S) ((ModuleCat.subobjectModule N) T) hm
      refine ⟨((a.trans c).trans b.symm).toModuleIso, ?_⟩
      intro x
      exact congrArg Subtype.val (b.apply_symm_apply (c (a x)))
    obtain ⟨b, hb⟩ := restrict B B' hB
    obtain ⟨z, hz⟩ := restrict Z Z' hZ
    have comm : Subobject.ofLE B Z h ≫ z.hom = b.hom ≫ Subobject.ofLE B' Z' h' := by
      apply (cancel_mono Z'.arrow).1
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change Z'.arrow (z.hom (Subobject.ofLE B Z h x)) =
        Z'.arrow (Subobject.ofLE B' Z' h' (b.hom x))
      rw [hz]
      have hs := congrArg (fun f => f.hom x) (Subobject.ofLE_arrow h)
      have ht := congrArg (fun f => f.hom (b.hom x)) (Subobject.ofLE_arrow h')
      change Z.arrow (Subobject.ofLE B Z h x) = B.arrow x at hs
      change Z'.arrow (Subobject.ofLE B' Z' h' (b.hom x)) = B'.arrow (b.hom x) at ht
      rw [hs, ht, hb]
    let q := cokernel.mapIso (Subobject.ofLE B Z h) (Subobject.ofLE B' Z' h') b z comm
    refine ⟨q, fun a => ⟨z.hom a, hz a, ?_⟩⟩
    have hq : cokernel.π (Subobject.ofLE B Z h) ≫ q.hom =
        z.hom ≫ cokernel.π (Subobject.ofLE B' Z' h') := by
      simp (config := { congrConsts := false }) only [q, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc]
    exact congrArg (fun f => f.hom a) hq
  let homotopyIso (m : ℤ) :
      AbstractAdamsTower.homotopy tmf m ≅ AbstractAdamsTower.homotopy background.auxiliary.detector m := {
    hom := ModuleCat.ofHom (inducedMap e.hom m).toIntLinearMap
    inv := ModuleCat.ofHom (inducedMap e.inv m).toIntLinearMap
    hom_inv_id := by
      ext a
      change (a ≫ e.hom) ≫ e.inv = a
      simp (config := { congrConsts := false }) only [Category.assoc, e.hom_inv_id, Category.comp_id]
    inv_hom_id := by
      ext a
      change (a ≫ e.inv) ≫ e.hom = a
      simp (config := { congrConsts := false }) only [Category.assoc, e.inv_hom_id, Category.comp_id] }
  let infinityIso (p : ℤ × ℤ) :
      ((background.classical.obj tmf).ssData p).eInfty ≅ ((background.classical.obj background.auxiliary.detector).ssData p).eInfty := {
    hom := (background.classical.map e.hom).eInftyMap p
    inv := (background.classical.map e.inv).eInftyMap p
    hom_inv_id := by
      rw [← SpectralSequenceMorphism.eInftyMap_comp, ← background.classical.map_comp, e.hom_inv_id,
        background.classical.map_id, SpectralSequenceMorphism.eInftyMap_id]
    inv_hom_id := by
      rw [← SpectralSequenceMorphism.eInftyMap_comp, ← background.classical.map_comp, e.inv_hom_id,
        background.classical.map_id, SpectralSequenceMorphism.eInftyMap_id] }
  have gr (s m : ℤ) :
      ∃ q : (background.classicalTower.tower tmf).filtration.associatedGraded s m ≅
        (background.classicalTower.tower background.auxiliary.detector).filtration.associatedGraded s m,
        ∀ b : (Subobject.underlying.obj ((background.classicalTower.tower tmf).filtration.F s m) : ModuleCat ℤ),
          ∃ b' : (Subobject.underlying.obj ((background.classicalTower.tower background.auxiliary.detector).filtration.F s m) : ModuleCat ℤ),
            ((background.classicalTower.tower background.auxiliary.detector).filtration.F s m).arrow b' =
              ((background.classicalTower.tower tmf).filtration.F s m).arrow b ≫ e.hom ∧
            q.hom ((background.classicalTower.tower tmf).filtration.toAssociatedGraded s m b) =
              (background.classicalTower.tower background.auxiliary.detector).filtration.toAssociatedGraded s m b' := by
    exact tmf_quotient_iso
      ((background.classicalTower.tower tmf).filtration.F (s+1) m) ((background.classicalTower.tower tmf).filtration.F s m)
      ((background.classicalTower.tower background.auxiliary.detector).filtration.F (s+1) m) ((background.classicalTower.tower background.auxiliary.detector).filtration.F s m)
      ((background.classicalTower.tower tmf).filtration.mono s m) ((background.classicalTower.tower background.auxiliary.detector).filtration.mono s m)
      (homotopyIso m).toLinearEquiv
      (tmf_filtration_iso_mem e (s+1) m) (tmf_filtration_iso_mem e s m)
  let q := fun s m => (gr s m).choose
  refine ⟨fun p => infinityIso p ≪≫ c.identification p ≪≫ (q p.1 (p.2-p.1)).symm, ?_⟩
  intro p a z hz b hb
  let z' := (background.classical.map e.hom).toSSDataMorphism.cycleMap p ⊤ z
  let a' := a ≫ (background.classicalTower.map e.hom).stage p.1.toNat
  obtain ⟨b', hb', hq⟩ := (gr p.1 (p.2-p.1)).choose_spec b
  have hz' : (background.classicalTower.sequence background.auxiliary.detector).infiniteRepresentativeE1 p z' =
      (background.classicalTower.tower background.auxiliary.detector).layerMap p a' := by
    have hc := congrArg (fun f => f.hom z)
      ((background.classical.map e.hom).toSSDataMorphism.cycleMap_arrow p ⊤)
    change (((background.classical.obj background.auxiliary.detector).ssData p).Z ⊤).arrow z' =
      (background.classical.map e.hom).φ p ((((background.classical.obj tmf).ssData p).Z ⊤).arrow z) at hc
    unfold TowerSequencePresentation.infiniteRepresentativeE1
    rw [hc, background.classicalTower.natural]
    change (background.classicalTower.sequence tmf).infiniteRepresentativeE1 p z ≫ (background.classicalTower.map e.hom).layer p.1 =
      (background.classicalTower.tower background.auxiliary.detector).layerMap p a'
    rw [hz]
    change (a ≫ HasFunctorialCofiber.cofibι _) ≫ (background.classicalTower.map e.hom).layer p.1 =
      (a ≫ (background.classicalTower.map e.hom).stage p.1.toNat) ≫ HasFunctorialCofiber.cofibι _
    dsimp only [TowerMap.layer]
    rw [Category.assoc, ← HasFunctorialCofiber.cofibMap_ι, ← Category.assoc]
  have hb'' : ((background.classicalTower.tower background.auxiliary.detector).filtration.F p.1 (p.2-p.1)).arrow b' =
      a' ≫ (background.classicalTower.tower background.auxiliary.detector).projection p.1 := by
    rw [hb', hb]
    change (a ≫ (background.classicalTower.tower tmf).projection p.1) ≫ e.hom =
      (a ≫ (background.classicalTower.map e.hom).stage p.1.toNat) ≫ (background.classicalTower.tower background.auxiliary.detector).projection p.1
    simpa (config := { congrConsts := false }) only [Category.assoc] using
      congrArg (fun f => a ≫ f) ((background.classicalTower.map e.hom).projection p.1).symm
  have hc := c.canonical p a' z' hz' b' hb''
  have hpage := congrArg (fun f => f.hom z)
    ((background.classical.map e.hom).toSSDataMorphism.pageπ_pageMap p ⊤)
  change (background.classical.map e.hom).eInftyMap p (((background.classical.obj tmf).ssData p).pageπ ⊤ z) =
    ((background.classical.obj background.auxiliary.detector).ssData p).pageπ ⊤ z' at hpage
  change (q p.1 (p.2-p.1)).inv
      ((c.identification p).hom
        ((background.classical.map e.hom).eInftyMap p (((background.classical.obj tmf).ssData p).pageπ ⊤ z))) = _
  rw [hpage, hc, ← hq]
  exact congrArg (fun f => f.hom ((background.classicalTower.tower tmf).filtration.toAssociatedGraded p.1 (p.2-p.1) b))
    (q p.1 (p.2-p.1)).hom_inv_id
end TmfConvergenceTransport

private structure KappaBarData where
  kappaBar :
  HomotopyGroup (C := Spectrum) 20 SphereSpectrum
  kappaBar_detection :
  ClassicalDetects (background.classicalConvergence .sphere) (4,24) g kappaBar

private def kappaBarConstruction : KappaBarData where
  kappaBar := by sorry
  kappaBar_detection := by sorry

/-- The fixed mathematical object on the project background. -/
public def kappaBar :
  HomotopyGroup (C := Spectrum) 20 SphereSpectrum := by
  exact kappaBarConstruction.kappaBar

private structure WClassData where
  wClass :
  HomotopyGroup (C := Spectrum) 45 SphereSpectrum
  w_detection :
  ClassicalDetects (background.classicalConvergence .sphere) (9,54) deltaH1g wClass

private def wConstruction : WClassData where
  wClass := by sorry
  w_detection := by sorry

/-- The fixed mathematical object on the project background. -/
public def wClass :
  HomotopyGroup (C := Spectrum) 45 SphereSpectrum :=
  wConstruction.wClass

private structure TmfDifferentialData where
  tmfV2Sixteen :
  (background.classical.obj tmf).Page 2 (16,112)
  tmfBetaGFour :
  (background.classical.obj tmf).Page 2 (19,114)
  tmf_v2_sixteen_d3 :
  HasDifferential (background.classical.obj tmf) 3 (16,112) (19,114)
    tmfV2Sixteen tmfBetaGFour

private def tmfDifferentialConstruction : TmfDifferentialData where
  tmfV2Sixteen := by sorry
  tmfBetaGFour := by sorry
  tmf_v2_sixteen_d3 := by sorry

/-- The fixed mathematical object on the project background. -/
public def tmfV2Sixteen :
  (background.classical.obj tmf).Page 2 (16,112) :=
  tmfDifferentialConstruction.tmfV2Sixteen

/-- The fixed mathematical object on the project background. -/
public def tmfBetaGFour :
  (background.classical.obj tmf).Page 2 (19,114) :=
  tmfDifferentialConstruction.tmfBetaGFour

private def tmfSourceData : TmfSourceData background tmfBindingData where
  algebra := tmf_algebra
  algebra_unit := tmf_algebra_unit
  convergence := tmf_convergence
  kappaBar := kappaBar
  wClass := wClass
  v2Sixteen := tmfV2Sixteen
  betaGFour := tmfBetaGFour

public def high125 := classicalSphereProduct
  (classicalSphereProduct (classicalSphereProduct kappaBar kappaBar)
    (classicalSphereProduct kappaBar kappaBar)) wClass

/-- Transfer connectivity from the same detector along the specified tmf isomorphism. -/
public theorem tmf_connective :
  ∀ n : ℤ, n < 0 → Subsingleton (HomotopyGroup n tmf) := by
  intro n hn
  haveI : Subsingleton (Sphere n ⟶ background.auxiliary.detector) :=
    KIP126.AdamsSynthetic.Completed.detector_isPaperSpectrum.1 n hn
  constructor
  intro a b
  apply (cancel_mono tmfIso.hom).mp
  exact Subsingleton.elim (a ≫ tmfIso.hom) (b ≫ tmfIso.hom)

/-- Transfer degreewise finite coefficient homology along the specified tmf isomorphism. -/
public theorem tmf_finiteModTwoType :
  ∀ n : ℤ, Finite (ModTwoHomology background.coefficients n tmf) := by
  intro n
  haveI : Finite (Sphere n ⟶ (tensorLeft background.coefficients.object).obj
      background.auxiliary.detector) :=
    KIP126.AdamsSynthetic.Completed.detector_isPaperSpectrum.2 n
  let e := Iso.homCongr (Iso.refl (Sphere (C := Spectrum) n))
    ((tensorLeft background.coefficients.object).mapIso tmfIso)
  exact Finite.of_equiv _ e.symm


public theorem g_nonzero :
  g ≠ 0 := by
  exact gConstruction.g_nonzero


public theorem g_unique :
  ∀ x : background.classical.sphere.Page 2 (4,24), x ≠ 0 → x = g := by
  exact gConstruction.g_unique


public theorem deltaH1g_nonzero :
  deltaH1g ≠ 0 := by
  exact deltaH1gConstruction.deltaH1g_nonzero


public theorem deltaH1g_unique :
  ∀ x : background.classical.sphere.Page 2 (9,54), x ≠ 0 → x = deltaH1g := by
  exact deltaH1gConstruction.deltaH1g_unique


public theorem tmf_vanishing62 :
  ∀ x : HomotopyGroup (C := Spectrum) 62 tmf, x = 0 := by
  sorry


public theorem tmf_low_filtration63 :
  ∀ s : ℤ, s ≤ 0 →
    Subsingleton ((background.classical.obj tmf).Page 2 (s,63+s)) := by
  sorry


public theorem kappaBar_detection :
  ClassicalDetects (background.classicalConvergence .sphere) (4,24) g kappaBar := by
  exact kappaBarConstruction.kappaBar_detection


public theorem w_detection :
  ClassicalDetects (background.classicalConvergence .sphere) (9,54) deltaH1g wClass := by
  exact wConstruction.w_detection

/-- The specified image retains the non-odd-torsion content of the BMQ
2-local Hurewicz result. The source-to-model comparison uses the fixed
source classes and unit. -/
public theorem tmf_high125_nonzero :
  ¬ IsOddTorsionMap (high125 ≫ tmfUnit) := by
  sorry


/-- The tmf d₃ on v₂¹⁶ with target βg⁴ (BR21, Theorem 5.18 and Table 5.4). -/
public theorem tmf_v2_sixteen_d3 :
  HasDifferential (background.classical.obj tmf) 3 (16,112) (19,114)
    tmfV2Sixteen tmfBetaGFour := by
  exact tmfDifferentialConstruction.tmf_v2_sixteen_d3


public theorem detector_d3 :
  HasDifferential (background.classical.obj background.auxiliary.detector) 3 (16,112) (19,114)
    ((background.classical.map tmfIso.hom).pageMap 2 (16,112) tmfV2Sixteen)
    ((background.classical.map tmfIso.hom).pageMap 2 (19,114) tmfBetaGFour) := (background.classical.map tmfIso.hom).hasDifferential tmf_v2_sixteen_d3

private structure SyntheticH0Data where
  syntheticH0 :
  BiHom 0 1 (S_0_0 : SyntheticSpectrum)
  syntheticH0_first_quotient_label :
  KIP126.AdamsSynthetic.sphereFirstQuotient background.nu background.quotients.functoriality background.firstQuotient
    1 1 (quotientClass 1 syntheticH0) = background.standardClasses.standardHi 0
  lambdaMultiply_syntheticH0 :
  lambdaMultiply 1 syntheticH0 = Route.syntheticTwo
  sphereProduct_syntheticH0_eta :
  sphereProduct syntheticH0 eta = 0
  sphereProduct_syntheticH0_eq_zero_in_bidegree_two_three :
  ∀ a : BiHom 2 3 (S_0_0 : SyntheticSpectrum), sphereProduct syntheticH0 a = 0

private def syntheticH0Construction : SyntheticH0Data where
  syntheticH0 := by sorry
  syntheticH0_first_quotient_label := by sorry
  lambdaMultiply_syntheticH0 := by sorry
  sphereProduct_syntheticH0_eta := by sorry
  sphereProduct_syntheticH0_eq_zero_in_bidegree_two_three := by sorry

/-- The fixed mathematical object on the project background. -/
public def syntheticH0 :
  BiHom 0 1 (S_0_0 : SyntheticSpectrum) :=
  syntheticH0Construction.syntheticH0


public theorem syntheticH0_first_quotient_label :
  KIP126.AdamsSynthetic.sphereFirstQuotient background.nu background.quotients.functoriality background.firstQuotient
    1 1 (quotientClass 1 syntheticH0) = background.standardClasses.standardHi 0 := by
  exact syntheticH0Construction.syntheticH0_first_quotient_label


public theorem lambdaMultiply_syntheticH0 :
  lambdaMultiply 1 syntheticH0 = Route.syntheticTwo := by
  exact syntheticH0Construction.lambdaMultiply_syntheticH0


public theorem sphereProduct_syntheticH0_eta :
  sphereProduct syntheticH0 eta = 0 := by
  exact syntheticH0Construction.sphereProduct_syntheticH0_eta


public theorem sphereProduct_syntheticH0_eq_zero_in_bidegree_two_three :
  ∀ a : BiHom 2 3 (S_0_0 : SyntheticSpectrum), sphereProduct syntheticH0 a = 0 := by
  exact syntheticH0Construction.sphereProduct_syntheticH0_eq_zero_in_bidegree_two_three


public theorem selected_realization_kernel :
  RealizationKernel background := by
  sorry

/- The rotation and suspension-square argument. The fixed triangle-lift and realization-kernel inputs remain
explicit above. -/

end KIP126.Literature.Standard
end
