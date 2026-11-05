module

public import KIP126.AdamsSynthetic.Completed.MappingOperations
import all KIP126.AdamsSynthetic.Completed.MappingOperations
import all KIP126.AdamsSynthetic.Completed.Background
import all KIP126.AdamsSynthetic.Enrichment

/-! Coherent shifts, graded Hom, and transport of the same filtration,
pages, representatives, and sphere multiplication. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.Kervaire.Route
noncomputable section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Shift associativity from the fixed quotient coherence. -/
public theorem biShift_associativity : ∀ (a b c ab bc total : ℤ × ℤ)
      (hab : a + b = ab) (hbc : b + c = bc)
      (habc : ab + c = total) (habc' : a + bc = total) (X : SyntheticSpectrum),
    (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).hom.app X) ≫
        (biShiftAddIso ab c total habc).hom.app X =
      (biShiftAddIso b c bc hbc).hom.app ((SyntheticCategory.biShift a).obj X) ≫
        (biShiftAddIso a bc total habc').hom.app X := quotients.coherence.associativity

public theorem biShift_left_unit : ∀ (a : ℤ × ℤ) (X : SyntheticSpectrum),
    (biShiftAddIso 0 a a (zero_add a)).hom.app X =
      (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app X) := quotients.coherence.left_unit

public theorem biShift_right_unit : ∀ (a : ℤ × ℤ) (X : SyntheticSpectrum),
    (biShiftAddIso a 0 a (add_zero a)).hom.app X =
      SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj X) := quotients.coherence.right_unit

public theorem biShift_lambda_comm : ∀ (a : ℤ × ℤ) (X : SyntheticSpectrum),
    SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj X) =
      (biShiftAddIso a (0, -1) (a + (0, -1)) rfl).hom.app X ≫
        (biShiftAddIso (0, -1) a (a + (0, -1)) (add_comm _ _)).inv.app X ≫
        (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app X) := quotients.coherence.lambda_comm

public theorem graded_coherence : BiShiftCoherence SyntheticSpectrum := quotients.coherence

/-- Additivity of the fixed bigraded shifts. -/
public theorem graded_shiftAdditive : ∀ p : ℤ × ℤ, (SyntheticCategory.biShift p : SyntheticSpectrum ⥤ SyntheticSpectrum).Additive := exactness.shiftAdditive

/-! The total λ map extends precomposition to the direct sum, and evaluation at this
map defines the polynomial action. -/

private def totalLambda (X Y : SyntheticSpectrum) :
    TotalWeightHom X Y →ₗ[ℤ] TotalWeightHom X Y :=
  (DirectSum.toAddMonoid fun w =>
    (weightHomInclusion (w-1)).comp
      (Preadditive.leftComp Y
        (weightHomLambda (X := X) (𝟙 ((SyntheticCategory.biShift (0,w)).obj X))))).toIntLinearMap

private theorem totalLambda_of (X Y : SyntheticSpectrum) (w : ℤ) (f : WeightHom X Y w) :
    totalLambda X Y (weightHomInclusion w f) =
      weightHomInclusion (w-1) (weightHomLambda f) := by
  change DirectSum.toAddMonoid
    (fun v : ℤ => (DirectSum.of (WeightHom X Y) (v-1)).comp
      (Preadditive.leftComp Y
        (weightHomLambda (X := X) (𝟙 ((SyntheticCategory.biShift (0,v)).obj X)))))
    (DirectSum.of (WeightHom X Y) w f) =
      DirectSum.of (WeightHom X Y) (w-1) (weightHomLambda f)
  rw [DirectSum.toAddMonoid_of]
  change DirectSum.of (WeightHom X Y) (w-1)
      ((weightHomLambda (X := X) (𝟙 ((SyntheticCategory.biShift (0,w)).obj X))) ≫ f) =
    DirectSum.of (WeightHom X Y) (w-1) (weightHomLambda f)
  apply congrArg (DirectSum.of (WeightHom X Y) (w-1))
  dsimp only [weightHomLambda, Functor.id_obj, Functor.comp_obj]
  rw [Category.comp_id, Category.assoc]

/-- The polynomial action obtained by evaluating X at actual graded λ. -/
@[implicit_reducible] public def graded_module : ∀ X Y : SyntheticSpectrum, Module (Polynomial ℤ) (TotalWeightHom X Y) := by
  intro X Y
  exact
    (fun (M : Type) [AddCommGroup M] (D : M →+ M) =>
      let A := Module.End ℤ M
      letI : Ring A := inferInstance
      let ring : NonAssocRing A := inferInstance
      letI : Module A M := inferInstance
      let L : A := D.toIntLinearMap
      let hom : Polynomial ℤ →+* A :=
        Polynomial.eval₂RingHom' (Int.castRingHom A) L
          (fun a => @Int.cast_commute A ring a L)
      Module.compHom M hom)
      (TotalWeightHom X Y)
      (DirectSum.toAddMonoid fun w =>
        (weightHomInclusion (w-1)).comp
          (Preadditive.leftComp Y
            (weightHomLambda (X := X) (𝟙 ((SyntheticCategory.biShift (0,w)).obj X)))))


/-- The polynomial generator acts by the specified degree-lowering λ map. -/
public theorem graded_lambda_smul : ∀ (X Y : SyntheticSpectrum) (w : ℤ) (f : WeightHom X Y w),
    letI := graded_module X Y
    (Polynomial.X : Polynomial ℤ) • weightHomInclusion w f =
      weightHomInclusion (w-1) (weightHomLambda f) := by
  intro X Y w f
  letI := graded_module X Y
  change (Polynomial.eval₂ (Int.castRingHom _) (totalLambda X Y) Polynomial.X) _ = _
  rw [Polynomial.eval₂_X]
  exact totalLambda_of X Y w f

/-- Commuting polynomial scalar actions on total-weight Hom. -/
public theorem graded_compose._proof_1 (X Z : SyntheticSpectrum) :
    @SMulCommClass (Polynomial ℤ) (Polynomial ℤ) (TotalWeightHom X Z)
      (@SemigroupAction.toSMul _ _ (@Monoid.toSemigroup (Polynomial ℤ) (@CommMonoid.toMonoid (Polynomial ℤ) (@CommRing.toCommMonoid (Polynomial ℤ) (@Polynomial.commRing ℤ Int.instCommRing)))) (@MulAction.toSemigroupAction _ _ (@CommMonoid.toMonoid (Polynomial ℤ) (@CommRing.toCommMonoid (Polynomial ℤ) (@Polynomial.commRing ℤ Int.instCommRing)))
        (@DistribMulAction.toMulAction _ _ (@CommMonoid.toMonoid (Polynomial ℤ) (@CommRing.toCommMonoid (Polynomial ℤ) (@Polynomial.commRing ℤ Int.instCommRing))) _ (@Module.toDistribMulAction _ _ _ _ (graded_module X Z)))))
      (@SemigroupAction.toSMul _ _ (@Monoid.toSemigroup (Polynomial ℤ) (@CommMonoid.toMonoid (Polynomial ℤ) (@CommRing.toCommMonoid (Polynomial ℤ) (@Polynomial.commRing ℤ Int.instCommRing)))) (@MulAction.toSemigroupAction _ _ (@CommMonoid.toMonoid (Polynomial ℤ) (@CommRing.toCommMonoid (Polynomial ℤ) (@Polynomial.commRing ℤ Int.instCommRing)))
        (@DistribMulAction.toMulAction _ _ (@CommMonoid.toMonoid (Polynomial ℤ) (@CommRing.toCommMonoid (Polynomial ℤ) (@Polynomial.commRing ℤ Int.instCommRing))) _ (@Module.toDistribMulAction _ _ _ _ (graded_module X Z))))) := by
  letI := graded_module X Z
  exact smulCommClass_self _ _

private def totalComp (X Y Z : SyntheticSpectrum) :
    TotalWeightHom Y Z →+ (TotalWeightHom X Y →+ TotalWeightHom X Z) := by
  letI : ∀ p : ℤ × ℤ,
      (SyntheticCategory.biShift p : SyntheticSpectrum ⥤ SyntheticSpectrum).Additive :=
    exactness.shiftAdditive
  exact DirectSum.toAddMonoid fun b =>
    { toFun := fun g => DirectSum.toAddMonoid fun a =>
        { toFun := fun f => weightHomInclusion (a+b) (weightHomComp f g)
          map_zero' := by
            dsimp only [weightHomComp]
            rw [Functor.map_zero, Limits.zero_comp, Limits.comp_zero, map_zero]
          map_add' := by
            intro f f'
            dsimp only [weightHomComp]
            rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, map_add] }
      map_zero' := by
        apply DirectSum.addHom_ext
        intro a f
        change (DirectSum.toAddMonoid (γ := TotalWeightHom X Z) _)
          (DirectSum.of (WeightHom X Y) a f) = 0
        rw [DirectSum.toAddMonoid_of]
        change weightHomInclusion (a+b) (weightHomComp f (0 : WeightHom Y Z b)) = 0
        dsimp only [weightHomComp]
        rw [Limits.comp_zero, Limits.comp_zero, map_zero]
      map_add' := by
        intro g g'
        apply DirectSum.addHom_ext
        intro a f
        rw [AddMonoidHom.add_apply]
        change (DirectSum.toAddMonoid (γ := TotalWeightHom X Z) _)
          (DirectSum.of (WeightHom X Y) a f) =
          (DirectSum.toAddMonoid (γ := TotalWeightHom X Z) _)
            (DirectSum.of (WeightHom X Y) a f) +
          (DirectSum.toAddMonoid (γ := TotalWeightHom X Z) _)
            (DirectSum.of (WeightHom X Y) a f)
        rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
        change weightHomInclusion (a+b) (weightHomComp f (g+g')) =
          weightHomInclusion (a+b) (weightHomComp f g) +
          weightHomInclusion (a+b) (weightHomComp f g')
        dsimp only [weightHomComp]
        rw [Preadditive.comp_add, Preadditive.comp_add, map_add] }

private theorem totalComp_of (X Y Z : SyntheticSpectrum) (a b : ℤ)
    (f : WeightHom X Y a) (g : WeightHom Y Z b) :
    totalComp X Y Z (weightHomInclusion b g) (weightHomInclusion a f) =
      weightHomInclusion (a+b) (weightHomComp f g) := by
  change (DirectSum.toAddMonoid (γ := TotalWeightHom X Y →+ TotalWeightHom X Z) _)
    (DirectSum.of (WeightHom Y Z) b g) (weightHomInclusion a f) = _
  rw [DirectSum.toAddMonoid_of]
  change (DirectSum.toAddMonoid (γ := TotalWeightHom X Z) _)
    (DirectSum.of (WeightHom X Y) a f) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

private theorem totalComp_assoc (W X Y Z : SyntheticSpectrum)
    (f : TotalWeightHom W X) (g : TotalWeightHom X Y) (h : TotalWeightHom Y Z) :
    totalComp W Y Z h (totalComp W X Y g f) =
      totalComp W X Z (totalComp X Y Z h g) f := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f f' hf hf' => simp only [map_add, hf, hf']
  | of a f =>
    induction g using DirectSum.induction_on with
    | zero => simp only [map_zero, AddMonoidHom.zero_apply]
    | add g g' hg hg' => simp only [map_add, AddMonoidHom.add_apply, hg, hg']
    | of b g =>
      induction h using DirectSum.induction_on with
      | zero => simp only [map_zero, AddMonoidHom.zero_apply]
      | add h h' hh hh' => simp only [map_add, AddMonoidHom.add_apply, hh, hh']
      | of c h =>
        change totalComp W Y Z (weightHomInclusion c h)
          (totalComp W X Y (weightHomInclusion b g) (weightHomInclusion a f)) =
          totalComp W X Z (totalComp X Y Z (weightHomInclusion c h) (weightHomInclusion b g))
            (weightHomInclusion a f)
        rw [totalComp_of, totalComp_of, totalComp_of, totalComp_of]
        exact homogeneous_assoc quotients.coherence a b c f g h

private theorem lambda_comm_named (a c : ℤ × ℤ)
    (hac : a + (0,-1) = c) (hca : (0,-1) + a = c) (X : SyntheticSpectrum) :
    SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj X) =
      (biShiftAddIso a (0,-1) c hac).hom.app X ≫
        (biShiftAddIso (0,-1) a c hca).inv.app X ≫
          (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app X) := by
  cases hac
  exact quotients.coherence.lambda_comm a X

private theorem totalComp_lambda_central (X Y : SyntheticSpectrum) (f : TotalWeightHom X Y) :
    totalComp X X Y f (weightHomInclusion (-1) (SyntheticCategory.lam.app X)) =
      totalComp X Y Y (weightHomInclusion (-1) (SyntheticCategory.lam.app Y)) f := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | add f f' hf hf' => simp only [map_add, AddMonoidHom.add_apply, hf, hf']
  | of w f =>
    change totalComp X X Y (weightHomInclusion w f) _ = totalComp X Y Y _ (weightHomInclusion w f)
    rw [totalComp_of, totalComp_of]
    rw [homogeneous_regrade (-1) w (w-1) (by omega), homogeneous_regrade w (-1) (w-1) (by omega)]
    apply congrArg (weightHomInclusion (w-1))
    rw [SyntheticCategory.lam.naturality]
    rw [lambda_comm_named (0,w) (0,w-1) (by ext <;> simp [sub_eq_add_neg]) (by ext <;> simp [sub_eq_add_neg, add_comm]) X]
    repeat rw [Category.assoc]
    rw [Iso.inv_hom_id_app_assoc, Functor.id_map]

private def compLambda (X Y : SyntheticSpectrum) :
    TotalWeightHom X Y →ₗ[ℤ] TotalWeightHom X Y :=
  (totalComp X Y Y (weightHomInclusion (-1) (SyntheticCategory.lam.app Y))).toIntLinearMap

private theorem compLambda_of (X Y : SyntheticSpectrum) (w : ℤ) (f : WeightHom X Y w) :
    compLambda X Y (weightHomInclusion w f) =
      weightHomInclusion (w-1) (weightHomLambda f) := by
  simp only [compLambda, AddMonoidHom.coe_toIntLinearMap]
  rw [totalComp_of]
  change weightHomInclusion (w + -1)
    ((biShiftAddIso (0,w) (0,-1) (0,w + -1) _).inv.app X ≫
      (SyntheticCategory.biShift (0,-1)).map f ≫ SyntheticCategory.lam.app Y) = _
  rw [SyntheticCategory.lam.naturality]
  rfl

private theorem totalComp_lambda_left (X Y Z : SyntheticSpectrum)
    (f : TotalWeightHom X Y) (g : TotalWeightHom Y Z) :
    totalComp X Y Z (compLambda Y Z g) f =
      compLambda X Z (totalComp X Y Z g f) := by
  simpa only [compLambda, AddMonoidHom.coe_toIntLinearMap] using
    (totalComp_assoc X Y Z Z f g (weightHomInclusion (-1) (SyntheticCategory.lam.app Z))).symm

private theorem totalComp_lambda_right (X Y Z : SyntheticSpectrum)
    (f : TotalWeightHom X Y) (g : TotalWeightHom Y Z) :
    totalComp X Y Z g (compLambda X Y f) =
      compLambda X Z (totalComp X Y Z g f) := by
  simp only [compLambda, AddMonoidHom.coe_toIntLinearMap]
  rw [totalComp_assoc, totalComp_lambda_central]
  exact (totalComp_assoc X Y Z Z f g (weightHomInclusion (-1) (SyntheticCategory.lam.app Z))).symm

private theorem additive_polynomial_smul {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (Polynomial ℤ) M] [Module (Polynomial ℤ) N]
    (f : M →+ N)
    (hX : ∀ m, f ((Polynomial.X : Polynomial ℤ) • m) = (Polynomial.X : Polynomial ℤ) • f m)
    (p : Polynomial ℤ) (m : M) : f (p • m) = p • f m := by
  induction p using Polynomial.induction_on generalizing m with
  | C a =>
    have ha : (Polynomial.C a : Polynomial ℤ) = (a : Polynomial ℤ) := Polynomial.C_eq_intCast a
    rw [ha]
    exact map_intCast_smul f (Polynomial ℤ) (Polynomial ℤ) a m
  | add p q hp hq => simp only [add_smul, map_add, hp, hq]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc]
    rw [mul_smul, ih, hX]
    simp only [mul_smul]

private theorem totalLambda_eq_compLambda (X Y : SyntheticSpectrum) :
    totalLambda X Y = compLambda X Y := by
  apply LinearMap.ext
  intro f
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | of w f =>
    change totalLambda X Y (weightHomInclusion w f) = compLambda X Y (weightHomInclusion w f)
    rw [totalLambda_of, compLambda_of]

private theorem graded_X_smul (X Y : SyntheticSpectrum) (f : TotalWeightHom X Y) :
    letI := graded_module X Y
    (Polynomial.X : Polynomial ℤ) • f = compLambda X Y f := by
  letI := graded_module X Y
  change (Polynomial.eval₂ (Int.castRingHom _) (totalLambda X Y) Polynomial.X) f = _
  rw [Polynomial.eval₂_X, totalLambda_eq_compLambda]

/-- Actual shifted composition, extended bilinearly over the polynomial action. -/
@[no_expose] public def graded_compose : ∀ X Y Z : SyntheticSpectrum,
    letI := graded_module X Y
    letI := graded_module Y Z
    letI := graded_module X Z
    TotalWeightHom Y Z →ₗ[Polynomial ℤ]
      TotalWeightHom X Y →ₗ[Polynomial ℤ] TotalWeightHom X Z := by
  intro X Y Z
  letI := graded_module X Y
  letI := graded_module Y Z
  letI := graded_module X Z
  let C : TotalWeightHom Y Z →+ (TotalWeightHom X Y →+ TotalWeightHom X Z) :=
    totalComp X Y Z
  let F : TotalWeightHom Y Z →+ (TotalWeightHom X Y →ₗ[Polynomial ℤ] TotalWeightHom X Z) :=
    { toFun := fun g =>
        { toFun := C g
          map_add' := (C g).map_add
          map_smul' := by
            intro p f
            apply additive_polynomial_smul (C g) (fun f => ?_) p f
            change totalComp X Y Z g ((Polynomial.X : Polynomial ℤ) • f) =
              (Polynomial.X : Polynomial ℤ) • totalComp X Y Z g f
            rw [graded_X_smul, graded_X_smul]
            exact totalComp_lambda_right X Y Z f g }
      map_zero' := by
        apply LinearMap.ext
        intro f
        exact congrArg (fun h : TotalWeightHom X Y →+ TotalWeightHom X Z => h f) (map_zero (totalComp X Y Z))
      map_add' := by
        intro g g'
        apply LinearMap.ext
        intro f
        exact congrArg (fun h : TotalWeightHom X Y →+ TotalWeightHom X Z => h f) ((totalComp X Y Z).map_add g g') }
  exact
    { toFun := F
      map_add' := F.map_add
      map_smul' := by
        intro p g
        apply additive_polynomial_smul F (fun g => ?_) p g
        apply LinearMap.ext
        intro f
        change totalComp X Y Z ((Polynomial.X : Polynomial ℤ) • g) f =
          (Polynomial.X : Polynomial ℤ) • totalComp X Y Z g f
        rw [graded_X_smul, graded_X_smul]
        exact totalComp_lambda_left X Y Z f g }

/-- The extension agrees with actual composition on homogeneous maps. -/
public theorem graded_compose_homogeneous : ∀ (X Y Z : SyntheticSpectrum) (a b : ℤ)
      (f : WeightHom X Y a) (g : WeightHom Y Z b),
    graded_compose X Y Z (weightHomInclusion b g) (weightHomInclusion a f) =
      weightHomInclusion (a+b) (weightHomComp f g) := by
  intro X Y Z a b f g
  exact totalComp_of X Y Z a b f g

public def gradedEnrichment : GradedLambdaEnrichment SyntheticSpectrum where
  coherence := graded_coherence
  shiftAdditive := graded_shiftAdditive
  module := graded_module
  lambda_smul := graded_lambda_smul
  compose := graded_compose
  compose_homogeneous := graded_compose_homogeneous

/-- The same shift construction supplies the actual filtered homotopy map,
finite-page comparison, and their common infinite-page representatives.
Its four fields use the same shift and compatibility comparisons. -/
private def essShiftConstruction (δ : ℤ × ℤ) :
    SyntheticESSShiftComparison background δ := by
  sorry

public def shift_filtered (δ : ℤ × ℤ) : ∀ (X : SyntheticObject) (p : ℤ × ℤ),
    FilteredPieceIso (background.convergence X).filtration
      (background.convergence (.shift δ X)).filtration p (p+δ) :=
  (essShiftConstruction δ).filtered


set_option backward.privateInPublic true in
private def weightMapImplementation : ∀ (X : AdamsObject) (s t w₁ w₂ : ℤ) (_hw : w₁ ≤ w₂) (_ht : w₂ ≤ t),
    ((background.family.obj (background.nu.functor.obj (X.obj background.auxiliary))).sequence.ssData (s,t,w₂)).eInfty ⟶
      ((background.family.obj (background.nu.functor.obj (X.obj background.auxiliary))).sequence.ssData (s,t,w₁)).eInfty := by
  intro X s t w₁ w₂ hw ht
  let k : ℕ := (w₂-w₁).toNat
  let δ : ℤ × ℤ := (0,-(k:ℤ))
  let p : ℤ × ℤ := (t-s,w₂)
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  have hk : w₂ - (k:ℤ) = w₁ := by
    dsimp only [k]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hw)]
    omega
  let sh := towerInfinityIso (background.convergence (.nu X))
    (background.convergence (.shift δ (.nu X))) (shift_filtered δ (.nu X) p) s
  have hsrc : (s,p.1+s,p.2) = (s,t,w₂) := by
    dsimp only [p]
    ext <;> simp
  have htgt : (s,(p+δ).1+s,(p+δ).2) = (s,t,w₁) := by
    dsimp only [p, δ, Prod.fst_add, Prod.snd_add]
    ext <;> simp_all only [add_zero, sub_add_cancel]
    omega
  let e : ((background.family.obj A).sequence.ssData (s,t,w₂)).eInfty ≅
      ((background.family.obj ((SyntheticCategory.biShift δ).obj A)).sequence.ssData (s,t,w₁)).eInfty :=
    eqToIso (congrArg (fun q => ((background.family.obj A).sequence.ssData q).eInfty) hsrc.symm) ≪≫
      sh ≪≫
        eqToIso (congrArg (fun q =>
          ((background.family.obj ((SyntheticCategory.biShift δ).obj A)).sequence.ssData q).eInfty) htgt)
  exact e.hom ≫ (background.family.map (lambdaPow k A)).eInftyMap (s,t,w₁)


set_option backward.privateInPublic true in
private def weightMapSourceEquality (F : Tridegree → ModuleCat ℤ)
    (s t w : ℤ) : F (s,t,w) = F (s,(t-s)+s,w) := by
  exact congrArg F (by ext <;> simp)

set_option backward.privateInPublic true in
private def weightMapTargetEquality (F : Tridegree → ModuleCat ℤ)
    (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) :
    let k : ℕ := (w₂-w₁).toNat
    let δ : ℤ × ℤ := (0,-(k:ℤ))
    let p : ℤ × ℤ := (t-s,w₂)
    F (s,(p+δ).1+s,(p+δ).2) = F (s,t,w₁) := by
  dsimp only
  apply congrArg F
  have hk : w₂ - (((w₂-w₁).toNat : ℕ) : ℤ) = w₁ := by
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hw)]
    omega
  ext <;> simp_all only [Prod.fst_add, Prod.snd_add, add_zero, sub_add_cancel]
  omega

set_option backward.privateInPublic true in
/-- Actual weight lowering: shift the fixed filtered homotopy, then apply the same λ power. -/
public def weight_map : ∀ (X : AdamsObject) (s t w₁ w₂ : ℤ) (_hw : w₁ ≤ w₂) (_ht : w₂ ≤ t),
    ((background.family.obj (background.nu.functor.obj (X.obj background.auxiliary))).sequence.ssData (s,t,w₂)).eInfty ⟶
      ((background.family.obj (background.nu.functor.obj (X.obj background.auxiliary))).sequence.ssData (s,t,w₁)).eInfty := by
  intro X s t w₁ w₂ hw ht
  let k : ℕ := (w₂-w₁).toNat
  let δ : ℤ × ℤ := (0,-(k:ℤ))
  let p : ℤ × ℤ := (t-s,w₂)
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let F : Tridegree → ModuleCat ℤ := fun q => ((background.family.obj A).sequence.ssData q).eInfty
  let G : Tridegree → ModuleCat ℤ := fun q =>
    ((background.family.obj ((SyntheticCategory.biShift δ).obj A)).sequence.ssData q).eInfty
  let sh := towerInfinityIso (background.convergence (.nu X))
    (background.convergence (.shift δ (.nu X))) (shift_filtered δ (.nu X) p) s
  let e : ((background.family.obj A).sequence.ssData (s,t,w₂)).eInfty ≅
      ((background.family.obj ((SyntheticCategory.biShift δ).obj A)).sequence.ssData (s,t,w₁)).eInfty :=
    eqToIso (weightMapSourceEquality F s t w₂) ≪≫ sh ≪≫
      eqToIso (weightMapTargetEquality G s t w₁ w₂ hw)
  exact e.hom ≫ (background.family.map (lambdaPow k A)).eInftyMap (s,t,w₁)

/-- Compatibility of weight maps with infinity representatives. -/
public theorem weight_representative : ∀ (X : AdamsObject) (s t w₁ w₂ : ℤ)
      (hw : w₁ ≤ w₂) (ht : w₂ ≤ t)
      (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
      (z : ((background.family.obj (background.nu.functor.obj (X.obj background.auxiliary))).sequence.ssData (s,t,w₂)).eInfty),
    HasInfinityRepresentative _ 2 (s,t,w₂) (nuWeightLabel background X s t w₂ ht x) z →
      HasInfinityRepresentative _ 2 (s,t,w₁) (nuWeightLabel background X s t w₁ (hw.trans ht) x)
        (weight_map X s t w₁ w₂ hw ht z) := by sorry

private def weightRawPageIso
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Tridegree}
    (e : E ≅ F) (r : ℤ) (p : Tridegree) : E.Page r p ≅ F.Page r p where
  hom := e.hom.pageMap r p
  inv := e.inv.pageMap r p
  hom_inv_id := by
    rw [← SpectralSequenceMorphism.pageMap_comp, e.hom_inv_id,
      SpectralSequenceMorphism.pageMap_id]
  inv_hom_id := by
    rw [← SpectralSequenceMorphism.pageMap_comp, e.inv_hom_id,
      SpectralSequenceMorphism.pageMap_id]

private theorem weightLabelBijective (X : AdamsObject) (s t w : ℤ) (hw : w ≤ t) :
    Function.Bijective (nuWeightLabel background X s t w hw) := by
  let zeroIso := SyntheticCategory.biShift_zero.app
    (background.nu.functor.obj (X.obj background.auxiliary))
  let zeroPage := weightRawPageIso (background.family.functor.mapIso zeroIso) 2
    (s,t,t-(t-w).toNat)
  have hzero : Function.Bijective zeroPage.hom := ConcreteCategory.bijective_of_isIso _
  change Function.Bijective (fun x => nuWeightLabel background X s t w hw x)
  dsimp only [nuWeightLabel, regradeE2, targetNuLabel]
  apply Function.Bijective.comp
  · exact ConcreteCategory.bijective_of_isIso _
  · apply Function.Bijective.comp
    · exact hzero
    · change Function.Bijective
        ((fun z : (background.family.obj ((SyntheticCategory.biShift (0,0)).obj
            (background.nu.functor.obj (X.obj background.auxiliary)))).E₂
              (s,t,t+0-(t-w).toNat) =>
          Eq.mp (by simp only [add_zero]) z) ∘
            (background.comparison.nuE2 X 0 s t (t-w).toNat))
      exact (Equiv.cast _).bijective.comp
        (background.comparison.nuE2 X 0 s t (t-w).toNat).bijective

private theorem infinityHasWeightLabel (X : AdamsObject) (s t w : ℤ) (hw : w ≤ t)
    (z : ((background.family.obj (background.nu.functor.obj (X.obj background.auxiliary))).sequence.ssData
      (s,t,w)).eInfty) :
    ∃ x, HasInfinityRepresentative _ 2 (s,t,w) (nuWeightLabel background X s t w hw x) z := by
  let A := background.family.obj (background.nu.functor.obj (X.obj background.auxiliary))
  haveI : Epi ((A.sequence.ssData (s,t,w)).pageπ ⊤) :=
    inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective
    ((A.sequence.ssData (s,t,w)).pageπ ⊤)).mp inferInstance z
  obtain ⟨x, hx⟩ := (weightLabelBijective X s t w hw).surjective
    ((Subobject.ofLE _ _ ((A.sequence.ssData (s,t,w)).Z_anti le_top) ≫
      (A.sequence.ssData (s,t,w)).pageπ
        (↑(2-A.sequence.r₀).toNat : WithTop ℕ)) a)
  exact ⟨x, by omega, a, hx.symm, ha⟩

private theorem familyPageMapCast
    {U V : SyntheticSpectrum} (g : U ⟶ V) {p q : Tridegree} (h : p = q)
    (x : (background.family.obj U).E₂ p) :
    background.family.pageMap g 2 q
      (Eq.mp (congrArg (fun a : Tridegree => ((background.family.obj U).E₂ a : Type)) h) x) =
      Eq.mp (congrArg (fun a : Tridegree => ((background.family.obj V).E₂ a : Type)) h)
        (background.family.pageMap g 2 p x) := by
  subst q
  rfl

private theorem targetNuLabelNatural
    (X Y : AdamsObject) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t : ℤ) (k : ℕ) (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :
    background.family.pageMap (background.nu.functor.map f) 2 (s,t,t-k)
      (targetNuLabel background X s t k x) =
    targetNuLabel background Y s t k ((background.classical.map f).pageMap 2 (s,t) x) := by
  let p : Tridegree := (s,t,t-k)
  let nuf := background.nu.functor.map f
  let x₀ : (background.family.obj ((SyntheticCategory.biShift (0,0)).obj
      (background.nu.functor.obj (X.obj background.auxiliary)))).E₂ p := by
    simpa only [add_zero] using background.comparison.nuE2 X 0 s t k x
  let y₀ : (background.family.obj ((SyntheticCategory.biShift (0,0)).obj
      (background.nu.functor.obj (Y.obj background.auxiliary)))).E₂ p := by
    simpa only [add_zero] using background.comparison.nuE2 Y 0 s t k
      ((background.classical.map f).pageMap 2 (s,t) x)
  have hxy : background.family.pageMap ((SyntheticCategory.biShift (0,0)).map nuf) 2 p x₀ = y₀ := by
    have hdeg : (s,t,t+0-(k : ℤ)) = p := by dsimp [p]; simp only [add_zero]
    have hraw := background.comparison.nu_natural X Y f 0 s t k x
    have hc := familyPageMapCast ((SyntheticCategory.biShift (0,0)).map nuf) hdeg
      (background.comparison.nuE2 X 0 s t k x)
    exact hc.trans (congrArg
      (fun z => Eq.mp (congrArg (fun a : Tridegree =>
        ((background.family.obj ((SyntheticCategory.biShift (0,0)).obj
          (background.nu.functor.obj (Y.obj background.auxiliary)))).E₂ a : Type)) hdeg) z) hraw)
  let zx := SyntheticCategory.biShift_zero.hom.app
    (background.nu.functor.obj (X.obj background.auxiliary))
  let zy := SyntheticCategory.biShift_zero.hom.app
    (background.nu.functor.obj (Y.obj background.auxiliary))
  have hn : (SyntheticCategory.biShift (0,0)).map nuf ≫ zy = zx ≫ nuf :=
    SyntheticCategory.biShift_zero.hom.naturality nuf
  change background.family.pageMap nuf 2 p (background.family.pageMap zx 2 p x₀) =
    background.family.pageMap zy 2 p y₀
  calc
    _ = background.family.pageMap (zx ≫ nuf) 2 p x₀ :=
      (ConcreteCategory.congr_hom (familyPageMap_comp background.family zx nuf 2 p) x₀).symm
    _ = background.family.pageMap ((SyntheticCategory.biShift (0,0)).map nuf ≫ zy) 2 p x₀ :=
      congrArg (fun g => background.family.pageMap g 2 p x₀) hn.symm
    _ = background.family.pageMap zy 2 p
        (background.family.pageMap ((SyntheticCategory.biShift (0,0)).map nuf) 2 p x₀) :=
      ConcreteCategory.congr_hom
        (familyPageMap_comp background.family ((SyntheticCategory.biShift (0,0)).map nuf) zy 2 p) x₀
    _ = _ := congrArg (background.family.pageMap zy 2 p) hxy

private theorem familyPageMapRegrade
    {U V : SyntheticSpectrum} (g : U ⟶ V) {p q : Tridegree} (h : p = q)
    (x : (background.family.obj U).E₂ p) :
    background.family.pageMap g 2 q (regradeE2 h x) =
      regradeE2 h (background.family.pageMap g 2 p x) := by
  subst q
  rfl

private theorem weightLabelNatural
    (X Y : AdamsObject) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t w : ℤ) (hw : w ≤ t)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :
    background.family.pageMap (background.nu.functor.map f) 2 (s,t,w)
      (nuWeightLabel background X s t w hw x) =
    nuWeightLabel background Y s t w hw ((background.classical.map f).pageMap 2 (s,t) x) := by
  unfold nuWeightLabel
  rw [familyPageMapRegrade, targetNuLabelNatural]

/-- The fixed weight maps preserve identities. -/
public theorem weight_map_self : ∀ (X : AdamsObject) (s t w : ℤ) (hw : w ≤ t),
    weight_map X s t w w le_rfl hw = 𝟙 _ := by
  intro X s t w hw
  ext z
  obtain ⟨x, hx⟩ := infinityHasWeightLabel X s t w hw z
  have hm := weight_representative X s t w w le_rfl hw x z hx
  exact HasInfinityRepresentative.unique hm hx


/-- The fixed weight maps compose along increasing weights. -/
public theorem weight_map_comp : ∀ (X : AdamsObject) (s t w₁ w₂ w₃ : ℤ)
      (h₁₂ : w₁ ≤ w₂) (h₂₃ : w₂ ≤ w₃) (h₃ : w₃ ≤ t),
    weight_map X s t w₂ w₃ h₂₃ h₃ ≫ weight_map X s t w₁ w₂ h₁₂ (h₂₃.trans h₃) =
      weight_map X s t w₁ w₃ (h₁₂.trans h₂₃) h₃ := by
  intro X s t w₁ w₂ w₃ h₁₂ h₂₃ h₃
  ext z
  obtain ⟨x, hx⟩ := infinityHasWeightLabel X s t w₃ h₃ z
  have h₂ := weight_representative X s t w₂ w₃ h₂₃ h₃ x z hx
  have h₁ := weight_representative X s t w₁ w₂ h₁₂ (h₂₃.trans h₃) x _ h₂
  have h₁' := weight_representative X s t w₁ w₃ (h₁₂.trans h₂₃) h₃ x z hx
  exact HasInfinityRepresentative.unique h₁ h₁'


/-- The fixed weight maps commute with maps induced by nu. -/
public theorem weight_naturality : ∀ (X Y : AdamsObject) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
      (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t),
    (background.family.map (background.nu.functor.map f)).eInftyMap (s,t,w₂) ≫ weight_map Y s t w₁ w₂ hw ht =
      weight_map X s t w₁ w₂ hw ht ≫ (background.family.map (background.nu.functor.map f)).eInftyMap (s,t,w₁) := by
  intro X Y f s t w₁ w₂ hw ht
  ext z
  obtain ⟨x, hx⟩ := infinityHasWeightLabel X s t w₂ ht z
  have hy := infinity_rep_map (background.nu.functor.map f) (s,t,w₂) hx
  rw [weightLabelNatural] at hy
  have hleft := weight_representative Y s t w₁ w₂ hw ht
    ((background.classical.map f).pageMap 2 (s,t) x) _ hy
  have hlow := weight_representative X s t w₁ w₂ hw ht x z hx
  have hright := infinity_rep_map (background.nu.functor.map f) (s,t,w₁) hlow
  rw [weightLabelNatural] at hright
  exact HasInfinityRepresentative.unique hleft hright


public def weightMaps : NuInfinityWeightMaps background where
  map := weight_map
  map_self := weight_map_self
  map_comp := weight_map_comp
  naturality := weight_naturality
  representative := weight_representative


public theorem shift_ambient_eq (δ : ℤ × ℤ) : ∀ (X : SyntheticObject) (p : ℤ × ℤ)
      (a : BiHom p.1 p.2 (X.obj background.nu background.auxiliary)),
    ((shift_filtered δ) X p).ambient.hom a = shiftHomotopyClass δ p a :=
  (essShiftConstruction δ).ambient_eq

public def shift_page (δ : ℤ × ℤ) : ∀ (X : SyntheticObject) (r : ℤ) (_hr : 2 ≤ r) (p : ℤ × ℤ) (s : ℤ),
    (background.family.obj (X.obj background.nu background.auxiliary)).Page r (s,p.1+s,p.2) ≅
      (background.family.obj ((SyntheticObject.shift δ X).obj background.nu background.auxiliary)).Page r
        (s,(p+δ).1+s,(p+δ).2) :=
  (essShiftConstruction δ).page

public theorem shift_representative_iff (δ : ℤ × ℤ) : ∀ (X : SyntheticObject) (r : ℤ) (hr : 2 ≤ r)
      (p : ℤ × ℤ) (s : ℤ)
      (x : (background.family.obj (X.obj background.nu background.auxiliary)).Page r (s,p.1+s,p.2))
      (z : ((background.family.obj (X.obj background.nu background.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty),
    HasInfinityRepresentative _ r (s,p.1+s,p.2) x z ↔
      HasInfinityRepresentative _ r (s,(p+δ).1+s,(p+δ).2)
        (((shift_page δ) X r hr p s).hom x)
        ((towerInfinityIso (background.convergence X) (background.convergence (.shift δ X))
          ((shift_filtered δ) X p) s).hom z) :=
  (essShiftConstruction δ).representative_iff

public def essShift (δ : ℤ × ℤ) : SyntheticESSShiftComparison background δ :=
  essShiftConstruction δ

public def essShiftSystem : SyntheticAdamsESSShiftSystem background := ⟨fun n => essShift (1,-(n:ℤ))⟩


/-- The fixed mapping-sphere multiplication is the already selected sphere E₂ product. -/
public theorem mapping_sphere_product (p q : ℤ × ℤ)
    (x : (mappingSystem.hom ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
      ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩).underlying.E.Page 2 p)
    (y : (mappingSystem.hom ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
      ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩).underlying.E.Page 2 q) :
    (sphereMappingAdamsIso closedBackground classical).hom.pageMap 2 (p + q)
      ((mapping_pairing ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
        ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
        ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩).ssPairing.pair 2 p q x y) =
      sphereAlgebra.product p q
        ((sphereMappingAdamsIso closedBackground classical).hom.pageMap 2 p x)
        ((sphereMappingAdamsIso closedBackground classical).hom.pageMap 2 q y) :=
  mapping_sphere_product_compat p q x y

public theorem mapping_sphere_unit :
    (sphereMappingAdamsIso closedBackground classical).hom.pageMap 2 (0,0)
      ((mapping_identity ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩).page 2) =
        sphereAlgebra.unit := by
  let S : FiniteSpectrum := ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
  let e := sphereMappingAdamsIso closedBackground classical
  let u := e.inv.pageMap 2 (0,0) sphereAlgebra.unit
  have hu : e.hom.pageMap 2 (0,0) u = sphereAlgebra.unit := by
    have h := congrArg (fun f => f sphereAlgebra.unit)
      (congrArg (fun f => f.pageMap 2 (0,0)) e.inv_hom_id)
    simpa only [SpectralSequenceMorphism.pageMap_comp,
      SpectralSequenceMorphism.pageMap_id, ModuleCat.comp_apply,
      ModuleCat.id_apply] using h
  have h := mapping_sphere_product (0,0) (0,0) ((mapping_identity S).page 2) u
  have hleft := eq_of_heq (mapping_page_left_unital S S 2 (0,0) u)
  rw [hleft] at h
  change e.hom.pageMap 2 (0,0) u = sphereAlgebra.product (0,0) (0,0)
    (e.hom.pageMap 2 (0,0) ((mapping_identity S).page 2))
    (e.hom.pageMap 2 (0,0) u) at h
  rw [hu] at h
  exact (eq_of_heq (sphereAlgebra.unit_right (0,0)
    (e.hom.pageMap 2 (0,0) ((mapping_identity S).page 2)))).symm.trans h.symm

public theorem graded_associative (W X Y Z : SyntheticSpectrum)
    (f : TotalWeightHom W X) (g : TotalWeightHom X Y) (h : TotalWeightHom Y Z) :
    graded_compose W Y Z h (graded_compose W X Y g f) =
      graded_compose W X Z (graded_compose X Y Z h g) f :=
  gradedEnrichment.assoc W X Y Z f g h

public theorem graded_left_unit (X Y : SyntheticSpectrum) (f : TotalWeightHom X Y) :
    graded_compose X Y Y
      (weightHomInclusion 0 (SyntheticCategory.biShift_zero.hom.app Y)) f = f :=
  gradedEnrichment.left_unit X Y f

public theorem graded_right_unit (X Y : SyntheticSpectrum) (f : TotalWeightHom X Y) :
    graded_compose X X Y f
      (weightHomInclusion 0 (SyntheticCategory.biShift_zero.hom.app X)) = f :=
  gradedEnrichment.right_unit X Y f

end
end KIP126.AdamsSynthetic.Completed
