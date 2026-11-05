module

public import KIP126.AdamsSynthetic.ModelFoundation.Cofiber
public import Mathlib.CategoryTheory.Localization.Predicate

/-! Homotopy invariance of the point-set cofiber. The pushout construction is
used only after cofibrant arrow replacement. Brown factorization on cofibrant
arrows supplies invariance without a left properness hypothesis. -/

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomotopicalAlgebra
universe u v w z
variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The relative target of a square, before imposing its target relation. -/
noncomputable def relativeTargetMap {f g : Arrow C} (φ : f ⟶ g) :
    pushout f.hom φ.left ⟶ g.right :=
  pushout.desc φ.right g.hom φ.w.symm

@[reassoc (attr := simp)] lemma relativeTargetMap_inl {f g : Arrow C} (φ : f ⟶ g) :
    pushout.inl f.hom φ.left ≫ relativeTargetMap φ = φ.right := by
  simp [relativeTargetMap]

@[reassoc (attr := simp)] lemma relativeTargetMap_inr {f g : Arrow C} (φ : f ⟶ g) :
    pushout.inr f.hom φ.left ≫ relativeTargetMap φ = g.hom := by
  simp [relativeTargetMap]

private noncomputable def coprodRelativeLeft {A B A' B' M : C}
    (f : A ⟶ B) (g : A' ⟶ B') (a : A ⨿ A' ⟶ M) :
    pushout f (coprod.inl ≫ a) ⟶ pushout (coprod.map f g) a :=
  pushout.desc (coprod.inl ≫ pushout.inl _ _) (pushout.inr _ _) (by
    have h := congrArg (fun k => coprod.inl ≫ k) (pushout.condition (f := coprod.map f g) (g := a))
    simpa using h)

@[reassoc (attr := simp)] private lemma coprodRelativeLeft_inl {A B A' B' M : C}
    (f : A ⟶ B) (g : A' ⟶ B') (a : A ⨿ A' ⟶ M) :
    pushout.inl f (coprod.inl ≫ a) ≫ coprodRelativeLeft f g a =
      coprod.inl ≫ pushout.inl _ _ := by simp [coprodRelativeLeft]
@[reassoc (attr := simp)] private lemma coprodRelativeLeft_inr {A B A' B' M : C}
    (f : A ⟶ B) (g : A' ⟶ B') (a : A ⨿ A' ⟶ M) :
    pushout.inr f (coprod.inl ≫ a) ≫ coprodRelativeLeft f g a =
      pushout.inr _ _ := by simp [coprodRelativeLeft]

private lemma coprodRelativeLeft_isPushout {A B A' B' M : C}
    (f : A ⟶ B) (g : A' ⟶ B') (a : A ⨿ A' ⟶ M) :
    IsPushout g (coprod.inr ≫ a ≫ pushout.inr f (coprod.inl ≫ a))
      (coprod.inr ≫ pushout.inl (coprod.map f g) a) (coprodRelativeLeft f g a) := by
  apply IsPushout.mk'
  · have h := congrArg (fun k => coprod.inr ≫ k)
      (pushout.condition (f := coprod.map f g) (g := a))
    simpa [Category.assoc] using h
  · intro T φ ψ h₁ h₂
    apply pushout.hom_ext
    · apply coprod.hom_ext
      · have h := congrArg (fun k => pushout.inl f (coprod.inl ≫ a) ≫ k) h₂
        simpa [Category.assoc] using h
      · simpa [Category.assoc] using h₁
    · have h := congrArg (fun k => pushout.inr f (coprod.inl ≫ a) ≫ k) h₂
      simpa [Category.assoc] using h
  · intro T b l h
    refine ⟨pushout.desc (coprod.desc (pushout.inl f (coprod.inl ≫ a) ≫ l) b)
      (pushout.inr f (coprod.inl ≫ a) ≫ l) ?_, ?_, ?_⟩
    · apply coprod.hom_ext
      · simp only [coprod.inl_map_assoc, coprod.inl_desc]
        rw [← Category.assoc, pushout.condition]
        simp [Category.assoc]
      · simpa [Category.assoc] using h
    · simp
    · apply pushout.hom_ext <;> simp [Category.assoc, coprodRelativeLeft]

private lemma coprodRelativeLeft_cofibration {A B A' B' M : C}
    (f : A ⟶ B) (g : A' ⟶ B') (a : A ⨿ A' ⟶ M) [Cofibration g] :
    Cofibration (coprodRelativeLeft f g a) := by
  rw [cofibration_iff]
  exact MorphismProperty.of_isPushout (coprodRelativeLeft_isPushout f g a).flip
    (mem_cofibrations g)

private noncomputable def coprodRelativeRight {A B A' B' M : C}
    (f : A ⟶ B) (g : A' ⟶ B') (a : A ⨿ A' ⟶ M) :
    pushout g (coprod.inr ≫ a) ⟶ pushout (coprod.map f g) a :=
  pushout.desc (coprod.inr ≫ pushout.inl _ _) (pushout.inr _ _) (by
    have h := congrArg (fun k => coprod.inr ≫ k) (pushout.condition (f := coprod.map f g) (g := a))
    simpa using h)

@[reassoc (attr := simp)] private lemma coprodRelativeRight_inl {A B A' B' M : C}
    (f : A ⟶ B) (g : A' ⟶ B') (a : A ⨿ A' ⟶ M) :
    pushout.inl g (coprod.inr ≫ a) ≫ coprodRelativeRight f g a =
      coprod.inr ≫ pushout.inl _ _ := by simp [coprodRelativeRight]
@[reassoc (attr := simp)] private lemma coprodRelativeRight_inr {A B A' B' M : C}
    (f : A ⟶ B) (g : A' ⟶ B') (a : A ⨿ A' ⟶ M) :
    pushout.inr g (coprod.inr ≫ a) ≫ coprodRelativeRight f g a =
      pushout.inr _ _ := by simp [coprodRelativeRight]

private lemma coprodRelativeRight_isPushout {A B A' B' M : C}
    (f : A ⟶ B) (g : A' ⟶ B') (a : A ⨿ A' ⟶ M) :
    IsPushout f (coprod.inl ≫ a ≫ pushout.inr g (coprod.inr ≫ a))
      (coprod.inl ≫ pushout.inl (coprod.map f g) a) (coprodRelativeRight f g a) := by
  apply IsPushout.mk'
  · have h := congrArg (fun k => coprod.inl ≫ k)
      (pushout.condition (f := coprod.map f g) (g := a))
    simpa [Category.assoc] using h
  · intro T φ ψ h₁ h₂
    apply pushout.hom_ext
    · apply coprod.hom_ext
      · simpa [Category.assoc] using h₁
      · have h := congrArg (fun k => pushout.inl g (coprod.inr ≫ a) ≫ k) h₂
        simpa [Category.assoc] using h
    · have h := congrArg (fun k => pushout.inr g (coprod.inr ≫ a) ≫ k) h₂
      simpa [Category.assoc] using h
  · intro T b l h
    refine ⟨pushout.desc (coprod.desc b (pushout.inl g (coprod.inr ≫ a) ≫ l))
      (pushout.inr g (coprod.inr ≫ a) ≫ l) ?_, ?_, ?_⟩
    · apply coprod.hom_ext
      · simpa [Category.assoc] using h
      · simp only [coprod.inr_map_assoc, coprod.inr_desc]
        rw [← Category.assoc, pushout.condition]
        simp [Category.assoc]
    · simp
    · apply pushout.hom_ext <;> simp [Category.assoc, coprodRelativeRight]

private lemma coprodRelativeRight_cofibration {A B A' B' M : C}
    (f : A ⟶ B) (g : A' ⟶ B') (a : A ⨿ A' ⟶ M) [Cofibration f] :
    Cofibration (coprodRelativeRight f g a) := by
  rw [cofibration_iff]
  exact MorphismProperty.of_isPushout (coprodRelativeRight_isPushout f g a).flip
    (mem_cofibrations f)

private theorem reedyBrownExists {f g : Arrow C} (φ : f ⟶ g)
    [IsCofibrant f.left] [IsCofibrant g.left]
    [Cofibration f.hom] [Cofibration g.hom] :
    ∃ (h : Arrow C) (i : f ⟶ h) (p : h ⟶ g) (s : g ⟶ h),
      i ≫ p = φ ∧ s ≫ p = 𝟙 g ∧
      weakEquivalences C p.left ∧ weakEquivalences C p.right ∧
      Cofibration i.left ∧ Cofibration s.left ∧
      Cofibration (relativeTargetMap i) ∧ Cofibration (relativeTargetMap s) := by
  let A := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C)
    (coprod.desc φ.left (𝟙 g.left))
  let z : pushout (coprod.map f.hom g.hom) A.i ⟶ g.right :=
    pushout.desc (coprod.desc φ.right (𝟙 g.right)) (A.p ≫ g.hom) (by
      apply coprod.hom_ext
      · simpa only [Category.assoc, coprod.inl_map_assoc, coprod.inl_desc,
          A.fac_assoc, coprod.inl_desc_assoc] using φ.w.symm
      · simp)
  let B := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C) z
  let h : Arrow C := Arrow.mk (pushout.inr (coprod.map f.hom g.hom) A.i ≫ B.i)
  let i : f ⟶ h := Arrow.homMk (coprod.inl ≫ A.i) (coprod.inl ≫ pushout.inl _ _ ≫ B.i) (by
    have hh := congrArg (fun k => coprod.inl ≫ k)
      (pushout.condition (f := coprod.map f.hom g.hom) (g := A.i))
    simpa [Category.assoc, h] using (congrArg (fun k => k ≫ B.i) hh).symm)
  let s : g ⟶ h := Arrow.homMk (coprod.inr ≫ A.i) (coprod.inr ≫ pushout.inl _ _ ≫ B.i) (by
    have hh := congrArg (fun k => coprod.inr ≫ k)
      (pushout.condition (f := coprod.map f.hom g.hom) (g := A.i))
    simpa [Category.assoc, h] using (congrArg (fun k => k ≫ B.i) hh).symm)
  let p : h ⟶ g := Arrow.homMk A.p B.p (by simp [h, z, Category.assoc])
  have hi : relativeTargetMap i = coprodRelativeLeft f.hom g.hom A.i ≫ B.i := by
    apply pushout.hom_ext <;> simp [relativeTargetMap, i, h, Category.assoc, coprodRelativeLeft]
  have hs : relativeTargetMap s = coprodRelativeRight f.hom g.hom A.i ≫ B.i := by
    apply pushout.hom_ext <;> simp [relativeTargetMap, s, h, Category.assoc, coprodRelativeRight]
  letI : Cofibration A.i := (cofibration_iff _).2 A.hi
  letI : Cofibration B.i := (cofibration_iff _).2 B.hi
  letI : Cofibration (coprodRelativeLeft f.hom g.hom A.i) :=
    coprodRelativeLeft_cofibration _ _ _
  letI : Cofibration (coprodRelativeRight f.hom g.hom A.i) :=
    coprodRelativeRight_cofibration _ _ _
  refine ⟨h,i,p,s,?_,?_,A.hp.2,B.hp.2,?_,?_,?_,?_⟩
  · ext <;> simp [i,p,z,Category.assoc]
  · ext <;> simp [s,p,z,Category.assoc]
  · change Cofibration (coprod.inl ≫ A.i)
    infer_instance
  · change Cofibration (coprod.inr ≫ A.i)
    infer_instance
  · rw [hi]
    infer_instance
  · rw [hs]
    infer_instance


/-- Functorial cofibrant arrow replacement preserves levelwise weak equivalences.
This follows from its natural levelwise weak equivalence to the identity. -/
public theorem cofibrantArrowReplacement_weakEquivalences
    (G : CofibrantGeneration C) {f g : Arrow C} (φ : f ⟶ g)
    (hφ : (weakEquivalences C).arrow φ) :
    (weakEquivalences C).arrow (G.cofibrantArrowReplacement.map φ) := by
  haveI : WeakEquivalence φ.left := (weakEquivalence_iff _).2 hφ.1
  haveI : WeakEquivalence φ.right := (weakEquivalence_iff _).2 hφ.2
  haveI : WeakEquivalence (G.cofibrantArrowComparison.app f).left :=
    (weakEquivalence_iff _).2 (G.cofibrantArrowComparison_weakEquivalences f).1
  haveI : WeakEquivalence (G.cofibrantArrowComparison.app f).right :=
    (weakEquivalence_iff _).2 (G.cofibrantArrowComparison_weakEquivalences f).2
  haveI : WeakEquivalence (G.cofibrantArrowComparison.app g).left :=
    (weakEquivalence_iff _).2 (G.cofibrantArrowComparison_weakEquivalences g).1
  haveI : WeakEquivalence (G.cofibrantArrowComparison.app g).right :=
    (weakEquivalence_iff _).2 (G.cofibrantArrowComparison_weakEquivalences g).2
  constructor
  · apply (weakEquivalence_iff _).1
    have heq : (G.cofibrantArrowReplacement.map φ).left ≫
        (G.cofibrantArrowComparison.app g).left =
        (G.cofibrantArrowComparison.app f).left ≫ φ.left :=
      congrArg Arrow.Hom.left (G.cofibrantArrowComparison.naturality φ)
    exact weakEquivalence_of_postcomp_of_fac heq
  · apply (weakEquivalence_iff _).1
    have heq : (G.cofibrantArrowReplacement.map φ).right ≫
        (G.cofibrantArrowComparison.app g).right =
        (G.cofibrantArrowComparison.app f).right ≫ φ.right :=
      congrArg Arrow.Hom.right (G.cofibrantArrowComparison.naturality φ)
    exact weakEquivalence_of_postcomp_of_fac heq

variable [HasZeroMorphisms C] [HasZeroObject C]
attribute [local instance] HasZeroObject.zero'

noncomputable def rawCofiberFunctor : Arrow C ⥤ C where
  obj f := pushout f.hom (0 : f.left ⟶ (0 : C))
  map {f g} φ := pushout.map _ _ _ _ φ.right (𝟙 (0 : C)) φ.left φ.w.symm (by simp)
  map_id f := by
    apply pushout.hom_ext
    · simp
    · exact (isZero_zero C).eq_of_src _ _
  map_comp φ ψ := by
    apply pushout.hom_ext <;> simp [Category.assoc]

noncomputable def relativeCofiberMap {f g : Arrow C} (φ : f ⟶ g) :
    pushout f.hom φ.left ⟶ rawCofiberFunctor.obj f :=
  pushout.desc (pushout.inl _ _) 0 (by simp [pushout.condition])

lemma relativeCofiberMap_isPushout {f g : Arrow C} (φ : f ⟶ g) :
    IsPushout (relativeTargetMap φ) (relativeCofiberMap φ)
      (pushout.inl g.hom (0 : g.left ⟶ (0 : C)))
      (rawCofiberFunctor.map φ) := by
  have hz : pushout.inr g.hom (0 : g.left ⟶ (0 : C)) = 0 :=
    (isZero_zero C).eq_of_src _ _
  let z : g.left ⟶ (0 : C) := 0
  have top := IsPushout.of_hasPushout f.hom φ.left
  have whole : IsPushout f.hom (φ.left ≫ z)
      (pushout.inl f.hom (0 : f.left ⟶ (0 : C)))
      (pushout.inr f.hom (0 : f.left ⟶ (0 : C))) := by
    simpa [z] using IsPushout.of_hasPushout f.hom (0 : f.left ⟶ (0 : C))
  have bottom : IsPushout (pushout.inr f.hom φ.left) z
      (relativeCofiberMap φ) (pushout.inr f.hom (0 : f.left ⟶ (0 : C))) := by
    apply IsPushout.of_top (v₁₂ := pushout.inl f.hom φ.left)
      (v₂₂ := relativeCofiberMap φ) _ _ top
    · simpa [relativeCofiberMap] using whole
    · simp [relativeCofiberMap, z]
  have outer : IsPushout
      (pushout.inr f.hom φ.left ≫ relativeTargetMap φ) z
      (pushout.inl g.hom (0 : g.left ⟶ (0 : C)))
      (pushout.inr f.hom (0 : f.left ⟶ (0 : C)) ≫ rawCofiberFunctor.map φ) := by
    simpa [rawCofiberFunctor, z, hz] using
      IsPushout.of_hasPushout g.hom (0 : g.left ⟶ (0 : C))
  apply IsPushout.of_left outer _ bottom
  apply pushout.hom_ext <;> simp [relativeTargetMap, relativeCofiberMap,
    rawCofiberFunctor, pushout.condition]

/-- A levelwise weak equivalence which is a Reedy cofibration induces a
trivial cofibration on cofibers. -/
lemma rawCofiberFunctor_trivialCofibration {f g : Arrow C} (φ : f ⟶ g)
    [Cofibration φ.left] [WeakEquivalence φ.left] [WeakEquivalence φ.right]
    [Cofibration (relativeTargetMap φ)] :
    trivialCofibrations C (rawCofiberFunctor.map φ) := by
  have : WeakEquivalence (relativeTargetMap φ) :=
    weakEquivalence_of_precomp_of_fac (relativeTargetMap_inl φ)
  exact MorphismProperty.of_isPushout (relativeCofiberMap_isPushout φ).flip
    (mem_trivialCofibrations (relativeTargetMap φ))

lemma rawCofiberFunctor_weakEquivalence_of_brown
    {f g h : Arrow C} (φ : f ⟶ g) (i : f ⟶ h) (p : h ⟶ g) (s : g ⟶ h)
    (hi : i ≫ p = φ) (hs : s ≫ p = 𝟙 g)
    (hp : (weakEquivalences C).arrow p)
    [WeakEquivalence φ.left] [WeakEquivalence φ.right]
    [Cofibration i.left] [Cofibration s.left]
    [Cofibration (relativeTargetMap i)] [Cofibration (relativeTargetMap s)] :
    WeakEquivalence (rawCofiberFunctor.map φ) := by
  haveI : WeakEquivalence p.left := (weakEquivalence_iff _).2 hp.1
  haveI : WeakEquivalence p.right := (weakEquivalence_iff _).2 hp.2
  have hiL : i.left ≫ p.left = φ.left := congrArg Arrow.Hom.left hi
  have hiR : i.right ≫ p.right = φ.right := congrArg Arrow.Hom.right hi
  have hsL : s.left ≫ p.left = 𝟙 _ := congrArg Arrow.Hom.left hs
  have hsR : s.right ≫ p.right = 𝟙 _ := congrArg Arrow.Hom.right hs
  haveI : WeakEquivalence i.left := weakEquivalence_of_postcomp_of_fac hiL
  haveI : WeakEquivalence i.right := weakEquivalence_of_postcomp_of_fac hiR
  haveI : WeakEquivalence s.left := weakEquivalence_of_postcomp_of_fac hsL
  haveI : WeakEquivalence s.right := weakEquivalence_of_postcomp_of_fac hsR
  haveI : WeakEquivalence (rawCofiberFunctor.map i) :=
    (weakEquivalence_iff _).2 (rawCofiberFunctor_trivialCofibration i).2
  haveI : WeakEquivalence (rawCofiberFunctor.map s) :=
    (weakEquivalence_iff _).2 (rawCofiberFunctor_trivialCofibration s).2
  have hsp : rawCofiberFunctor.map s ≫ rawCofiberFunctor.map p =
      𝟙 (rawCofiberFunctor.obj g) := by
    rw [← rawCofiberFunctor.map_comp, hs, rawCofiberFunctor.map_id]
  haveI : WeakEquivalence (rawCofiberFunctor.map p) :=
    weakEquivalence_of_precomp_of_fac hsp
  rw [← hi, Functor.map_comp]
  infer_instance

/-- Cofibers preserve weak equivalences between cofibrant arrows by Reedy Brown
factorization. -/
lemma rawCofiberFunctor_weakEquivalence {f g : Arrow C} (φ : f ⟶ g)
    [IsCofibrant f.left] [IsCofibrant g.left]
    [Cofibration f.hom] [Cofibration g.hom]
    [WeakEquivalence φ.left] [WeakEquivalence φ.right] :
    WeakEquivalence (rawCofiberFunctor.map φ) := by
  obtain ⟨h, i, p, s, hi, hs, hpL, hpR, hiL, hsL, hiT, hsT⟩ := reedyBrownExists φ
  letI := hiL
  letI := hsL
  letI := hiT
  letI := hsT
  exact rawCofiberFunctor_weakEquivalence_of_brown φ i p s hi hs ⟨hpL, hpR⟩

/-- The derived point-set cofiber preserves every levelwise weak equivalence
of arrows. Cofibrancy is supplied by its constructed arrow replacement. -/
public theorem cofiberFunctor_weakEquivalences
    (G : CofibrantGeneration C) {f g : Arrow C} (φ : f ⟶ g)
    (hφ : (weakEquivalences C).arrow φ) :
    weakEquivalences C (G.cofiberFunctor.map φ) := by
  letI := G.cofibrantArrowReplacement_source f
  letI := G.cofibrantArrowReplacement_source g
  letI : Cofibration (G.cofibrantArrowReplacement.obj f).hom :=
    (cofibration_iff _).2 (G.cofibrantArrowReplacement_cofibration f)
  letI : Cofibration (G.cofibrantArrowReplacement.obj g).hom :=
    (cofibration_iff _).2 (G.cofibrantArrowReplacement_cofibration g)
  have hR := G.cofibrantArrowReplacement_weakEquivalences φ hφ
  letI : WeakEquivalence (G.cofibrantArrowReplacement.map φ).left :=
    (weakEquivalence_iff _).2 hR.1
  letI : WeakEquivalence (G.cofibrantArrowReplacement.map φ).right :=
    (weakEquivalence_iff _).2 hR.2
  exact (weakEquivalence_iff _).1
    (rawCofiberFunctor_weakEquivalence (G.cofibrantArrowReplacement.map φ))

variable (G : CofibrantGeneration C)
  {H : Type w} [Category.{z} H] (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)]

/-- After localization the point-set cofiber inverts the levelwise weak
 equivalences in the actual arrow category. -/
public theorem cofiberFunctor_inverts :
    (weakEquivalences C).arrow.IsInvertedBy (G.cofiberFunctor ⋙ L) := by
  intro f g φ hφ
  exact Localization.inverts L (weakEquivalences C) _
    (G.cofiberFunctor_weakEquivalences φ hφ)

/-- Cofiber is a functor on the localization of the point-set arrow category,
whose objects retain coherent arrow data. -/
public noncomputable def derivedCofiberFunctor :
    (weakEquivalences C).arrow.Localization ⥤ H :=
  Localization.lift (G.cofiberFunctor ⋙ L) (G.cofiberFunctor_inverts L)
    (weakEquivalences C).arrow.Q

/-- The derived functor agrees naturally with the actual point-set construction. -/
public noncomputable def derivedCofiberFunctorComparison :
    (weakEquivalences C).arrow.Q ⋙ G.derivedCofiberFunctor L ≅ G.cofiberFunctor ⋙ L :=
  Localization.fac (G.cofiberFunctor ⋙ L) (G.cofiberFunctor_inverts L)
    (weakEquivalences C).arrow.Q

public instance localizedCofibrantArrowComparison_right_isIso (f : Arrow C) :
    IsIso (L.map (G.cofibrantArrowComparison.app f).right) :=
  Localization.inverts L (weakEquivalences C) _
    (G.cofibrantArrowComparison_weakEquivalences f).2

/-- The inclusion of the original arrow target is natural after localization.
The inverse comparison is justified by the constructed trivial fibrations. -/
public noncomputable def localizedCofiberInclusion :
    Arrow.rightFunc ⋙ L ⟶ G.cofiberFunctor ⋙ L := by
  let τ : G.cofibrantArrowReplacement ⋙ Arrow.rightFunc ⋙ L ⟶ Arrow.rightFunc ⋙ L :=
    whiskerRight (whiskerRight G.cofibrantArrowComparison Arrow.rightFunc) L
  haveI (f : Arrow C) : IsIso (τ.app f) :=
    Localization.inverts L (weakEquivalences C) _
      (G.cofibrantArrowComparison_weakEquivalences f).2
  haveI : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact CategoryTheory.inv τ ≫ whiskerRight G.cofiberInclusion L

/-- The localized inclusion has the expected map on each arrow. -/
public theorem localizedCofiberInclusion_app (f : Arrow C) :
    (G.localizedCofiberInclusion L).app f =
      CategoryTheory.inv (L.map (G.cofibrantArrowComparison.app f).right) ≫
        L.map (G.cofiberInclusion.app f) := by
  simp [localizedCofiberInclusion, NatIso.isIso_inv_app]

/-- The source comparison is also inverted by localization. -/
public instance localizedCofibrantArrowComparison_left_isIso (f : Arrow C) :
    IsIso (L.map (G.cofibrantArrowComparison.app f).left) :=
  Localization.inverts L (weakEquivalences C) _
    (G.cofibrantArrowComparison_weakEquivalences f).1

/-- The original arrow followed by the localized inclusion is zero. -/
public theorem localizedCofiberInclusion_comp [HasZeroMorphisms H]
    [L.PreservesZeroMorphisms] (f : Arrow C) :
    L.map f.hom ≫ (G.localizedCofiberInclusion L).app f = 0 := by
  have hw : (G.cofibrantArrowComparison.app f).left ≫ f.hom =
      (G.cofibrantArrowReplacement.obj f).hom ≫
        (G.cofibrantArrowComparison.app f).right :=
    (G.cofibrantArrowComparison.app f).w
  apply (cancel_epi (L.map (G.cofibrantArrowComparison.app f).left)).1
  rw [localizedCofiberInclusion_app, comp_zero, ← Category.assoc, ← L.map_comp,
    hw, L.map_comp]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← L.map_comp, G.cofiberInclusion_comp, L.map_zero]

omit [HasZeroMorphisms C] [HasZeroObject C] in
/-- Evaluation at the target inverts levelwise weak equivalences. -/
public theorem arrowTarget_inverts :
    (weakEquivalences C).arrow.IsInvertedBy (Arrow.rightFunc ⋙ L) := by
  intro f g φ hφ
  exact Localization.inverts L (weakEquivalences C) _ hφ.2

/-- Evaluation at the target descends to the localization of actual arrows. -/
public noncomputable def derivedTargetFunctor :
    (weakEquivalences C).arrow.Localization ⥤ H :=
  Localization.lift (Arrow.rightFunc ⋙ L) (arrowTarget_inverts L)
    (weakEquivalences C).arrow.Q

/-- The cofiber inclusion descends naturally to the localization of actual
arrows, compatibly with the functor obtained from cofibrant replacement. -/
public noncomputable def derivedCofiberInclusion :
    derivedTargetFunctor L ⟶ G.derivedCofiberFunctor L := by
  letI : Localization.Lifting (weakEquivalences C).arrow.Q (weakEquivalences C).arrow
      (Arrow.rightFunc ⋙ L) (derivedTargetFunctor L) :=
    Localization.liftingLift _ (arrowTarget_inverts L) _
  letI : Localization.Lifting (weakEquivalences C).arrow.Q (weakEquivalences C).arrow
      (G.cofiberFunctor ⋙ L) (G.derivedCofiberFunctor L) :=
    Localization.liftingLift _ (G.cofiberFunctor_inverts L) _
  exact Localization.liftNatTrans (weakEquivalences C).arrow.Q (weakEquivalences C).arrow
    (Arrow.rightFunc ⋙ L) (G.cofiberFunctor ⋙ L)
    (derivedTargetFunctor L) (G.derivedCofiberFunctor L) (G.localizedCofiberInclusion L)

end KIP126.StableHomotopy.CofibrantGeneration
