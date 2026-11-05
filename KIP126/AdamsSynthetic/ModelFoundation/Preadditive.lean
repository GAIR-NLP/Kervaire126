module

public import KIP126.AdamsSynthetic.ModelFoundation.Suspension
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.OfBiproducts
import all KIP126.AdamsSynthetic.ModelFoundation.Cylinder
import all KIP126.AdamsSynthetic.ModelFoundation.LocalizedCoproducts

/-! Additivity from the actual suspension pinch. The construction first derives
coaddition and an inverse from the model cylinder, descends them along the
localization, and transports them across the actual suspension equivalence.
No additive structure on the target category is assumed. -/

@[expose] section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ModelNaturalCoaddition construction. -/
set_option backward.isDefEq.respectTransparency false
namespace ModelNaturalCoaddition
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryCoproducts C]

variable (Δ : ∀ X : C, X ⟶ X ⨿ X)
  (hnat : ∀ {X Y : C} (f : X ⟶ Y), f ≫ Δ Y = Δ X ≫ coprod.map f f)
  (hleft : ∀ X : C, Δ X ≫ coprod.desc (𝟙 X) 0 = 𝟙 X)
  (hright : ∀ X : C, Δ X ≫ coprod.desc 0 (𝟙 X) = 𝟙 X)

private def first (X Y : C) : X ⨿ Y ⟶ X := coprod.desc (𝟙 X) 0
private def second (X Y : C) : X ⨿ Y ⟶ Y := coprod.desc 0 (𝟙 Y)

private def pair {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⨿ Y :=
  Δ W ≫ coprod.map f g

include hleft in
private theorem pair_first {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y) :
    pair Δ f g ≫ first X Y = f := by
  have h : coprod.desc f (0 : W ⟶ X) = coprod.desc (𝟙 W) 0 ≫ f := by
    apply coprod.hom_ext <;> simp
  simp only [pair, first, Category.assoc, coprod.map_desc, Category.comp_id, comp_zero]
  rw [h, ← Category.assoc, hleft, Category.id_comp]

include hright in
private theorem pair_second {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y) :
    pair Δ f g ≫ second X Y = g := by
  have h : coprod.desc (0 : W ⟶ Y) g = coprod.desc 0 (𝟙 W) ≫ g := by
    apply coprod.hom_ext <;> simp
  simp only [pair, second, Category.assoc, coprod.map_desc, Category.comp_id, comp_zero]
  rw [h, ← Category.assoc, hright, Category.id_comp]

include hnat hleft hright in
private theorem pair_projections (X Y : C) :
    pair Δ (first X Y) (second X Y) = 𝟙 (X ⨿ Y) := by
  apply coprod.hom_ext
  · change coprod.inl ≫ (Δ (X ⨿ Y) ≫ coprod.map (first X Y) (second X Y)) = _
    rw [← Category.assoc, hnat, Category.assoc, coprod.map_map]
    simp only [first, second, coprod.inl_desc, Category.comp_id]
    have h : coprod.map (𝟙 X) (0 : X ⟶ Y) = coprod.desc (𝟙 X) 0 ≫
        (coprod.inl : X ⟶ X ⨿ Y) := by
      apply coprod.hom_ext <;> simp
    rw [h, ← Category.assoc, hleft, Category.id_comp]
  · change coprod.inr ≫ (Δ (X ⨿ Y) ≫ coprod.map (first X Y) (second X Y)) = _
    rw [← Category.assoc, hnat, Category.assoc, coprod.map_map]
    simp only [first, second, coprod.inr_desc, Category.comp_id]
    have h : coprod.map (0 : Y ⟶ X) (𝟙 Y) = coprod.desc 0 (𝟙 Y) ≫
        (coprod.inr : Y ⟶ X ⨿ Y) := by
      apply coprod.hom_ext <;> simp
    rw [h, ← Category.assoc, hright, Category.id_comp]

include hnat hleft hright in
private theorem pair_unique {W X Y : C} (m : W ⟶ X ⨿ Y) :
    m = pair Δ (m ≫ first X Y) (m ≫ second X Y) := by
  calc
    m = m ≫ pair Δ (first X Y) (second X Y) := by
      rw [pair_projections Δ hnat hleft hright, Category.comp_id]
    _ = pair Δ (m ≫ first X Y) (m ≫ second X Y) := by
      dsimp only [pair]
      rw [← Category.assoc, hnat, Category.assoc, coprod.map_map]

private def bicone (X Y : C) : BinaryBicone X Y where
  pt := X ⨿ Y
  fst := first X Y
  snd := second X Y
  inl := coprod.inl
  inr := coprod.inr
  inl_fst := by simp only [first, coprod.inl_desc]
  inl_snd := by simp only [second, coprod.inl_desc]
  inr_fst := by simp only [first, coprod.inr_desc]
  inr_snd := by simp only [second, coprod.inr_desc]

include hnat hleft hright in
private def biconeIsLimit (X Y : C) : IsLimit (bicone X Y).toCone := by
  refine BinaryFan.isLimitMk (fun s => pair Δ s.fst s.snd) ?_ ?_ ?_
  · intro s
    exact pair_first Δ hleft s.fst s.snd
  · intro s
    exact pair_second Δ hright s.fst s.snd
  · intro s m hf hg
    dsimp only [bicone] at m hf hg ⊢
    rw [pair_unique Δ hnat hleft hright m, hf, hg]

private def biconeIsColimit (X Y : C) : IsColimit (bicone X Y).toCocone := by
  refine BinaryCofan.isColimitMk (fun s => coprod.desc s.inl s.inr) ?_ ?_ ?_
  · intro s
    exact coprod.inl_desc _ _
  · intro s
    exact coprod.inr_desc _ _
  · intro s m hf hg
    apply coprod.hom_ext
    · simpa only [bicone, coprod.inl_desc] using hf
    · simpa only [bicone, coprod.inr_desc] using hg

include hnat hleft hright in
/-- Natural unital coaddition makes every given binary coproduct a biproduct. -/
private theorem hasBinaryBiproducts : HasBinaryBiproducts C where
  has_binary_biproduct X Y := HasBinaryBiproduct.mk
    ⟨bicone X Y, ⟨biconeIsLimit Δ hnat hleft hright X Y, biconeIsColimit X Y⟩⟩

section Semiadditive
variable [HasBinaryBiproducts C]
local instance homMonoid (X Y : C) : AddCommMonoid (X ⟶ Y) :=
  SemiadditiveOfBinaryBiproducts.addCommMonoidHomOfHasBinaryBiproducts X Y

include hleft hright in
private theorem add_eq_coaddition {X Y : C} (f g : X ⟶ Y) :
    f + g = Δ X ≫ coprod.desc f g := by
  let c : X ⨿ X ⟶ X ⊞ X := coprod.desc biprod.inl biprod.inr
  have hc : Δ X ≫ c = biprod.lift (𝟙 X) (𝟙 X) := by
    apply biprod.hom_ext
    · simpa only [c, Category.assoc, coprod.desc_comp, biprod.inl_fst,
        biprod.inr_fst, biprod.lift_fst] using hleft X
    · simpa only [c, Category.assoc, coprod.desc_comp, biprod.inl_snd,
        biprod.inr_snd, biprod.lift_snd] using hright X
  rw [SemiadditiveOfBinaryBiproducts.add_eq_right_addition, ← hc, Category.assoc]
  congr 1
  apply coprod.hom_ext <;> simp [c]

variable (reflection : ∀ X : C, X ⟶ X)
  (hreflection : ∀ X : C, Δ X ≫ coprod.desc (𝟙 X) (reflection X) = 0)

include hleft hright hreflection in
private theorem inverse_add {X Y : C} (f : X ⟶ Y) :
    (reflection X ≫ f) + f = 0 := by
  rw [add_comm, add_eq_coaddition Δ hleft hright]
  have h : coprod.desc f (reflection X ≫ f) =
      coprod.desc (𝟙 X) (reflection X) ≫ f := by
    apply coprod.hom_ext <;> simp
  rw [h, ← Category.assoc, hreflection X, zero_comp]

@[implicit_reducible]
private def homGroup (X Y : C) : AddCommGroup (X ⟶ Y) := by
  letI : Neg (X ⟶ Y) := ⟨fun f => reflection X ≫ f⟩
  exact { homMonoid X Y with
    neg := Neg.neg
    neg_add_cancel := inverse_add Δ hleft hright reflection hreflection
    zsmul := zsmulRec }

/-- The hom groups retain precisely mathlib's biproduct addition. -/
@[implicit_reducible]
private def preadditiveFromBiproducts : Preadditive C where
  homGroup := homGroup Δ hleft hright reflection hreflection
  add_comp _ _ _ f g h := SemiadditiveOfBinaryBiproducts.add_comp f g h
  comp_add _ _ _ f g h := SemiadditiveOfBinaryBiproducts.comp_add f g h
end Semiadditive

/-- Natural coaddition with two counits and an objectwise right inverse
constructs preadditivity. No additive, group or triangulated input is used. -/
@[implicit_reducible]
private def preadditive (reflection : ∀ X : C, X ⟶ X)
    (hreflection : ∀ X : C, Δ X ≫ coprod.desc (𝟙 X) (reflection X) = 0) :
    Preadditive C := by
  letI := hasBinaryBiproducts Δ hnat hleft hright
  exact preadditiveFromBiproducts Δ hleft hright reflection hreflection

/-- The constructed addition is the specified coaddition, with no change
of the chosen binary coproducts or underlying morphisms. -/
private theorem preadditive_add_eq (reflection : ∀ X : C, X ⟶ X)
    (hreflection : ∀ X : C, Δ X ≫ coprod.desc (𝟙 X) (reflection X) = 0)
    {X Y : C} (f g : X ⟶ Y) :
    letI := preadditive Δ hnat hleft hright reflection hreflection;
    f + g = Δ X ≫ coprod.desc f g := by
  letI := hasBinaryBiproducts Δ hnat hleft hright
  exact add_eq_coaddition Δ hleft hright f g

/-- Negation is induced by the specified source reflection. -/
private theorem preadditive_neg_eq (reflection : ∀ X : C, X ⟶ X)
    (hreflection : ∀ X : C, Δ X ≫ coprod.desc (𝟙 X) (reflection X) = 0)
    {X Y : C} (f : X ⟶ Y) :
    letI := preadditive Δ hnat hleft hright reflection hreflection;
    -f = reflection X ≫ f := by rfl

end ModelNaturalCoaddition

/-! ModelCoadditionTransport construction. -/
set_option backward.isDefEq.respectTransparency false
namespace ModelCoadditionTransport
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryCoproducts C]

private def transport {A B : C} (e : A ≅ B) (d : A ⟶ A ⨿ A) : B ⟶ B ⨿ B :=
  e.inv ≫ d ≫ coprod.map e.hom e.hom

private theorem transport_left {A B : C} (e : A ≅ B) (d : A ⟶ A ⨿ A)
    (hd : d ≫ coprod.desc (𝟙 A) 0 = 𝟙 A) :
    transport e d ≫ coprod.desc (𝟙 B) 0 = 𝟙 B := by
  have h : coprod.desc e.hom (0 : A ⟶ B) = coprod.desc (𝟙 A) 0 ≫ e.hom := by
    apply coprod.hom_ext <;> simp
  simp only [transport, Category.assoc, coprod.map_desc, Category.comp_id, comp_zero]
  rw [h, ← Category.assoc d, hd, Category.id_comp, e.inv_hom_id]

private theorem transport_right {A B : C} (e : A ≅ B) (d : A ⟶ A ⨿ A)
    (hd : d ≫ coprod.desc 0 (𝟙 A) = 𝟙 A) :
    transport e d ≫ coprod.desc 0 (𝟙 B) = 𝟙 B := by
  have h : coprod.desc (0 : A ⟶ B) e.hom = coprod.desc 0 (𝟙 A) ≫ e.hom := by
    apply coprod.hom_ext <;> simp
  simp only [transport, Category.assoc, coprod.map_desc, Category.comp_id, comp_zero]
  rw [h, ← Category.assoc d, hd, Category.id_comp, e.inv_hom_id]

private theorem transport_inverse {A B : C} (e : A ≅ B) (d : A ⟶ A ⨿ A)
    (n : A ⟶ A) (hn : d ≫ coprod.desc (𝟙 A) n = 0) :
    transport e d ≫ coprod.desc (𝟙 B) (e.inv ≫ n ≫ e.hom) = 0 := by
  have h : coprod.desc e.hom (n ≫ e.hom) = coprod.desc (𝟙 A) n ≫ e.hom := by
    apply coprod.hom_ext <;> simp
  simp only [transport, Category.assoc, coprod.map_desc, Category.comp_id,
    e.hom_inv_id_assoc]
  rw [h, ← Category.assoc d, hn, zero_comp, comp_zero]

variable (S : C ⥤ C) [S.IsEquivalence]
  (δ : ∀ X : C, S.obj X ⟶ S.obj X ⨿ S.obj X)
  (hnat : ∀ {X Y : C} (f : X ⟶ Y),
    S.map f ≫ δ Y = δ X ≫ coprod.map (S.map f) (S.map f))
  (hleft : ∀ X : C, δ X ≫ coprod.desc (𝟙 (S.obj X)) 0 = 𝟙 (S.obj X))
  (hright : ∀ X : C, δ X ≫ coprod.desc 0 (𝟙 (S.obj X)) = 𝟙 (S.obj X))

private def preimage (X : C) : C := S.asEquivalence.inverse.obj X
private def recognition (X : C) : S.obj (preimage S X) ≅ X :=
  S.asEquivalence.counitIso.app X

/-- Coaddition on all objects, using the specified equivalence's counit. -/
private def coaddition (X : C) : X ⟶ X ⨿ X :=
  transport (recognition S X) (δ (preimage S X))

include hnat in
omit [HasZeroMorphisms C] in
private theorem coaddition_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ coaddition S δ Y = coaddition S δ X ≫ coprod.map f f := by
  let g := S.asEquivalence.inverse.map f
  have hinv : f ≫ (recognition S Y).inv = (recognition S X).inv ≫ S.map g :=
    S.asEquivalence.counitIso.inv.naturality f
  have hhom : S.map g ≫ (recognition S Y).hom = (recognition S X).hom ≫ f :=
    S.asEquivalence.counitIso.hom.naturality f
  change f ≫ ((recognition S Y).inv ≫ δ (preimage S Y) ≫
    coprod.map (recognition S Y).hom (recognition S Y).hom) =
      ((recognition S X).inv ≫ δ (preimage S X) ≫
        coprod.map (recognition S X).hom (recognition S X).hom) ≫ coprod.map f f
  dsimp only [preimage]
  rw [← Category.assoc f, hinv]
  simp only [Category.assoc]
  rw [← Category.assoc (S.map g), hnat g]
  simp only [Category.assoc, coprod.map_map, hhom]

include hnat in
omit [HasZeroMorphisms C] in
/-- On every image object this transport returns the original coaddition,
so the chosen preimages do not change the given geometric operation. -/
private theorem coaddition_obj (X : C) : coaddition S δ (S.obj X) = δ X := by
  let e := recognition S (S.obj X)
  let f : preimage S (S.obj X) ⟶ X := S.preimage e.hom
  have hf : S.map f = e.hom := S.map_preimage _
  have hd : e.hom ≫ δ X = δ (preimage S (S.obj X)) ≫ coprod.map e.hom e.hom := by
    simpa only [hf] using hnat f
  change e.inv ≫ δ (preimage S (S.obj X)) ≫ coprod.map e.hom e.hom = δ X
  rw [← hd, ← Category.assoc, e.inv_hom_id, Category.id_comp]

include hleft in
private theorem coaddition_left (X : C) :
    coaddition S δ X ≫ coprod.desc (𝟙 X) 0 = 𝟙 X :=
  transport_left (recognition S X) (δ (preimage S X)) (hleft _)

include hright in
private theorem coaddition_right (X : C) :
    coaddition S δ X ≫ coprod.desc 0 (𝟙 X) = 𝟙 X :=
  transport_right (recognition S X) (δ (preimage S X)) (hright _)

variable (hinverse : ∀ X : C, ∃ n : S.obj X ⟶ S.obj X,
  δ X ≫ coprod.desc (𝟙 (S.obj X)) n = 0)

/-- The given existential inverse on each image object is conjugated along
that same counit; no naturality of this chosen inverse is assumed. -/
private def reflection (X : C) : X ⟶ X :=
  (recognition S X).inv ≫ Classical.choose (hinverse (preimage S X)) ≫
    (recognition S X).hom

private theorem coaddition_inverse (X : C) :
    coaddition S δ X ≫ coprod.desc (𝟙 X) (reflection S δ hinverse X) = 0 :=
  transport_inverse (recognition S X) (δ (preimage S X))
    (Classical.choose (hinverse (preimage S X))) (Classical.choose_spec (hinverse _))

/-- Natural unital coaddition with imagewise inverses on the specified
autoequivalence constructs a preadditive structure on the original category. -/
@[implicit_reducible]
private def preadditive : Preadditive C :=
  ModelNaturalCoaddition.preadditive (coaddition S δ)
    (coaddition_naturality S δ hnat) (coaddition_left S δ hleft)
    (coaddition_right S δ hright) (reflection S δ hinverse)
    (coaddition_inverse S δ hinverse)

/-- The resulting hom addition is the transported coaddition. -/
private theorem preadditive_add_eq {X Y : C} (f g : X ⟶ Y) :
    letI := preadditive S δ hnat hleft hright hinverse;
    f + g = coaddition S δ X ≫ coprod.desc f g :=
  ModelNaturalCoaddition.preadditive_add_eq (coaddition S δ)
    (coaddition_naturality S δ hnat) (coaddition_left S δ hleft)
    (coaddition_right S δ hright) (reflection S δ hinverse)
    (coaddition_inverse S δ hinverse) f g

/-- On an image object addition is induced by the original operation δ. -/
private theorem preadditive_add_image {X Y : C} (f g : S.obj X ⟶ Y) :
    letI := preadditive S δ hnat hleft hright hinverse;
    f + g = δ X ≫ coprod.desc f g := by
  rw [preadditive_add_eq S δ hnat hleft hright hinverse, coaddition_obj S δ hnat X]

end ModelCoadditionTransport

/-! ModelCogroupProbe construction. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
universe u v w z
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasZeroMorphisms C] [HasZeroObject C] (G : CofibrantGeneration C)
attribute [local instance] HasZeroObject.zero'

private def suspensionOf {X : C} (P : Cylinder X) : C :=
  pushout P.i (0 : X ⨿ X ⟶ (0 : C))

private def suspensionProjection {X : C} (P : Cylinder X) : P.I ⟶ suspensionOf P :=
  pushout.inl _ _

private theorem cylinder_i₀_projection {X : C} (P : Cylinder X) :
    P.i₀ ≫ suspensionProjection P = 0 := by
  rw [← P.inl_i, Category.assoc]
  have h : P.i ≫ suspensionProjection P = 0 := by
    simpa [suspensionProjection] using pushout.condition (f := P.i)
      (g := (0 : X ⨿ X ⟶ (0 : C)))
  rw [h, comp_zero]

private theorem cylinder_i₁_projection {X : C} (P : Cylinder X) :
    P.i₁ ≫ suspensionProjection P = 0 := by
  rw [← P.inr_i, Category.assoc]
  have h : P.i ≫ suspensionProjection P = 0 := by
    simpa [suspensionProjection] using pushout.condition (f := P.i)
      (g := (0 : X ⨿ X ⟶ (0 : C)))
  rw [h, comp_zero]

private def transPinchPre {X : C} [IsCofibrant X] (P : Cylinder X) [P.IsGood] :
    (P.trans P).I ⟶ suspensionOf P ⨿ suspensionOf P :=
  pushout.desc (suspensionProjection P ≫ coprod.inl)
    (suspensionProjection P ≫ coprod.inr) (by
      rw [← Category.assoc, cylinder_i₁_projection, zero_comp,
        ← Category.assoc, cylinder_i₀_projection, zero_comp])

private def transPinch {X : C} [IsCofibrant X] (P : Cylinder X) [P.IsGood] :
    suspensionOf (P.trans P) ⟶ suspensionOf P ⨿ suspensionOf P :=
  pushout.desc (transPinchPre P) 0 (by
    apply coprod.hom_ext
    · simp only [comp_zero]
      rw [← Category.assoc, (P.trans P).inl_i]
      change (P.i₀ ≫ pushout.inl P.i₁ P.i₀) ≫ transPinchPre P = 0
      rw [Category.assoc]
      simp only [transPinchPre, pushout.inl_desc]
      rw [← Category.assoc, cylinder_i₀_projection, zero_comp]
    · simp only [comp_zero]
      rw [← Category.assoc, (P.trans P).inr_i]
      change (P.i₁ ≫ pushout.inr P.i₁ P.i₀) ≫ transPinchPre P = 0
      rw [Category.assoc]
      simp only [transPinchPre, pushout.inr_desc]
      rw [← Category.assoc, cylinder_i₁_projection, zero_comp])

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem transCollapseLeft_π {X : C} [IsCofibrant X]
    (P : Cylinder X) [P.IsGood] : transCollapseLeft P ≫ P.π = (P.trans P).π := by
  apply pushout.hom_ext <;> simp [transCollapseLeft, Cylinder.trans, Precylinder.trans]

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem transCollapseLeft_weakEquivalence {X : C} [IsCofibrant X]
    (P : Cylinder X) [P.IsGood] : WeakEquivalence (transCollapseLeft P) :=
  weakEquivalence_of_postcomp_of_fac (transCollapseLeft_π P)

private theorem transCollapseQuotient_weakEquivalence {X : C} [IsCofibrant X]
    (P : Cylinder X) [P.IsGood] :
    WeakEquivalence (cylinderQuotientMap (P.trans P) P (transCollapseLeft P)
      (transCollapseLeft_i P)) := by
  let φ : cylinderArrow (P.trans P) ⟶ cylinderArrow P :=
    Arrow.homMk (𝟙 _) (transCollapseLeft P) (by
      simpa [cylinderArrow] using (transCollapseLeft_i P).symm)
  letI : IsCofibrant (X ⨿ X) :=
    isCofibrant_of_cofibration (coprod.inl : X ⟶ X ⨿ X)
  haveI : IsCofibrant (cylinderArrow (P.trans P)).left := ‹IsCofibrant (X ⨿ X)›
  haveI : IsCofibrant (cylinderArrow P).left := ‹IsCofibrant (X ⨿ X)›
  haveI : Cofibration (cylinderArrow (P.trans P)).hom :=
    inferInstanceAs (Cofibration (P.trans P).i)
  haveI : Cofibration (cylinderArrow P).hom := inferInstanceAs (Cofibration P.i)
  haveI : WeakEquivalence φ.left := inferInstanceAs (WeakEquivalence (𝟙 _))
  haveI : WeakEquivalence φ.right := transCollapseLeft_weakEquivalence P
  exact rawCofiberFunctor_weakEquivalence φ

private theorem transPinch_first {X : C} [IsCofibrant X]
    (P : Cylinder X) [P.IsGood] :
    transPinch P ≫ coprod.desc (𝟙 _) (0 : suspensionOf P ⟶ suspensionOf P) =
      cylinderQuotientMap (P.trans P) P (transCollapseLeft P) (transCollapseLeft_i P) := by
  apply pushout.hom_ext
  · dsimp [transPinch, cylinderQuotientMap, rawCofiberFunctor]
    simp only [pushout.inl_desc_assoc, pushout.inl_desc]
    apply pushout.hom_ext <;>
      simp only [transPinchPre, transCollapseLeft, pushout.inl_desc_assoc,
        pushout.inr_desc_assoc, Category.assoc, coprod.inl_desc, coprod.inr_desc,
        Category.comp_id, comp_zero]
    · simp only [Category.id_comp]; rfl
    · change 0 = P.π ≫ (P.i₁ ≫ suspensionProjection P)
      rw [cylinder_i₁_projection, comp_zero]
  · exact (isZero_zero C).eq_of_src _ _

private theorem transPinch_second {X : C} [IsCofibrant X]
    (P : Cylinder X) [P.IsGood] :
    transPinch P ≫ coprod.desc (0 : suspensionOf P ⟶ suspensionOf P) (𝟙 _) =
      cylinderQuotientMap (P.trans P) P (transCollapseRight P) (transCollapseRight_i P) := by
  apply pushout.hom_ext
  · dsimp [transPinch, cylinderQuotientMap, rawCofiberFunctor]
    simp only [pushout.inl_desc_assoc, pushout.inl_desc]
    apply pushout.hom_ext <;>
      simp only [transPinchPre, transCollapseRight, pushout.inl_desc_assoc,
        pushout.inr_desc_assoc, Category.assoc, coprod.inl_desc, coprod.inr_desc,
        Category.comp_id, comp_zero]
    · change 0 = P.π ≫ (P.i₀ ≫ suspensionProjection P)
      rw [cylinder_i₀_projection, comp_zero]
    · simp only [Category.id_comp]; rfl
  · exact (isZero_zero C).eq_of_src _ _

end KIP126.StableHomotopy.CofibrantGeneration

/-! ModelPinchNaturality construction. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
universe u v w z
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasZeroMorphisms C] [HasZeroObject C] (G : CofibrantGeneration C)
attribute [local instance] HasZeroObject.zero'

private def transCylinderMap {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    ((G.functorialCylinder X).trans (G.functorialCylinder X)).I ⟶
      ((G.functorialCylinder Y).trans (G.functorialCylinder Y)).I :=
  pushout.map _ _ _ _ (G.functorialCylinderMap f) (G.functorialCylinderMap f) f
    (G.cylinder_i₁_map f) (G.cylinder_i₀_map f)

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem cylinder_map_π {X Y : C} (f : X ⟶ Y) :
    G.functorialCylinderMap f ≫ (G.functorialCylinder Y).π =
      (G.functorialCylinder X).π ≫ f := by
  exact G.cofibrationTrivialFibrationFactorization.p.naturality (foldMap f)

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem transCylinderMap_i {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) :
    ((G.functorialCylinder X).trans (G.functorialCylinder X)).i ≫
        G.transCylinderMap f =
      coprod.map f f ≫ ((G.functorialCylinder Y).trans (G.functorialCylinder Y)).i := by
  apply coprod.hom_ext
  · simp only [← Category.assoc, Precylinder.inl_i, coprod.inl_map]
    change ((G.functorialCylinder X).i₀ ≫ pushout.inl _ _) ≫ G.transCylinderMap f = _
    simp only [transCylinderMap, Category.assoc, pushout.inl_desc]
    rw [← Category.assoc, G.cylinder_i₀_map, Category.assoc]
    rw [((G.functorialCylinder Y).trans (G.functorialCylinder Y)).inl_i]
    rfl
  · simp only [← Category.assoc, Precylinder.inr_i, coprod.inr_map]
    change ((G.functorialCylinder X).i₁ ≫ pushout.inr _ _) ≫ G.transCylinderMap f = _
    simp only [transCylinderMap, Category.assoc, pushout.inr_desc]
    rw [← Category.assoc, G.cylinder_i₁_map, Category.assoc]
    rw [((G.functorialCylinder Y).trans (G.functorialCylinder Y)).inr_i]
    rfl

private def transSuspensionMap {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    suspensionOf ((G.functorialCylinder X).trans (G.functorialCylinder X)) ⟶
      suspensionOf ((G.functorialCylinder Y).trans (G.functorialCylinder Y)) :=
  pushout.map _ _ _ _ (G.transCylinderMap f) (𝟙 (0 : C)) (coprod.map f f)
    (G.transCylinderMap_i f) (by simp)

private theorem transPinch_naturality {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) :
    G.transSuspensionMap f ≫ transPinch (G.functorialCylinder Y) =
      transPinch (G.functorialCylinder X) ≫
        coprod.map (G.cylinderSuspensionMap f) (G.cylinderSuspensionMap f) := by
  apply pushout.hom_ext
  · simp only [transSuspensionMap, transPinch, pushout.inl_desc_assoc,
      pushout.inl_desc, Category.assoc]
    apply pushout.hom_ext <;>
      simp [transCylinderMap, transPinchPre, cylinderSuspensionMap,
        suspensionProjection, Category.assoc] <;> rfl
  · exact (isZero_zero C).eq_of_src _ _

private theorem transCollapse_naturality {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) :
    G.transSuspensionMap f ≫
      cylinderQuotientMap ((G.functorialCylinder Y).trans (G.functorialCylinder Y))
        (G.functorialCylinder Y) (transCollapseLeft (G.functorialCylinder Y))
          (transCollapseLeft_i (G.functorialCylinder Y)) =
      cylinderQuotientMap ((G.functorialCylinder X).trans (G.functorialCylinder X))
        (G.functorialCylinder X) (transCollapseLeft (G.functorialCylinder X))
          (transCollapseLeft_i (G.functorialCylinder X)) ≫
      G.cylinderSuspensionMap f := by
  apply pushout.hom_ext
  · dsimp [transSuspensionMap, cylinderQuotientMap, rawCofiberFunctor,
      cylinderSuspensionMap]
    simp only [pushout.inl_desc_assoc, pushout.inl_desc, Category.assoc]
    apply pushout.hom_ext
    · simp [transCylinderMap, transCollapseLeft, cylinderArrow]
    · simp only [transCylinderMap, transCollapseLeft, pushout.inr_desc_assoc,
        Category.assoc]
      rw [← Category.assoc, ← Category.assoc, G.cylinder_map_π]
      rw [Category.assoc, Category.assoc, ← Category.assoc
        (G.functorialCylinder X).i₁, G.cylinder_i₁_map, Category.assoc]
      rfl
  · exact (isZero_zero C).eq_of_src _ _

end KIP126.StableHomotopy.CofibrantGeneration

/-! ModelPinchInverse construction. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
universe u v w z
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasZeroMorphisms C] [HasZeroObject C] (G : CofibrantGeneration C)
attribute [local instance] HasZeroObject.zero'

private def transCylinderToCone (X : C) [IsCofibrant X] :
    ((G.functorialCylinder X).trans (G.functorialCylinder X)).I ⟶
      G.cylinderCone X :=
  pushout.desc
    (pushout.inl (G.functorialCylinder X).i₀ (0 : X ⟶ (0 : C)))
    (G.cylinderSwap X ≫ pushout.inl (G.functorialCylinder X).i₀ 0) (by
      rw [← Category.assoc, G.cylinder_i₀_swap])

private def transSuspensionToCone (X : C) [IsCofibrant X] :
    suspensionOf ((G.functorialCylinder X).trans (G.functorialCylinder X)) ⟶
      G.cylinderCone X :=
  pushout.desc (G.transCylinderToCone X) 0 (by
    apply coprod.hom_ext
    · simp only [comp_zero]
      rw [← Category.assoc, ((G.functorialCylinder X).trans
        (G.functorialCylinder X)).inl_i]
      change ((G.functorialCylinder X).i₀ ≫ pushout.inl _ _) ≫
        G.transCylinderToCone X = 0
      simp only [Category.assoc, transCylinderToCone, pushout.inl_desc]
      simpa using pushout.condition (f := (G.functorialCylinder X).i₀)
        (g := (0 : X ⟶ (0 : C)))
    · simp only [comp_zero]
      rw [← Category.assoc, ((G.functorialCylinder X).trans
        (G.functorialCylinder X)).inr_i]
      change ((G.functorialCylinder X).i₁ ≫ pushout.inr _ _) ≫
        G.transCylinderToCone X = 0
      simp only [Category.assoc, transCylinderToCone, pushout.inr_desc]
      rw [← Category.assoc, G.cylinder_i₁_swap]
      simpa using pushout.condition (f := (G.functorialCylinder X).i₀)
        (g := (0 : X ⟶ (0 : C))))

private theorem transPinch_inverse_factorization (X : C) [IsCofibrant X] :
    transPinch (G.functorialCylinder X) ≫
      coprod.desc (𝟙 (G.cylinderSuspension X)) (G.cylinderSuspensionSwap X) =
    G.transSuspensionToCone X ≫ G.cylinderConeQuotient X := by
  apply pushout.hom_ext
  · simp only [transPinch, transSuspensionToCone, pushout.inl_desc_assoc]
    apply pushout.hom_ext
    · simp [transPinchPre, transCylinderToCone, cylinderConeQuotient,
        suspensionProjection]
      exact Category.comp_id _
    · simp [transPinchPre, transCylinderToCone, cylinderConeQuotient,
        suspensionProjection, cylinderSuspensionSwap]
  · exact (isZero_zero C).eq_of_src _ _

private theorem localizedTransPinch_inverse
    {H : Type w} [Category.{z} H] [HasZeroMorphisms H]
    (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)]
    (X : C) [IsCofibrant X] :
    L.map (transPinch (G.functorialCylinder X) ≫
      coprod.desc (𝟙 (G.cylinderSuspension X)) (G.cylinderSuspensionSwap X)) = 0 := by
  haveI : IsIso (L.map (0 : (0 : C) ⟶ G.cylinderCone X)) :=
    Localization.inverts L (weakEquivalences C) _
      ((weakEquivalence_iff _).1 (G.cylinderCone_weakZero X))
  have hz : IsZero (L.obj (G.cylinderCone X)) :=
    (localization_isZero L (weakEquivalences C)).of_iso
      (asIso (L.map (0 : (0 : C) ⟶ G.cylinderCone X))).symm
  rw [G.transPinch_inverse_factorization, L.map_comp,
    hz.eq_of_src (L.map (G.cylinderConeQuotient X)) 0, comp_zero]

private theorem localizedTransPinch_left_inverse
    {H : Type w} [Category.{z} H] [HasZeroMorphisms H]
    (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)]
    (X : C) [IsCofibrant X] :
    L.map (transPinch (G.functorialCylinder X) ≫
      coprod.desc (G.cylinderSuspensionSwap X) (𝟙 (G.cylinderSuspension X))) = 0 := by
  have h : coprod.desc (G.cylinderSuspensionSwap X) (𝟙 (G.cylinderSuspension X)) =
      coprod.desc (𝟙 (G.cylinderSuspension X)) (G.cylinderSuspensionSwap X) ≫
        G.cylinderSuspensionSwap X := by
    apply coprod.hom_ext
    · simp
    · simp only [coprod.inr_desc, coprod.inr_desc_assoc]
      exact (G.cylinderSuspensionSwap_sq X).symm
  calc
    L.map (transPinch (G.functorialCylinder X) ≫
        coprod.desc (G.cylinderSuspensionSwap X) (𝟙 (G.cylinderSuspension X))) =
      L.map (transPinch (G.functorialCylinder X) ≫
        (coprod.desc (𝟙 (G.cylinderSuspension X)) (G.cylinderSuspensionSwap X) ≫
          G.cylinderSuspensionSwap X)) :=
      congrArg (fun k => L.map (transPinch (G.functorialCylinder X) ≫ k)) h
    _ = 0 := by
      rw [← Category.assoc, L.map_comp, G.localizedTransPinch_inverse, zero_comp]


end KIP126.StableHomotopy.CofibrantGeneration

/-! ModelLocalizedPinch construction. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
universe u v w z
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasZeroMorphisms C] [HasZeroObject C] (G : CofibrantGeneration C)
  {H : Type w} [Category.{z} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)] [HasBinaryCoproducts H]
attribute [local instance] HasZeroObject.zero' cylinderSuspension_isCofibrant

private instance localizedCoprodComparison_isIso (X Y : C)
    [IsCofibrant X] [IsCofibrant Y] : IsIso (coprodComparison L X Y) := by
  let e := (coprodIsCoprod (L.obj X) (L.obj Y)).coconePointUniqueUpToIso
    (ModelFoundation.localizedCoprodIsColimit L X Y)
  have he : e.hom = coprodComparison L X Y := by
    apply coprod.hom_ext
    · simpa [BinaryCofan.mk, e] using
        IsColimit.comp_coconePointUniqueUpToIso_hom
          (coprodIsCoprod (L.obj X) (L.obj Y))
          (ModelFoundation.localizedCoprodIsColimit L X Y) ⟨WalkingPair.left⟩
    · simpa [BinaryCofan.mk, e] using
        IsColimit.comp_coconePointUniqueUpToIso_hom
          (coprodIsCoprod (L.obj X) (L.obj Y))
          (ModelFoundation.localizedCoprodIsColimit L X Y) ⟨WalkingPair.right⟩
  rw [← he]
  infer_instance

private def collapseQuotient (X : C) [IsCofibrant X] :
    suspensionOf ((G.functorialCylinder X).trans (G.functorialCylinder X)) ⟶
      G.cylinderSuspension X :=
  cylinderQuotientMap ((G.functorialCylinder X).trans (G.functorialCylinder X))
    (G.functorialCylinder X) (transCollapseLeft (G.functorialCylinder X))
      (transCollapseLeft_i (G.functorialCylinder X))

private def pinchQuotient (X : C) [IsCofibrant X] :
    suspensionOf ((G.functorialCylinder X).trans (G.functorialCylinder X)) ⟶
      G.cylinderSuspension X ⨿ G.cylinderSuspension X :=
  transPinch (G.functorialCylinder X)

private theorem pinchQuotient_naturality {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) :
    G.transSuspensionMap f ≫ G.pinchQuotient Y = G.pinchQuotient X ≫
      coprod.map (G.cylinderSuspensionMap f) (G.cylinderSuspensionMap f) :=
  G.transPinch_naturality f

private theorem collapseQuotient_naturality {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) :
    G.transSuspensionMap f ≫ G.collapseQuotient Y =
      G.collapseQuotient X ≫ G.cylinderSuspensionMap f :=
  G.transCollapse_naturality f

private theorem pinchQuotient_first (X : C) [IsCofibrant X] :
    G.pinchQuotient X ≫ coprod.desc (𝟙 _) (0 : G.cylinderSuspension X ⟶ _) =
      G.collapseQuotient X := transPinch_first (G.functorialCylinder X)

omit [HasBinaryCoproducts H] in
private theorem pinchQuotient_second_localized (X : C) [IsCofibrant X] :
    L.map (G.pinchQuotient X ≫ coprod.desc (0 : G.cylinderSuspension X ⟶ _) (𝟙 _)) =
      L.map (G.collapseQuotient X) := by
  change L.map (transPinch (G.functorialCylinder X) ≫ coprod.desc 0 (𝟙 _)) = _
  rw [transPinch_second]
  exact (G.transCollapse_same_suspension L (G.functorialCylinder X)).symm

private instance collapseQuotient_weakEquivalence (X : C) [IsCofibrant X] :
    WeakEquivalence (G.collapseQuotient X) :=
  transCollapseQuotient_weakEquivalence (G.functorialCylinder X)

private instance localizedCollapseQuotient_isIso (X : C) [IsCofibrant X] :
    IsIso (L.map (G.collapseQuotient X)) :=
  Localization.inverts L (weakEquivalences C) _ (mem_weakEquivalences _)

private def localizedCylinderPinch (X : C) [IsCofibrant X] :
    L.obj (G.cylinderSuspension X) ⟶
      L.obj (G.cylinderSuspension X) ⨿ L.obj (G.cylinderSuspension X) :=
  inv (L.map (G.collapseQuotient X)) ≫
    L.map (G.pinchQuotient X) ≫
    inv (coprodComparison L (G.cylinderSuspension X) (G.cylinderSuspension X))

private theorem localizedCylinderPinch_naturality {X Y : C}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    L.map (G.cylinderSuspensionMap f) ≫ G.localizedCylinderPinch L Y =
      G.localizedCylinderPinch L X ≫
        coprod.map (L.map (G.cylinderSuspensionMap f))
          (L.map (G.cylinderSuspensionMap f)) := by
  have h : L.map (G.cylinderSuspensionMap f) ≫ inv (L.map (G.collapseQuotient Y)) =
      inv (L.map (G.collapseQuotient X)) ≫ L.map (G.transSuspensionMap f) := by
    rw [IsIso.comp_inv_eq, Category.assoc, ← L.map_comp,
      G.collapseQuotient_naturality, L.map_comp, IsIso.inv_hom_id_assoc]
  dsimp [localizedCylinderPinch]
  rw [← Category.assoc, h, Category.assoc, ← L.map_comp_assoc,
    G.pinchQuotient_naturality, L.map_comp, Category.assoc,
    ← coprodComparison_inv_natural]
  simp only [Category.assoc]

variable [HasZeroMorphisms H] [L.PreservesZeroMorphisms]

omit [HasZeroMorphisms C] [HasZeroObject C] [HasZeroMorphisms H]
    [L.PreservesZeroMorphisms] in
private theorem localizedCoprodComparison_inv_desc (X Y Z : C)
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Z) (g : Y ⟶ Z) :
    inv (coprodComparison L X Y) ≫ coprod.desc (L.map f) (L.map g) =
      L.map (coprod.desc f g) := by
  apply (cancel_epi (coprodComparison L X Y)).1
  simp only [IsIso.hom_inv_id_assoc]
  apply coprod.hom_ext <;> simp [← L.map_comp]

private theorem localizedCylinderPinch_first (X : C) [IsCofibrant X] :
    G.localizedCylinderPinch L X ≫ coprod.desc (𝟙 _) (0 : L.obj (G.cylinderSuspension X) ⟶ _) =
      𝟙 _ := by
  have h := localizedCoprodComparison_inv_desc L (G.cylinderSuspension X)
    (G.cylinderSuspension X) (G.cylinderSuspension X) (𝟙 _) 0
  simp only [L.map_id, L.map_zero] at h
  dsimp [localizedCylinderPinch]
  rw [Category.assoc, Category.assoc, h, ← L.map_comp, G.pinchQuotient_first]
  exact IsIso.inv_hom_id _

private theorem localizedCylinderPinch_second (X : C) [IsCofibrant X] :
    G.localizedCylinderPinch L X ≫ coprod.desc (0 : L.obj (G.cylinderSuspension X) ⟶ _) (𝟙 _) =
      𝟙 _ := by
  have h := localizedCoprodComparison_inv_desc L (G.cylinderSuspension X)
    (G.cylinderSuspension X) (G.cylinderSuspension X) 0 (𝟙 _)
  simp only [L.map_id, L.map_zero] at h
  dsimp [localizedCylinderPinch]
  rw [Category.assoc, Category.assoc, h, ← L.map_comp, G.pinchQuotient_second_localized L]
  exact IsIso.inv_hom_id _

omit [L.PreservesZeroMorphisms] in
private theorem localizedCylinderPinch_inverse (X : C) [IsCofibrant X] :
    G.localizedCylinderPinch L X ≫
      coprod.desc (𝟙 _) (L.map (G.cylinderSuspensionSwap X)) = 0 := by
  have h := localizedCoprodComparison_inv_desc L (G.cylinderSuspension X)
    (G.cylinderSuspension X) (G.cylinderSuspension X) (𝟙 _)
      (G.cylinderSuspensionSwap X)
  simp only [L.map_id] at h
  have hzero : L.map (G.pinchQuotient X ≫
      coprod.desc (𝟙 _) (G.cylinderSuspensionSwap X)) = 0 :=
    G.localizedTransPinch_inverse L X
  dsimp [localizedCylinderPinch]
  rw [Category.assoc, Category.assoc, h, ← L.map_comp, hzero, comp_zero]

end KIP126.StableHomotopy.CofibrantGeneration

/-! ModelDerivedPinch construction. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomotopicalAlgebra
universe u v w z
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasZeroMorphisms C] [HasZeroObject C] (G : CofibrantGeneration C)
  {H : Type w} [Category.{z} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)] [HasBinaryCoproducts H]
attribute [local instance] HasZeroObject.zero' cofibrantReplacement_isCofibrant

private instance localizedSuspensionCounit_isIso (X : C) :
    IsIso (L.map (G.suspensionFunctor.map (G.cofibrantReplacementCounit.app X))) :=
  Localization.inverts L (weakEquivalences C) _
    (G.suspensionFunctor_weakEquivalences _ (G.cofibrantReplacementCounit_weakEquivalence X))

private def derivedCylinderComparison (X : C) :
    (G.derivedSuspensionFunctor L).obj (L.obj X) ≅
      L.obj (G.cylinderSuspension (G.cofibrantReplacementFunctor.obj X)) :=
  (G.derivedSuspensionFunctorComparison L).app X ≪≫
    (asIso (L.map (G.suspensionFunctor.map (G.cofibrantReplacementCounit.app X)))).symm ≪≫
      G.localizedCylinderSuspensionIso L (G.cofibrantReplacementFunctor.obj X)

omit [HasBinaryCoproducts H] in
private theorem derivedCylinderComparison_naturality {X Y : C} (f : X ⟶ Y) :
    (G.derivedSuspensionFunctor L).map (L.map f) ≫ (G.derivedCylinderComparison L Y).hom =
      (G.derivedCylinderComparison L X).hom ≫
        L.map (G.cylinderSuspensionMap (G.cofibrantReplacementFunctor.map f)) := by
  have hc : L.map (G.suspensionFunctor.map f) ≫
      inv (L.map (G.suspensionFunctor.map (G.cofibrantReplacementCounit.app Y))) =
    inv (L.map (G.suspensionFunctor.map (G.cofibrantReplacementCounit.app X))) ≫
      L.map (G.suspensionFunctor.map (G.cofibrantReplacementFunctor.map f)) := by
    rw [IsIso.comp_inv_eq, Category.assoc, ← L.map_comp,
      ← G.suspensionFunctor.map_comp, G.cofibrantReplacementCounit.naturality,
      G.suspensionFunctor.map_comp, L.map_comp, IsIso.inv_hom_id_assoc]
    rfl
  have hn := (G.derivedSuspensionFunctorComparison L).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  dsimp [derivedCylinderComparison]
  rw [← Category.assoc, hn,
    Category.assoc, ← Category.assoc (L.map (G.suspensionFunctor.map f)), hc,
    Category.assoc, G.localizedCylinderSuspensionIso_naturality]
  simp only [Category.assoc]

private def doubleCoproductFunctor : H ⥤ H where
  obj X := X ⨿ X
  map f := coprod.map f f
  map_id X := by apply coprod.hom_ext <;> simp
  map_comp f g := by apply coprod.hom_ext <;> simp

private def pointDerivedPinch :
    L ⋙ G.derivedSuspensionFunctor L ⟶
      L ⋙ G.derivedSuspensionFunctor L ⋙ (doubleCoproductFunctor : H ⥤ H) where
  app X := (G.derivedCylinderComparison L X).hom ≫
    G.localizedCylinderPinch L (G.cofibrantReplacementFunctor.obj X) ≫
      coprod.map (G.derivedCylinderComparison L X).inv (G.derivedCylinderComparison L X).inv
  naturality X Y f := by
    have hc := G.derivedCylinderComparison_naturality L f
    have hi : L.map (G.cylinderSuspensionMap (G.cofibrantReplacementFunctor.map f)) ≫
        (G.derivedCylinderComparison L Y).inv =
      (G.derivedCylinderComparison L X).inv ≫
        (G.derivedSuspensionFunctor L).map (L.map f) := by
      rw [Iso.comp_inv_eq, Category.assoc, hc, Iso.inv_hom_id_assoc]
    change (G.derivedSuspensionFunctor L).map (L.map f) ≫ _ =
      _ ≫ coprod.map ((G.derivedSuspensionFunctor L).map (L.map f))
        ((G.derivedSuspensionFunctor L).map (L.map f))
    rw [← Category.assoc, hc, Category.assoc,
      ← Category.assoc (L.map (G.cylinderSuspensionMap (G.cofibrantReplacementFunctor.map f))),
      G.localizedCylinderPinch_naturality, Category.assoc,
      coprod.map_map, hi]
    simp only [Category.assoc, coprod.map_map]

private def derivedPinch : G.derivedSuspensionFunctor L ⟶
    G.derivedSuspensionFunctor L ⋙ (doubleCoproductFunctor : H ⥤ H) := by
  letI : Localization.Lifting L (weakEquivalences C)
      (L ⋙ G.derivedSuspensionFunctor L) (G.derivedSuspensionFunctor L) := ⟨Iso.refl _⟩
  letI : Localization.Lifting L (weakEquivalences C)
      (L ⋙ G.derivedSuspensionFunctor L ⋙ doubleCoproductFunctor)
      (G.derivedSuspensionFunctor L ⋙ doubleCoproductFunctor) := ⟨Iso.refl _⟩
  exact Localization.liftNatTrans L (weakEquivalences C) _ _ _ _ (G.pointDerivedPinch L)

private theorem derivedPinch_app (X : C) :
    (G.derivedPinch L).app (L.obj X) = (G.pointDerivedPinch L).app X := by
  simp [derivedPinch, Localization.liftNatTrans_app, Localization.Lifting.iso]

variable [HasZeroMorphisms H] [L.PreservesZeroMorphisms]

private theorem pointDerivedPinch_first (X : C) :
    (G.pointDerivedPinch L).app X ≫ coprod.desc (𝟙 _) (0 : _ ⟶
      (G.derivedSuspensionFunctor L).obj (L.obj X)) = 𝟙 _ := by
  change ((G.derivedCylinderComparison L X).hom ≫
    G.localizedCylinderPinch L (G.cofibrantReplacementFunctor.obj X) ≫
      coprod.map _ _) ≫ _ = _
  rw [Category.assoc, Category.assoc, coprod.map_desc]
  simp only [Category.comp_id, comp_zero]
  have hd : coprod.desc (G.derivedCylinderComparison L X).inv
      (0 : L.obj (G.cylinderSuspension (G.cofibrantReplacementFunctor.obj X)) ⟶ _) =
      coprod.desc (𝟙 _) 0 ≫ (G.derivedCylinderComparison L X).inv := by simp
  rw [hd, ← Category.assoc
    (G.localizedCylinderPinch L (G.cofibrantReplacementFunctor.obj X)),
    G.localizedCylinderPinch_first, Category.id_comp, Iso.hom_inv_id]
  rfl

private theorem pointDerivedPinch_second (X : C) :
    (G.pointDerivedPinch L).app X ≫ coprod.desc (0 : _ ⟶
      (G.derivedSuspensionFunctor L).obj (L.obj X)) (𝟙 _) = 𝟙 _ := by
  change ((G.derivedCylinderComparison L X).hom ≫
    G.localizedCylinderPinch L (G.cofibrantReplacementFunctor.obj X) ≫
      coprod.map _ _) ≫ _ = _
  rw [Category.assoc, Category.assoc, coprod.map_desc]
  simp only [Category.comp_id, comp_zero]
  have hd : coprod.desc
      (0 : L.obj (G.cylinderSuspension (G.cofibrantReplacementFunctor.obj X)) ⟶ _)
      (G.derivedCylinderComparison L X).inv =
      coprod.desc 0 (𝟙 _) ≫ (G.derivedCylinderComparison L X).inv := by simp
  rw [hd, ← Category.assoc
    (G.localizedCylinderPinch L (G.cofibrantReplacementFunctor.obj X)),
    G.localizedCylinderPinch_second, Category.id_comp, Iso.hom_inv_id]
  rfl

private def firstCoproductProjection : (doubleCoproductFunctor : H ⥤ H) ⟶ 𝟭 H where
  app X := coprod.desc (𝟙 X) 0
  naturality X Y f := by apply coprod.hom_ext <;> simp [doubleCoproductFunctor]

private def secondCoproductProjection : (doubleCoproductFunctor : H ⥤ H) ⟶ 𝟭 H where
  app X := coprod.desc 0 (𝟙 X)
  naturality X Y f := by apply coprod.hom_ext <;> simp [doubleCoproductFunctor]

private theorem derivedPinch_first (X : H) :
    (G.derivedPinch L).app X ≫ coprod.desc (𝟙 _) (0 : _ ⟶
      (G.derivedSuspensionFunctor L).obj X) = 𝟙 _ := by
  have h : G.derivedPinch L ≫
      whiskerLeft (G.derivedSuspensionFunctor L) firstCoproductProjection =
    (Functor.rightUnitor (G.derivedSuspensionFunctor L)).inv := by
    apply Localization.natTrans_ext L (weakEquivalences C)
    intro Y
    simpa only [NatTrans.comp_app, whiskerLeft_app, firstCoproductProjection,
      G.derivedPinch_app, Functor.rightUnitor_inv_app, Functor.comp_obj,
      Functor.id_obj] using G.pointDerivedPinch_first L Y
  exact congr_app h X

private theorem derivedPinch_second (X : H) :
    (G.derivedPinch L).app X ≫ coprod.desc (0 : _ ⟶
      (G.derivedSuspensionFunctor L).obj X) (𝟙 _) = 𝟙 _ := by
  have h : G.derivedPinch L ≫
      whiskerLeft (G.derivedSuspensionFunctor L) secondCoproductProjection =
    (Functor.rightUnitor (G.derivedSuspensionFunctor L)).inv := by
    apply Localization.natTrans_ext L (weakEquivalences C)
    intro Y
    simpa only [NatTrans.comp_app, whiskerLeft_app, secondCoproductProjection,
      G.derivedPinch_app, Functor.rightUnitor_inv_app, Functor.comp_obj,
      Functor.id_obj] using G.pointDerivedPinch_second L Y
  exact congr_app h X

omit [L.PreservesZeroMorphisms] in
private theorem pointDerivedPinch_inverse (X : C) :
    ∃ r : (G.derivedSuspensionFunctor L).obj (L.obj X) ⟶
        (G.derivedSuspensionFunctor L).obj (L.obj X),
      (G.pointDerivedPinch L).app X ≫ coprod.desc (𝟙 _) r = 0 := by
  let e := G.derivedCylinderComparison L X
  let r := L.map (G.cylinderSuspensionSwap (G.cofibrantReplacementFunctor.obj X))
  refine ⟨e.hom ≫ r ≫ e.inv, ?_⟩
  change (e.hom ≫ G.localizedCylinderPinch L (G.cofibrantReplacementFunctor.obj X) ≫
    coprod.map e.inv e.inv) ≫ coprod.desc (𝟙 _) (e.hom ≫ r ≫ e.inv) = 0
  rw [Category.assoc, Category.assoc, coprod.map_desc]
  simp only [Category.comp_id, Iso.inv_hom_id_assoc]
  have hd : coprod.desc e.inv (r ≫ e.inv) = coprod.desc (𝟙 _) r ≫ e.inv := by simp
  rw [hd, ← Category.assoc (G.localizedCylinderPinch L _),
    G.localizedCylinderPinch_inverse, zero_comp, comp_zero]

omit [L.PreservesZeroMorphisms] in
private theorem derivedPinch_inverse (X : H) :
    ∃ r : (G.derivedSuspensionFunctor L).obj X ⟶ (G.derivedSuspensionFunctor L).obj X,
      (G.derivedPinch L).app X ≫ coprod.desc (𝟙 _) r = 0 := by
  letI := Localization.essSurj L (weakEquivalences C)
  let Y := L.objPreimage X
  let e := (G.derivedSuspensionFunctor L).mapIso (L.objObjPreimageIso X)
  obtain ⟨r, hr⟩ := G.pointDerivedPinch_inverse L Y
  rw [← G.derivedPinch_app] at hr
  refine ⟨e.inv ≫ r ≫ e.hom, ?_⟩
  apply (cancel_epi e.hom).1
  rw [← Category.assoc]
  have hn := (G.derivedPinch L).naturality (L.objObjPreimageIso X).hom
  change e.hom ≫ (G.derivedPinch L).app X =
    (G.derivedPinch L).app (L.obj Y) ≫ coprod.map e.hom e.hom at hn
  rw [hn, Category.assoc, coprod.map_desc]
  simp only [Category.comp_id, Iso.hom_inv_id_assoc, comp_zero]
  have hd : coprod.desc e.hom (r ≫ e.hom) = coprod.desc (𝟙 _) r ≫ e.hom := by simp; rfl
  rw [hd, ← Category.assoc, hr, zero_comp]

end KIP126.StableHomotopy.CofibrantGeneration

/-! ModelPreadditive construction. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
universe u v w z
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasZeroMorphisms C] [HasZeroObject C] (G : CofibrantGeneration C)
  {H : Type w} [Category.{z} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]
  [(G.derivedSuspensionFunctor L).IsEquivalence]

/-- The suspension pinch and its endpoint reflection induce additive Hom groups.
Stability transports this operation from suspensions to all objects. -/
@[implicit_reducible, no_expose]
public def modelPreadditive : Preadditive H := by
  letI : HasZeroMorphisms H := (localization_isZero L (weakEquivalences C)).hasZeroMorphisms
  letI : HasBinaryCoproducts H := ModelFoundation.modelLocalization_hasBinaryCoproducts L
  letI := localization_preservesZeroMorphisms L (weakEquivalences C)
  exact ModelCoadditionTransport.preadditive (G.derivedSuspensionFunctor L)
    (fun X => (G.derivedPinch L).app X)
    (fun {X Y} f => (G.derivedPinch L).naturality f)
    (G.derivedPinch_first L) (G.derivedPinch_second L) (G.derivedPinch_inverse L)

/-- Every actual integer shift is additive for the model-derived addition,
because it is an equivalence and preserves the binary biproducts constructed above. -/
public theorem modelShiftAdditive (n : ℤ) :
    letI := G.modelPreadditive L;
    letI := G.derivedSuspensionHasShift L;
    (shiftFunctor H n).Additive := by
  letI := G.modelPreadditive L
  letI := G.derivedSuspensionHasShift L
  letI := localization_hasZeroObject L (weakEquivalences C)
  letI : HasBinaryCoproducts H := ModelFoundation.modelLocalization_hasBinaryCoproducts L
  letI : HasBinaryBiproducts H := HasBinaryBiproducts.of_hasBinaryCoproducts
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts (shiftFunctor H n)
  exact Functor.additive_of_preservesBinaryBiproducts (shiftFunctor H n)

end KIP126.StableHomotopy.CofibrantGeneration
