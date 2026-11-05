module
public import KIP126.AdamsSynthetic.ModelFoundation.Suspension
import all KIP126.AdamsSynthetic.ModelFoundation.CofiberInvariance
import all KIP126.AdamsSynthetic.ModelFoundation.LocalizedCoproducts
public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasZeroMorphisms C] [HasZeroObject C] (G : CofibrantGeneration C)
attribute [local instance] HasZeroObject.zero'
noncomputable section

private def foldArrow (X : C) : Arrow C := Arrow.mk (codiag X)

private def foldSwap (X : C) : foldArrow X ⟶ foldArrow X :=
  Arrow.homMk (coprod.braiding X X).hom (𝟙 X) (by
    dsimp [foldArrow]
    apply coprod.hom_ext <;> simp)

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem foldSwap_sq (X : C) : foldSwap X ≫ foldSwap X = 𝟙 _ := by
  ext
  · exact coprod.symmetry X X
  · simp [foldSwap, foldArrow]

private def functorialCylinder (X : C) : Cylinder X :=
  Cylinder.ofFactorizationData
    (G.cofibrationTrivialFibrationFactorization.factorizationData (codiag X))

private instance functorialCylinder_good (X : C) :
    (G.functorialCylinder X).IsVeryGood := by
  unfold functorialCylinder
  infer_instance

private def cylinderSwap (X : C) :
    (G.functorialCylinder X).I ⟶ (G.functorialCylinder X).I :=
  G.cofibrationTrivialFibrationFactorization.Z.map (foldSwap X)

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem cylinderSwap_sq (X : C) :
    G.cylinderSwap X ≫ G.cylinderSwap X = 𝟙 _ := by
  change G.cofibrationTrivialFibrationFactorization.Z.map (foldSwap X) ≫
    G.cofibrationTrivialFibrationFactorization.Z.map (foldSwap X) = _
  rw [← CategoryTheory.Functor.map_comp, foldSwap_sq]
  exact G.cofibrationTrivialFibrationFactorization.Z.map_id _

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem cylinder_i_swap (X : C) :
    (G.functorialCylinder X).i ≫ G.cylinderSwap X =
      (coprod.braiding X X).hom ≫ (G.functorialCylinder X).i := by
  simpa [functorialCylinder, cylinderSwap, foldSwap, foldArrow,
    MorphismProperty.FunctorialFactorizationData.factorizationData] using
    (G.cofibrationTrivialFibrationFactorization.i.naturality (foldSwap X)).symm

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem cylinder_i₀_swap (X : C) :
    (G.functorialCylinder X).i₀ ≫ G.cylinderSwap X =
      (G.functorialCylinder X).i₁ := by
  rw [← (G.functorialCylinder X).inl_i, Category.assoc, G.cylinder_i_swap]
  simp [coprod.braiding]

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem cylinder_i₁_swap (X : C) :
    (G.functorialCylinder X).i₁ ≫ G.cylinderSwap X =
      (G.functorialCylinder X).i₀ := by
  rw [← (G.functorialCylinder X).inr_i, Category.assoc, G.cylinder_i_swap]
  simp [coprod.braiding]

private def cylinderCone (X : C) : C :=
  pushout (G.functorialCylinder X).i₀ (0 : X ⟶ (0 : C))

private def cylinderConeInclusion (X : C) : X ⟶ G.cylinderCone X :=
  (G.functorialCylinder X).i₁ ≫ pushout.inl _ _

private theorem cylinderCone_weakZero (X : C) [IsCofibrant X] :
    WeakEquivalence (0 : (0 : C) ⟶ G.cylinderCone X) := by
  have h : pushout.inr (G.functorialCylinder X).i₀ (0 : X ⟶ (0 : C)) = 0 :=
    (isZero_zero C).eq_of_src _ _
  rw [← h]
  infer_instance

private theorem cylinderCone_isPushout (X : C) :
    IsPushout (G.functorialCylinder X).i
      (coprod.desc (0 : X ⟶ X) (𝟙 X))
      (pushout.inl (G.functorialCylinder X).i₀ (0 : X ⟶ (0 : C)))
      (G.cylinderConeInclusion X) := by
  apply IsPushout.mk'
  · apply coprod.hom_ext
    · simpa using pushout.condition (f := (G.functorialCylinder X).i₀)
        (g := (0 : X ⟶ (0 : C)))
    · simp [cylinderConeInclusion]
  · intro T a b h₁ h₂
    apply pushout.hom_ext
    · exact h₁
    · exact (isZero_zero C).eq_of_src _ _
  · intro T a b h
    have h₀ : (G.functorialCylinder X).i₀ ≫ a = 0 := by
      have hi := congrArg (fun k => coprod.inl ≫ k) h
      simpa using hi
    have h₁ : (G.functorialCylinder X).i₁ ≫ a = b := by
      have hi := congrArg (fun k => coprod.inr ≫ k) h
      simpa using hi
    refine ⟨pushout.desc a 0 (by simpa using h₀), by simp, ?_⟩
    simpa [cylinderConeInclusion] using h₁

private theorem cylinderConeInclusion_cofibration (X : C) :
    Cofibration (G.cylinderConeInclusion X) := by
  rw [cofibration_iff]
  exact MorphismProperty.of_isPushout (G.cylinderCone_isPushout X).flip
    (mem_cofibrations (G.functorialCylinder X).i)

private def cylinderSuspension (X : C) : C :=
  pushout (G.functorialCylinder X).i (0 : X ⨿ X ⟶ (0 : C))

private def cylinderSuspensionSwap (X : C) :
    G.cylinderSuspension X ⟶ G.cylinderSuspension X :=
  pushout.map _ _ _ _ (G.cylinderSwap X) (𝟙 (0 : C))
    (coprod.braiding X X).hom (G.cylinder_i_swap X) (by simp)

private theorem cylinderSuspensionSwap_sq (X : C) :
    G.cylinderSuspensionSwap X ≫ G.cylinderSuspensionSwap X = 𝟙 _ := by
  dsimp [cylinderSuspensionSwap, cylinderSuspension]
  apply pushout.hom_ext
  · simp only [pushout.inl_desc_assoc, pushout.inl_desc, Category.comp_id, Category.assoc]
    rw [← Category.assoc, G.cylinderSwap_sq, Category.id_comp]
  · exact (isZero_zero C).eq_of_src _ _

private theorem cylinderSuspension_isCofibrant (X : C) :
    IsCofibrant (G.cylinderSuspension X) := by
  apply (isCofibrant_iff_of_isInitial
    (pushout.inr (G.functorialCylinder X).i (0 : X ⨿ X ⟶ (0 : C)))
    (isZero_zero C).isInitial).2
  infer_instance

private theorem cylinderSuspension_i_comp (X : C) :
    (G.functorialCylinder X).i ≫
      pushout.inl (G.functorialCylinder X).i (0 : X ⨿ X ⟶ (0 : C)) = 0 := by
  simpa using pushout.condition (f := (G.functorialCylinder X).i)
    (g := (0 : X ⨿ X ⟶ (0 : C)))

private def cylinderConeQuotient (X : C) :
    G.cylinderCone X ⟶ G.cylinderSuspension X :=
  pushout.desc (pushout.inl (G.functorialCylinder X).i 0) 0 (by
    rw [← (G.functorialCylinder X).inl_i, Category.assoc, G.cylinderSuspension_i_comp]
    simp)

private theorem cylinderConeQuotient_isPushout (X : C) :
    IsPushout (G.cylinderConeInclusion X) (0 : X ⟶ (0 : C))
      (G.cylinderConeQuotient X) (0 : (0 : C) ⟶ G.cylinderSuspension X) := by
  apply IsPushout.mk'
  · dsimp [cylinderConeInclusion, cylinderConeQuotient]
    rw [Category.assoc, pushout.inl_desc, ← (G.functorialCylinder X).inr_i,
      Category.assoc, G.cylinderSuspension_i_comp]
    simp
  · intro T a b h₁ h₂
    apply pushout.hom_ext
    · have h := congrArg (fun k =>
        pushout.inl (G.functorialCylinder X).i₀ (0 : X ⟶ (0 : C)) ≫ k) h₁
      simpa [cylinderConeQuotient] using h
    · exact (isZero_zero C).eq_of_src _ _
  · intro T a b h
    refine ⟨pushout.desc (pushout.inl (G.functorialCylinder X).i₀ 0 ≫ a) b ?_, ?_, ?_⟩
    · apply coprod.hom_ext
      · simp only [← Category.assoc, (G.functorialCylinder X).inl_i]
        rw [pushout.condition]
        simp
      · simpa [cylinderConeInclusion] using h
    · apply pushout.hom_ext
      · simp [cylinderConeQuotient]
      · exact (isZero_zero C).eq_of_src _ _
    · exact (isZero_zero C).eq_of_src _ _

private def cylinderSuspensionIsoRaw (X : C) :
    G.cylinderSuspension X ≅
      pushout (G.cylinderConeInclusion X) (0 : X ⟶ (0 : C)) :=
  (G.cylinderConeQuotient_isPushout X).isoPushout

private def actualToRawCofiber (f : Arrow C) :
    G.cofiberFunctor.obj f ⟶ pushout f.hom (0 : f.left ⟶ (0 : C)) :=
  rawCofiberFunctor.map (G.cofibrantArrowComparison.app f)

private theorem actualToRawCofiber_weakEquivalence (f : Arrow C)
    [IsCofibrant f.left] [Cofibration f.hom] :
    WeakEquivalence (G.actualToRawCofiber f) := by
  letI := G.cofibrantArrowReplacement_source f
  letI : Cofibration (G.cofibrantArrowReplacement.obj f).hom :=
    (cofibration_iff _).2 (G.cofibrantArrowReplacement_cofibration f)
  letI : WeakEquivalence (G.cofibrantArrowComparison.app f).left :=
    (weakEquivalence_iff _).2 (G.cofibrantArrowComparison_weakEquivalences f).1
  letI : WeakEquivalence (G.cofibrantArrowComparison.app f).right :=
    (weakEquivalence_iff _).2 (G.cofibrantArrowComparison_weakEquivalences f).2
  exact rawCofiberFunctor_weakEquivalence (f := G.cofibrantArrowReplacement.obj f)
    (g := f) (G.cofibrantArrowComparison.app f)

private def cylinderConeArrow (X : C) : Arrow C :=
  Arrow.mk (G.cylinderConeInclusion X)

private def cylinderConeToZero (X : C) :
    G.cylinderConeArrow X ⟶ sourceZeroArrowFunctor.obj X :=
  Arrow.homMk (𝟙 X) 0 (by simp [cylinderConeArrow, sourceZeroArrowFunctor])

private theorem cylinderConeToZero_weakEquivalences (X : C) [IsCofibrant X] :
    (weakEquivalences C).arrow (G.cylinderConeToZero X) := by
  constructor
  · exact mem_weakEquivalences (𝟙 X)
  · letI := G.cylinderCone_weakZero X
    have h : (0 : (0 : C) ⟶ G.cylinderCone X) ≫ (0 : G.cylinderCone X ⟶ (0 : C)) =
        𝟙 (0 : C) := (isZero_zero C).eq_of_src _ _
    haveI : WeakEquivalence (0 : G.cylinderCone X ⟶ (0 : C)) :=
      weakEquivalence_of_precomp_of_fac h
    exact mem_weakEquivalences (0 : G.cylinderCone X ⟶ (0 : C))

private theorem actualConeCofiber_to_suspension_weakEquivalence (X : C) [IsCofibrant X] :
    weakEquivalences C (G.cofiberFunctor.map (G.cylinderConeToZero X)) :=
  G.cofiberFunctor_weakEquivalences _ (G.cylinderConeToZero_weakEquivalences X)

private theorem actualConeCofiber_to_raw_weakEquivalence (X : C) [IsCofibrant X] :
    WeakEquivalence (G.actualToRawCofiber (G.cylinderConeArrow X)) := by
  letI : IsCofibrant (G.cylinderConeArrow X).left := ‹IsCofibrant X›
  letI : Cofibration (G.cylinderConeArrow X).hom := G.cylinderConeInclusion_cofibration X
  exact G.actualToRawCofiber_weakEquivalence (G.cylinderConeArrow X)

private def localizedCylinderSuspensionIso
    {H : Type*} [Category* H] (L : C ⥤ H)
    [L.IsLocalization (weakEquivalences C)] (X : C) [IsCofibrant X] :
    L.obj (G.suspensionFunctor.obj X) ≅ L.obj (G.cylinderSuspension X) := by
  haveI : IsIso (L.map (G.cofiberFunctor.map (G.cylinderConeToZero X))) :=
    Localization.inverts L (weakEquivalences C) _
      (G.actualConeCofiber_to_suspension_weakEquivalence X)
  haveI : IsIso (L.map (G.actualToRawCofiber (G.cylinderConeArrow X))) :=
    Localization.inverts L (weakEquivalences C) _
      ((weakEquivalence_iff _).1 (G.actualConeCofiber_to_raw_weakEquivalence X))
  exact (asIso (L.map (G.cofiberFunctor.map (G.cylinderConeToZero X)))).symm ≪≫
    asIso (L.map (G.actualToRawCofiber (G.cylinderConeArrow X))) ≪≫
      L.mapIso (G.cylinderSuspensionIsoRaw X).symm

private def actualSuspensionInvolution
    {H : Type*} [Category* H] (L : C ⥤ H)
    [L.IsLocalization (weakEquivalences C)] (X : C) [IsCofibrant X] :
    L.obj (G.suspensionFunctor.obj X) ⟶ L.obj (G.suspensionFunctor.obj X) :=
  (G.localizedCylinderSuspensionIso L X).hom ≫
    L.map (G.cylinderSuspensionSwap X) ≫ (G.localizedCylinderSuspensionIso L X).inv

private theorem actualSuspensionInvolution_sq
    {H : Type*} [Category* H] (L : C ⥤ H)
    [L.IsLocalization (weakEquivalences C)] (X : C) [IsCofibrant X] :
    G.actualSuspensionInvolution L X ≫ G.actualSuspensionInvolution L X = 𝟙 _ := by
  simp only [actualSuspensionInvolution, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← L.map_comp_assoc, G.cylinderSuspensionSwap_sq, L.map_id,
    Category.id_comp, Iso.hom_inv_id]

end
end KIP126.StableHomotopy.CofibrantGeneration

end


@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
universe u v w z
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasZeroMorphisms C] [HasZeroObject C] (G : CofibrantGeneration C)
  {H : Type w} [Category.{z} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]
attribute [local instance] HasZeroObject.zero'
noncomputable section

private theorem actualToRawCofiber_naturality {f g : Arrow C} (φ : f ⟶ g) :
    G.cofiberFunctor.map φ ≫ G.actualToRawCofiber g =
      G.actualToRawCofiber f ≫ rawCofiberFunctor.map φ := by
  change rawCofiberFunctor.map (G.cofibrantArrowReplacement.map φ) ≫
      rawCofiberFunctor.map (G.cofibrantArrowComparison.app g) =
    rawCofiberFunctor.map (G.cofibrantArrowComparison.app f) ≫ rawCofiberFunctor.map φ
  rw [← rawCofiberFunctor.map_comp, ← rawCofiberFunctor.map_comp]
  exact congrArg (fun q => rawCofiberFunctor.map q)
    (G.cofibrantArrowComparison.naturality φ)

private theorem actualCofiber_maps_eq_of_postcomp {f g h : Arrow C}
    (φ ψ : f ⟶ g) (χ : g ⟶ h)
    (hχ : (weakEquivalences C).arrow χ) (heq : φ ≫ χ = ψ ≫ χ) :
    L.map (G.cofiberFunctor.map φ) = L.map (G.cofiberFunctor.map ψ) := by
  haveI : IsIso (L.map (G.cofiberFunctor.map χ)) :=
    Localization.inverts L (weakEquivalences C) _
      (G.cofiberFunctor_weakEquivalences χ hχ)
  apply (cancel_mono (L.map (G.cofiberFunctor.map χ))).1
  rw [← L.map_comp, ← L.map_comp, ← G.cofiberFunctor.map_comp,
    ← G.cofiberFunctor.map_comp, heq]

include G in
private theorem rawCofiber_maps_eq_of_postcomp {f g h : Arrow C}
    [IsCofibrant f.left] [IsCofibrant g.left]
    [Cofibration f.hom] [Cofibration g.hom]
    (φ ψ : f ⟶ g) (χ : g ⟶ h)
    (hχ : (weakEquivalences C).arrow χ) (heq : φ ≫ χ = ψ ≫ χ) :
    L.map (rawCofiberFunctor.map φ) = L.map (rawCofiberFunctor.map ψ) := by
  haveI : IsIso (L.map (G.actualToRawCofiber f)) :=
    Localization.inverts L (weakEquivalences C) _
      ((weakEquivalence_iff _).1 (G.actualToRawCofiber_weakEquivalence f))
  apply (cancel_epi (L.map (G.actualToRawCofiber f))).1
  rw [← L.map_comp, ← L.map_comp, ← G.actualToRawCofiber_naturality,
    ← G.actualToRawCofiber_naturality, L.map_comp, L.map_comp,
    G.actualCofiber_maps_eq_of_postcomp L φ ψ χ hχ heq]

private def cylinderArrow {X : C} (P : Cylinder X) : Arrow C := Arrow.mk P.i

private def cylinderQuotientMap {X : C} (P Q : Cylinder X)
    (s : P.I ⟶ Q.I) (hs : P.i ≫ s = Q.i) :
    pushout P.i (0 : X ⨿ X ⟶ (0 : C)) ⟶ pushout Q.i (0 : X ⨿ X ⟶ (0 : C)) :=
  rawCofiberFunctor.map (Arrow.homMk (𝟙 _) s (by simpa [cylinderArrow] using hs.symm) :
    cylinderArrow P ⟶ cylinderArrow Q)

include G in
private theorem cylinderQuotientMap_eq {X : C} [IsCofibrant X]
    (P Q : Cylinder X) [P.IsGood] [Q.IsGood]
    (s t : P.I ⟶ Q.I) (hs : P.i ≫ s = Q.i) (ht : P.i ≫ t = Q.i)
    (hπ : s ≫ Q.π = t ≫ Q.π) :
    L.map (cylinderQuotientMap P Q s hs) = L.map (cylinderQuotientMap P Q t ht) := by
  let φ : cylinderArrow P ⟶ cylinderArrow Q :=
    Arrow.homMk (𝟙 _) s (by simpa [cylinderArrow] using hs.symm)
  let ψ : cylinderArrow P ⟶ cylinderArrow Q :=
    Arrow.homMk (𝟙 _) t (by simpa [cylinderArrow] using ht.symm)
  let χ : cylinderArrow Q ⟶ foldArrow X := Arrow.homMk (𝟙 _) Q.π (by
    change 𝟙 _ ≫ codiag X = Q.i ≫ Q.π
    apply coprod.hom_ext <;> simp)
  have hχ : (weakEquivalences C).arrow χ :=
    ⟨mem_weakEquivalences (𝟙 _), mem_weakEquivalences Q.π⟩
  have heq : φ ≫ χ = ψ ≫ χ := by
    ext
    · rfl
    · exact hπ
  letI : IsCofibrant (cylinderArrow P).left := by
    change IsCofibrant (X ⨿ X)
    exact isCofibrant_of_cofibration (coprod.inl : X ⟶ X ⨿ X)
  letI : IsCofibrant (cylinderArrow Q).left := by
    change IsCofibrant (X ⨿ X)
    exact isCofibrant_of_cofibration (coprod.inl : X ⟶ X ⨿ X)
  letI : Cofibration (cylinderArrow P).hom := inferInstanceAs (Cofibration P.i)
  letI : Cofibration (cylinderArrow Q).hom := inferInstanceAs (Cofibration Q.i)
  exact G.rawCofiber_maps_eq_of_postcomp L φ ψ χ hχ heq

private def transCollapseLeft {X : C} [IsCofibrant X]
    (P : Cylinder X) [P.IsGood] : (P.trans P).I ⟶ P.I :=
  pushout.desc (𝟙 P.I) (P.π ≫ P.i₁) (by simp)

private def transCollapseRight {X : C} [IsCofibrant X]
    (P : Cylinder X) [P.IsGood] : (P.trans P).I ⟶ P.I :=
  pushout.desc (P.π ≫ P.i₀) (𝟙 P.I) (by simp)

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem transCollapseLeft_i {X : C} [IsCofibrant X]
    (P : Cylinder X) [P.IsGood] : (P.trans P).i ≫ transCollapseLeft P = P.i := by
  apply coprod.hom_ext <;>
    simp [transCollapseLeft, Precylinder.i, Cylinder.trans, Precylinder.trans]

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem transCollapseRight_i {X : C} [IsCofibrant X]
    (P : Cylinder X) [P.IsGood] : (P.trans P).i ≫ transCollapseRight P = P.i := by
  apply coprod.hom_ext <;>
    simp [transCollapseRight, Precylinder.i, Cylinder.trans, Precylinder.trans]

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem transCollapse_over_base {X : C} [IsCofibrant X]
    (P : Cylinder X) [P.IsGood] : transCollapseLeft P ≫ P.π = transCollapseRight P ≫ P.π := by
  apply pushout.hom_ext <;> simp [transCollapseLeft, transCollapseRight]

include G in
private theorem transCollapse_same_suspension {X : C} [IsCofibrant X]
    (P : Cylinder X) [P.IsGood] :
    L.map (cylinderQuotientMap (P.trans P) P (transCollapseLeft P) (transCollapseLeft_i P)) =
      L.map (cylinderQuotientMap (P.trans P) P (transCollapseRight P)
        (transCollapseRight_i P)) :=
  G.cylinderQuotientMap_eq L (P.trans P) P _ _ _ _ (transCollapse_over_base P)

end
end KIP126.StableHomotopy.CofibrantGeneration

end


@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasZeroMorphisms C] [HasZeroObject C] (G : CofibrantGeneration C)
attribute [local instance] HasZeroObject.zero'
noncomputable section

private def foldMap {A B : C} (f : A ⟶ B) : foldArrow A ⟶ foldArrow B :=
  Arrow.homMk (coprod.map f f) f (by
    dsimp [foldArrow]
    apply coprod.hom_ext <;> simp)

private def functorialCylinderMap {A B : C} (f : A ⟶ B) :
    (G.functorialCylinder A).I ⟶ (G.functorialCylinder B).I :=
  G.cofibrationTrivialFibrationFactorization.Z.map (foldMap f)

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem cylinder_i_map {A B : C} (f : A ⟶ B) :
    (G.functorialCylinder A).i ≫ G.functorialCylinderMap f =
      coprod.map f f ≫ (G.functorialCylinder B).i := by
  simpa [functorialCylinder, functorialCylinderMap, foldMap, foldArrow,
    MorphismProperty.FunctorialFactorizationData.factorizationData] using
    (G.cofibrationTrivialFibrationFactorization.i.naturality (foldMap f)).symm

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem cylinder_i₀_map {A B : C} (f : A ⟶ B) :
    (G.functorialCylinder A).i₀ ≫ G.functorialCylinderMap f =
      f ≫ (G.functorialCylinder B).i₀ := by
  rw [← (G.functorialCylinder A).inl_i, Category.assoc, G.cylinder_i_map]
  simp

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem cylinder_i₁_map {A B : C} (f : A ⟶ B) :
    (G.functorialCylinder A).i₁ ≫ G.functorialCylinderMap f =
      f ≫ (G.functorialCylinder B).i₁ := by
  rw [← (G.functorialCylinder A).inr_i, Category.assoc, G.cylinder_i_map]
  simp

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem cylinderSwap_naturality {A B : C} (f : A ⟶ B) :
    G.cylinderSwap A ≫ G.functorialCylinderMap f =
      G.functorialCylinderMap f ≫ G.cylinderSwap B := by
  change G.cofibrationTrivialFibrationFactorization.Z.map (foldSwap A) ≫
      G.cofibrationTrivialFibrationFactorization.Z.map (foldMap f) =
    G.cofibrationTrivialFibrationFactorization.Z.map (foldMap f) ≫
      G.cofibrationTrivialFibrationFactorization.Z.map (foldSwap B)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext
  · dsimp [foldSwap, foldMap]
    apply coprod.hom_ext <;> simp
  · change 𝟙 A ≫ f = f ≫ 𝟙 B
    simp

private def cylinderConeMap {A B : C} (f : A ⟶ B) :
    G.cylinderCone A ⟶ G.cylinderCone B :=
  pushout.map _ _ _ _ (G.functorialCylinderMap f) (𝟙 (0 : C)) f
    (G.cylinder_i₀_map f) (by simp)

private theorem cylinderConeInclusion_naturality {A B : C} (f : A ⟶ B) :
    G.cylinderConeInclusion A ≫ G.cylinderConeMap f =
      f ≫ G.cylinderConeInclusion B := by
  dsimp [cylinderConeInclusion, cylinderConeMap]
  simp only [Category.assoc, pushout.inl_desc]
  rw [← Category.assoc, G.cylinder_i₁_map, Category.assoc]

private def cylinderSuspensionMap {A B : C} (f : A ⟶ B) :
    G.cylinderSuspension A ⟶ G.cylinderSuspension B :=
  pushout.map _ _ _ _ (G.functorialCylinderMap f) (𝟙 (0 : C)) (coprod.map f f)
    (G.cylinder_i_map f) (by simp)

private theorem cylinderConeQuotient_naturality {A B : C} (f : A ⟶ B) :
    G.cylinderConeMap f ≫ G.cylinderConeQuotient B =
      G.cylinderConeQuotient A ≫ G.cylinderSuspensionMap f := by
  apply pushout.hom_ext
  · simp [cylinderConeMap, cylinderConeQuotient, cylinderSuspensionMap]
  · exact (isZero_zero C).eq_of_src _ _

private theorem cylinderSuspensionSwap_naturality {A B : C} (f : A ⟶ B) :
    G.cylinderSuspensionSwap A ≫ G.cylinderSuspensionMap f =
      G.cylinderSuspensionMap f ≫ G.cylinderSuspensionSwap B := by
  apply pushout.hom_ext
  · simp only [cylinderSuspensionSwap, cylinderSuspensionMap,
      pushout.inl_desc_assoc, pushout.inl_desc, Category.assoc]
    rw [← Category.assoc, G.cylinderSwap_naturality, Category.assoc]
  · exact (isZero_zero C).eq_of_src _ _



private def cylinderConeArrowMap {A B : C} (f : A ⟶ B) :
    G.cylinderConeArrow A ⟶ G.cylinderConeArrow B :=
  Arrow.homMk f (G.cylinderConeMap f)
    (G.cylinderConeInclusion_naturality f).symm

private theorem cylinderConeToZero_naturality {A B : C} (f : A ⟶ B) :
    G.cylinderConeArrowMap f ≫ G.cylinderConeToZero B =
      G.cylinderConeToZero A ≫ sourceZeroArrowFunctor.map f := by
  ext
  · change f ≫ 𝟙 B = 𝟙 A ≫ f
    simp
  · change G.cylinderConeMap f ≫ 0 = 0 ≫ 𝟙 (0 : C)
    simp

private theorem cylinderSuspensionIsoRaw_naturality {A B : C} (f : A ⟶ B) :
    rawCofiberFunctor.map (G.cylinderConeArrowMap f) ≫
      (G.cylinderSuspensionIsoRaw B).inv =
        (G.cylinderSuspensionIsoRaw A).inv ≫ G.cylinderSuspensionMap f := by
  apply pushout.hom_ext
  · simp only [rawCofiberFunctor, cylinderConeArrowMap, pushout.inl_desc_assoc]
    change (G.cylinderConeMap f ≫
      pushout.inl (G.cylinderConeInclusion B) (0 : B ⟶ (0 : C))) ≫
        (G.cylinderSuspensionIsoRaw B).inv =
      (pushout.inl (G.cylinderConeInclusion A) (0 : A ⟶ (0 : C))) ≫
        (G.cylinderSuspensionIsoRaw A).inv ≫ G.cylinderSuspensionMap f
    simp only [cylinderSuspensionIsoRaw, Category.assoc,
      IsPushout.inl_isoPushout_inv_assoc, IsPushout.inl_isoPushout_inv]
    exact G.cylinderConeQuotient_naturality f
  · exact (isZero_zero C).eq_of_src _ _

private theorem localizedCylinderSuspensionIso_cancel
    {H : Type*} [Category* H] (L : C ⥤ H)
    [L.IsLocalization (weakEquivalences C)] (A : C) [IsCofibrant A] :
    L.map (G.cofiberFunctor.map (G.cylinderConeToZero A)) ≫
      (G.localizedCylinderSuspensionIso L A).hom =
    L.map (G.actualToRawCofiber (G.cylinderConeArrow A)) ≫
      L.map (G.cylinderSuspensionIsoRaw A).inv := by
  haveI : IsIso (L.map (G.cofiberFunctor.map (G.cylinderConeToZero A))) :=
    Localization.inverts L (weakEquivalences C) _
      (G.actualConeCofiber_to_suspension_weakEquivalence A)
  simp only [localizedCylinderSuspensionIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv, Functor.mapIso_hom, IsIso.hom_inv_id_assoc]

private theorem localizedCylinderSuspensionIso_naturality
    {H : Type*} [Category* H] (L : C ⥤ H)
    [L.IsLocalization (weakEquivalences C)]
    {A B : C} (f : A ⟶ B) [IsCofibrant A] [IsCofibrant B] :
    L.map (G.suspensionFunctor.map f) ≫
      (G.localizedCylinderSuspensionIso L B).hom =
    (G.localizedCylinderSuspensionIso L A).hom ≫ L.map (G.cylinderSuspensionMap f) := by
  haveI : IsIso (L.map (G.cofiberFunctor.map (G.cylinderConeToZero A))) :=
    Localization.inverts L (weakEquivalences C) _
      (G.actualConeCofiber_to_suspension_weakEquivalence A)
  have hzero : L.map (G.cofiberFunctor.map (G.cylinderConeToZero A)) ≫
      L.map (G.suspensionFunctor.map f) =
    L.map (G.cofiberFunctor.map (G.cylinderConeArrowMap f)) ≫
      L.map (G.cofiberFunctor.map (G.cylinderConeToZero B)) := by
    rw [← L.map_comp, ← L.map_comp]
    change L.map (G.cofiberFunctor.map (G.cylinderConeToZero A) ≫
        G.cofiberFunctor.map (sourceZeroArrowFunctor.map f)) = _
    rw [← G.cofiberFunctor.map_comp, ← G.cofiberFunctor.map_comp,
      G.cylinderConeToZero_naturality]
  apply (cancel_epi (L.map (G.cofiberFunctor.map (G.cylinderConeToZero A)))).1
  rw [← Category.assoc, hzero, Category.assoc, G.localizedCylinderSuspensionIso_cancel,
    ← Category.assoc (L.map (G.cofiberFunctor.map (G.cylinderConeArrowMap f))),
    ← L.map_comp, G.actualToRawCofiber_naturality, L.map_comp, Category.assoc,
    ← L.map_comp, G.cylinderSuspensionIsoRaw_naturality, L.map_comp,
    ← Category.assoc, ← G.localizedCylinderSuspensionIso_cancel, Category.assoc]

private theorem actualSuspensionInvolution_naturality
    {H : Type*} [Category* H] (L : C ⥤ H)
    [L.IsLocalization (weakEquivalences C)]
    {A B : C} (f : A ⟶ B) [IsCofibrant A] [IsCofibrant B] :
    L.map (G.suspensionFunctor.map f) ≫ G.actualSuspensionInvolution L B =
      G.actualSuspensionInvolution L A ≫ L.map (G.suspensionFunctor.map f) := by
  have hi : L.map (G.cylinderSuspensionMap f) ≫
      (G.localizedCylinderSuspensionIso L B).inv =
    (G.localizedCylinderSuspensionIso L A).inv ≫
      L.map (G.suspensionFunctor.map f) := by
    have h := congrArg (fun k => (G.localizedCylinderSuspensionIso L A).inv ≫
      k ≫ (G.localizedCylinderSuspensionIso L B).inv)
        (G.localizedCylinderSuspensionIso_naturality L f)
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using h.symm
  dsimp [actualSuspensionInvolution]
  rw [← Category.assoc, G.localizedCylinderSuspensionIso_naturality, Category.assoc,
    ← L.map_comp_assoc, ← G.cylinderSuspensionSwap_naturality,
    L.map_comp, Category.assoc, hi]
  simp only [Category.assoc]

end
end KIP126.StableHomotopy.CofibrantGeneration
end
