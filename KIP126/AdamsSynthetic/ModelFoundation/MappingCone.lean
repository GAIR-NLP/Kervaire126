module
import all KIP126.AdamsSynthetic.ModelFoundation.Cylinder

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

private def mappingCylinder {A B : C} (f : A ⟶ B) : C :=
  pushout (G.functorialCylinder A).i₁ f

private def mappingCylinderEndpoint {A B : C} (f : A ⟶ B) :
    A ⟶ G.mappingCylinder f :=
  (G.functorialCylinder A).i₀ ≫ pushout.inl _ _

private def mappingCylinderInclusion {A B : C} (f : A ⟶ B) :
    B ⟶ G.mappingCylinder f := pushout.inr _ _

private def mappingCylinderProjection {A B : C} (f : A ⟶ B) :
    G.mappingCylinder f ⟶ B :=
  pushout.desc ((G.functorialCylinder A).π ≫ f) (𝟙 B) (by simp)

private def mappingCylinderCoproduct {A B : C} (f : A ⟶ B) :
    B ⨿ A ⟶ G.mappingCylinder f :=
  coprod.desc (G.mappingCylinderInclusion f) (G.mappingCylinderEndpoint f)

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem mappingCylinder_isPushout {A B : C} (f : A ⟶ B) :
    IsPushout (G.functorialCylinder A).i
      (coprod.desc (coprod.inr : A ⟶ B ⨿ A) (f ≫ coprod.inl))
      (pushout.inl (G.functorialCylinder A).i₁ f)
      (G.mappingCylinderCoproduct f) := by
  apply IsPushout.mk'
  · apply coprod.hom_ext
    · simp [mappingCylinderCoproduct, mappingCylinderEndpoint]
    · simpa [mappingCylinderCoproduct, mappingCylinderInclusion] using
        (pushout.condition (f := (G.functorialCylinder A).i₁) (g := f))
  · intro Z a b h₁ h₂
    apply pushout.hom_ext
    · exact h₁
    · have h := congrArg (fun k => coprod.inl ≫ k) h₂
      simpa [mappingCylinderCoproduct, mappingCylinderInclusion] using h
  · intro Z a b h
    have h₀ : (G.functorialCylinder A).i₀ ≫ a = coprod.inr ≫ b := by
      have h' := congrArg (fun k => coprod.inl ≫ k) h
      simpa using h'
    have h₁ : (G.functorialCylinder A).i₁ ≫ a = f ≫ coprod.inl ≫ b := by
      have h' := congrArg (fun k => coprod.inr ≫ k) h
      simpa using h'
    refine ⟨pushout.desc a (coprod.inl ≫ b) h₁, by simp, ?_⟩
    apply coprod.hom_ext
    · simp [mappingCylinderCoproduct, mappingCylinderInclusion]
    · simpa [mappingCylinderCoproduct, mappingCylinderEndpoint] using h₀

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem mappingCylinderEndpoint_cofibration {A B : C} (f : A ⟶ B)
    [IsCofibrant B] : Cofibration (G.mappingCylinderEndpoint f) := by
  haveI : Cofibration (G.mappingCylinderCoproduct f) := by
    rw [cofibration_iff]
    exact MorphismProperty.of_isPushout (G.mappingCylinder_isPushout f).flip
      (mem_cofibrations (G.functorialCylinder A).i)
  have he : G.mappingCylinderEndpoint f =
      (coprod.inr : A ⟶ B ⨿ A) ≫ G.mappingCylinderCoproduct f := by
    simp [mappingCylinderCoproduct]
  rw [he]
  infer_instance

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem mappingCylinderInclusion_weakEquivalence {A B : C} (f : A ⟶ B)
    [IsCofibrant A] : WeakEquivalence (G.mappingCylinderInclusion f) := by
  change WeakEquivalence (pushout.inr (G.functorialCylinder A).i₁ f)
  infer_instance

omit [HasZeroMorphisms C] [HasZeroObject C] in
private theorem mappingCylinderProjection_weakEquivalence {A B : C} (f : A ⟶ B)
    [IsCofibrant A] : WeakEquivalence (G.mappingCylinderProjection f) := by
  letI := G.mappingCylinderInclusion_weakEquivalence f
  have h : G.mappingCylinderInclusion f ≫ G.mappingCylinderProjection f = 𝟙 B := by
    simp [mappingCylinderInclusion, mappingCylinderProjection]
  exact weakEquivalence_of_precomp_of_fac h

private def mappingCylinderComparison {A B : C} (f : A ⟶ B) :
    Arrow.mk (G.mappingCylinderEndpoint f) ⟶ Arrow.mk f :=
  Arrow.homMk (𝟙 A) (G.mappingCylinderProjection f) (by
    simp [mappingCylinderEndpoint, mappingCylinderProjection])

private def mappingConeCollapse {A B : C} (f : A ⟶ B) :
    pushout (G.mappingCylinderEndpoint f) (0 : A ⟶ (0 : C)) ⟶
      pushout f (0 : A ⟶ (0 : C)) :=
  rawCofiberFunctor.map (G.mappingCylinderComparison f)

private theorem mappingConeCollapse_weakEquivalence {A B : C} (f : A ⟶ B)
    [IsCofibrant A] [Cofibration f] :
    WeakEquivalence (G.mappingConeCollapse f) := by
  haveI : IsCofibrant B := isCofibrant_of_cofibration f
  letI := G.mappingCylinderEndpoint_cofibration f
  letI : IsCofibrant (Arrow.mk (G.mappingCylinderEndpoint f)).left := ‹IsCofibrant A›
  letI : IsCofibrant (Arrow.mk f).left := ‹IsCofibrant A›
  letI : Cofibration (Arrow.mk (G.mappingCylinderEndpoint f)).hom :=
    G.mappingCylinderEndpoint_cofibration f
  letI : Cofibration (Arrow.mk f).hom := ‹Cofibration f›
  haveI : WeakEquivalence (G.mappingCylinderComparison f).left := by
    change WeakEquivalence (𝟙 A)
    infer_instance
  haveI : WeakEquivalence (G.mappingCylinderComparison f).right :=
    G.mappingCylinderProjection_weakEquivalence f
  exact rawCofiberFunctor_weakEquivalence (G.mappingCylinderComparison f)


private def mappingCone {A B : C} (f : A ⟶ B) : C :=
  pushout (G.mappingCylinderEndpoint f) (0 : A ⟶ (0 : C))

private def mappingConeInclusion {A B : C} (f : A ⟶ B) : B ⟶ G.mappingCone f :=
  G.mappingCylinderInclusion f ≫ pushout.inl _ _

private def coneToMappingCone {A B : C} (f : A ⟶ B) :
    G.cylinderCone A ⟶ G.mappingCone f :=
  pushout.desc
    (pushout.inl (G.functorialCylinder A).i₁ f ≫
      pushout.inl (G.mappingCylinderEndpoint f) 0) 0 (by
    simpa only [mappingCylinderEndpoint, Category.assoc, zero_comp] using
      pushout.condition (f := G.mappingCylinderEndpoint f)
      (g := (0 : A ⟶ (0 : C))))

private theorem mappingCone_isPushout {A B : C} (f : A ⟶ B) :
    IsPushout f (G.cylinderConeInclusion A)
      (G.mappingConeInclusion f) (G.coneToMappingCone f) := by
  apply IsPushout.mk'
  · dsimp [mappingConeInclusion, mappingCylinderInclusion,
      cylinderConeInclusion, coneToMappingCone, mappingCylinder]
    rw [Category.assoc, pushout.inl_desc]
    simpa only [Category.assoc] using
      congrArg (fun h => h ≫ pushout.inl (G.mappingCylinderEndpoint f)
        (0 : A ⟶ (0 : C)))
        (pushout.condition (f := (G.functorialCylinder A).i₁) (g := f)).symm
  · intro Z a b h₁ h₂
    apply pushout.hom_ext
    · apply pushout.hom_ext
      · have h := congrArg (fun k =>
          pushout.inl (G.functorialCylinder A).i₀ (0 : A ⟶ (0 : C)) ≫ k) h₂
        simpa [coneToMappingCone] using h
      · simpa [mappingConeInclusion, mappingCylinderInclusion] using h₁
    · exact (isZero_zero C).eq_of_src _ _
  · intro Z a b h
    let v : G.mappingCylinder f ⟶ Z :=
      pushout.desc (pushout.inl (G.functorialCylinder A).i₀ 0 ≫ b) a (by
        simpa [cylinderConeInclusion, Category.assoc] using h.symm)
    have hv : G.mappingCylinderEndpoint f ≫ v = 0 := by
      dsimp [mappingCylinderEndpoint, v]
      rw [Category.assoc, pushout.inl_desc, ← Category.assoc, pushout.condition]
      simp
    refine ⟨pushout.desc v 0 (by simpa using hv), ?_, ?_⟩
    · simp [mappingConeInclusion, mappingCylinderInclusion, v]
    · apply pushout.hom_ext
      · simp [coneToMappingCone, v]
      · exact (isZero_zero C).eq_of_src _ _

private theorem mappingConeInclusion_cofibration {A B : C} (f : A ⟶ B) :
    Cofibration (G.mappingConeInclusion f) := by
  rw [cofibration_iff]
  exact MorphismProperty.of_isPushout (G.mappingCone_isPushout f)
    ((cofibration_iff _).1 (G.cylinderConeInclusion_cofibration A))

private def mappingConeToSuspension {A B : C} (f : A ⟶ B) :
    G.mappingCone f ⟶ G.cylinderSuspension A :=
  (G.mappingCone_isPushout f).desc 0 (G.cylinderConeQuotient A) (by
    have h := (G.cylinderConeQuotient_isPushout A).w
    simpa using h.symm)

private theorem mappingConeToSuspension_isPushout {A B : C} (f : A ⟶ B) :
    IsPushout (G.mappingConeInclusion f) (0 : B ⟶ (0 : C))
      (G.mappingConeToSuspension f) (0 : (0 : C) ⟶ G.cylinderSuspension A) := by
  have hc : G.mappingConeInclusion f ≫ G.mappingConeToSuspension f = 0 := by
    simp [mappingConeToSuspension]
  have hd : G.coneToMappingCone f ≫ G.mappingConeToSuspension f =
      G.cylinderConeQuotient A := by
    simp [mappingConeToSuspension]
  have h := G.cylinderConeQuotient_isPushout A
  have h' : IsPushout (G.cylinderConeInclusion A)
      (f ≫ (0 : B ⟶ (0 : C)))
      (G.coneToMappingCone f ≫ G.mappingConeToSuspension f)
      (0 : (0 : C) ⟶ G.cylinderSuspension A) := by
    simpa only [comp_zero, hd] using h
  exact h'.of_top (by simpa using hc) (G.mappingCone_isPushout f).flip

private def mappingConeSecondCofiberIso {A B : C} (f : A ⟶ B) :
    pushout (G.mappingConeInclusion f) (0 : B ⟶ (0 : C)) ≅
      G.cylinderSuspension A :=
  (G.mappingConeToSuspension_isPushout f).isoPushout.symm


private def mappingConeInclusionComparison {A B : C} (f : A ⟶ B) :
    Arrow.mk (G.mappingConeInclusion f) ⟶
      Arrow.mk (pushout.inl f (0 : A ⟶ (0 : C))) :=
  Arrow.homMk (𝟙 B) (G.mappingConeCollapse f) (by
    simp [mappingConeInclusion, mappingConeCollapse, rawCofiberFunctor,
      mappingCylinderComparison, mappingCylinderInclusion, mappingCylinderProjection])

private theorem mappingConeInclusionComparison_weakEquivalences
    {A B : C} (f : A ⟶ B) [IsCofibrant A] [Cofibration f] :
    (weakEquivalences C).arrow (G.mappingConeInclusionComparison f) := by
  constructor
  · exact mem_weakEquivalences (𝟙 B)
  · exact (weakEquivalence_iff _).1 (G.mappingConeCollapse_weakEquivalence f)

private def actualSecondCofiberIso
    {H : Type*} [Category* H] (L : C ⥤ H)
    [L.IsLocalization (weakEquivalences C)]
    {A B : C} (f : A ⟶ B) [IsCofibrant A] [Cofibration f] :
    L.obj (G.cofiberFunctor.obj (Arrow.mk (pushout.inl f (0 : A ⟶ (0 : C))))) ≅
      L.obj (G.suspensionFunctor.obj A) := by
  haveI : IsCofibrant B := isCofibrant_of_cofibration f
  letI : IsCofibrant (Arrow.mk (G.mappingConeInclusion f)).left := ‹IsCofibrant B›
  letI : Cofibration (Arrow.mk (G.mappingConeInclusion f)).hom :=
    G.mappingConeInclusion_cofibration f
  haveI : IsIso (L.map (G.cofiberFunctor.map (G.mappingConeInclusionComparison f))) :=
    Localization.inverts L (weakEquivalences C) _
      (G.cofiberFunctor_weakEquivalences _
        (G.mappingConeInclusionComparison_weakEquivalences f))
  haveI : IsIso (L.map (G.actualToRawCofiber (Arrow.mk (G.mappingConeInclusion f)))) :=
    Localization.inverts L (weakEquivalences C) _
      ((weakEquivalence_iff _).1 (G.actualToRawCofiber_weakEquivalence
        (Arrow.mk (G.mappingConeInclusion f))))
  exact (asIso (L.map (G.cofiberFunctor.map
      (G.mappingConeInclusionComparison f)))).symm ≪≫
    asIso (L.map (G.actualToRawCofiber (Arrow.mk (G.mappingConeInclusion f)))) ≪≫
      L.mapIso (G.mappingConeSecondCofiberIso f) ≪≫
        (G.localizedCylinderSuspensionIso L A).symm



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

private theorem mappingConeCollapse_on_inclusion {A B : C} (f : A ⟶ B) :
    G.mappingConeInclusion f ≫ G.mappingConeCollapse f =
      pushout.inl f (0 : A ⟶ (0 : C)) := by
  simp [mappingConeInclusion, mappingCylinderInclusion, mappingConeCollapse,
    rawCofiberFunctor, mappingCylinderComparison, mappingCylinderProjection]

private theorem mappingConeCollapse_on_cone {A B : C} (f : A ⟶ B) :
    G.coneToMappingCone f ≫ G.mappingConeCollapse f = 0 := by
  apply pushout.hom_ext
  · simp only [coneToMappingCone, pushout.inl_desc_assoc]
    dsimp [mappingConeCollapse, rawCofiberFunctor, mappingCylinderComparison,
      mappingCylinderProjection]
    simp only [Category.assoc, pushout.inl_desc, pushout.inl_desc_assoc]
    change (G.functorialCylinder A).π ≫ f ≫
      pushout.inl f (0 : A ⟶ (0 : C)) = _
    rw [pushout.condition]
    simp
  · exact (isZero_zero C).eq_of_src _ _

private def doubleConeToSecondCone {A B : C} (f : A ⟶ B) :
    pushout (G.cylinderConeInclusion A) (G.cylinderConeInclusion A) ⟶
      G.mappingCone (G.mappingConeInclusion f) :=
  pushout.desc
    (G.coneToMappingCone f ≫ G.mappingConeInclusion (G.mappingConeInclusion f))
    (G.cylinderConeMap f ≫ G.coneToMappingCone (G.mappingConeInclusion f)) (by
      rw [← Category.assoc, ← (G.mappingCone_isPushout f).w,
        Category.assoc, (G.mappingCone_isPushout (G.mappingConeInclusion f)).w,
        ← Category.assoc, ← G.cylinderConeInclusion_naturality, Category.assoc])

private def secondConeToFirstSuspension {A B : C} (f : A ⟶ B) :
    G.mappingCone (G.mappingConeInclusion f) ⟶ G.cylinderSuspension A :=
  G.mappingConeCollapse (G.mappingConeInclusion f) ≫
    (G.mappingConeSecondCofiberIso f).hom

private theorem secondCofiberIso_inclusion {A B : C} (f : A ⟶ B) :
    pushout.inl (G.mappingConeInclusion f) (0 : B ⟶ (0 : C)) ≫
      (G.mappingConeSecondCofiberIso f).hom = G.mappingConeToSuspension f :=
  (G.mappingConeToSuspension_isPushout f).inl_isoPushout_inv

private theorem doubleConeToSecondCone_first {A B : C} (f : A ⟶ B) :
    G.doubleConeToSecondCone f ≫ G.secondConeToFirstSuspension f =
      pushout.desc (G.cylinderConeQuotient A) 0
        (by simpa using (G.cylinderConeQuotient_isPushout A).w) := by
  apply pushout.hom_ext
  · simp only [doubleConeToSecondCone, secondConeToFirstSuspension,
      pushout.inl_desc_assoc, pushout.inl_desc, Category.assoc]
    rw [← Category.assoc (G.mappingConeInclusion (G.mappingConeInclusion f)),
      G.mappingConeCollapse_on_inclusion, G.secondCofiberIso_inclusion]
    simp [mappingConeToSuspension]
  · simp only [doubleConeToSecondCone, secondConeToFirstSuspension,
      pushout.inr_desc_assoc, pushout.inr_desc, Category.assoc]
    rw [← Category.assoc (G.coneToMappingCone (G.mappingConeInclusion f)),
      G.mappingConeCollapse_on_cone, zero_comp, comp_zero]

private theorem doubleConeToSecondCone_second {A B : C} (f : A ⟶ B) :
    G.doubleConeToSecondCone f ≫
      G.mappingConeToSuspension (G.mappingConeInclusion f) =
      pushout.desc 0 (G.cylinderConeQuotient A)
        (by simpa using (G.cylinderConeQuotient_isPushout A).w.symm) ≫
          G.cylinderSuspensionMap f := by
  apply pushout.hom_ext
  · simp [doubleConeToSecondCone, mappingConeToSuspension]
  · simp only [doubleConeToSecondCone, pushout.inr_desc_assoc, Category.assoc]
    simp only [mappingConeToSuspension, IsPushout.inr_desc]
    exact G.cylinderConeQuotient_naturality f

private theorem secondConeToFirstSuspension_weakEquivalence
    {A B : C} (f : A ⟶ B) [IsCofibrant B] :
    WeakEquivalence (G.secondConeToFirstSuspension f) := by
  letI := G.mappingConeInclusion_cofibration f
  letI := G.mappingConeCollapse_weakEquivalence (G.mappingConeInclusion f)
  dsimp [secondConeToFirstSuspension]
  infer_instance

end
end KIP126.StableHomotopy.CofibrantGeneration
end
