module
import all KIP126.AdamsSynthetic.ModelFoundation.MappingCone
import all KIP126.AdamsSynthetic.ModelFoundation.Triangles
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Triangulated.Rotate

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
universe u v w z
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasZeroMorphisms C] [HasZeroObject C] (G : CofibrantGeneration C)
attribute [local instance] HasZeroObject.zero'
noncomputable section

private def doubleCone (X : C) : C :=
  pushout (G.cylinderConeInclusion X) (G.cylinderConeInclusion X)

private def doubleConeFirst (X : C) : G.doubleCone X ⟶ G.cylinderSuspension X :=
  pushout.desc (G.cylinderConeQuotient X) 0 (by
    simpa using (G.cylinderConeQuotient_isPushout X).w)

private def doubleConeSecond (X : C) : G.doubleCone X ⟶ G.cylinderSuspension X :=
  pushout.desc 0 (G.cylinderConeQuotient X) (by
    simpa using (G.cylinderConeQuotient_isPushout X).w.symm)

private theorem mappingConeCollapse_inclusion {A B : C} (f : A ⟶ B) :
    G.mappingConeInclusion f ≫ G.mappingConeCollapse f =
      pushout.inl f (0 : A ⟶ (0 : C)) := by
  simp [mappingConeInclusion, mappingCylinderInclusion, mappingConeCollapse,
    rawCofiberFunctor, mappingCylinderComparison, mappingCylinderProjection]

private theorem mappingConeCollapse_cone {A B : C} (f : A ⟶ B) :
    G.coneToMappingCone f ≫ G.mappingConeCollapse f = 0 := by
  apply pushout.hom_ext
  · simp only [coneToMappingCone, pushout.inl_desc_assoc]
    dsimp [mappingConeCollapse, rawCofiberFunctor, mappingCylinderComparison,
      mappingCylinderProjection]
    simp only [Category.assoc, pushout.inl_desc, pushout.inl_desc_assoc]
    simp only [comp_zero]
    change (G.functorialCylinder A).π ≫ f ≫
      pushout.inl f (0 : A ⟶ (0 : C)) = 0
    rw [pushout.condition]
    simp
  · exact (isZero_zero C).eq_of_src _ _

private theorem doubleConeFirst_eq (X : C) :
    G.doubleConeFirst X =
      (G.mappingCone_isPushout (G.cylinderConeInclusion X)).isoPushout.inv ≫
        G.mappingConeCollapse (G.cylinderConeInclusion X) ≫
          (G.cylinderSuspensionIsoRaw X).inv := by
  apply pushout.hom_ext
  · simp only [doubleConeFirst, pushout.inl_desc, ← Category.assoc,
      IsPushout.inl_isoPushout_inv]
    rw [G.mappingConeCollapse_inclusion]
    exact (G.cylinderConeQuotient_isPushout X).inl_isoPushout_inv.symm
  · simp only [doubleConeFirst, pushout.inr_desc, ← Category.assoc,
      IsPushout.inr_isoPushout_inv]
    rw [G.mappingConeCollapse_cone, zero_comp]

private theorem doubleConeFirst_weakEquivalence (X : C) [IsCofibrant X] :
    WeakEquivalence (G.doubleConeFirst X) := by
  letI := G.cylinderConeInclusion_cofibration X
  letI := G.mappingConeCollapse_weakEquivalence (G.cylinderConeInclusion X)
  rw [G.doubleConeFirst_eq]
  infer_instance

private theorem doubleConeSecond_weakEquivalence (X : C) [IsCofibrant X] :
    WeakEquivalence (G.doubleConeSecond X) := by
  have h : G.doubleConeSecond X =
      (pushoutSymmetry (G.cylinderConeInclusion X) (G.cylinderConeInclusion X)).hom ≫
        G.doubleConeFirst X := by
    apply pushout.hom_ext <;> simp [doubleConeFirst, doubleConeSecond]
  rw [h]
  letI := G.doubleConeFirst_weakEquivalence X
  infer_instance

private def doubleConePinch (X : C) :
    G.doubleCone X ⟶ G.cylinderSuspension X ⨿ G.cylinderSuspension X :=
  pushout.desc (G.cylinderConeQuotient X ≫ coprod.inl)
    (G.cylinderConeQuotient X ≫ coprod.inr) (by
      have h : G.cylinderConeInclusion X ≫ G.cylinderConeQuotient X = 0 := by
        simpa using (G.cylinderConeQuotient_isPushout X).w
      simp only [← Category.assoc, h, zero_comp])

private theorem doubleConePinch_first (X : C) :
    G.doubleConePinch X ≫ coprod.desc (𝟙 _) 0 = G.doubleConeFirst X := by
  apply pushout.hom_ext <;> simp [doubleConePinch, doubleConeFirst]

private theorem doubleConePinch_second (X : C) :
    G.doubleConePinch X ≫ coprod.desc 0 (𝟙 _) = G.doubleConeSecond X := by
  apply pushout.hom_ext <;> simp [doubleConePinch, doubleConeSecond]

private theorem doubleConePinch_fold (X : C) :
    G.doubleConePinch X ≫ codiag (G.cylinderSuspension X) =
      pushout.desc (𝟙 (G.cylinderCone X)) (𝟙 (G.cylinderCone X)) (by simp) ≫
        G.cylinderConeQuotient X := by
  apply pushout.hom_ext <;> simp [doubleConePinch]

variable {H : Type w} [Category.{z} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)] [Preadditive H]

private theorem localized_codiag_eq_sum (X : C) [IsCofibrant X] :
    L.map (codiag X) = L.map (coprod.desc (𝟙 X) (0 : X ⟶ X)) +
      L.map (coprod.desc (0 : X ⟶ X) (𝟙 X)) := by
  letI := localization_preservesZeroMorphisms L (weakEquivalences C)
  apply ModelFoundation.localizedCoprod_hom_ext L X X <;>
    simp [Preadditive.comp_add, ← L.map_comp]

private theorem doubleCone_sum_zero (X : C) [IsCofibrant X] :
    L.map (G.doubleConeFirst X) + L.map (G.doubleConeSecond X) = 0 := by
  letI := localization_preservesZeroMorphisms L (weakEquivalences C)
  letI := G.cylinderSuspension_isCofibrant X
  haveI : IsIso (L.map (0 : (0 : C) ⟶ G.cylinderCone X)) :=
    Localization.inverts L (weakEquivalences C) _
      ((weakEquivalence_iff _).1 (G.cylinderCone_weakZero X))
  have hz : IsZero (L.obj (G.cylinderCone X)) :=
    (localization_isZero L (weakEquivalences C)).of_iso
      (asIso (L.map (0 : (0 : C) ⟶ G.cylinderCone X))).symm
  rw [← G.doubleConePinch_first, ← G.doubleConePinch_second,
    L.map_comp, L.map_comp, ← Preadditive.comp_add,
    ← localized_codiag_eq_sum L, ← L.map_comp, G.doubleConePinch_fold, L.map_comp,
    hz.eq_of_src (L.map (G.cylinderConeQuotient X)) 0, comp_zero]

private def doubleConeReflection (X : C) [IsCofibrant X] :
    L.obj (G.cylinderSuspension X) ⟶ L.obj (G.cylinderSuspension X) :=
  haveI : IsIso (L.map (G.doubleConeFirst X)) :=
    Localization.inverts L (weakEquivalences C) _
      ((weakEquivalence_iff _).1 (G.doubleConeFirst_weakEquivalence X))
  inv (L.map (G.doubleConeFirst X)) ≫ L.map (G.doubleConeSecond X)

private theorem doubleConeReflection_eq_neg_id (X : C) [IsCofibrant X] :
    G.doubleConeReflection L X = -𝟙 (L.obj (G.cylinderSuspension X)) := by
  haveI : IsIso (L.map (G.doubleConeFirst X)) :=
    Localization.inverts L (weakEquivalences C) _
      ((weakEquivalence_iff _).1 (G.doubleConeFirst_weakEquivalence X))
  have h : L.map (G.doubleConeSecond X) = - L.map (G.doubleConeFirst X) :=
    eq_neg_of_add_eq_zero_right (G.doubleCone_sum_zero L X)
  dsimp [doubleConeReflection]
  rw [h, Preadditive.comp_neg, IsIso.inv_hom_id]

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
attribute [local instance] HasZeroObject.zero'
noncomputable section

private def mappingCylinderToCone {A B : C} (f : A ⟶ B) :
    G.mappingCylinder f ⟶ G.cylinderCone A :=
  pushout.desc (G.cylinderSwap A ≫ pushout.inl (G.functorialCylinder A).i₀ 0) 0 (by
    rw [← Category.assoc, G.cylinder_i₁_swap]
    simpa using pushout.condition (f := (G.functorialCylinder A).i₀)
      (g := (0 : A ⟶ (0 : C))))

private def mappingCylinderBoundarySquare {A B : C} (f : A ⟶ B) :
    Arrow.mk (G.mappingCylinderEndpoint f) ⟶ G.cylinderConeArrow A :=
  Arrow.homMk (𝟙 A) (G.mappingCylinderToCone f) (by
    dsimp [mappingCylinderEndpoint, mappingCylinderToCone, cylinderConeArrow,
      cylinderConeInclusion]
    rw [Category.id_comp, Category.assoc, pushout.inl_desc,
      ← Category.assoc, G.cylinder_i₀_swap])

private theorem mappingCylinderBoundarySquare_to_zero {A B : C} (f : A ⟶ B) :
    G.mappingCylinderBoundarySquare f ≫ G.cylinderConeToZero A =
      G.mappingCylinderComparison f ≫ arrowToSourceZero.app (Arrow.mk f) := by
  ext <;> simp [mappingCylinderBoundarySquare, cylinderConeToZero,
    mappingCylinderComparison, arrowToSourceZero]

private theorem mappingConeToSuspension_cylinder {A B : C} (f : A ⟶ B) :
    pushout.inl (G.functorialCylinder A).i₁ f ≫
      pushout.inl (G.mappingCylinderEndpoint f) (0 : A ⟶ (0 : C)) ≫
        G.mappingConeToSuspension f =
      pushout.inl (G.functorialCylinder A).i (0 : A ⨿ A ⟶ (0 : C)) := by
  have h : G.coneToMappingCone f ≫ G.mappingConeToSuspension f =
      G.cylinderConeQuotient A := by simp [mappingConeToSuspension]
  have h' := congrArg (fun k =>
    pushout.inl (G.functorialCylinder A).i₀ (0 : A ⟶ (0 : C)) ≫ k) h
  simpa [coneToMappingCone, cylinderConeQuotient] using h'

private theorem mappingCylinderBoundary_raw {A B : C} (f : A ⟶ B) :
    rawCofiberFunctor.map (G.mappingCylinderBoundarySquare f) ≫
      (G.cylinderSuspensionIsoRaw A).inv =
        G.mappingConeToSuspension f ≫ G.cylinderSuspensionSwap A := by
  dsimp only [rawCofiberFunctor, mappingCylinderBoundarySquare, cylinderConeArrow]
  apply pushout.hom_ext
  · simp only [pushout.inl_desc_assoc]
    rw [Category.assoc]
    change G.mappingCylinderToCone f ≫
      pushout.inl (G.cylinderConeInclusion A) (0 : A ⟶ (0 : C)) ≫
        (G.cylinderConeQuotient_isPushout A).isoPushout.inv =
      pushout.inl (G.mappingCylinderEndpoint f) (0 : A ⟶ (0 : C)) ≫
        G.mappingConeToSuspension f ≫ G.cylinderSuspensionSwap A
    rw [(G.cylinderConeQuotient_isPushout A).inl_isoPushout_inv]
    apply pushout.hom_ext
    · simp only [mappingCylinderToCone, pushout.inl_desc_assoc, Category.assoc,
        cylinderConeQuotient, pushout.inl_desc]
      calc
        _ = pushout.inl (G.functorialCylinder A).i (0 : A ⨿ A ⟶ (0 : C)) ≫
            G.cylinderSuspensionSwap A := by simp [cylinderSuspensionSwap]
        _ = _ := by
          simpa only [Category.assoc] using
            (congrArg (fun k => k ≫ G.cylinderSuspensionSwap A)
              (G.mappingConeToSuspension_cylinder f)).symm
    · simp only [mappingCylinderToCone, pushout.inr_desc_assoc, zero_comp]
      have h : G.mappingConeInclusion f ≫ G.mappingConeToSuspension f = 0 := by
        simp [mappingConeToSuspension]
      simpa only [mappingConeInclusion, mappingCylinderInclusion, Category.assoc, zero_comp]
        using (congrArg (fun k => k ≫ G.cylinderSuspensionSwap A) h).symm
  · exact (isZero_zero C).eq_of_src _ _

private instance localizedMappingConeCollapse_isIso
    {H : Type w} [Category.{z} H] (L : C ⥤ H)
    [L.IsLocalization (weakEquivalences C)] {A B : C} (f : A ⟶ B)
    [IsCofibrant A] [Cofibration f] : IsIso (L.map (G.mappingConeCollapse f)) :=
  Localization.inverts L (weakEquivalences C) _
    ((weakEquivalence_iff _).1 (G.mappingConeCollapse_weakEquivalence f))

private theorem actualBoundary_mappingCone_roof
    {H : Type w} [Category.{z} H] (L : C ⥤ H)
    [L.IsLocalization (weakEquivalences C)] {A B : C} (f : A ⟶ B)
    [IsCofibrant A] [Cofibration f] :
    L.map (G.cofiberBoundary.app (Arrow.mk f)) ≫
        (G.localizedCylinderSuspensionIso L A).hom =
      L.map (G.actualToRawCofiber (Arrow.mk f)) ≫
        inv (L.map (G.mappingConeCollapse f)) ≫
          L.map (G.mappingConeToSuspension f) ≫ L.map (G.cylinderSuspensionSwap A) := by
  haveI : IsIso (L.map (G.mappingConeCollapse f)) :=
    Localization.inverts L (weakEquivalences C) _
      ((weakEquivalence_iff _).1 (G.mappingConeCollapse_weakEquivalence f))
  have hχ : (weakEquivalences C).arrow (G.mappingCylinderComparison f) := by
    refine ⟨mem_weakEquivalences (𝟙 A), ?_⟩
    exact (weakEquivalence_iff _).1 (G.mappingCylinderProjection_weakEquivalence f)
  haveI : IsIso (L.map (G.cofiberFunctor.map (G.mappingCylinderComparison f))) :=
    Localization.inverts L (weakEquivalences C) _
      (G.cofiberFunctor_weakEquivalences _ hχ)
  haveI : IsIso (L.map (G.cofiberFunctor.map (G.cylinderConeToZero A))) :=
    Localization.inverts L (weakEquivalences C) _
      (G.actualConeCofiber_to_suspension_weakEquivalence A)
  have hcomp : G.cofiberFunctor.map (G.mappingCylinderComparison f) ≫
      G.cofiberBoundary.app (Arrow.mk f) =
        G.cofiberFunctor.map (G.mappingCylinderBoundarySquare f) ≫
          G.cofiberFunctor.map (G.cylinderConeToZero A) := by
    change G.cofiberFunctor.map (G.mappingCylinderComparison f) ≫
      G.cofiberFunctor.map (arrowToSourceZero.app (Arrow.mk f)) = _
    rw [← G.cofiberFunctor.map_comp, ← G.cofiberFunctor.map_comp,
      G.mappingCylinderBoundarySquare_to_zero]
  have hβ : L.map (G.cofiberFunctor.map (G.cylinderConeToZero A)) ≫
      (G.localizedCylinderSuspensionIso L A).hom =
        L.map (G.actualToRawCofiber (G.cylinderConeArrow A)) ≫
          L.map (G.cylinderSuspensionIsoRaw A).inv := by
    simp [localizedCylinderSuspensionIso]
  have hα := congrArg (fun k => L.map k)
    (G.actualToRawCofiber_naturality (G.mappingCylinderBoundarySquare f))
  simp only [L.map_comp] at hα
  have hχnat := congrArg (fun k => L.map k)
    (G.actualToRawCofiber_naturality (G.mappingCylinderComparison f))
  change L.map (G.cofiberFunctor.map (G.mappingCylinderComparison f) ≫
      G.actualToRawCofiber (Arrow.mk f)) =
    L.map (G.actualToRawCofiber (Arrow.mk (G.mappingCylinderEndpoint f)) ≫
      G.mappingConeCollapse f) at hχnat
  simp only [L.map_comp] at hχnat
  apply (cancel_epi (L.map (G.cofiberFunctor.map (G.mappingCylinderComparison f)))).1
  calc
    _ = L.map (G.cofiberFunctor.map (G.mappingCylinderBoundarySquare f)) ≫
        L.map (G.cofiberFunctor.map (G.cylinderConeToZero A)) ≫
          (G.localizedCylinderSuspensionIso L A).hom := by
      rw [← L.map_comp_assoc, hcomp, L.map_comp]
      simp only [Category.assoc]
    _ = L.map (G.cofiberFunctor.map (G.mappingCylinderBoundarySquare f)) ≫
        L.map (G.actualToRawCofiber (G.cylinderConeArrow A)) ≫
          L.map (G.cylinderSuspensionIsoRaw A).inv := by rw [hβ]
    _ = L.map (G.actualToRawCofiber (Arrow.mk (G.mappingCylinderEndpoint f))) ≫
        L.map (rawCofiberFunctor.map (G.mappingCylinderBoundarySquare f)) ≫
          L.map (G.cylinderSuspensionIsoRaw A).inv := by
      rw [← Category.assoc, hα, Category.assoc]
    _ = L.map (G.actualToRawCofiber (Arrow.mk (G.mappingCylinderEndpoint f))) ≫
        L.map (G.mappingConeToSuspension f) ≫ L.map (G.cylinderSuspensionSwap A) := by
      rw [← L.map_comp, G.mappingCylinderBoundary_raw, L.map_comp]
    _ = _ := by
      rw [← Category.assoc (L.map (G.cofiberFunctor.map (G.mappingCylinderComparison f)))
        (L.map (G.actualToRawCofiber (Arrow.mk f))), hχnat]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]

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
  [L.IsLocalization (weakEquivalences C)] [Preadditive H]
attribute [local instance] HasZeroObject.zero'
noncomputable section

private instance mappingConeInclusion_cofibration_inst {A B : C} (f : A ⟶ B) :
    Cofibration (G.mappingConeInclusion f) := G.mappingConeInclusion_cofibration f

private instance secondConeToFirstSuspension_isIso {A B : C} (f : A ⟶ B)
    [IsCofibrant B] : IsIso (L.map (G.secondConeToFirstSuspension f)) :=
  Localization.inverts L (weakEquivalences C) _
    ((weakEquivalence_iff _).1 (G.secondConeToFirstSuspension_weakEquivalence f))

omit [Preadditive H] in
private theorem secondConeBoundary_formula {A B : C} (f : A ⟶ B)
    [IsCofibrant A] [IsCofibrant B] :
    inv (L.map (G.secondConeToFirstSuspension f)) ≫
      L.map (G.mappingConeToSuspension (G.mappingConeInclusion f)) =
        G.doubleConeReflection L A ≫ L.map (G.cylinderSuspensionMap f) := by
  haveI : IsIso (L.map (G.doubleConeFirst A)) :=
    Localization.inverts L (weakEquivalences C) _
      ((weakEquivalence_iff _).1 (G.doubleConeFirst_weakEquivalence A))
  have h₀ : L.map (G.doubleConeToSecondCone f) ≫
      L.map (G.secondConeToFirstSuspension f) = L.map (G.doubleConeFirst A) := by
    rw [← L.map_comp]
    exact congrArg L.map (G.doubleConeToSecondCone_first f)
  have h₁ : L.map (G.doubleConeToSecondCone f) ≫
      L.map (G.mappingConeToSuspension (G.mappingConeInclusion f)) =
      L.map (G.doubleConeSecond A) ≫ L.map (G.cylinderSuspensionMap f) := by
    rw [← L.map_comp, ← L.map_comp]
    exact congrArg L.map (G.doubleConeToSecondCone_second f)
  apply (cancel_epi (L.map (G.doubleConeFirst A))).1
  simp only [doubleConeReflection, Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← h₀, Category.assoc, IsIso.hom_inv_id_assoc]
  exact h₁

omit [Preadditive H] in
private theorem secondConeBoundary_formula' {A B : C} (f : A ⟶ B)
    [IsCofibrant A] [IsCofibrant B] :
    inv (L.map (G.mappingConeCollapse (G.mappingConeInclusion f))) ≫
      L.map (G.mappingConeToSuspension (G.mappingConeInclusion f)) =
        L.map (G.mappingConeSecondCofiberIso f).hom ≫
          G.doubleConeReflection L A ≫ L.map (G.cylinderSuspensionMap f) := by
  have h := G.secondConeBoundary_formula L f
  have hi : L.map (G.mappingConeSecondCofiberIso f).hom ≫
      inv (L.map (G.secondConeToFirstSuspension f)) =
      inv (L.map (G.mappingConeCollapse (G.mappingConeInclusion f))) := by
    simp [secondConeToFirstSuspension, L.map_comp]
  rw [← hi, Category.assoc, h]

private theorem secondBoundary_signed_coordinates {A B : C} (f : A ⟶ B)
    [IsCofibrant A] [IsCofibrant B] :
    L.map (G.cofiberBoundary.app (Arrow.mk (G.mappingConeInclusion f))) ≫
        (G.localizedCylinderSuspensionIso L B).hom =
      -(L.map (G.actualToRawCofiber (Arrow.mk (G.mappingConeInclusion f))) ≫
        L.map (G.mappingConeSecondCofiberIso f).hom ≫
          L.map (G.cylinderSuspensionMap f) ≫ L.map (G.cylinderSuspensionSwap B)) := by
  rw [G.actualBoundary_mappingCone_roof L (G.mappingConeInclusion f),
    ← Category.assoc (inv (L.map (G.mappingConeCollapse (G.mappingConeInclusion f)))),
    G.secondConeBoundary_formula', G.doubleConeReflection_eq_neg_id]
  simp only [Category.assoc, Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp]

private def cylinderSuspensionSwapIso (X : C) :
    G.cylinderSuspension X ≅ G.cylinderSuspension X where
  hom := G.cylinderSuspensionSwap X
  inv := G.cylinderSuspensionSwap X
  hom_inv_id := G.cylinderSuspensionSwap_sq X
  inv_hom_id := G.cylinderSuspensionSwap_sq X

private def mappingConeRotationIso {A B : C} (f : A ⟶ B)
    [IsCofibrant A] [IsCofibrant B] :
    L.obj (G.cofiberFunctor.obj (Arrow.mk (G.mappingConeInclusion f))) ≅
      L.obj (G.suspensionFunctor.obj A) := by
  letI : IsCofibrant (Arrow.mk (G.mappingConeInclusion f)).left := ‹IsCofibrant B›
  letI : Cofibration (Arrow.mk (G.mappingConeInclusion f)).hom :=
    G.mappingConeInclusion_cofibration f
  haveI : IsIso (L.map (G.actualToRawCofiber (Arrow.mk (G.mappingConeInclusion f)))) :=
    Localization.inverts L (weakEquivalences C) _
      ((weakEquivalence_iff _).1
        (G.actualToRawCofiber_weakEquivalence (Arrow.mk (G.mappingConeInclusion f))))
  exact asIso (L.map (G.actualToRawCofiber (Arrow.mk (G.mappingConeInclusion f)))) ≪≫
    L.mapIso (G.mappingConeSecondCofiberIso f) ≪≫
      L.mapIso (G.cylinderSuspensionSwapIso A) ≪≫
        (G.localizedCylinderSuspensionIso L A).symm

private theorem mappingConeRotation_boundary {A B : C} (f : A ⟶ B)
    [IsCofibrant A] [IsCofibrant B] :
    L.map (G.cofiberBoundary.app (Arrow.mk (G.mappingConeInclusion f))) =
      -((G.mappingConeRotationIso L f).hom ≫ L.map (G.suspensionFunctor.map f)) := by
  apply (cancel_mono (G.localizedCylinderSuspensionIso L B).hom).1
  rw [G.secondBoundary_signed_coordinates, Preadditive.neg_comp]
  congr 1
  have hn : (G.localizedCylinderSuspensionIso L A).inv ≫
      L.map (G.suspensionFunctor.map f) ≫
      (G.localizedCylinderSuspensionIso L B).hom = L.map (G.cylinderSuspensionMap f) := by
    rw [G.localizedCylinderSuspensionIso_naturality]
    simp
  simp only [mappingConeRotationIso, Iso.trans_hom, asIso_hom,
    Functor.mapIso_hom, Iso.symm_hom, cylinderSuspensionSwapIso, Category.assoc]
  rw [hn]
  have hs := congrArg (fun q => L.map q) (G.cylinderSuspensionSwap_naturality f)
  simp only [L.map_comp] at hs
  rw [hs]

omit [Preadditive H] in
private theorem cofiberInclusion_actualToRaw (f : Arrow C) :
    G.cofiberInclusion.app f ≫ G.actualToRawCofiber f =
      (G.cofibrantArrowComparison.app f).right ≫
        pushout.inl f.hom (0 : f.left ⟶ (0 : C)) := by
  simp [cofiberInclusion, actualToRawCofiber, rawCofiberFunctor]

omit [Preadditive H] in
private theorem localizedInclusion_actualToRaw (f : Arrow C) :
    (G.localizedCofiberInclusion L).app f ≫ L.map (G.actualToRawCofiber f) =
      L.map (pushout.inl f.hom (0 : f.left ⟶ (0 : C))) := by
  rw [G.localizedCofiberInclusion_app, Category.assoc, ← L.map_comp,
    G.cofiberInclusion_actualToRaw, L.map_comp]
  simp

private def mappingConeComparisonIso {A B : C} (f : A ⟶ B)
    [IsCofibrant A] [Cofibration f] :
    L.obj (G.cofiberFunctor.obj (Arrow.mk f)) ≅ L.obj (G.mappingCone f) := by
  letI : IsCofibrant (Arrow.mk f).left := ‹IsCofibrant A›
  letI : Cofibration (Arrow.mk f).hom := ‹Cofibration f›
  haveI : IsIso (L.map (G.actualToRawCofiber (Arrow.mk f))) :=
    Localization.inverts L (weakEquivalences C) _
      ((weakEquivalence_iff _).1 (G.actualToRawCofiber_weakEquivalence (Arrow.mk f)))
  exact asIso (L.map (G.actualToRawCofiber (Arrow.mk f))) ≪≫
    (asIso (L.map (G.mappingConeCollapse f))).symm

omit [Preadditive H] in
private theorem mappingConeComparison_inclusion {A B : C} (f : A ⟶ B)
    [IsCofibrant A] [Cofibration f] :
    (G.localizedCofiberInclusion L).app (Arrow.mk f) ≫
      (G.mappingConeComparisonIso L f).hom = L.map (G.mappingConeInclusion f) := by
  simp only [mappingConeComparisonIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  rw [← Category.assoc, G.localizedInclusion_actualToRaw]
  change L.map (pushout.inl f (0 : A ⟶ (0 : C))) ≫
    inv (L.map (G.mappingConeCollapse f)) = _
  rw [← G.mappingConeCollapse_on_inclusion, L.map_comp]
  simp

omit [Preadditive H] in
private theorem mappingConeRotation_inclusion {A B : C} (f : A ⟶ B)
    [IsCofibrant A] [IsCofibrant B] [Cofibration f] :
    (G.mappingConeComparisonIso L f).hom ≫
        (G.localizedCofiberInclusion L).app (Arrow.mk (G.mappingConeInclusion f)) ≫
          (G.mappingConeRotationIso L f).hom =
      L.map (G.cofiberBoundary.app (Arrow.mk f)) := by
  apply (cancel_mono (G.localizedCylinderSuspensionIso L A).hom).1
  rw [G.actualBoundary_mappingCone_roof]
  simp only [mappingConeRotationIso, mappingConeComparisonIso, Iso.trans_hom,
    asIso_hom, asIso_inv, Functor.mapIso_hom, Iso.symm_hom,
    cylinderSuspensionSwapIso, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc ((G.localizedCofiberInclusion L).app _),
    G.localizedInclusion_actualToRaw]
  change L.map (G.actualToRawCofiber (Arrow.mk f)) ≫
      inv (L.map (G.mappingConeCollapse f)) ≫
        L.map (pushout.inl (G.mappingConeInclusion f) (0 : B ⟶ (0 : C))) ≫
          L.map (G.mappingConeSecondCofiberIso f).hom ≫
            L.map (G.cylinderSuspensionSwap A) = _
  rw [← L.map_comp_assoc, G.secondCofiberIso_inclusion]

end
end KIP126.StableHomotopy.CofibrantGeneration

end


@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.Functor
universe u v w z
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasZeroMorphisms C] [HasZeroObject C] (G : CofibrantGeneration C)
  {H : Type w} [Category.{z} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)] [Preadditive H]
  [HasShift H ℤ] (σ : shiftFunctor H (1 : ℤ) ≅ G.derivedSuspensionFunctor L)
noncomputable section

private def pointSetSuspensionShiftIso :
    G.suspensionFunctor ⋙ L ≅ L ⋙ shiftFunctor H (1 : ℤ) :=
  (G.derivedSuspensionFunctorComparison L).symm ≪≫ isoWhiskerLeft L σ.symm

omit [Preadditive H] in
private theorem shiftedBoundary_as_map (f : Arrow C) :
    (G.shiftedCofiberBoundaryWithShift L σ).app f =
      L.map (G.cofiberBoundary.app f) ≫ (G.pointSetSuspensionShiftIso L σ).hom.app f.left := by
  simp [shiftedCofiberBoundaryWithShift, localizedCofiberBoundary, pointSetSuspensionShiftIso,
    Category.assoc]

private def cofibrantModelTriangleRotateIso {A B : C} (f : A ⟶ B)
    [IsCofibrant A] [Cofibration f] :
    (G.modelCofiberTriangleWithShift L σ (Arrow.mk f)).rotate ≅
      G.modelCofiberTriangleWithShift L σ (Arrow.mk (G.mappingConeInclusion f)) := by
  letI : IsCofibrant B := isCofibrant_of_cofibration f
  let e₂ := G.mappingConeComparisonIso L f
  let e₃ := G.mappingConeRotationIso L f ≪≫ (G.pointSetSuspensionShiftIso L σ).app A
  refine Triangle.isoMk (G.modelCofiberTriangleWithShift L σ (Arrow.mk f)).rotate
    (G.modelCofiberTriangleWithShift L σ (Arrow.mk (G.mappingConeInclusion f)))
    (Iso.refl (L.obj B)) e₂ e₃.symm ?_ ?_ ?_
  · simpa [Triangle.rotate, modelCofiberTriangleWithShift, e₂] using
      G.mappingConeComparison_inclusion L f
  · change ((G.shiftedCofiberBoundaryWithShift L σ).app (Arrow.mk f)) ≫ e₃.inv =
      e₂.hom ≫ (G.localizedCofiberInclusion L).app (Arrow.mk (G.mappingConeInclusion f))
    rw [G.shiftedBoundary_as_map]
    dsimp [e₃]
    simp only [Category.assoc]
    apply (cancel_mono (G.mappingConeRotationIso L f).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [Iso.hom_inv_id_app, Category.comp_id]
    exact (G.mappingConeRotation_inclusion L f).symm
  · change (-(shiftFunctor H (1 : ℤ)).map (L.map f)) ≫
        (shiftFunctor H (1 : ℤ)).map (𝟙 (L.obj B)) =
      e₃.inv ≫ (G.shiftedCofiberBoundaryWithShift L σ).app (Arrow.mk (G.mappingConeInclusion f))
    rw [(shiftFunctor H (1 : ℤ)).map_id, Category.comp_id, G.shiftedBoundary_as_map,
      G.mappingConeRotation_boundary]
    dsimp [e₃]
    simp only [Category.assoc, Preadditive.comp_neg,
      Preadditive.neg_comp, Iso.inv_hom_id_assoc]
    congr 1
    have hn := (G.pointSetSuspensionShiftIso L σ).hom.naturality f
    change L.map (G.suspensionFunctor.map f) ≫
        (G.pointSetSuspensionShiftIso L σ).hom.app B =
      (G.pointSetSuspensionShiftIso L σ).hom.app A ≫
        (shiftFunctor H (1 : ℤ)).map (L.map f) at hn
    rw [hn]
    simp

private theorem modelCofiberTriangle_rotate_mem (f : Arrow C) :
    (G.modelCofiberTriangleWithShift L σ f).rotate ∈ G.modelCofiberTrianglesWithShift L σ := by
  let r := G.cofibrantArrowReplacement.obj f
  letI : IsCofibrant r.left := G.cofibrantArrowReplacement_source f
  letI : Cofibration r.hom :=
    (cofibration_iff _).2 (G.cofibrantArrowReplacement_cofibration f)
  have hφ := G.cofibrantArrowComparison_weakEquivalences f
  haveI : IsIso ((G.modelCofiberTriangleFunctorWithShift L σ).map
      (G.cofibrantArrowComparison.app f)) :=
    G.modelCofiberTriangleFunctor_invertsWithShift L σ _ hφ
  let e : G.modelCofiberTriangleWithShift L σ r ≅ G.modelCofiberTriangleWithShift L σ f :=
    asIso ((G.modelCofiberTriangleFunctorWithShift L σ).map (G.cofibrantArrowComparison.app f))
  refine ⟨Arrow.mk (G.mappingConeInclusion r.hom), ⟨?_⟩⟩
  exact ((CategoryTheory.Pretriangulated.rotate H).mapIso e).symm ≪≫
    G.cofibrantModelTriangleRotateIso L σ r.hom

/-- Forward rotation for the class of the actual model cofiber triangles.
The reverse implication uses the weak triangle axioms. -/
private theorem modelCofiberTriangles_rotateWithShift
    (T : Triangle H) (hT : T ∈ G.modelCofiberTrianglesWithShift L σ) :
    T.rotate ∈ G.modelCofiberTrianglesWithShift L σ := by
  obtain ⟨f, ⟨e⟩⟩ := hT
  exact G.modelCofiberTriangles_isomorphicWithShift L σ _ _
    (G.modelCofiberTriangle_rotate_mem L σ f)
    ((CategoryTheory.Pretriangulated.rotate H).mapIso e)

end
end KIP126.StableHomotopy.CofibrantGeneration

end
