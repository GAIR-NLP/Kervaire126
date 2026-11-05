module
public import KIP126.AdamsSynthetic.ModelFoundation.Monoidal
import all KIP126.AdamsSynthetic.ModelFoundation.MonoidalLocalization

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.ModelGoodMonoidal
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Functor
open HomotopicalAlgebra MonoidalCategory MorphismProperty Localization
universe u v w z
noncomputable section
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  (M : MonoidalModelCompatibility C) (G : CofibrantGeneration C)
  {H : Type w} [Category.{z} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]

private def preferredUnitIso :
    L.obj (𝟙_ C) ≅ L.obj (G.cofibrantReplacementFunctor.obj (𝟙_ C)) := by
  haveI : IsIso (L.map (G.cofibrantReplacementCounit.app (𝟙_ C))) :=
    Localization.inverts L (weakEquivalences C) _
      (G.cofibrantReplacementCounit_weakEquivalence (𝟙_ C))
  exact (asIso (L.map (G.cofibrantReplacementCounit.app (𝟙_ C)))).symm

private abbrev derivedMonoidalCategory : MonoidalCategory H := by
  letI := goodObjectsMonoidal M
  letI := goodWeakEquivalences_isMonoidal M G
  letI := goodInclusion_isLocalization G L
  exact inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal ((goodObjects C).ι ⋙ L) (goodWeakEquivalences (C := C))
      (preferredUnitIso G L)))

private abbrev derivedSymmetricCategory :
    letI := derivedMonoidalCategory M G L
    SymmetricCategory H := by
  letI := goodObjectsMonoidal M
  letI := goodWeakEquivalences_isMonoidal M G
  letI := goodInclusion_isLocalization G L
  exact inferInstanceAs (SymmetricCategory
    (LocalizedMonoidal ((goodObjects C).ι ⋙ L) (goodWeakEquivalences (C := C))
      (preferredUnitIso G L)))

private abbrev derivedGoodFunctorMonoidal :
    letI := goodObjectsMonoidal M
    letI := derivedMonoidalCategory M G L
    ((goodObjects C).ι ⋙ L).Monoidal := by
  letI := goodObjectsMonoidal M
  letI := goodWeakEquivalences_isMonoidal M G
  letI := goodInclusion_isLocalization G L
  exact inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    ((goodObjects C).ι ⋙ L) (goodWeakEquivalences (C := C)) (preferredUnitIso G L)).Monoidal

private def derivedTensorComparison (X Y : C)
    (hX : goodObjects C X) (hY : goodObjects C Y) :
    letI := derivedMonoidalCategory M G L
    L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y := by
  letI := goodObjectsMonoidal M
  letI := derivedMonoidalCategory M G L
  letI := derivedGoodFunctorMonoidal M G L
  exact (Functor.Monoidal.μIso ((goodObjects C).ι ⋙ L) ⟨X, hX⟩ ⟨Y, hY⟩).symm

private theorem derivedTensorComparison_naturality
    {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y')
    (hX : goodObjects C X) (hX' : goodObjects C X')
    (hY : goodObjects C Y) (hY' : goodObjects C Y') :
    letI := derivedMonoidalCategory M G L
    L.map (f ⊗ₘ g) ≫ (derivedTensorComparison M G L X' Y' hX' hY').hom =
      (derivedTensorComparison M G L X Y hX hY).hom ≫ (L.map f ⊗ₘ L.map g) := by
  letI := goodObjectsMonoidal M
  letI := derivedMonoidalCategory M G L
  letI := derivedGoodFunctorMonoidal M G L
  exact (Functor.OplaxMonoidal.δ_natural ((goodObjects C).ι ⋙ L)
    (ObjectProperty.homMk f : (⟨X, hX⟩ : (goodObjects C).FullSubcategory) ⟶ ⟨X', hX'⟩)
    (ObjectProperty.homMk g : (⟨Y, hY⟩ : (goodObjects C).FullSubcategory) ⟶ ⟨Y', hY'⟩)).symm

private def derivedUnitComparison :
    letI := derivedMonoidalCategory M G L
    (𝟙_ H) ≅ L.obj (G.cofibrantReplacementFunctor.obj (𝟙_ C)) :=
  Iso.refl _

private def derivedTensorReplacementComparison (X Y : C) :
    letI := derivedMonoidalCategory M G L
    L.obj X ⊗ L.obj Y ≅
      L.obj (G.cofibrantReplacementFunctor.obj X ⊗ G.cofibrantReplacementFunctor.obj Y) := by
  letI := derivedMonoidalCategory M G L
  haveI : IsIso (L.map (G.cofibrantReplacementCounit.app X)) :=
    Localization.inverts L (weakEquivalences C) _
      (G.cofibrantReplacementCounit_weakEquivalence X)
  haveI : IsIso (L.map (G.cofibrantReplacementCounit.app Y)) :=
    Localization.inverts L (weakEquivalences C) _
      (G.cofibrantReplacementCounit_weakEquivalence Y)
  exact ((asIso (L.map (G.cofibrantReplacementCounit.app X))).symm ⊗ᵢ
      (asIso (L.map (G.cofibrantReplacementCounit.app Y))).symm) ≪≫
    (derivedTensorComparison M G L _ _
      (Or.inl (G.cofibrantReplacement_isCofibrant X))
      (Or.inl (G.cofibrantReplacement_isCofibrant Y))).symm

private def anyCofibrantUnitComparison {QI : C} (q : QI ⟶ 𝟙_ C)
    (hq : weakEquivalences C q) :
    letI := derivedMonoidalCategory M G L
    L.obj QI ≅ 𝟙_ H := by
  letI := derivedMonoidalCategory M G L
  haveI : IsIso (L.map q) := Localization.inverts L (weakEquivalences C) q hq
  exact asIso (L.map q) ≪≫ preferredUnitIso G L

private theorem derivedTensorReplacementComparison_naturality
    {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    letI := derivedMonoidalCategory M G L
    L.map (G.cofibrantReplacementFunctor.map f ⊗ₘ G.cofibrantReplacementFunctor.map g) ≫
      (derivedTensorReplacementComparison M G L X' Y').inv =
    (derivedTensorReplacementComparison M G L X Y).inv ≫ (L.map f ⊗ₘ L.map g) := by
  letI := derivedMonoidalCategory M G L
  let hQ : ∀ X, goodObjects C (G.cofibrantReplacementFunctor.obj X) :=
    fun X => Or.inl (G.cofibrantReplacement_isCofibrant X)
  change L.map (G.cofibrantReplacementFunctor.map f ⊗ₘ G.cofibrantReplacementFunctor.map g) ≫
      ((derivedTensorComparison M G L _ _ (hQ X') (hQ Y')).hom ≫
        (L.map (G.cofibrantReplacementCounit.app X') ⊗ₘ
          L.map (G.cofibrantReplacementCounit.app Y'))) =
    ((derivedTensorComparison M G L _ _ (hQ X) (hQ Y)).hom ≫
      (L.map (G.cofibrantReplacementCounit.app X) ⊗ₘ
        L.map (G.cofibrantReplacementCounit.app Y))) ≫ (L.map f ⊗ₘ L.map g)
  rw [← assoc, derivedTensorComparison_naturality M G L _ _ (hQ X) (hQ X') (hQ Y) (hQ Y'),
    assoc, tensorHom_comp_tensorHom, ← L.map_comp, ← L.map_comp,
    G.cofibrantReplacementCounit.naturality f, G.cofibrantReplacementCounit.naturality g,
    L.map_comp, L.map_comp, ← tensorHom_comp_tensorHom, ← assoc]
  rfl



end
end KIP126.StableHomotopy.ModelGoodMonoidal

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomotopicalAlgebra
open MonoidalCategory
universe u v w z
noncomputable section
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  (G : CofibrantGeneration C) (M : MonoidalModelCompatibility C)
  {H : Type w} [Category.{z} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]

/-- The symmetric monoidal model structure induces a monoidal structure on the
same localization target. Its unit is the localized cofibrant replacement of
the point-set unit; the point-set unit need not be cofibrant. -/
@[implicit_reducible, no_expose]
public def derivedMonoidalCategory : MonoidalCategory H :=
  ModelGoodMonoidal.derivedMonoidalCategory M G L

/-- The derived tensor is symmetric, with all coherence inherited through
monoidal localization. -/
@[implicit_reducible, no_expose]
public def derivedSymmetricCategory :
    letI := G.derivedMonoidalCategory M L
    SymmetricCategory H :=
  ModelGoodMonoidal.derivedSymmetricCategory M G L

/-- Cofibrant point-set objects compute the tensor on the localization. -/
@[no_expose]
public def derivedTensorComparison (X Y : C)
    (hX : IsCofibrant X) (hY : IsCofibrant Y) :
    letI := G.derivedMonoidalCategory M L
    L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y :=
  ModelGoodMonoidal.derivedTensorComparison M G L X Y (Or.inl hX) (Or.inl hY)

/-- The cofibrant tensor comparison uses the actual tensor of the two maps. -/
public theorem derivedTensorComparison_naturality
    {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y')
    (hX : IsCofibrant X) (hX' : IsCofibrant X')
    (hY : IsCofibrant Y) (hY' : IsCofibrant Y') :
    letI := G.derivedMonoidalCategory M L
    L.map (f ⊗ₘ g) ≫ (G.derivedTensorComparison M L X' Y' hX' hY').hom =
      (G.derivedTensorComparison M L X Y hX hY).hom ≫ (L.map f ⊗ₘ L.map g) :=
  ModelGoodMonoidal.derivedTensorComparison_naturality M G L f g
    (Or.inl hX) (Or.inl hX') (Or.inl hY) (Or.inl hY')

/-- Arbitrary inputs are computed by the tensor of their specified functorial
cofibrant replacements, using the same localization functor. -/
@[no_expose]
public def derivedTensorReplacementComparison (X Y : C) :
    letI := G.derivedMonoidalCategory M L
    L.obj X ⊗ L.obj Y ≅
      L.obj (G.cofibrantReplacementFunctor.obj X ⊗ G.cofibrantReplacementFunctor.obj Y) :=
  ModelGoodMonoidal.derivedTensorReplacementComparison M G L X Y

/-- Naturality of the tensor computation by functorial replacements. -/
public theorem derivedTensorReplacementComparison_naturality
    {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    letI := G.derivedMonoidalCategory M L
    L.map (G.cofibrantReplacementFunctor.map f ⊗ₘ G.cofibrantReplacementFunctor.map g) ≫
      (G.derivedTensorReplacementComparison M L X' Y').inv =
    (G.derivedTensorReplacementComparison M L X Y).inv ≫ (L.map f ⊗ₘ L.map g) :=
  ModelGoodMonoidal.derivedTensorReplacementComparison_naturality M G L f g

/-- The unit of the derived monoidal structure is the localized replacement
of the same point-set unit. -/
@[no_expose]
public def derivedUnitComparison :
    letI := G.derivedMonoidalCategory M L
    (𝟙_ H) ≅ L.obj (G.cofibrantReplacementFunctor.obj (𝟙_ C)) :=
  ModelGoodMonoidal.derivedUnitComparison M G L

/-- Any weak equivalence to the point-set unit computes the same derived unit.
In particular this applies to every cofibrant replacement of that unit. -/
@[no_expose]
public def derivedUnitComparisonOfWeakEquivalence {QI : C} (q : QI ⟶ 𝟙_ C)
    (hq : weakEquivalences C q) :
    letI := G.derivedMonoidalCategory M L
    L.obj QI ≅ 𝟙_ H :=
  ModelGoodMonoidal.anyCofibrantUnitComparison M G L q hq

end
end KIP126.StableHomotopy.CofibrantGeneration
end
