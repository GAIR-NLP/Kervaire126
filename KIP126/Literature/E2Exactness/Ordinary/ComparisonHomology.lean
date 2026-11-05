module
import all KIP126.Literature.E2Exactness.Ordinary.CochainCoordinates
import all KIP126.Literature.E2Exactness.Ordinary.ShiftedHomotopyCochain
import all KIP126.Literature.E2Exactness.Ordinary.ComparisonAugmentation
import all KIP126.Literature.E2Exactness.Ordinary.TowerCochainComparison

@[expose] section
namespace KIP126.Literature.Standard.E2TowerComparison
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open KIP126.StableHomotopy KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.E2Cochain
open KIP126.Literature.Standard.CochainCoordinates
open KIP126.Literature.Standard.FixedTensorE2
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H X Y Z : C} {unit : SphereSpectrum ⟶ H}

private theorem homologyMap_eq_of_shifted_conjugation
    (T : AbstractAdamsTower unit X) (U : AbstractAdamsTower unit Y) (t s : ℤ)
    (φ ψ : cochain T t ⟶ cochain U t)
    (Φ Ψ : shiftedLayerComplex T ⟶ shiftedLayerComplex U)
    (hφ : φ ≫ (shiftedHomotopyCochainIso U t).hom =
      (shiftedHomotopyCochainIso T t).hom ≫ homotopyCochainMap Φ t)
    (hψ : ψ ≫ (shiftedHomotopyCochainIso U t).hom =
      (shiftedHomotopyCochainIso T t).hom ≫ homotopyCochainMap Ψ t)
    (he : homologyMap (homotopyCochainMap Φ t) s =
      homologyMap (homotopyCochainMap Ψ t) s) :
    homologyMap φ s = homologyMap ψ s := by
  letI : IsIso (homologyMap (shiftedHomotopyCochainIso U t).hom s) := by
    change IsIso ((homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℤ) s).map
      (shiftedHomotopyCochainIso U t).hom)
    infer_instance
  apply (cancel_mono (homologyMap (shiftedHomotopyCochainIso U t).hom s)).mp
  rw [← homologyMap_comp, ← homologyMap_comp, hφ, hψ,
    homologyMap_comp, homologyMap_comp, he]

private theorem shiftedHomotopyCochainIso_composite
    {T : AbstractAdamsTower unit X} {U : AbstractAdamsTower unit Y}
    {V : AbstractAdamsTower unit Z} {f : X ⟶ Y} {g : Y ⟶ Z}
    (φ : TowerMap unit T U f) (ψ : TowerMap unit U V g) (t : ℤ) :
    (cochainMap φ t ≫ cochainMap ψ t) ≫ (shiftedHomotopyCochainIso V t).hom =
      (shiftedHomotopyCochainIso T t).hom ≫
        homotopyCochainMap (shiftedLayerComplexMap φ ≫ shiftedLayerComplexMap ψ) t := by
  rw [Category.assoc, shiftedHomotopyCochainIso_natural, ← Category.assoc,
    shiftedHomotopyCochainIso_natural, Category.assoc]
  congr 1
  exact (((homotopyModuleFunctor t).mapHomologicalComplex (ComplexShape.up ℤ)).map_comp _ _).symm
end
end KIP126.Literature.Standard.E2TowerComparison
end
