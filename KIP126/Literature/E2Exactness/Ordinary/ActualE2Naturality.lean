module
import all KIP126.Literature.E2Exactness.Ordinary.CochainCoordinates
import all KIP126.Literature.E2Exactness.Ordinary.ClassicalCochainNaturality
import all KIP126.Literature.E2Exactness.Ordinary.NormalizationNaturality

@[expose] section
namespace KIP126.Literature.Standard.ActualE2LES
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.AdamsSynthetic.E2Cochain
open KIP126.Literature.Standard.CochainCoordinates
open KIP126.Literature.Standard.FixedTensorE2
open KIP126.Literature.Standard.TensorNormalization
open KIP126.Literature.Standard.E2TowerComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem iso_inv_natural {C : Type*} [Category C]
    {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B') (eA : A ≅ A') (eB : B ≅ B')
    (h : f ≫ eB.hom = eA.hom ≫ g) : g ≫ eB.inv = eA.inv ≫ f := by
  apply (cancel_epi eA.hom).mp
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc]

private theorem actualE2ObjectIso_natural {X Y : Spectrum}
    (f : X ⟶ Y) (t s : ℤ) :
    homologyMap (tensorHomotopyCochainMap baseTensorTower t f) s ≫
      (actualE2ObjectIso Y t s).hom =
    (actualE2ObjectIso X t s).hom ≫
      (classical.map f).toSSDataMorphism.pageMap (s,t) 0 := by
  let F := homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℤ) s
  have hn := iso_inv_natural
    (homologyMap (cochainMap (FiniteBoundaryStage21.TensorTower.tensorTowerMap coefficients.unit f) t) s)
    (homologyMap (tensorHomotopyCochainMap baseTensorTower t f) s)
    (F.mapIso (tensorTowerCochainIso X t)) (F.mapIso (tensorTowerCochainIso Y t))
    (tensorTowerCochainIso_homology_natural f t s)
  have hc := iso_inv_natural
    (homologyMap (cochainMap (classicalTower.map f) t) s)
    (homologyMap (cochainMap (FiniteBoundaryStage21.TensorTower.tensorTowerMap coefficients.unit f) t) s)
    (F.mapIso (fixedTowerCochainIso (classicalTower.tower X) t))
    (F.mapIso (fixedTowerCochainIso (classicalTower.tower Y) t))
    (fixedTowerCochainIso_homology_natural (classicalTower.map f) t s)
  simp only [Functor.mapIso_inv] at hn hc
  simp only [actualE2ObjectIso, Iso.trans_hom, Functor.mapIso_hom,
    tensorHomotopyCochainIso, Iso.symm_hom, Functor.map_comp]
  change _ ≫ (F.map (tensorTowerCochainIso Y t).inv ≫
      F.map (fixedTowerCochainIso (classicalTower.tower Y) t).inv) ≫
      (e2CohomologyIso (classicalTower.sequence Y) t s).hom =
    (F.map (tensorTowerCochainIso X t).inv ≫
      F.map (fixedTowerCochainIso (classicalTower.tower X) t).inv) ≫
      (e2CohomologyIso (classicalTower.sequence X) t s).hom ≫ _
  simp only [← Category.assoc]
  rw [hn]
  rw [Category.assoc (F.map (tensorTowerCochainIso X t).inv) _
    (F.map (fixedTowerCochainIso (classicalTower.tower Y) t).inv), hc]
  simp only [Category.assoc]
  rw [classical_e2CohomologyIso_natural]
  rfl

end
end KIP126.Literature.Standard.ActualE2LES
end
