module
import all KIP126.Literature.E2Exactness.Ordinary.CochainCoordinates
import all KIP126.Literature.E2Exactness.Ordinary.TensorCochainNormalization
import all KIP126.Literature.E2Exactness.Ordinary.TowerCochainComparison
import KIP126.AdamsSynthetic.E2Cochain
import all KIP126.Literature.E2Exactness.Ordinary.FixedTensorLES

@[expose] section
namespace KIP126.Literature.Standard.ActualE2LES
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated HomologicalComplex
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.AdamsSynthetic.E2Cochain
open KIP126.Literature.Standard.CochainCoordinates
open KIP126.Literature.Standard.FixedTensorE2
open KIP126.Literature.Standard.TensorNormalization
open KIP126.Literature.Standard.E2TowerComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private def actualE2ObjectIso (X : Spectrum) (t s : ℤ) :
    (tensorHomotopyCochain baseTensorTower t X).homology s ≅
      ((classical.obj X).ssData (s,t)).page 0 :=
  (homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℤ) s).mapIso
    ((tensorHomotopyCochainIso X t) ≪≫
      (fixedTowerCochainIso (classicalTower.tower X) t).symm) ≪≫
    e2CohomologyIso (classicalTower.sequence X) t s

private def actualE2Boundary (U : Triangle Spectrum)
    (hU : U ∈ distTriang Spectrum) (hH : HomologyShortExact coefficients U) (t s : ℤ) :
    ((classical.obj U.obj₃).ssData (s,t)).page 0 ⟶
      ((classical.obj U.obj₁).ssData (s+1,t)).page 0 :=
  (actualE2ObjectIso U.obj₃ t s).inv ≫
    tensorCochainBoundary baseTensorTower t U hU hH s ≫
      (actualE2ObjectIso U.obj₁ t (s+1)).hom
end
end KIP126.Literature.Standard.ActualE2LES
end
