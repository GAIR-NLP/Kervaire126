module
import all KIP126.Literature.E2Exactness.Ordinary.CochainCoordinates
import all KIP126.Literature.E2Exactness.Ordinary.ActualE2Object
import all KIP126.Literature.E2Exactness.Ordinary.ActualComparisonHomology

@[expose] section
namespace KIP126.Literature.Standard.ActualE2LES
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.AdamsSynthetic.E2Cochain
open KIP126.Literature.Standard.CochainCoordinates
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem classical_e2CohomologyIso_natural {X Y : Spectrum}
    (f : X ⟶ Y) (t s : ℤ) :
    homologyMap (cochainMap (classicalTower.map f) t) s ≫
      (e2CohomologyIso (classicalTower.sequence Y) t s).hom =
    (e2CohomologyIso (classicalTower.sequence X) t s).hom ≫
      (classical.map f).toSSDataMorphism.pageMap (s,t) 0 :=
  e2CohomologyIso_natural (classicalTower.sequence X) (classicalTower.sequence Y)
    (classicalTower.map f) (classical.map f).toSSDataMorphism
    (classicalTower.natural f) t s
end
end KIP126.Literature.Standard.ActualE2LES
end
