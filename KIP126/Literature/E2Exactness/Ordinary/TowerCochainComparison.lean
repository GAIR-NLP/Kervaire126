module
import all KIP126.Literature.E2Exactness.Ordinary.TensorAdamsTower
import all KIP126.Literature.E2Exactness.Ordinary.CochainCoordinates

@[expose] section
namespace KIP126.Literature.Standard.E2TowerComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.AdamsSynthetic
open KIP126.Literature.BocksteinComparison.Stages
open KIP126.Literature.FiniteBoundaryStage21.TensorTower
open KIP126.AdamsSynthetic.E2Cochain
open KIP126.Literature.Standard.CochainCoordinates
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H X Y : C} {unit : SphereSpectrum ⟶ H}

private theorem comparisonLayer_isIso (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (s : ℤ) :
    IsIso ((comparisonMap T U e).layer s) := by
  let φ := comparisonMap T U e
  let f := T.mapAt (show s ≤ s+1 by omega)
  let g := U.mapAt (show s ≤ s+1 by omega)
  let w : Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f) ⟶
      Triangle.mk g (HasFunctorialCofiber.cofibι g) (HasFunctorialCofiber.cofibδ g) :=
    { hom₁ := φ.stage (s+1).toNat
      hom₂ := φ.stage s.toNat
      hom₃ := φ.layer s
      comm₁ := (φ.natural _).symm
      comm₂ := (HasFunctorialCofiber.cofibMap_ι _ _ _ _ _).symm
      comm₃ := (HasFunctorialCofiber.cofibMap_δ _ _ _ _ _).symm }
  exact isIso₃_of_isIso₁₂ w (HasFunctorialCofiber.cofib_distinguished f)
    (HasFunctorialCofiber.cofib_distinguished g) (by dsimp [w,φ,comparisonMap]; infer_instance)
    (by dsimp [w,φ,comparisonMap]; infer_instance)

private theorem comparisonCochainMap_isIso (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (t : ℤ) :
    IsIso (cochainMap (comparisonMap T U e) t) := by
  let φ := comparisonMap T U e
  have hi (s : ℤ) : IsIso ((cochainMap φ t).f s) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    letI := comparisonLayer_isIso T U e s
    constructor
    · intro a b hab
      exact (cancel_mono (φ.layer s)).mp hab
    · intro b
      refine ⟨b ≫ inv (φ.layer s), ?_⟩
      change (b ≫ inv (φ.layer s)) ≫ φ.layer s = b
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  letI := hi
  exact HomologicalComplex.Hom.isIso_of_components _

private def comparisonCochainIso (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (t : ℤ) :
    cochain T t ≅ cochain U t := by
  letI := comparisonCochainMap_isIso T U e t
  exact asIso (cochainMap (comparisonMap T U e) t)

variable [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]

private def fixedTowerCochainIso (T : AbstractAdamsTower unit X) (t : ℤ) :
    cochain T t ≅ cochain (tensorTower unit X) t :=
  comparisonCochainIso T (tensorTower unit X) (Iso.refl X) t

end
end KIP126.Literature.Standard.E2TowerComparison
end
