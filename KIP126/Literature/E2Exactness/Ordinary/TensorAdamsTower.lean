module

import all KIP126.Literature.BocksteinComparison
import KIP126.Literature.May

@[expose] section
namespace KIP126.Literature.FiniteBoundaryStage21.TensorTower
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated KIP126.StableHomotopy KIP126.AdamsSynthetic
open KIP126.Synthetic.Context
open KIP126.Literature.BocksteinComparison.Stages
universe u v
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : SphereSpectrum ⟶ H)

private def coefficientTriangle : Triangle C :=
  (Triangle.mk unit (HasFunctorialCofiber.cofibι unit)
    (HasFunctorialCofiber.cofibδ unit)).invRotate

private theorem coefficientTriangle_distinguished : coefficientTriangle unit ∈ distTriang C :=
  inv_rot_of_distTriang _ (HasFunctorialCofiber.cofib_distinguished unit)

private abbrev fiberObject : C := (coefficientTriangle unit).obj₁
private abbrev fiberAugmentation : fiberObject unit ⟶ SphereSpectrum :=
  (coefficientTriangle unit).mor₁

private def tensorStep (A : C) : fiberObject unit ⊗ A ⟶ A :=
  fiberAugmentation unit ▷ A ≫ (λ_ A).hom

private theorem tensorStep_natural {A B : C} (f : A ⟶ B) :
    fiberObject unit ◁ f ≫ tensorStep unit B = tensorStep unit A ≫ f := by
  dsimp only [tensorStep]
  rw [← Category.assoc, whisker_exchange, Category.assoc, leftUnitor_naturality, Category.assoc]

variable [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]

private def tensorBoundary (A : C) : H ⊗ A ⟶ (fiberObject unit ⊗ A)⟦(1:ℤ)⟧ :=
  (coefficientTriangle unit).mor₃ ▷ A ≫
    ((tensorRight A).commShiftIso (1:ℤ)).hom.app (fiberObject unit)

private def tensorStepTriangleIso (A : C) :
    (tensorRight A).mapTriangle.obj (coefficientTriangle unit) ≅
      Triangle.mk (tensorStep unit A) (unitAt unit A) (tensorBoundary unit A) := by
  refine Triangle.isoMk _ _ (Iso.refl _) (λ_ A) (Iso.refl _) ?_ ?_ ?_
  · change (fiberAugmentation unit ▷ A) ≫ (λ_ A).hom = 𝟙 _ ≫ tensorStep unit A
    rw [Category.id_comp]
    rfl
  · change (unit ▷ A) ≫ 𝟙 _ = (λ_ A).hom ≫ ((λ_ A).inv ≫ unit ▷ A)
    simp only [Category.comp_id, Iso.hom_inv_id_assoc]
  · change tensorBoundary unit A ≫ (shiftFunctor C (1:ℤ)).map (𝟙 _) =
      𝟙 _ ≫ tensorBoundary unit A
    rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

private theorem tensorStepTriangle_distinguished (A : C) :
    Triangle.mk (tensorStep unit A) (unitAt unit A) (tensorBoundary unit A) ∈ distTriang C :=
  isomorphic_distinguished _ ((tensorRight A).map_distinguished _
    (coefficientTriangle_distinguished unit)) _ (tensorStepTriangleIso unit A).symm

private def stageFunctor : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n+1 => stageFunctor n ⋙ tensorLeft (fiberObject unit)

private def tensorStage (X : C) (n : ℕ) : C := (stageFunctor unit n).obj X
private def tensorStageStep (X : C) (n : ℕ) : tensorStage unit X (n+1) ⟶ tensorStage unit X n :=
  tensorStep unit (tensorStage unit X n)
private def tensorStageBoundary (X : C) (n : ℕ) :
    H ⊗ tensorStage unit X n ⟶ (tensorStage unit X (n+1))⟦(1:ℤ)⟧ :=
  tensorBoundary unit (tensorStage unit X n)

private def tensorTower (X : C) : AbstractAdamsTower unit X :=
  towerFromTriangles (tensorStage unit X) (tensorStageStep unit X)
    (tensorStageBoundary unit X) (fun _ => tensorStepTriangle_distinguished unit _)
    (Iso.refl X)

private def fixedStageComparison (X : C) (T : AbstractAdamsTower unit X) (n : ℕ) :
    T.stage n ≅ tensorStage unit X n := stageIso T (tensorTower unit X) (Iso.refl _) n

private theorem fixedStageComparison_step (X : C) (T : AbstractAdamsTower unit X) (n : ℕ) :
    (fixedStageComparison unit X T (n+1)).hom ≫ tensorStageStep unit X n =
      T.map (Nat.le_succ n) ≫ (fixedStageComparison unit X T n).hom := by
  exact comparisonWithTriangles_step T (tensorStage unit X) (tensorStageStep unit X)
    (tensorStageBoundary unit X) (fun _ => tensorStepTriangle_distinguished unit _)
    (Iso.refl _) (Iso.refl _) n

private theorem fixedStageComparison_boundary (X : C) (T : AbstractAdamsTower unit X) (n : ℕ) :
    (T.layerIso n).inv ≫ HasFunctorialCofiber.cofibδ (T.map (Nat.le_succ n)) ≫
      (shiftFunctor C (1:ℤ)).map (fixedStageComparison unit X T (n+1)).hom =
    (H ◁ (fixedStageComparison unit X T n).hom) ≫ tensorStageBoundary unit X n := by
  exact comparisonWithTriangles_boundary T (tensorStage unit X) (tensorStageStep unit X)
    (tensorStageBoundary unit X) (fun _ => tensorStepTriangle_distinguished unit _)
    (Iso.refl _) (Iso.refl _) n

private def tensorTowerMap {X Y : C} (f : X ⟶ Y) :
    TowerMap unit (tensorTower unit X) (tensorTower unit Y) f where
  stage n := (stageFunctor unit n).map f
  natural {s t} h := by
    induction t, h using Nat.le_induction with
    | base => simp only [AbstractAdamsTower.map_self, Category.id_comp, Category.comp_id]
    | succ t h ih =>
      rw [← (tensorTower unit Y).map_comp h (Nat.le_succ t),
        ← (tensorTower unit X).map_comp h (Nat.le_succ t)]
      rw [← Category.assoc]
      have hs : (stageFunctor unit (t+1)).map f ≫
          (tensorTower unit Y).map (Nat.le_succ t) =
          (tensorTower unit X).map (Nat.le_succ t) ≫ (stageFunctor unit t).map f := by
        rw [show (tensorTower unit Y).map (Nat.le_succ t) = tensorStageStep unit Y t from
          towerFromTriangles_step _ _ _ _ _ _,
          show (tensorTower unit X).map (Nat.le_succ t) = tensorStageStep unit X t from
          towerFromTriangles_step _ _ _ _ _ _]
        change fiberObject unit ◁ (stageFunctor unit t).map f ≫ tensorStep unit _ =
          tensorStep unit _ ≫ (stageFunctor unit t).map f
        exact tensorStep_natural unit _
      rw [hs, Category.assoc, ih, Category.assoc]
  zero := by
    change f ≫ 𝟙 Y = 𝟙 X ≫ f
    rw [Category.comp_id, Category.id_comp]

private theorem tensorTowerMap_id (X : C) (n : ℕ) :
    (tensorTowerMap unit (𝟙 X)).stage n = 𝟙 _ :=
  (stageFunctor unit n).map_id X

private theorem tensorTowerMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (tensorTowerMap unit (f ≫ g)).stage n =
      (tensorTowerMap unit f).stage n ≫ (tensorTowerMap unit g).stage n :=
  (stageFunctor unit n).map_comp f g

variable [(tensorLeft (fiberObject unit)).CommShift ℤ]
  [(tensorLeft (fiberObject unit)).IsTriangulated]

private instance stageFunctor_commShift (n : ℕ) : (stageFunctor unit n).CommShift ℤ := by
  induction n with
  | zero => exact inferInstanceAs ((𝟭 C).CommShift ℤ)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs ((stageFunctor unit n ⋙ tensorLeft (fiberObject unit)).CommShift ℤ)

private instance stageFunctor_exact (n : ℕ) : (stageFunctor unit n).IsTriangulated := by
  induction n with
  | zero => exact inferInstanceAs ((𝟭 C).IsTriangulated)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs ((stageFunctor unit n ⋙ tensorLeft (fiberObject unit)).IsTriangulated)

omit [∀ A : C, (tensorRight A).IsTriangulated]
  [∀ A : C, (tensorRight A).CommShift ℤ] in
/-- Objectwise preservation of the input distinguished triangle by each
functorial Adams stage. -/
private theorem tensorStages_preserve_triangle (T : Triangle C) (hT : T ∈ distTriang C)
    (n : ℕ) : (stageFunctor unit n).mapTriangle.obj T ∈ distTriang C :=
  (stageFunctor unit n).map_distinguished T hT


end
end KIP126.Literature.FiniteBoundaryStage21.TensorTower
