module
import all KIP126.Literature.E2Exactness.Ordinary.TensorAdamsTower

@[expose] section
namespace KIP126.Literature.FiniteBoundaryStage22
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated KIP126.StableHomotopy KIP126.AdamsSynthetic
open KIP126.Literature.FiniteBoundaryStage21.TensorTower
open KIP126.Literature.BocksteinComparison.Stages
universe u v
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : SphereSpectrum ⟶ H)

private def stageTensorIso (X : C) : ∀ n : ℕ,
    tensorStage unit (SphereSpectrum : C) n ⊗ X ≅ tensorStage unit X n
  | 0 => λ_ X
  | n+1 => (α_ (fiberObject unit) (tensorStage unit SphereSpectrum n) X) ≪≫
      whiskerLeftIso (fiberObject unit) (stageTensorIso X n)

private theorem stageTensorIso_step (X : C) (n : ℕ) :
    tensorStageStep unit SphereSpectrum n ▷ X ≫ (stageTensorIso unit X n).hom =
      (stageTensorIso unit X (n+1)).hom ≫ tensorStageStep unit X n := by
  change ((fiberAugmentation unit ▷ tensorStage unit SphereSpectrum n) ≫
      (λ_ (tensorStage unit SphereSpectrum n)).hom) ▷ X ≫ (stageTensorIso unit X n).hom =
    ((α_ (fiberObject unit) (tensorStage unit SphereSpectrum n) X).hom ≫
      fiberObject unit ◁ (stageTensorIso unit X n).hom) ≫
      (fiberAugmentation unit ▷ tensorStage unit X n) ≫ (λ_ (tensorStage unit X n)).hom
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, leftUnitor_naturality]
  rw [← Category.assoc, ← Category.assoc,
    ← associator_naturality_left, Category.assoc, leftUnitor_tensor_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem stageTensorIso_natural {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    tensorStage unit SphereSpectrum n ◁ f ≫ (stageTensorIso unit Y n).hom =
      (stageTensorIso unit X n).hom ≫ (stageFunctor unit n).map f := by
  induction n with
  | zero => exact leftUnitor_naturality f
  | succ n ih =>
    change (fiberObject unit ⊗ tensorStage unit SphereSpectrum n) ◁ f ≫
        (α_ (fiberObject unit) (tensorStage unit SphereSpectrum n) Y).hom ≫
          fiberObject unit ◁ (stageTensorIso unit Y n).hom =
      ((α_ (fiberObject unit) (tensorStage unit SphereSpectrum n) X).hom ≫
          fiberObject unit ◁ (stageTensorIso unit X n).hom) ≫
        fiberObject unit ◁ (stageFunctor unit n).map f
    rw [← Category.assoc, associator_naturality_right, Category.assoc,
      ← whiskerLeft_comp, ih, whiskerLeft_comp, Category.assoc]

variable [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]

private theorem stageTensorIso_map (X : C) (s t : ℕ) (h : s ≤ t) :
    (tensorTower unit SphereSpectrum).map h ▷ X ≫ (stageTensorIso unit X s).hom =
      (stageTensorIso unit X t).hom ≫ (tensorTower unit X).map h := by
  induction t, h using Nat.le_induction with
  | base =>
      simp only [AbstractAdamsTower.map_self, id_whiskerRight, Category.id_comp]
      change (stageTensorIso unit X s).hom = (stageTensorIso unit X s).hom ≫
        𝟙 (tensorStage unit X s)
      rw [Category.comp_id]
  | succ t h ih =>
    rw [← (tensorTower unit SphereSpectrum).map_comp h (Nat.le_succ t),
      ← (tensorTower unit X).map_comp h (Nat.le_succ t), comp_whiskerRight]
    rw [Category.assoc, ih, ← Category.assoc]
    have hs : (tensorTower unit SphereSpectrum).map (Nat.le_succ t) ▷ X ≫
        (stageTensorIso unit X t).hom =
      (stageTensorIso unit X (t+1)).hom ≫ (tensorTower unit X).map (Nat.le_succ t) := by
      rw [show (tensorTower unit SphereSpectrum).map (Nat.le_succ t) =
          tensorStageStep unit SphereSpectrum t from towerFromTriangles_step _ _ _ _ _ _,
        show (tensorTower unit X).map (Nat.le_succ t) =
          tensorStageStep unit X t from towerFromTriangles_step _ _ _ _ _ _]
      exact stageTensorIso_step unit X t
    rw [hs, Category.assoc]

private def finiteAugmentation (q : ℕ) : tensorStage unit SphereSpectrum q ⟶ SphereSpectrum :=
  (tensorTower unit SphereSpectrum).map (Nat.zero_le q)

private theorem stageTensorIso_projection (X : C) (q : ℕ) :
    finiteAugmentation unit q ▷ X ≫ (λ_ X).hom =
      (stageTensorIso unit X q).hom ≫ (tensorTower unit X).map (Nat.zero_le q) :=
  stageTensorIso_map unit X 0 q (Nat.zero_le q)

private def coefficientIntervalTriangle (s t : ℕ) (h : s ≤ t) : Triangle C :=
  Triangle.mk ((tensorTower unit SphereSpectrum).map h)
    (HasFunctorialCofiber.cofibι ((tensorTower unit SphereSpectrum).map h))
    (HasFunctorialCofiber.cofibδ ((tensorTower unit SphereSpectrum).map h))

private def actualIntervalTriangle (X : C) (s t : ℕ) (h : s ≤ t) : Triangle C :=
  Triangle.mk ((tensorTower unit X).map h)
    (HasFunctorialCofiber.cofibι ((tensorTower unit X).map h))
    (HasFunctorialCofiber.cofibδ ((tensorTower unit X).map h))

private def intervalTriangleIso (X : C) (s t : ℕ) (h : s ≤ t) :
    actualIntervalTriangle unit X s t h ≅
      (tensorRight X).mapTriangle.obj (coefficientIntervalTriangle unit s t h) := by
  apply isoTriangleOfIso₁₂ _ _ (HasFunctorialCofiber.cofib_distinguished _)
    ((tensorRight X).map_distinguished _ (HasFunctorialCofiber.cofib_distinguished _))
    (stageTensorIso unit X t).symm (stageTensorIso unit X s).symm
  change (tensorTower unit X).map h ≫ (stageTensorIso unit X s).inv =
    (stageTensorIso unit X t).inv ≫ ((tensorTower unit SphereSpectrum).map h ▷ X)
  apply (cancel_mono (stageTensorIso unit X s).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [stageTensorIso_map]
  simp only [Iso.inv_hom_id_assoc]

private def intervalCofiberIso (X : C) (s t : ℕ) (h : s ≤ t) :
    HasFunctorialCofiber.cofib ((tensorTower unit X).map h) ≅
      HasFunctorialCofiber.cofib ((tensorTower unit SphereSpectrum).map h) ⊗ X :=
  Triangle.π₃.mapIso (intervalTriangleIso unit X s t h)

private theorem intervalCofiberIso_inclusion (X : C) (s t : ℕ) (h : s ≤ t) :
    HasFunctorialCofiber.cofibι ((tensorTower unit X).map h) ≫
        (intervalCofiberIso unit X s t h).hom =
      (stageTensorIso unit X s).inv ≫
        (HasFunctorialCofiber.cofibι ((tensorTower unit SphereSpectrum).map h) ▷ X) := by
  have he := (intervalTriangleIso unit X s t h).hom.comm₂
  have h₂ : (intervalTriangleIso unit X s t h).hom.hom₂ =
      (stageTensorIso unit X s).inv := by
    simp only [intervalTriangleIso, isoTriangleOfIso₁₂_hom_hom₂, Iso.symm_hom]
  change HasFunctorialCofiber.cofibι ((tensorTower unit X).map h) ≫
    (intervalTriangleIso unit X s t h).hom.hom₃ =
      (intervalTriangleIso unit X s t h).hom.hom₂ ≫
        (HasFunctorialCofiber.cofibι ((tensorTower unit SphereSpectrum).map h) ▷ X) at he
  rw [h₂] at he
  exact he

private theorem intervalCofiberIso_boundary (X : C) (s t : ℕ) (h : s ≤ t) :
    (intervalCofiberIso unit X s t h).hom ≫
        (HasFunctorialCofiber.cofibδ ((tensorTower unit SphereSpectrum).map h) ▷ X) ≫
        ((tensorRight X).commShiftIso (1:ℤ)).hom.app (tensorStage unit SphereSpectrum t) =
      HasFunctorialCofiber.cofibδ ((tensorTower unit X).map h) ≫
        (shiftFunctor C (1:ℤ)).map (stageTensorIso unit X t).inv := by
  have he := (intervalTriangleIso unit X s t h).hom.comm₃
  have h₁ : (intervalTriangleIso unit X s t h).hom.hom₁ =
      (stageTensorIso unit X t).inv := by
    simp only [intervalTriangleIso, isoTriangleOfIso₁₂_hom_hom₁, Iso.symm_hom]
  change HasFunctorialCofiber.cofibδ ((tensorTower unit X).map h) ≫
      (shiftFunctor C (1:ℤ)).map (intervalTriangleIso unit X s t h).hom.hom₁ =
    (intervalTriangleIso unit X s t h).hom.hom₃ ≫
        (HasFunctorialCofiber.cofibδ ((tensorTower unit SphereSpectrum).map h) ▷ X) ≫
        ((tensorRight X).commShiftIso (1:ℤ)).hom.app (tensorStage unit SphereSpectrum t) at he
  rw [h₁] at he
  exact he.symm

private def fixedIntervalTriangleIso (X : C) (T : AbstractAdamsTower unit X)
    (s t : ℕ) (h : s ≤ t) :
    Triangle.mk (T.map h) (HasFunctorialCofiber.cofibι (T.map h))
      (HasFunctorialCofiber.cofibδ (T.map h)) ≅ actualIntervalTriangle unit X s t h :=
  isoTriangleOfIso₁₂ _ _ (HasFunctorialCofiber.cofib_distinguished _)
    (HasFunctorialCofiber.cofib_distinguished _)
    (fixedStageComparison unit X T t) (fixedStageComparison unit X T s)
    (stageIso_natural T (tensorTower unit X) (Iso.refl _) s t h).symm

private def fixedIntervalCofiberIso (X : C) (T : AbstractAdamsTower unit X)
    (s t : ℕ) (h : s ≤ t) :
    HasFunctorialCofiber.cofib (T.map h) ≅
      HasFunctorialCofiber.cofib ((tensorTower unit X).map h) :=
  Triangle.π₃.mapIso (fixedIntervalTriangleIso unit X T s t h)

private theorem fixedIntervalCofiberIso_inclusion (X : C) (T : AbstractAdamsTower unit X)
    (s t : ℕ) (h : s ≤ t) :
    HasFunctorialCofiber.cofibι (T.map h) ≫ (fixedIntervalCofiberIso unit X T s t h).hom =
      (fixedStageComparison unit X T s).hom ≫
        HasFunctorialCofiber.cofibι ((tensorTower unit X).map h) := by
  have he := (fixedIntervalTriangleIso unit X T s t h).hom.comm₂
  have h₂ : (fixedIntervalTriangleIso unit X T s t h).hom.hom₂ =
      (fixedStageComparison unit X T s).hom := by
    simp only [fixedIntervalTriangleIso, isoTriangleOfIso₁₂_hom_hom₂]
  change HasFunctorialCofiber.cofibι (T.map h) ≫
      (fixedIntervalTriangleIso unit X T s t h).hom.hom₃ =
    (fixedIntervalTriangleIso unit X T s t h).hom.hom₂ ≫
      HasFunctorialCofiber.cofibι ((tensorTower unit X).map h) at he
  rw [h₂] at he
  exact he

private theorem fixedIntervalCofiberIso_boundary (X : C) (T : AbstractAdamsTower unit X)
    (s t : ℕ) (h : s ≤ t) :
    (fixedIntervalCofiberIso unit X T s t h).hom ≫
        HasFunctorialCofiber.cofibδ ((tensorTower unit X).map h) =
      HasFunctorialCofiber.cofibδ (T.map h) ≫
        (shiftFunctor C (1:ℤ)).map (fixedStageComparison unit X T t).hom := by
  have he := (fixedIntervalTriangleIso unit X T s t h).hom.comm₃
  have h₁ : (fixedIntervalTriangleIso unit X T s t h).hom.hom₁ =
      (fixedStageComparison unit X T t).hom := by
    simp only [fixedIntervalTriangleIso, isoTriangleOfIso₁₂_hom_hom₁]
  change HasFunctorialCofiber.cofibδ (T.map h) ≫
      (shiftFunctor C (1:ℤ)).map (fixedIntervalTriangleIso unit X T s t h).hom.hom₁ =
    (fixedIntervalTriangleIso unit X T s t h).hom.hom₃ ≫
      HasFunctorialCofiber.cofibδ ((tensorTower unit X).map h) at he
  rw [h₁] at he
  exact he.symm


end
end KIP126.Literature.FiniteBoundaryStage22
