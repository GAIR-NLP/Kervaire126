module

import KIP126.AdamsSynthetic.Tower
import KIP126.AdamsSynthetic.Quotients
import Mathlib.CategoryTheory.Functor.OfSequence

/-! Geometric Bockstein comparison for specified source triangles and
representative equations. Application to the Standard ν source uses agreement
between its E₂ labels and the layer isomorphisms. The relative cap calculation
uses the two cofiber-map squares. -/

@[expose] section
namespace KIP126.Literature.BocksteinComparison.Stages
open KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated KIP126.StableHomotopy
universe u v
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
  {X Y : C}

private def unitAt (unit : SphereSpectrum ⟶ H) (A : C) : A ⟶ H ⊗ A :=
  (λ_ A).inv ≫ unit ▷ A

omit [HasFunctorialCofiber (C := C)] in
private theorem unitAt_natural {A B : C} (f : A ⟶ B) :
    f ≫ unitAt unit B = unitAt unit A ≫ H ◁ f := by
  simp only [unitAt, ← Category.assoc, leftUnitor_inv_naturality]
  simp only [Category.assoc, whisker_exchange]

omit [HasFunctorialCofiber (C := C)] in
private def triangleIso23 (T U : Triangle C)
    (hT : T ∈ distTriang C) (hU : U ∈ distTriang C)
    (e₂ : T.obj₂ ≅ U.obj₂) (e₃ : T.obj₃ ≅ U.obj₃)
    (h : T.mor₂ ≫ e₃.hom = e₂.hom ≫ U.mor₂) : T ≅ U :=
  (rotCompInvRot.app T) ≪≫ (invRotate C).mapIso
    (isoTriangleOfIso₁₂ T.rotate U.rotate (rot_of_distTriang _ hT)
      (rot_of_distTriang _ hU) e₂ e₃ h) ≪≫ (rotCompInvRot.app U).symm

omit [HasFunctorialCofiber (C := C)] in
private theorem triangleIso23_hom2 (T U : Triangle C)
    (hT : T ∈ distTriang C) (hU : U ∈ distTriang C)
    (e₂ : T.obj₂ ≅ U.obj₂) (e₃ : T.obj₃ ≅ U.obj₃)
    (h : T.mor₂ ≫ e₃.hom = e₂.hom ≫ U.mor₂) :
    (triangleIso23 T U hT hU e₂ e₃ h).hom.hom₂ = e₂.hom := by
  simp [triangleIso23]
  exact Category.comp_id _

omit [HasFunctorialCofiber (C := C)] in
private theorem triangleIso23_hom3 (T U : Triangle C)
    (hT : T ∈ distTriang C) (hU : U ∈ distTriang C)
    (e₂ : T.obj₂ ≅ U.obj₂) (e₃ : T.obj₃ ≅ U.obj₃)
    (h : T.mor₂ ≫ e₃.hom = e₂.hom ≫ U.mor₂) :
    (triangleIso23 T U hT hU e₂ e₃ h).hom.hom₃ = e₃.hom := by
  simp [triangleIso23]
  exact Category.comp_id _

private def stepTriangle (T : AbstractAdamsTower unit X) (n : ℕ) : Triangle C :=
  Triangle.mk (T.map (Nat.le_succ n))
    (HasFunctorialCofiber.cofibι (T.map (Nat.le_succ n)))
    (HasFunctorialCofiber.cofibδ (T.map (Nat.le_succ n)))

private def layerIsoOfStage {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} (n : ℕ) (e : T.stage n ≅ U.stage n) :
    (stepTriangle T n).obj₃ ≅ (stepTriangle U n).obj₃ :=
  T.layerIso n ≪≫ whiskerLeftIso H e ≪≫ (U.layerIso n).symm

private theorem layerIsoOfStage_unit {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} (n : ℕ) (e : T.stage n ≅ U.stage n) :
    (stepTriangle T n).mor₂ ≫ (layerIsoOfStage n e).hom =
      e.hom ≫ (stepTriangle U n).mor₂ := by
  change HasFunctorialCofiber.cofibι (T.map (Nat.le_succ n)) ≫
    ((T.layerIso n).hom ≫ (H ◁ e.hom) ≫ (U.layerIso n).inv) =
    e.hom ≫ HasFunctorialCofiber.cofibι (U.map (Nat.le_succ n))
  rw [← Category.assoc, ← Category.assoc, T.layer_unit]
  change (unitAt unit (T.stage n) ≫ H ◁ e.hom) ≫ (U.layerIso n).inv = _
  rw [← unitAt_natural e.hom]
  dsimp only [unitAt]
  rw [Category.assoc, ← U.layer_unit]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private def nextTriangleIso {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} (n : ℕ) (e : T.stage n ≅ U.stage n) :
    stepTriangle T n ≅ stepTriangle U n :=
  triangleIso23 _ _ (HasFunctorialCofiber.cofib_distinguished _)
    (HasFunctorialCofiber.cofib_distinguished _) e (layerIsoOfStage n e)
    (layerIsoOfStage_unit n e)

private theorem nextTriangleIso_hom2 {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} (n : ℕ) (e : T.stage n ≅ U.stage n) :
    (nextTriangleIso n e).hom.hom₂ = e.hom :=
  triangleIso23_hom2 _ _ _ _ _ _ _

private theorem nextTriangleIso_hom3 {T : AbstractAdamsTower unit X}
    {U : AbstractAdamsTower unit Y} (n : ℕ) (e : T.stage n ≅ U.stage n) :
    (nextTriangleIso n e).hom.hom₃ = (layerIsoOfStage n e).hom :=
  triangleIso23_hom3 _ _ _ _ _ _ _

private def stageIso (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) : ∀ n, T.stage n ≅ U.stage n
  | 0 => T.zeroIso ≪≫ e ≪≫ U.zeroIso.symm
  | n + 1 => Triangle.π₁.mapIso (nextTriangleIso n (stageIso T U e n))

private def stepTriangleIso (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (n : ℕ) :
    stepTriangle T n ≅ stepTriangle U n :=
  nextTriangleIso n (stageIso T U e n)

private theorem stepTriangleIso_hom1 (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (n : ℕ) :
    (stepTriangleIso T U e n).hom.hom₁ = (stageIso T U e (n+1)).hom := rfl

private theorem stepTriangleIso_hom2 (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (n : ℕ) :
    (stepTriangleIso T U e n).hom.hom₂ = (stageIso T U e n).hom :=
  nextTriangleIso_hom2 _ _

private theorem stepTriangleIso_layer (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (n : ℕ) :
    (stepTriangleIso T U e n).hom.hom₃ ≫ (U.layerIso n).hom =
      (T.layerIso n).hom ≫ H ◁ (stageIso T U e n).hom := by
  rw [show (stepTriangleIso T U e n).hom.hom₃ =
    (layerIsoOfStage n (stageIso T U e n)).hom from nextTriangleIso_hom3 _ _]
  simp only [layerIsoOfStage, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem stageIso_natural_step (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (n : ℕ) :
    (stageIso T U e (n+1)).hom ≫ U.map (Nat.le_succ n) =
      T.map (Nat.le_succ n) ≫ (stageIso T U e n).hom := by
  have h := (stepTriangleIso T U e n).hom.comm₁
  rw [stepTriangleIso_hom1, stepTriangleIso_hom2] at h
  exact h.symm

private theorem stageIso_natural (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (s t : ℕ) (h : s ≤ t) :
    (stageIso T U e t).hom ≫ U.map h =
      T.map h ≫ (stageIso T U e s).hom := by
  induction t, h using Nat.le_induction with
  | base => simp only [T.map_self, U.map_self, Category.comp_id, Category.id_comp]
  | succ t h ih =>
    rw [← U.map_comp h (Nat.le_succ t), ← T.map_comp h (Nat.le_succ t)]
    rw [← Category.assoc, stageIso_natural_step, Category.assoc, ih, Category.assoc]

private theorem stageIso_zero (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) :
    (stageIso T U e 0).hom ≫ U.zeroIso.hom = T.zeroIso.hom ≫ e.hom := by
  simp only [stageIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

private def comparisonMap (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) : TowerMap unit T U e.hom where
  stage n := (stageIso T U e n).hom
  natural {s t} h := stageIso_natural T U e s t h
  zero := stageIso_zero T U e

private theorem stageIso_mapAt (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) {s t : ℤ} (h : s ≤ t) :
    (stageIso T U e t.toNat).hom ≫ U.mapAt h =
      T.mapAt h ≫ (stageIso T U e s.toNat).hom :=
  stageIso_natural T U e _ _ _

private theorem stageIso_boundary (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (n : ℕ) :
    (T.layerIso n).inv ≫ HasFunctorialCofiber.cofibδ (T.map (Nat.le_succ n)) ≫
      (shiftFunctor C (1 : ℤ)).map (stageIso T U e (n+1)).hom =
    (H ◁ (stageIso T U e n).hom) ≫ (U.layerIso n).inv ≫
      HasFunctorialCofiber.cofibδ (U.map (Nat.le_succ n)) := by
  have h := (stepTriangleIso T U e n).hom.comm₃
  rw [stepTriangleIso_hom1] at h
  rw [show (stepTriangleIso T U e n).hom.hom₃ =
    (layerIsoOfStage n (stageIso T U e n)).hom from nextTriangleIso_hom3 _ _] at h
  have hh := congrArg (fun z => (T.layerIso n).inv ≫ z) h
  simpa only [stepTriangle, Triangle.mk, layerIsoOfStage, Iso.trans_hom,
    Iso.symm_hom, whiskerLeftIso_hom, Category.assoc,
    Iso.inv_hom_id_assoc] using hh


/-! A tower construction from explicit distinguished coefficient triangles.
All inputs below are source objects/arrows/triangle proofs. -/
private def sequenceMap (A : ℕ → C) (d : ∀ n, A (n+1) ⟶ A n)
    {s t : ℕ} (h : s ≤ t) : A t ⟶ A s :=
  (Functor.ofOpSequence d).map (homOfLE h).op

omit [HasFunctorialCofiber (C := C)] in
private theorem sequenceMap_step (A : ℕ → C) (d : ∀ n, A (n+1) ⟶ A n) (n : ℕ) :
    sequenceMap A d (Nat.le_succ n) = d n :=
  Functor.ofOpSequence_map_homOfLE_succ d n

private def sequenceStepTriangleIso (A : ℕ → C) (d : ∀ n, A (n+1) ⟶ A n)
    (δ : ∀ n, H ⊗ A n ⟶ (A (n+1))⟦(1 : ℤ)⟧)
    (hT : ∀ n, Triangle.mk (d n) (unitAt unit (A n)) (δ n) ∈ distTriang C)
    (n : ℕ) :
    Triangle.mk (sequenceMap A d (Nat.le_succ n))
      (HasFunctorialCofiber.cofibι (sequenceMap A d (Nat.le_succ n)))
      (HasFunctorialCofiber.cofibδ (sequenceMap A d (Nat.le_succ n))) ≅
    Triangle.mk (d n) (unitAt unit (A n)) (δ n) :=
  isoTriangleOfIso₁₂ _ _ (HasFunctorialCofiber.cofib_distinguished _) (hT n)
    (Iso.refl _) (Iso.refl _) (by
      simp only [Triangle.mk, Iso.refl_hom, Category.comp_id, Category.id_comp]
      exact sequenceMap_step A d n)

private def towerFromTriangles (A : ℕ → C) (d : ∀ n, A (n+1) ⟶ A n)
    (δ : ∀ n, H ⊗ A n ⟶ (A (n+1))⟦(1 : ℤ)⟧)
    (hT : ∀ n, Triangle.mk (d n) (unitAt unit (A n)) (δ n) ∈ distTriang C)
    (e₀ : A 0 ≅ X) : AbstractAdamsTower unit X where
  stage := A
  map := sequenceMap A d
  map_self s := (Functor.ofOpSequence d).map_id (Opposite.op s)
  map_comp hrs hst := by
    change (Functor.ofOpSequence d).map _ ≫ (Functor.ofOpSequence d).map _ = _
    rw [← Functor.map_comp]
    rfl
  zeroIso := e₀
  layerIso n := Triangle.π₃.mapIso (sequenceStepTriangleIso A d δ hT n)
  layer_unit n := by
    change HasFunctorialCofiber.cofibι (sequenceMap A d (Nat.le_succ n)) ≫
      (sequenceStepTriangleIso A d δ hT n).hom.hom₃ = unitAt unit (A n)
    have h := (sequenceStepTriangleIso A d δ hT n).hom.comm₂
    have h₂ : (sequenceStepTriangleIso A d δ hT n).hom.hom₂ = 𝟙 (A n) := by
      simp only [sequenceStepTriangleIso, isoTriangleOfIso₁₂_hom_hom₂, Iso.refl_hom]
      rfl
    change HasFunctorialCofiber.cofibι (sequenceMap A d (Nat.le_succ n)) ≫
      (sequenceStepTriangleIso A d δ hT n).hom.hom₃ =
        (sequenceStepTriangleIso A d δ hT n).hom.hom₂ ≫ unitAt unit (A n) at h
    exact h.trans ((congrArg (fun f : A n ⟶ A n => f ≫ unitAt unit (A n)) h₂).trans
      (Category.id_comp _))

private theorem towerFromTriangles_step (A : ℕ → C) (d : ∀ n, A (n+1) ⟶ A n)
    (δ : ∀ n, H ⊗ A n ⟶ (A (n+1))⟦(1 : ℤ)⟧)
    (hT : ∀ n, Triangle.mk (d n) (unitAt unit (A n)) (δ n) ∈ distTriang C)
    (e₀ : A 0 ≅ X) (n : ℕ) :
    (towerFromTriangles A d δ hT e₀).map (Nat.le_succ n) = d n :=
  sequenceMap_step A d n

private theorem towerFromTriangles_boundary (A : ℕ → C) (d : ∀ n, A (n+1) ⟶ A n)
    (δ : ∀ n, H ⊗ A n ⟶ (A (n+1))⟦(1 : ℤ)⟧)
    (hT : ∀ n, Triangle.mk (d n) (unitAt unit (A n)) (δ n) ∈ distTriang C)
    (e₀ : A 0 ≅ X) (n : ℕ) :
    ((towerFromTriangles A d δ hT e₀).layerIso n).hom ≫ δ n =
      HasFunctorialCofiber.cofibδ
        ((towerFromTriangles A d δ hT e₀).map (Nat.le_succ n)) := by
  change (sequenceStepTriangleIso A d δ hT n).hom.hom₃ ≫ δ n =
    HasFunctorialCofiber.cofibδ (sequenceMap A d (Nat.le_succ n))
  have h := (sequenceStepTriangleIso A d δ hT n).hom.comm₃
  have h₁ : (sequenceStepTriangleIso A d δ hT n).hom.hom₁ = 𝟙 (A (n+1)) := by
    simp only [sequenceStepTriangleIso, isoTriangleOfIso₁₂_hom_hom₁, Iso.refl_hom]
    rfl
  change HasFunctorialCofiber.cofibδ (sequenceMap A d (Nat.le_succ n)) ≫
    (shiftFunctor C (1 : ℤ)).map (sequenceStepTriangleIso A d δ hT n).hom.hom₁ =
      (sequenceStepTriangleIso A d δ hT n).hom.hom₃ ≫ δ n at h
  exact h.symm.trans ((congrArg (fun f : A (n+1) ⟶ A (n+1) =>
    HasFunctorialCofiber.cofibδ (sequenceMap A d (Nat.le_succ n)) ≫
      (shiftFunctor C (1 : ℤ)).map f) h₁).trans
    ((congrArg (fun f => HasFunctorialCofiber.cofibδ (sequenceMap A d (Nat.le_succ n)) ≫ f)
      ((shiftFunctor C (1 : ℤ)).map_id (A (n+1)))).trans (Category.comp_id _)))

private def comparisonWithTriangles (T : AbstractAdamsTower unit X)
    (A : ℕ → C) (d : ∀ n, A (n+1) ⟶ A n)
    (δ : ∀ n, H ⊗ A n ⟶ (A (n+1))⟦(1 : ℤ)⟧)
    (hT : ∀ n, Triangle.mk (d n) (unitAt unit (A n)) (δ n) ∈ distTriang C)
    (e₀ : A 0 ≅ Y) (e : X ≅ Y) (n : ℕ) : T.stage n ≅ A n :=
  stageIso T (towerFromTriangles A d δ hT e₀) e n

private theorem comparisonWithTriangles_step (T : AbstractAdamsTower unit X)
    (A : ℕ → C) (d : ∀ n, A (n+1) ⟶ A n)
    (δ : ∀ n, H ⊗ A n ⟶ (A (n+1))⟦(1 : ℤ)⟧)
    (hT : ∀ n, Triangle.mk (d n) (unitAt unit (A n)) (δ n) ∈ distTriang C)
    (e₀ : A 0 ≅ Y) (e : X ≅ Y) (n : ℕ) :
    (comparisonWithTriangles T A d δ hT e₀ e (n+1)).hom ≫ d n =
      T.map (Nat.le_succ n) ≫ (comparisonWithTriangles T A d δ hT e₀ e n).hom := by
  simpa only [comparisonWithTriangles, towerFromTriangles_step] using
    stageIso_natural_step T (towerFromTriangles A d δ hT e₀) e n

private theorem comparisonWithTriangles_boundary (T : AbstractAdamsTower unit X)
    (A : ℕ → C) (d : ∀ n, A (n+1) ⟶ A n)
    (δ : ∀ n, H ⊗ A n ⟶ (A (n+1))⟦(1 : ℤ)⟧)
    (hT : ∀ n, Triangle.mk (d n) (unitAt unit (A n)) (δ n) ∈ distTriang C)
    (e₀ : A 0 ≅ Y) (e : X ≅ Y) (n : ℕ) :
    (T.layerIso n).inv ≫ HasFunctorialCofiber.cofibδ (T.map (Nat.le_succ n)) ≫
      (shiftFunctor C (1 : ℤ)).map
        (comparisonWithTriangles T A d δ hT e₀ e (n+1)).hom =
    (H ◁ (comparisonWithTriangles T A d δ hT e₀ e n).hom) ≫ δ n := by
  have hb := towerFromTriangles_boundary A d δ hT e₀ n
  have hi := congrArg (fun z => ((towerFromTriangles A d δ hT e₀).layerIso n).inv ≫ z) hb
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at hi
  simpa only [comparisonWithTriangles, ← hi] using
    stageIso_boundary T (towerFromTriangles A d δ hT e₀) e n


/-- Existence of a coherent choice of stage and step-triangle isomorphisms. -/
private theorem actualCoefficientTowerComparison (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) :
    ∃ I : ∀ n, T.stage n ≅ U.stage n,
      (I 0).hom ≫ U.zeroIso.hom = T.zeroIso.hom ≫ e.hom ∧
      (∀ (s t : ℕ) (h : s ≤ t), (I t).hom ≫ U.map h = T.map h ≫ (I s).hom) ∧
      ∀ n, ∃ Φ : stepTriangle T n ≅ stepTriangle U n,
        Φ.hom.hom₁ = (I (n+1)).hom ∧ Φ.hom.hom₂ = (I n).hom ∧
          Φ.hom.hom₃ ≫ (U.layerIso n).hom = (T.layerIso n).hom ≫ H ◁ (I n).hom := by
  refine ⟨stageIso T U e, stageIso_zero T U e, stageIso_natural T U e, ?_⟩
  intro n
  exact ⟨stepTriangleIso T U e n, stepTriangleIso_hom1 T U e n,
    stepTriangleIso_hom2 T U e n, stepTriangleIso_layer T U e n⟩


end
end KIP126.Literature.BocksteinComparison.Stages
end

@[expose] section
namespace KIP126.Literature.BocksteinComparison.Stages
open KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated KIP126.StableHomotopy KIP126.Core.SpectralSequence
universe u v
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
  {X Y : C}

private def integerStepTriangle (T : AbstractAdamsTower unit X) (s : ℤ) : Triangle C :=
  Triangle.mk (T.mapAt (show s ≤ s+1 by omega))
    (HasFunctorialCofiber.cofibι (T.mapAt (show s ≤ s+1 by omega)))
    (HasFunctorialCofiber.cofibδ (T.mapAt (show s ≤ s+1 by omega)))

private def integerStepTriangleIso (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (s : ℤ) :
    integerStepTriangle T s ≅ integerStepTriangle U s := by
  cases s with
  | ofNat k => exact stepTriangleIso T U e k
  | negSucc k =>
    exact isoTriangleOfIso₁₂ _ _ (HasFunctorialCofiber.cofib_distinguished _)
      (HasFunctorialCofiber.cofib_distinguished _)
      (stageIso T U e (Int.negSucc k+1).toNat)
      (stageIso T U e (Int.negSucc k).toNat)
      (stageIso_mapAt T U e (show Int.negSucc k ≤ Int.negSucc k+1 by omega)).symm

private theorem integerStepTriangleIso_hom1 (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (s : ℤ) :
    (integerStepTriangleIso T U e s).hom.hom₁ =
      (stageIso T U e (s+1).toNat).hom := by
  cases s with
  | ofNat k => exact stepTriangleIso_hom1 T U e k
  | negSucc k =>
    exact isoTriangleOfIso₁₂_hom_hom₁ _ _
      (HasFunctorialCofiber.cofib_distinguished _)
      (HasFunctorialCofiber.cofib_distinguished _) _ _ _

private theorem integerStepTriangleIso_hom2 (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (s : ℤ) :
    (integerStepTriangleIso T U e s).hom.hom₂ =
      (stageIso T U e s.toNat).hom := by
  cases s with
  | ofNat k => exact stepTriangleIso_hom2 T U e k
  | negSucc k =>
    exact isoTriangleOfIso₁₂_hom_hom₂ _ _
      (HasFunctorialCofiber.cofib_distinguished _)
      (HasFunctorialCofiber.cofib_distinguished _) _ _ _

private def selectedLayerIso (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (s : ℤ) :
    T.layer s ≅ U.layer s :=
  Triangle.π₃.mapIso (integerStepTriangleIso T U e s)


private theorem selectedLayerIso_nat (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (n : ℕ) :
    (selectedLayerIso T U e (n : ℤ)).hom = (stepTriangleIso T U e n).hom.hom₃ := rfl

private theorem selectedLayerIso_coefficient (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (n : ℕ) :
    (selectedLayerIso T U e (n : ℤ)).hom ≫ (U.layerIso n).hom =
      (T.layerIso n).hom ≫ H ◁ (stageIso T U e n).hom :=
  stepTriangleIso_layer T U e n

private theorem selectedLayerIso_inclusion (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (s : ℤ) :
    HasFunctorialCofiber.cofibι (T.mapAt (show s ≤ s+1 by omega)) ≫
      (selectedLayerIso T U e s).hom =
    (stageIso T U e s.toNat).hom ≫
      HasFunctorialCofiber.cofibι (U.mapAt (show s ≤ s+1 by omega)) := by
  have h := (integerStepTriangleIso T U e s).hom.comm₂
  rw [integerStepTriangleIso_hom2] at h
  exact h

private theorem selectedLayerIso_boundary (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (s : ℤ) :
    (selectedLayerIso T U e s).hom ≫
      HasFunctorialCofiber.cofibδ (U.mapAt (show s ≤ s+1 by omega)) =
    HasFunctorialCofiber.cofibδ (T.mapAt (show s ≤ s+1 by omega)) ≫
      (shiftFunctor C (1 : ℤ)).map (stageIso T U e (s+1).toNat).hom := by
  have h := (integerStepTriangleIso T U e s).hom.comm₃
  rw [integerStepTriangleIso_hom1] at h
  exact h.symm

omit [HasFunctorialCofiber (C := C)] in
private theorem stageDesuspend_natural {A B : C} (g : A ⟶ B) (n : ℤ)
    (x : HomotopyGroup n (A⟦(1 : ℤ)⟧)) :
    AbstractAdamsTower.desuspend B n (x ≫ (shiftFunctor C (1 : ℤ)).map g) =
      AbstractAdamsTower.desuspend A n x ≫ g := by
  dsimp [AbstractAdamsTower.desuspend]
  simp only [Functor.map_comp, Category.assoc]
  have h := (shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by omega)).hom.naturality g
  simp only [Functor.comp_map, Functor.id_map] at h
  rw [h]

private def firstPageTransport (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (p : ℤ × ℤ)
    (x : T.FirstPage p) : U.FirstPage p :=
  x ≫ (selectedLayerIso T U e p.1).hom

private def stageTransport (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (n s : ℤ)
    (a : HomotopyGroup n (T.stageAt s)) : HomotopyGroup n (U.stageAt s) :=
  a ≫ (stageIso T U e s.toNat).hom

private theorem selectedLayerMap_natural (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    firstPageTransport T U e p (T.layerMap p a) =
      U.layerMap p (stageTransport T U e (p.2-p.1) p.1 a) := by
  change (a ≫ HasFunctorialCofiber.cofibι (T.mapAt _)) ≫
      (selectedLayerIso T U e p.1).hom =
    (a ≫ (stageIso T U e p.1.toNat).hom) ≫ HasFunctorialCofiber.cofibι (U.mapAt _)
  rw [Category.assoc, selectedLayerIso_inclusion, ← Category.assoc]

private theorem selectedConnecting_natural (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (p : ℤ × ℤ)
    (x : T.FirstPage p) :
    U.connecting p (firstPageTransport T U e p x) =
      stageTransport T U e (p.2-p.1-1) (p.1+1) (T.connecting p x) := by
  change AbstractAdamsTower.desuspend _ _
      ((x ≫ (selectedLayerIso T U e p.1).hom) ≫ HasFunctorialCofiber.cofibδ (U.mapAt _)) =
    AbstractAdamsTower.desuspend _ _ (x ≫ HasFunctorialCofiber.cofibδ (T.mapAt _)) ≫
      (stageIso T U e (p.1+1).toNat).hom
  rw [Category.assoc, selectedLayerIso_boundary, ← Category.assoc]
  exact stageDesuspend_natural _ _ _

private theorem selectedStageMap_natural (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (n s t : ℤ) (h : s ≤ t)
    (a : HomotopyGroup n (T.stageAt t)) :
    stageTransport T U e n t a ≫ U.mapAt h =
      stageTransport T U e n s (a ≫ T.mapAt h) := by
  change (a ≫ _) ≫ U.mapAt h = (a ≫ T.mapAt h) ≫ _
  rw [Category.assoc, stageIso_mapAt, ← Category.assoc]

private theorem stageTransport_cast (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (n n' s : ℤ) (hn : n = n')
    (a : HomotopyGroup n (T.stageAt s)) :
    stageTransport T U e n' s
      (Eq.mp (congrArg (fun m => HomotopyGroup m (T.stageAt s)) hn) a) =
    Eq.mp (congrArg (fun m => HomotopyGroup m (U.stageAt s)) hn)
      (stageTransport T U e n s a) := by
  subst n'
  rfl

private theorem selectedConnecting_lift (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (r : ℤ) (hr : 1 ≤ r)
    (p : ℤ × ℤ) (x : T.FirstPage p)
    (a : HomotopyGroup (p.2-p.1-1) (T.stageAt (p.1+r)))
    (ha : T.connecting p x = a ≫ T.mapAt (show p.1+1 ≤ p.1+r by omega)) :
    U.connecting p (firstPageTransport T U e p x) =
      stageTransport T U e (p.2-p.1-1) (p.1+r) a ≫
        U.mapAt (show p.1+1 ≤ p.1+r by omega) := by
  rw [selectedConnecting_natural, ha, selectedStageMap_natural]


private theorem selectedLayer_lift (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (r : ℤ)
    (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1-1) (T.stageAt (p.1+r)))
    (y : T.FirstPage (p+(r,r-1)))
    (hy : y = T.layerMap (p+(r,r-1))
      (Eq.mp (congrArg (fun m => HomotopyGroup m (T.stageAt (p.1+r)))
        (by dsimp; omega : p.2-p.1-1 = (p+(r,r-1)).2-(p+(r,r-1)).1)) a)) :
    firstPageTransport T U e (p+(r,r-1)) y =
      U.layerMap (p+(r,r-1))
        (Eq.mp (congrArg (fun m => HomotopyGroup m (U.stageAt (p.1+r)))
          (by dsimp; omega : p.2-p.1-1 = (p+(r,r-1)).2-(p+(r,r-1)).1))
          (stageTransport T U e (p.2-p.1-1) (p.1+r) a)) := by
  rw [hy, selectedLayerMap_natural]
  exact congrArg (U.layerMap (p+(r,r-1)))
    (stageTransport_cast T U e _ _ (p.1+r) (by dsimp; omega) a)

/-- The two actual lift-and-boundary equations transport together, through
one specified lift and the same complete step-triangle isomorphisms. -/
private theorem differentialRelation_transport (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (e : X ≅ Y) (r : ℤ) (hr : 2 ≤ r)
    (p : ℤ × ℤ) (x : T.FirstPage p)
    (a : HomotopyGroup (p.2-p.1-1) (T.stageAt (p.1+r)))
    (y : T.FirstPage (p+(r,r-1)))
    (ha : T.connecting p x = a ≫ T.mapAt (show p.1+1 ≤ p.1+r by omega))
    (hy : y = T.layerMap (p+(r,r-1))
      (Eq.mp (congrArg (fun m => HomotopyGroup m (T.stageAt (p.1+r)))
        (by dsimp; omega : p.2-p.1-1 = (p+(r,r-1)).2-(p+(r,r-1)).1)) a)) :
    U.connecting p (firstPageTransport T U e p x) =
      stageTransport T U e (p.2-p.1-1) (p.1+r) a ≫
        U.mapAt (show p.1+1 ≤ p.1+r by omega) ∧
    firstPageTransport T U e (p+(r,r-1)) y =
      U.layerMap (p+(r,r-1))
        (Eq.mp (congrArg (fun m => HomotopyGroup m (U.stageAt (p.1+r)))
          (by dsimp; omega : p.2-p.1-1 = (p+(r,r-1)).2-(p+(r,r-1)).1))
          (stageTransport T U e (p.2-p.1-1) (p.1+r) a)) :=
  ⟨selectedConnecting_lift T U e r (by omega) p x a ha,
    selectedLayer_lift T U e r p a y hy⟩

/-- Comparison of differential values under the two specified ambient
representative equations. -/
private theorem presentedDifferential_transport
    (T : AbstractAdamsTower unit X) (U : AbstractAdamsTower unit Y) (e : X ≅ Y)
    (D E : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ))
    (d : ∀ (r : ℤ) (p : ℤ × ℤ), (D p).page (↑(r-2).toNat : WithTop ℕ) ⟶
      (D (p+(r,r-1))).page (↑(r-2).toNat : WithTop ℕ))
    (d' : ∀ (r : ℤ) (p : ℤ × ℤ), (E p).page (↑(r-2).toNat : WithTop ℕ) ⟶
      (E (p+(r,r-1))).page (↑(r-2).toNat : WithTop ℕ))
    (P : TowerSequencePresentation unit T D d)
    (Q : TowerSequencePresentation unit U E d')
    (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((D p).Z (↑(r-2).toNat : WithTop ℕ)) : ModuleCat ℤ))
    (a : HomotopyGroup (p.2-p.1-1) (T.stageAt (p.1+r)))
    (z' : (Subobject.underlying.obj ((D (p+(r,r-1))).Z
      (↑(r-2).toNat : WithTop ℕ)) : ModuleCat ℤ))
    (w : (Subobject.underlying.obj ((E p).Z (↑(r-2).toNat : WithTop ℕ)) : ModuleCat ℤ))
    (w' : (Subobject.underlying.obj ((E (p+(r,r-1))).Z
      (↑(r-2).toNat : WithTop ℕ)) : ModuleCat ℤ))
    (hx : (((Q.ambient p).hom (((E p).Z _).arrow w)).val) =
      firstPageTransport T U e p (((P.ambient p).hom (((D p).Z _).arrow z)).val))
    (hy : (((Q.ambient (p+(r,r-1))).hom (((E (p+(r,r-1))).Z _).arrow w')).val) =
      firstPageTransport T U e (p+(r,r-1))
        (((P.ambient (p+(r,r-1))).hom (((D (p+(r,r-1))).Z _).arrow z')).val))
    (ha : T.connecting p (((P.ambient p).hom (((D p).Z _).arrow z)).val) =
      a ≫ T.mapAt (show p.1+1 ≤ p.1+r by omega))
    (hb : (((P.ambient (p+(r,r-1))).hom (((D (p+(r,r-1))).Z _).arrow z')).val) =
      T.layerMap (p+(r,r-1))
        (Eq.mp (congrArg (fun m => HomotopyGroup m (T.stageAt (p.1+r)))
          (by dsimp; omega : p.2-p.1-1 = (p+(r,r-1)).2-(p+(r,r-1)).1)) a)) :
    d r p ((D p).pageπ _ z) = (D (p+(r,r-1))).pageπ _ z' ∧
    d' r p ((E p).pageπ _ w) = (E (p+(r,r-1))).pageπ _ w' := by
  refine ⟨P.differential r hr p z a z' ha hb, ?_⟩
  apply Q.differential r hr p w
    (stageTransport T U e (p.2-p.1-1) (p.1+r) a) w'
  · rw [hx]
    exact selectedConnecting_lift T U e r (by omega) p _ a ha
  · rw [hy]
    exact selectedLayer_lift T U e r p a _ hb



end
end KIP126.Literature.BocksteinComparison.Stages
end

@[expose] section
namespace KIP126.Literature.BocksteinComparison.Caps
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
/-- The common cone remembers the relative class before passing to the
lambda quotient. -/
private noncomputable abbrev commonCone {A Y : Syn} (j : Y ⟶ A) (n : ℕ) : Syn :=
  HasFunctorialCofiber.cofib (lambdaPow n Y ≫ j)

private noncomputable def toRelative {A Y : Syn} (j : Y ⟶ A) (n : ℕ) :
    commonCone j n ⟶ HasFunctorialCofiber.cofib j :=
  HasFunctorialCofiber.cofibMap (lambdaPow n Y ≫ j) j
    (lambdaPow n Y) (𝟙 A) (by simp)

private noncomputable def toQuotient {A Y : Syn} (j : Y ⟶ A) (n : ℕ) :
    commonCone j n ⟶ XModLambdaN A n :=
  HasFunctorialCofiber.cofibMap (lambdaPow n Y ≫ j) (lambdaPow n A)
    ((SyntheticCategory.biShift (0, -(n : ℤ))).map j) (𝟙 A)
    (by simpa only [Category.comp_id] using lambdaPow_naturality n j)

@[reassoc] private theorem toRelative_boundary {A Y : Syn} (j : Y ⟶ A) (n : ℕ) :
    toRelative j n ≫ HasFunctorialCofiber.cofibδ j =
      HasFunctorialCofiber.cofibδ (lambdaPow n Y ≫ j) ≫
        (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n Y) :=
  HasFunctorialCofiber.cofibMap_δ _ _ _ _ _

@[reassoc] private theorem toQuotient_boundary {A Y : Syn} (j : Y ⟶ A) (n : ℕ) :
    toQuotient j n ≫ HasFunctorialCofiber.cofibδ (lambdaPow n A) =
      HasFunctorialCofiber.cofibδ (lambdaPow n Y ≫ j) ≫
        (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -(n : ℤ))).map j) :=
  HasFunctorialCofiber.cofibMap_δ _ _ _ _ _

/-- A specified relative class whose actual boundary is divisible by
lambda^n lifts to the common cone, retaining both that class and its chosen
divided boundary. The lift and its correction are constructed by exactness. -/
private theorem exists_commonLift_of_relative_boundary {A Y S : Syn}
    (j : Y ⟶ A) (n : ℕ) (x : S ⟶ HasFunctorialCofiber.cofib j)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj Y))
    (hxy : x ≫ HasFunctorialCofiber.cofibδ j =
      y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n Y)) :
    ∃ c : S ⟶ commonCone j n,
      c ≫ toRelative j n = x ∧
      c ≫ HasFunctorialCofiber.cofibδ (lambdaPow n Y ≫ j) = y := by
  have hjzero : HasFunctorialCofiber.cofibδ j ≫
      (shiftFunctor Syn (1 : ℤ)).map j = 0 :=
    comp_distTriang_mor_zero₃₁ _ (HasFunctorialCofiber.cofib_distinguished j)
  have hjzero' : HasFunctorialCofiber.cofibι (lambdaPow n Y ≫ j) ≫
      HasFunctorialCofiber.cofibδ (lambdaPow n Y ≫ j) = 0 :=
    comp_distTriang_mor_zero₂₃ _
      (HasFunctorialCofiber.cofib_distinguished (lambdaPow n Y ≫ j))
  have hyzero : y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n Y ≫ j) = 0 := by
    rw [Functor.map_comp, ← Category.assoc, ← hxy, Category.assoc,
      hjzero, comp_zero]
  obtain ⟨c, hc⟩ := Triangle.coyoneda_exact₁ _
    (HasFunctorialCofiber.cofib_distinguished (lambdaPow n Y ≫ j)) y hyzero
  change S ⟶ commonCone j n at c
  change y = c ≫ HasFunctorialCofiber.cofibδ (lambdaPow n Y ≫ j) at hc
  have hcz : (c ≫ toRelative j n) ≫ HasFunctorialCofiber.cofibδ j =
      y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n Y) := by
    rw [Category.assoc, toRelative_boundary, ← Category.assoc, ← hc]
  have hz : (x - c ≫ toRelative j n) ≫ HasFunctorialCofiber.cofibδ j = 0 := by
    rw [Preadditive.sub_comp, hxy, hcz, sub_self]
  obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₃ _
    (HasFunctorialCofiber.cofib_distinguished j)
    (x - c ≫ toRelative j n) hz
  change S ⟶ A at a
  change x - c ≫ toRelative j n = a ≫ HasFunctorialCofiber.cofibι j at ha
  have hi : HasFunctorialCofiber.cofibι (lambdaPow n Y ≫ j) ≫
      toRelative j n = HasFunctorialCofiber.cofibι j := by
    exact (HasFunctorialCofiber.cofibMap_ι (lambdaPow n Y ≫ j) j
      (lambdaPow n Y) (𝟙 A) (by simp)).symm.trans (Category.id_comp _)
  refine ⟨c + a ≫ HasFunctorialCofiber.cofibι (lambdaPow n Y ≫ j), ?_, ?_⟩
  · rw [Preadditive.add_comp, Category.assoc, hi, ← ha]
    abel
  · rw [Preadditive.add_comp, Category.assoc,
      hjzero', comp_zero, add_zero]
    exact hc.symm

/-- The lambda cap of a fixed relative source is constructed, together
with a common-cone witness preserving that source and the divided boundary. -/
private theorem exists_cap_of_relative_boundary {A Y S : Syn}
    (j : Y ⟶ A) (n : ℕ) (x : S ⟶ HasFunctorialCofiber.cofib j)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj Y))
    (hxy : x ≫ HasFunctorialCofiber.cofibδ j =
      y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n Y)) :
    ∃ (c : S ⟶ commonCone j n) (z : S ⟶ XModLambdaN A n),
      c ≫ toRelative j n = x ∧ c ≫ toQuotient j n = z ∧
      c ≫ HasFunctorialCofiber.cofibδ (lambdaPow n Y ≫ j) = y ∧
      z ≫ HasFunctorialCofiber.cofibδ (lambdaPow n A) =
        y ≫ (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -(n : ℤ))).map j) := by
  obtain ⟨c, hx, hy⟩ := exists_commonLift_of_relative_boundary j n x y hxy
  refine ⟨c, c ≫ toQuotient j n, hx, rfl, hy, ?_⟩
  rw [Category.assoc, toQuotient_boundary, ← Category.assoc, hy]


private theorem exists_cap_at_target_of_relative_boundary {A Y S X : Syn}
    (j : Y ⟶ A) (f : A ⟶ X) (n : ℕ)
    (x : S ⟶ HasFunctorialCofiber.cofib j)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj Y))
    (hxy : x ≫ HasFunctorialCofiber.cofibδ j =
      y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n Y)) :
    ∃ (c : S ⟶ commonCone j n) (z : S ⟶ XModLambdaN X n),
      c ≫ toRelative j n = x ∧
      c ≫ HasFunctorialCofiber.cofibδ (lambdaPow n Y ≫ j) = y ∧
      z = c ≫ toQuotient j n ≫ XModLambdaN.map f n ∧
      z ≫ XModLambdaN.proj X n =
        y ≫ (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -(n : ℤ))).map (j ≫ f)) := by
  obtain ⟨c,z,hx,hz,hy,hb⟩ := exists_cap_of_relative_boundary j n x y hxy
  refine ⟨c, z ≫ XModLambdaN.map f n, hx, hy, ?_, ?_⟩
  · rw [← hz, Category.assoc]
  · rw [Category.assoc, XModLambdaN.proj_naturality, ← Category.assoc]
    change (z ≫ HasFunctorialCofiber.cofibδ (lambdaPow n A)) ≫ _ = _
    rw [hb, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]


/-- Source triangle with its specified boundary and a normalized first
arrow equal to the displayed composite. -/
private def sourceTriangleIso {A Y D : Syn} (j : Y ⟶ A) (n : ℕ)
    (i : A ⟶ D)
    (δ : D ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj Y))
    (hT : Triangle.mk (lambdaPow n Y ≫ j) i δ ∈ distTriang Syn) :
    Triangle.mk (lambdaPow n Y ≫ j) i δ ≅
      Triangle.mk (lambdaPow n Y ≫ j)
        (HasFunctorialCofiber.cofibι (lambdaPow n Y ≫ j))
        (HasFunctorialCofiber.cofibδ (lambdaPow n Y ≫ j)) :=
  isoTriangleOfIso₁₂ _ _ hT (HasFunctorialCofiber.cofib_distinguished _)
    (Iso.refl _) (Iso.refl _) (by simp)

private def sourceConeIso {A Y D : Syn} (j : Y ⟶ A) (n : ℕ)
    (i : A ⟶ D)
    (δ : D ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj Y))
    (hT : Triangle.mk (lambdaPow n Y ≫ j) i δ ∈ distTriang Syn) :
    D ≅ commonCone j n :=
  Triangle.π₃.mapIso (sourceTriangleIso j n i δ hT)

@[reassoc] private theorem sourceConeIso_inclusion {A Y D : Syn} (j : Y ⟶ A) (n : ℕ)
    (i : A ⟶ D)
    (δ : D ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj Y))
    (hT : Triangle.mk (lambdaPow n Y ≫ j) i δ ∈ distTriang Syn) :
    i ≫ (sourceConeIso j n i δ hT).hom =
      HasFunctorialCofiber.cofibι (lambdaPow n Y ≫ j) := by
  have h := (sourceTriangleIso j n i δ hT).hom.comm₂
  change i ≫ (sourceConeIso j n i δ hT).hom =
    (sourceTriangleIso j n i δ hT).hom.hom₂ ≫
      HasFunctorialCofiber.cofibι (lambdaPow n Y ≫ j) at h
  simpa only [sourceTriangleIso, isoTriangleOfIso₁₂_hom_hom₂,
    Iso.refl_hom, Category.id_comp] using h

@[reassoc] private theorem sourceConeIso_boundary {A Y D : Syn} (j : Y ⟶ A) (n : ℕ)
    (i : A ⟶ D)
    (δ : D ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj Y))
    (hT : Triangle.mk (lambdaPow n Y ≫ j) i δ ∈ distTriang Syn) :
    (sourceConeIso j n i δ hT).hom ≫
      HasFunctorialCofiber.cofibδ (lambdaPow n Y ≫ j) = δ := by
  have h := (sourceTriangleIso j n i δ hT).hom.comm₃
  change δ ≫ (shiftFunctor Syn (1 : ℤ)).map
      (sourceTriangleIso j n i δ hT).hom.hom₁ =
    (sourceConeIso j n i δ hT).hom ≫
      HasFunctorialCofiber.cofibδ (lambdaPow n Y ≫ j) at h
  have h₁ : (sourceTriangleIso j n i δ hT).hom.hom₁ =
      𝟙 ((SyntheticCategory.biShift (0, -(n : ℤ))).obj Y) := by
    simp only [sourceTriangleIso, isoTriangleOfIso₁₂_hom_hom₁, Iso.refl_hom]
    rfl
  rw [h₁, CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h.symm

/-- A representative in the source relative triangle supplies the cap
over the fixed base, with relative face and boundary induced by c. -/
private theorem cap_from_source_triangle {A Y D S X : Syn}
    (j : Y ⟶ A) (f : A ⟶ X) (n : ℕ)
    (i : A ⟶ D)
    (δ : D ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj Y))
    (hT : Triangle.mk (lambdaPow n Y ≫ j) i δ ∈ distTriang Syn)
    (c : S ⟶ D) :
    ∃ (x : S ⟶ HasFunctorialCofiber.cofib j) (z : S ⟶ XModLambdaN X n),
      x = c ≫ (sourceConeIso j n i δ hT).hom ≫ toRelative j n ∧
      x ≫ HasFunctorialCofiber.cofibδ j =
        c ≫ δ ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n Y) ∧
      z = c ≫ (sourceConeIso j n i δ hT).hom ≫
        toQuotient j n ≫ XModLambdaN.map f n ∧
      z ≫ XModLambdaN.proj X n =
        c ≫ δ ≫ (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -(n : ℤ))).map (j ≫ f)) := by
  refine ⟨c ≫ (sourceConeIso j n i δ hT).hom ≫ toRelative j n,
    c ≫ (sourceConeIso j n i δ hT).hom ≫ toQuotient j n ≫ XModLambdaN.map f n,
    rfl, ?_, rfl, ?_⟩
  · simp only [Category.assoc, toRelative_boundary, sourceConeIso_boundary_assoc]
  · rw [Category.assoc, Category.assoc, Category.assoc,
      XModLambdaN.proj_naturality]
    change c ≫ (sourceConeIso j n i δ hT).hom ≫ toQuotient j n ≫
      HasFunctorialCofiber.cofibδ (lambdaPow n A) ≫ _ = _
    rw [toQuotient_boundary_assoc, sourceConeIso_boundary_assoc]
    simp only [Functor.map_comp]


end
end KIP126.Literature.BocksteinComparison.Caps
end

@[expose] section
namespace KIP126.Literature.BocksteinComparison.Stages
open KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated KIP126.StableHomotopy
universe u v
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  {H : C} {unit : SphereSpectrum ⟶ H}

private def coefficientTriangleIso {A B L : C}
    (d : A ⟶ B) (i : B ⟶ L) (δ : L ⟶ A⟦(1 : ℤ)⟧)
    (e : L ≅ H ⊗ B) (hunit : i ≫ e.hom = unitAt unit B) :
    Triangle.mk d i δ ≅ Triangle.mk d (unitAt unit B) (e.inv ≫ δ) :=
  Triangle.isoMk _ _ (Iso.refl A) (Iso.refl B) e
    (by change d ≫ 𝟙 B = 𝟙 A ≫ d; simp)
    (by
      change i ≫ e.hom = 𝟙 B ≫ unitAt unit B
      exact hunit.trans (Category.id_comp _).symm)
    (by
      change δ ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 A) = e.hom ≫ (e.inv ≫ δ)
      exact ((congrArg (fun f => δ ≫ f) ((shiftFunctor C (1 : ℤ)).map_id A)).trans
        (Category.comp_id δ)).trans (e.hom_inv_id_assoc δ).symm)

private theorem coefficientTriangle_distinguished {A B L : C}
    (d : A ⟶ B) (i : B ⟶ L) (δ : L ⟶ A⟦(1 : ℤ)⟧)
    (hT : Triangle.mk d i δ ∈ distTriang C)
    (e : L ≅ H ⊗ B) (hunit : i ≫ e.hom = unitAt unit B) :
    Triangle.mk d (unitAt unit B) (e.inv ≫ δ) ∈ distTriang C :=
  (distinguished_iff_of_iso (coefficientTriangleIso d i δ e hunit)).mp hT

private theorem coefficientTriangles_distinguished
    (A L : ℕ → C) (d : ∀ n, A (n+1) ⟶ A n)
    (i : ∀ n, A n ⟶ L n) (δ : ∀ n, L n ⟶ (A (n+1))⟦(1 : ℤ)⟧)
    (hT : ∀ n, Triangle.mk (d n) (i n) (δ n) ∈ distTriang C)
    (e : ∀ n, L n ≅ H ⊗ A n)
    (hunit : ∀ n, i n ≫ (e n).hom = unitAt unit (A n)) :
    ∀ n, Triangle.mk (d n) (unitAt unit (A n)) ((e n).inv ≫ δ n) ∈ distTriang C :=
  fun n => coefficientTriangle_distinguished (d n) (i n) (δ n) (hT n) (e n) (hunit n)

variable [HasFunctorialCofiber (C := C)] {X : C}

/-- Tower construction on the transported source triangles. -/
private def coefficientTowerFromSourceTriangles
    (A L : ℕ → C) (d : ∀ n, A (n+1) ⟶ A n)
    (i : ∀ n, A n ⟶ L n) (δ : ∀ n, L n ⟶ (A (n+1))⟦(1 : ℤ)⟧)
    (hT : ∀ n, Triangle.mk (d n) (i n) (δ n) ∈ distTriang C)
    (e : ∀ n, L n ≅ H ⊗ A n)
    (hunit : ∀ n, i n ≫ (e n).hom = unitAt unit (A n))
    (e₀ : A 0 ≅ X) : AbstractAdamsTower unit X :=
  towerFromTriangles A d (fun n => (e n).inv ≫ δ n)
    (coefficientTriangles_distinguished A L d i δ hT e hunit) e₀


end
end KIP126.Literature.BocksteinComparison.Stages
end
