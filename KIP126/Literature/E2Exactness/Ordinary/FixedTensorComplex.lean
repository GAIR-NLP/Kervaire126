module
import all KIP126.Literature.E2Exactness.Ordinary.TensorStageHomology
import all KIP126.Literature.E2Exactness.Ordinary.CochainCoordinates

@[expose] section
namespace KIP126.Literature.Standard.FixedTensorE2
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.AdamsSynthetic
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H X : C} {unit : SphereSpectrum ⟶ H}

private def layerBoundary (T : AbstractAdamsTower unit X) (s : ℤ) :
    T.layer s ⟶ (T.layer (s+1))⟦(1:ℤ)⟧ :=
  HasFunctorialCofiber.cofibδ (T.mapAt (show s ≤ s+1 by omega)) ≫
    (shiftFunctor C (1:ℤ)).map
      (HasFunctorialCofiber.cofibι (T.mapAt (show s+1 ≤ (s+1)+1 by omega)))

private theorem layerBoundary_sq (T : AbstractAdamsTower unit X) (s : ℤ) :
    layerBoundary T s ≫ (shiftFunctor C (1:ℤ)).map (layerBoundary T (s+1)) = 0 := by
  have hz : HasFunctorialCofiber.cofibι (T.mapAt (show s+1 ≤ (s+1)+1 by omega)) ≫
      HasFunctorialCofiber.cofibδ (T.mapAt (show s+1 ≤ (s+1)+1 by omega)) = 0 :=
    comp_distTriang_mor_zero₂₃ _ (HasFunctorialCofiber.cofib_distinguished _)
  dsimp only [layerBoundary]
  rw [Functor.map_comp, Category.assoc, ← Category.assoc
    ((shiftFunctor C (1:ℤ)).map _), ← Functor.map_comp, hz, Functor.map_zero,
    zero_comp, comp_zero]

private def shiftedLayerDifferential (T : AbstractAdamsTower unit X) (s : ℤ) :
    (T.layer s)⟦s⟧ ⟶ (T.layer (s+1))⟦s+1⟧ :=
  (shiftFunctor C s).map (layerBoundary T s) ≫
    (shiftFunctorAdd' C (1:ℤ) s (s+1) (by omega)).inv.app (T.layer (s+1))

private theorem shiftedLayerDifferential_sq (T : AbstractAdamsTower unit X) (s : ℤ) :
    shiftedLayerDifferential T s ≫ shiftedLayerDifferential T (s+1) = 0 := by
  dsimp only [shiftedLayerDifferential]
  rw [Category.assoc, ← Category.assoc
    ((shiftFunctorAdd' C (1:ℤ) s (s+1) (by omega)).inv.app _)]
  rw [← NatTrans.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [← Category.assoc, ← Functor.map_comp, layerBoundary_sq, Functor.map_zero, zero_comp]

private def shiftedLayerComplex (T : AbstractAdamsTower unit X) : CochainComplex C ℤ :=
  CochainComplex.of (fun s => (T.layer s)⟦s⟧) (shiftedLayerDifferential T)
    (shiftedLayerDifferential_sq T)

private theorem shiftedLayerComplex_d (T : AbstractAdamsTower unit X) (s : ℤ) :
    (shiftedLayerComplex T).d s (s+1) = shiftedLayerDifferential T s :=
  by
    unfold shiftedLayerComplex
    exact CochainComplex.of_d (fun s => (T.layer s)⟦s⟧) (shiftedLayerDifferential T) s

section Actual
open KIP126.AdamsSynthetic.Completed
variable {X₀ : Spectrum} (T : AbstractAdamsTower coefficients.unit X₀)

private def tensorHomotopyDifferential (t : ℤ) (X : Spectrum) (s : ℤ) :
    HomotopyGroup t ((T.layer s)⟦s⟧ ⊗ X) →ₗ[ℤ]
      HomotopyGroup t ((T.layer (s+1))⟦s+1⟧ ⊗ X) :=
  (inducedMap (shiftedLayerDifferential T s ▷ X) t).toIntLinearMap

private theorem tensorHomotopyDifferential_sq (t : ℤ) (X : Spectrum) (s : ℤ) :
    (tensorHomotopyDifferential T t X (s+1)).comp
      (tensorHomotopyDifferential T t X s) = 0 := by
  letI := closedBackground.tensorShift X
  letI := closedBackground.tensorExact X
  ext a
  change (a ≫ shiftedLayerDifferential T s ▷ X) ≫
    shiftedLayerDifferential T (s+1) ▷ X = 0
  rw [Category.assoc, ← comp_whiskerRight, shiftedLayerDifferential_sq]
  change a ≫ (tensorRight X).map 0 = 0
  rw [Functor.map_zero, comp_zero]

private def tensorHomotopyCochain (t : ℤ) (X : Spectrum) :
    CochainComplex (ModuleCat ℤ) ℤ :=
  CochainComplex.of (fun s => ModuleCat.of ℤ (HomotopyGroup t ((T.layer s)⟦s⟧ ⊗ X)))
    (fun s => ModuleCat.ofHom (tensorHomotopyDifferential T t X s)) (fun s => by
      ext a
      exact LinearMap.congr_fun (tensorHomotopyDifferential_sq T t X s) a)

private theorem tensorHomotopyCochain_d (t s : ℤ) (X : Spectrum) :
    (tensorHomotopyCochain T t X).d s (s+1) =
      ModuleCat.ofHom (tensorHomotopyDifferential T t X s) := by
  unfold tensorHomotopyCochain
  exact CochainComplex.of_d
    (fun s => ModuleCat.of ℤ (HomotopyGroup t ((T.layer s)⟦s⟧ ⊗ X)))
    (fun s => ModuleCat.ofHom (tensorHomotopyDifferential T t X s)) s

private def tensorHomotopyCochainMap (t : ℤ) {X Y : Spectrum} (f : X ⟶ Y) :
    tensorHomotopyCochain T t X ⟶ tensorHomotopyCochain T t Y :=
  CochainComplex.ofHom (fun s => ModuleCat.ofHom
    (inducedMap ((T.layer s)⟦s⟧ ◁ f) t).toIntLinearMap) (fun s => by
      rw [tensorHomotopyCochain_d, tensorHomotopyCochain_d]
      ext a
      symm
      change (a ≫ shiftedLayerDifferential T s ▷ X) ≫ (T.layer (s+1))⟦s+1⟧ ◁ f =
        (a ≫ (T.layer s)⟦s⟧ ◁ f) ≫ shiftedLayerDifferential T s ▷ Y
      simp only [Category.assoc]
      rw [whisker_exchange])

private theorem tensorHomotopyCochainMap_id (t : ℤ) (X : Spectrum) :
    tensorHomotopyCochainMap T t (𝟙 X) = 𝟙 _ := by
  ext s a
  change a ≫ (T.layer s)⟦s⟧ ◁ 𝟙 X = a
  rw [whiskerLeft_id, Category.comp_id]

private theorem tensorHomotopyCochainMap_comp (t : ℤ) {X Y Z : Spectrum}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    tensorHomotopyCochainMap T t (f ≫ g) =
      tensorHomotopyCochainMap T t f ≫ tensorHomotopyCochainMap T t g := by
  ext s a
  change a ≫ (T.layer s)⟦s⟧ ◁ (f ≫ g) =
    (a ≫ (T.layer s)⟦s⟧ ◁ f) ≫ (T.layer s)⟦s⟧ ◁ g
  rw [whiskerLeft_comp, Category.assoc]
end Actual
end
end KIP126.Literature.Standard.FixedTensorE2
end
