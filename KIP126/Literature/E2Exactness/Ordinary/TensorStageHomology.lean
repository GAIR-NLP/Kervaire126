module
import all KIP126.Literature.E2Exactness.TensorHomotopyDetection
import all KIP126.Literature.E2Exactness.Ordinary.TensorAdamsTower

@[expose] section
namespace KIP126.Literature.Standard.E2LayerSES
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Literature.Standard.HModuleDetection
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem homologyShortExact_boundary_annihilated (T : Triangle Spectrum)
    (hT : T ∈ distTriang Spectrum) (hH : HomologyShortExact coefficients T) :
    coefficients.object ◁ T.mor₃ = 0 := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift coefficients.object
  letI := closedBackground.tensorExact coefficients.object
  letI : (tensorLeft coefficients.object).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_iso (tensorLeftIsoTensorRight coefficients.object).symm
  apply coefficient_tensor_map_zero_of_homotopy_zero
  intro d a
  obtain ⟨b,hb⟩ := (hH d).2.2 a
  change b ≫ coefficients.object ◁ T.mor₂ = a at hb
  change a ≫ coefficients.object ◁ T.mor₃ = 0
  rw [← hb, Category.assoc, ← whiskerLeft_comp,
    comp_distTriang_mor_zero₂₃ T hT]
  change b ≫ (tensorLeft coefficients.object).map 0 = 0
  rw [Functor.map_zero, comp_zero]

private def tensorSwap (A B X : Spectrum) : A ⊗ (B ⊗ X) ≅ B ⊗ (A ⊗ X) := by
  letI := closedBackground.symmetric
  exact (α_ A B X).symm ≪≫ (tensorRight X).mapIso (β_ A B) ≪≫ α_ B A X

private theorem tensorSwap_natural (A B : Spectrum) {X Y : Spectrum} (f : X ⟶ Y) :
    A ◁ (B ◁ f) ≫ (tensorSwap A B Y).hom =
      (tensorSwap A B X).hom ≫ B ◁ (A ◁ f) := by
  letI := closedBackground.symmetric
  change A ◁ (B ◁ f) ≫ ((α_ A B Y).inv ≫ (β_ A B).hom ▷ Y ≫ (α_ B A Y).hom) =
    ((α_ A B X).inv ≫ (β_ A B).hom ▷ X ≫ (α_ B A X).hom) ≫ B ◁ (A ◁ f)
  rw [← Category.assoc, ← Category.assoc, associator_inv_naturality_right]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, associator_naturality_right]

private theorem tensor_left_preserves_coefficient_annihilation (A : Spectrum)
    {X Y : Spectrum} (f : X ⟶ Y) (hf : coefficients.object ◁ f = 0) :
    coefficients.object ◁ (A ◁ f) = 0 := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift A
  letI := closedBackground.tensorExact A
  letI : (tensorLeft A).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_iso (tensorLeftIsoTensorRight A).symm
  apply (cancel_mono (tensorSwap coefficients.object A Y).hom).mp
  rw [tensorSwap_natural, zero_comp, hf]
  change _ ≫ (tensorLeft A).map 0 = 0
  rw [Functor.map_zero, comp_zero]

private theorem homologyShortExact_of_boundary_annihilated (T : Triangle Spectrum)
    (hT : T ∈ distTriang Spectrum) (hH : coefficients.object ◁ T.mor₃ = 0) :
    HomologyShortExact coefficients T := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift coefficients.object
  letI := closedBackground.tensorExact coefficients.object
  let e := (tensorLeftIsoTensorRight coefficients.object).symm
  letI : (tensorLeft coefficients.object).CommShift ℤ := Functor.CommShift.ofIso e ℤ
  letI : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
  letI : (tensorLeft coefficients.object).IsTriangulated := Functor.isTriangulated_of_iso e
  let F := tensorLeft coefficients.object
  let U := F.mapTriangle.obj T
  have hU : U ∈ distTriang Spectrum := F.map_distinguished T hT
  have hz : U.mor₃ = 0 := by
    change coefficients.object ◁ T.mor₃ ≫ _ = 0
    rw [hH, zero_comp]
  letI : Mono U.mor₁ := U.mono₁ hU hz
  intro d
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    exact (cancel_mono U.mor₁).mp hab
  · intro a
    change a ≫ U.mor₂ = 0 ↔ ∃ b, b ≫ U.mor₁ = a
    constructor
    · intro ha
      obtain ⟨b,hb⟩ := U.coyoneda_exact₂ hU a ha
      exact ⟨b,hb.symm⟩
    · rintro ⟨b,rfl⟩
      rw [Category.assoc, comp_distTriang_mor_zero₁₂ U hU, comp_zero]
  · intro a
    obtain ⟨b,hb⟩ := U.coyoneda_exact₃ hU a (by rw [hz,comp_zero])
    exact ⟨b,hb.symm⟩

private theorem stageFunctor_preserves_coefficient_annihilation
    {X Y : Spectrum} (f : X ⟶ Y) (hf : coefficients.object ◁ f = 0) (n : ℕ) :
    coefficients.object ◁
      ((KIP126.Literature.FiniteBoundaryStage21.TensorTower.stageFunctor coefficients.unit n).map f) = 0 := by
  induction n with
  | zero => exact hf
  | succ n ih => exact tensor_left_preserves_coefficient_annihilation _ _ ih

private instance actualTensorLeftShift (A : Spectrum) : (tensorLeft A).CommShift ℤ := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift A
  exact Functor.CommShift.ofIso (tensorLeftIsoTensorRight A).symm ℤ

private instance actualTensorLeftExact (A : Spectrum) : (tensorLeft A).IsTriangulated := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift A
  letI := closedBackground.tensorExact A
  let e := (tensorLeftIsoTensorRight A).symm
  letI : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
  exact Functor.isTriangulated_of_iso e

private theorem tensorStages_homologyShortExact (T : Triangle Spectrum)
    (hT : T ∈ distTriang Spectrum) (hH : HomologyShortExact coefficients T) (n : ℕ) :
    HomologyShortExact coefficients
      ((KIP126.Literature.FiniteBoundaryStage21.TensorTower.stageFunctor coefficients.unit n).mapTriangle.obj T) := by
  let F := KIP126.Literature.FiniteBoundaryStage21.TensorTower.stageFunctor coefficients.unit n
  have ht : F.mapTriangle.obj T ∈ distTriang Spectrum := F.map_distinguished T hT
  apply homologyShortExact_of_boundary_annihilated _ ht
  change coefficients.object ◁ (F.map T.mor₃ ≫ _) = 0
  rw [whiskerLeft_comp,
    stageFunctor_preserves_coefficient_annihilation T.mor₃
      (homologyShortExact_boundary_annihilated T hT hH), zero_comp]

end
end KIP126.Literature.Standard.E2LayerSES
end
