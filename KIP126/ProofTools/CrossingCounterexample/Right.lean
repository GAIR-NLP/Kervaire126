module

import all KIP126.ProofTools.CrossingCounterexample.Sphere
import all KIP126.ProofTools.CrossingCounterexample.Moore
import all KIP126.ProofTools.CrossingCounterexample.Matrix
import all KIP126.ProofTools.CrossingCounterexample.Crossing
import all KIP126.ProofTools.GeneralizedLeibniz.Reverse

/-! The actual nonzero length-one extension in the larger finite λ quotient. -/
@[expose] section
namespace KIP126.ProofTools.Internal.CrossingCounterexample
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)
open KIP126.Literature KIP126.Computation KIP126.Computation.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private abbrev rightSourceObject : SyntheticObject (coefficients := background.coefficients) :=
  .quotient 3 (extensionSourceObject background candidateAdamsObject candidateAdamsObject matrixMap)

private abbrev rightTargetObject : SyntheticObject (coefficients := background.coefficients) :=
  .quotient 3 (.nu candidateAdamsObject)

private def rightSphereClass : BiHom 0 1 ((quotientNu 3).obj S) :=
  quotientClass 3 h0Nu

private def rightSource : BiHom 0 1 (rightSourceObject.obj background.nu background.auxiliary) :=
  biprod.lift ((2 : ℕ) • rightSphereClass) (biprod.lift 0 0) ≫
    (matrixFiniteCoordinates 3 (by decide)).inv

private def rightImage : BiHom 0 1 (rightTargetObject.obj background.nu background.auxiliary) :=
  ((4 : ℕ) • rightSphereClass) ≫ biprod.inr ≫ biprod.inr ≫
    (candidateQuotientBiprodIso 3 (by decide)).inv

private theorem right_source_single_coordinate :
    rightSource = ((2 : ℕ) • rightSphereClass) ≫ biprod.inl ≫
      (matrixFiniteCoordinates 3 (by decide)).inv := by
  have h : biprod.lift ((2 : ℕ) • rightSphereClass)
      (biprod.lift (0 : BiHom 0 1 ((quotientNu 3).obj mooreFour))
        (0 : BiHom 0 1 ((quotientNu 3).obj S))) =
      ((2 : ℕ) • rightSphereClass) ≫ biprod.inl := by
    apply biprod.hom_ext
    · simp
    · apply biprod.hom_ext <;> simp
  simpa only [rightSource, Category.assoc] using congrArg
    (fun z => z ≫ (matrixFiniteCoordinates 3 (by decide)).inv) h

private theorem right_sphere_two_bottom :
    ((2 : ℕ) • rightSphereClass) ≫ (quotientNu 3).map bottom = 0 := by
  have hz : ((2 : ℕ) • h0Nu) ≫ background.nu.functor.map bottom = 0 := by
    simpa only [h0Nu, Preadditive.nsmul_comp, Category.assoc] using moore_two_h0_zero
  change ((2 : ℕ) • (h0Nu ≫ XModLambdaN.incl _ 3)) ≫
      XModLambdaN.map (background.nu.functor.map bottom) 3 = 0
  rw [← Preadditive.nsmul_comp, Category.assoc, ← XModLambdaN.incl_naturality,
    ← Category.assoc, hz, zero_comp]

private theorem right_source_image :
    rightSource ≫ finiteExtensionMap background candidateAdamsObject candidateAdamsObject matrixMap 3 =
      rightImage := by
  apply (cancel_mono (candidateQuotientBiprodIso 3 (by decide)).hom).mp
  have h := matrix_image 3 (by decide) 0 1 ((2 : ℕ) • rightSphereClass)
    (0 : BiHom 0 1 ((quotientNu 3).obj mooreFour)) 0
  change rightSource ≫ finiteExtensionMap background candidateAdamsObject candidateAdamsObject matrixMap 3 ≫
    (candidateQuotientBiprodIso 3 (by decide)).hom = _ at h
  rw [Category.assoc, h, right_sphere_two_bottom]
  simp only [rightImage, Category.assoc, Iso.inv_hom_id, Category.comp_id, nsmul_zero,
    smul_smul, show (2 : ℕ) * 2 = 4 from rfl]
  apply biprod.hom_ext
  · simp
  · apply biprod.hom_ext <;> simp

private theorem right_sphere_two_filtration :
    FiltrationAtLeast background.syntheticTower 2 ((2 : ℕ) • rightSphereClass) := by
  have hd := sphere_finite_lambda_detects 3 (by decide) 2 2 1 h0Square h0SquareNu h0SquareNu_label
  have hf := detects_filtration (.quotient 3 (.nu .sphere)) (2,2,2-(1 : ℕ)) _ _ hd
  rw [h0SquareNu_lambda] at hf
  simpa only [rightSphereClass, quotientClass, Preadditive.nsmul_comp] using hf

private theorem right_sphere_four_filtration :
    FiltrationAtLeast background.syntheticTower 3 ((4 : ℕ) • rightSphereClass) := by
  have hd := sphere_finite_lambda_detects 3 (by decide) 3 3 2 h0Cube h0CubeNu h0CubeNu_label
  have hf := detects_filtration (.quotient 3 (.nu .sphere)) (3,3,3-(2 : ℕ)) _ _ hd
  rw [h0CubeNu_lambda_two] at hf
  simpa only [rightSphereClass, quotientClass, Preadditive.nsmul_comp] using hf

private theorem right_source_filtration :
    FiltrationAtLeast background.syntheticTower 2 rightSource := by
  rw [right_source_single_coordinate]
  exact map_preserves_filtration (background.convergentMap
    (.quotient 3 (.nu .sphere)) rightSourceObject
    (biprod.inl ≫ (matrixFiniteCoordinates 3 (by decide)).inv))
    (0,1) 2 ((2 : ℕ) • rightSphereClass) right_sphere_two_filtration

private theorem right_image_filtration :
    FiltrationAtLeast background.syntheticTower 3 rightImage :=
  map_preserves_filtration (background.convergentMap
    (.quotient 3 (.nu .sphere)) rightTargetObject
    (biprod.inr ≫ biprod.inr ≫ (candidateQuotientBiprodIso 3 (by decide)).inv))
    (0,1) 3 ((4 : ℕ) • rightSphereClass) right_sphere_four_filtration

private theorem right_image_ne_zero : rightImage ≠ 0 := by
  intro hz
  have h := congrArg (fun z => z ≫ (candidateQuotientBiprodIso 3 (by decide)).hom ≫
    biprod.snd ≫ biprod.snd) hz
  simp only [rightImage, Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_snd_assoc,
    biprod.inr_snd, Category.comp_id, zero_comp] at h
  apply four_h0Nu_quotient_ne_zero
  simpa only [rightSphereClass, quotientClass, Preadditive.nsmul_comp] using h

private theorem right_image_not_filtration_four :
    ¬ FiltrationAtLeast background.syntheticTower 4 rightImage := by
  intro hf
  exact right_image_ne_zero (finite_high_filtration_zero candidateAdamsObject 3 (by decide)
    0 1 4 (by decide) rightImage hf)

private theorem candidate_right_extension :
    ∃ (x : ((background.family.obj (rightSourceObject.obj background.nu background.auxiliary)).sequence.ssData
        (2,2,1)).eInfty)
      (y : ((background.family.obj (rightTargetObject.obj background.nu background.auxiliary)).sequence.ssData
        (3,3,1)).eInfty),
      y ≠ 0 ∧ TowerExtensionEquation
        (background.convergentMap rightSourceObject rightTargetObject
          (finiteExtensionMap background candidateAdamsObject candidateAdamsObject matrixMap 3))
        (0,1) 2 1 x y := by
  apply actual_extension_of_filtered_image
    (background.convergentMap rightSourceObject rightTargetObject
      (finiteExtensionMap background candidateAdamsObject candidateAdamsObject matrixMap 3))
    (0,1) 2 1 (by decide) rightSource right_source_filtration
  · rw [right_source_image]
    exact right_image_filtration
  · rw [right_source_image]
    exact right_image_not_filtration_four

end
end KIP126.ProofTools.Internal.CrossingCounterexample
