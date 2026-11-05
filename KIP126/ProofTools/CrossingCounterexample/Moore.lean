module

import all KIP126.ProofTools.CrossingCounterexample.Sphere
import all KIP126.ProofTools.GeneralizedLeibniz.Reverse

/-! The bottom-cell boundaries of the actual Moore(4) spectrum. -/
@[expose] section
namespace KIP126.ProofTools.Internal.CrossingCounterexample
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)
open KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Paper.DoublingNumericalExtensions
open KIP126.ProofTools.Paper.NuNumericalExtensions
open KIP126.ProofTools.Paper.NumericalExamples
open KIP126.Computation KIP126.Computation.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

private theorem moore_two_normalized_h0_zero :
    ((2 : ℕ) • h0NormalizedMap) ≫ background.nu.functor.map bottom = 0 := by
  rw [← moore_normalized_four, ← moore_normalized_bottom]
  have hz := comp_distTriang_mor_zero₁₂
    (normalizedTriangle background mooreTriangle moore_exponent_sum)
    moore_normalized_distinguished
  simp only [Category.assoc] at hz ⊢
  rw [← Category.assoc _ _ mooreNormalizedTargetIso.hom, hz, zero_comp, comp_zero]

private theorem moore_two_h0_zero :
    ((2 : ℕ) • KIP126.Literature.Standard.syntheticH0) ≫
      background.nu.unitIso.inv ≫ background.nu.functor.map bottom = 0 := by
  apply (cancel_epi ((SyntheticCategory.biShift (0,1)).map background.nu.unitIso.hom)).mp
  simpa only [h0NormalizedMap, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
    Category.assoc, comp_zero] using moore_two_normalized_h0_zero

private theorem moore_four_h0_zero :
    ((4 : ℕ) • KIP126.Literature.Standard.syntheticH0) ≫
      background.nu.unitIso.inv ≫ background.nu.functor.map bottom = 0 := by
  have h := congrArg (fun z => (2 : ℕ) • z) moore_two_h0_zero
  simpa only [Preadditive.nsmul_comp, smul_smul, smul_zero,
    show (2 : ℕ) * 2 = 4 from rfl] using h

private theorem moore_bottom_native_label (s t : ℤ)
    (y : Ambient background .sphere (s,t))
    (α : BiHom (t-s) t (background.nu.functor.obj S))
    (hα : α ≫ XModLambdaN.incl _ 1 = nativeFirstLabel .sphere s t y) :
    (α ≫ background.nu.functor.map bottom) ≫ XModLambdaN.incl _ 1 =
      nativeFirstLabel mooreAdamsObject s t
        ((background.classical.map bottom).pageMap 2 (s,t) y) := by
  rw [Category.assoc, XModLambdaN.incl_naturality, ← Category.assoc, hα]
  exact native_first_label_natural .sphere mooreAdamsObject bottom s t y

private theorem moore_bottom_boundary_of_lambda_zero (s t : ℤ)
    (k : ℕ) (hk : 0 < k) (y : Ambient background .sphere (s,t))
    (α : BiHom (t-s) t (background.nu.functor.obj S))
    (hα : α ≫ XModLambdaN.incl _ 1 = nativeFirstLabel .sphere s t y)
    (hz : lambdaMultiply k (α ≫ background.nu.functor.map bottom) = 0) :
    (background.classical.map bottom).pageMap 2 (s,t) y ∈
      boundaries background mooreAdamsObject (k+1) (s,t) :=
  first_label_lambda_zero_boundary mooreAdamsObject s t k hk
    ((background.classical.map bottom).pageMap 2 (s,t) y)
    (α ≫ background.nu.functor.map bottom) (moore_bottom_native_label s t y α hα) hz

private theorem moore_h0Square_boundary :
    (background.classical.map bottom).pageMap 2 (2,2) h0Square ∈
      boundaries background mooreAdamsObject 2 (2,2) := by
  apply moore_bottom_boundary_of_lambda_zero 2 2 1 (by decide) h0Square h0SquareNu
    h0SquareNu_label
  have hl : lambdaMultiply 1 (h0SquareNu ≫ background.nu.functor.map bottom) =
      lambdaMultiply 1 h0SquareNu ≫ background.nu.functor.map bottom := by
    simp only [lambdaMultiply, Category.assoc]
  rw [hl, h0SquareNu_lambda]
  simpa only [h0Nu, Preadditive.nsmul_comp, Category.assoc] using moore_two_h0_zero

private theorem moore_h0Cube_boundary :
    (background.classical.map bottom).pageMap 2 (3,3) h0Cube ∈
      boundaries background mooreAdamsObject 3 (3,3) := by
  apply moore_bottom_boundary_of_lambda_zero 3 3 2 (by decide) h0Cube h0CubeNu
    h0CubeNu_label
  have hl : lambdaMultiply 2 (h0CubeNu ≫ background.nu.functor.map bottom) =
      lambdaMultiply 2 h0CubeNu ≫ background.nu.functor.map bottom := by
    simp only [lambdaMultiply, Category.assoc]
  rw [hl, h0CubeNu_lambda_two]
  simpa only [h0Nu, Preadditive.nsmul_comp, Category.assoc] using moore_four_h0_zero

private theorem moore_bottom_degree_two_boundary (x : Ambient background .sphere (2,2)) :
    (background.classical.map bottom).pageMap 2 (2,2) x ∈
      boundaries background mooreAdamsObject 2 (2,2) := by
  rcases one_coordinate_label_cases rfl
    (KIP126.Computation.Standard.coordinates 2 2 (by decide)) h0Square h0Square_basis x with
      rfl | rfl
  · simpa only [map_zero] using (boundaries background mooreAdamsObject 2 (2,2)).zero_mem
  · exact moore_h0Square_boundary

private theorem moore_bottom_degree_three_boundary (x : Ambient background .sphere (3,3)) :
    (background.classical.map bottom).pageMap 2 (3,3) x ∈
      boundaries background mooreAdamsObject 3 (3,3) := by
  rcases one_coordinate_label_cases rfl
    (KIP126.Computation.Standard.coordinates 3 3 (by decide)) h0Cube h0Cube_basis x with
      rfl | rfl
  · simpa only [map_zero] using (boundaries background mooreAdamsObject 3 (3,3)).zero_mem
  · exact moore_h0Cube_boundary

end
end KIP126.ProofTools.Internal.CrossingCounterexample
