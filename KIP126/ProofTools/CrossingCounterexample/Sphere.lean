module

import all KIP126.ProofTools.CrossingCounterexample.Base
import all KIP126.ProofTools.GeneralizedMahowald.SphereLabels
import all KIP126.ProofTools.GeneralizedLeibniz.Reverse

/-! Actual sphere classes used in the crossing counterexample. -/
@[expose] section
namespace KIP126.ProofTools.Internal.CrossingCounterexample
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)
open KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Paper.NuNumericalExtensions
open KIP126.Computation KIP126.Computation.Standard
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

private theorem h0CubeNu_finite_lambda_ne_zero :
    quotientClass 3 (lambdaMultiply 2 h0CubeNu) ≠ 0 := by
  have hd := sphere_finite_lambda_detects 3 (by decide) 3 3 2 h0Cube h0CubeNu h0CubeNu_label
  have hc : h0Cube ∈ cycles background .sphere ((3 : ℤ)-3+(3-(2 : ℕ))) (3,3) :=
    permanentCycles_le_cycles background .sphere (3,3) _ h0Cube_permanent
  intro hz
  have hzero := detected_zero_infinity (.quotient 3 (.nu .sphere)) (3,3,3-(2 : ℕ))
    (finiteTargetLabel background .sphere 3 3 3 2 h0Cube) (hz ▸ hd)
  have hh := (finite_target_label_iff .sphere 3 (by decide) 3 3 2 (by decide)
    ⟨h0Cube,hc⟩ 0).mp hzero
  rw [map_zero] at hh
  have hb := (CrossingLabels.subquotient_zero_iff _ _ _).mp hh.symm
  rw [h0Cube_boundaries_eq_bot] at hb
  exact h0Cube_ne_zero hb

private theorem lambda_one_product_precomposition (w : ℤ)
    (x : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
    (y : BiHom 0 w (S_0_0 : SyntheticSpectrum)) :
    (biShiftAddIso (0,1+w) (0,-1) (0,w) (by ext <;> dsimp; omega)).inv.app S_0_0 ≫
      lambdaPow 1 (Smn (Syn := SyntheticSpectrum) 0 (1+w)) ≫ sphereProduct x y =
    (biShiftAddIso (0,0) (0,w) (0,w) (by ext <;> dsimp; omega)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (0,w)).map (lambdaMultiply 1 x) ≫ y := by
  let coh := background.quotients.coherence
  let A := (S_0_0 : SyntheticSpectrum)
  have h₁ := inverse_associativity coh (0,1) (0,w) (0,-1)
    (0,1+w) (0,w-1) (0,w) (by rfl) (by ext <;> dsimp; omega)
    (by ext <;> dsimp; omega) (by ext <;> dsimp; omega) A
  have h₂ := inverse_associativity coh (0,1) (0,-1) (0,w)
    (0,0) (0,w-1) (0,w) (by decide) (by ext <;> dsimp; omega)
    (by ext <;> dsimp; omega) (by ext <;> dsimp; omega) A
  have hl : lambdaPow 1 ((SyntheticCategory.biShift (0,w)).obj (Smn (Syn := SyntheticSpectrum) 0 1)) =
      (biShiftAddIso (0,w) (0,-1) (0,w-1) (by ext <;> dsimp; omega)).hom.app (Smn 0 1) ≫
        (biShiftAddIso (0,-1) (0,w) (0,w-1) (by ext <;> dsimp; omega)).inv.app (Smn 0 1) ≫
        (SyntheticCategory.biShift (0,w)).map (lambdaPow 1 (Smn 0 1)) := by
    rw [lambdaPow_one coh, lambdaPow_one coh]
    simpa only [biShiftAddIso, Iso.trans_hom, Iso.trans_inv, eqToIso.hom,
      eqToIso.inv, eqToHom_refl, Category.comp_id, Category.id_comp] using
      coh.lambda_comm (0,w) (Smn (Syn := SyntheticSpectrum) 0 1)
  have hp :
      (biShiftAddIso (0,1+w) (0,-1) (0,w) (by ext <;> dsimp; omega)).inv.app A ≫
        lambdaPow 1 (Smn (Syn := SyntheticSpectrum) 0 (1+w)) ≫
          (SyntheticCategory.biShift_comp (0,1) (0,w)).inv.app A =
      (biShiftAddIso (0,0) (0,w) (0,w) (by ext <;> dsimp; omega)).inv.app A ≫
        (SyntheticCategory.biShift (0,w)).map
          ((SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app A) ≫
        (SyntheticCategory.biShift (0,w)).map (lambdaPow 1 (Smn 0 1)) := by
    rw [← lambdaPow_naturality]
    have h₁' :
        (biShiftAddIso (0,1+w) (0,-1) (0,w) (by ext <;> dsimp; omega)).inv.app A ≫
          (SyntheticCategory.biShift (0,-1)).map
            ((SyntheticCategory.biShift_comp (0,1) (0,w)).inv.app A) =
        (biShiftAddIso (0,1) (0,w-1) (0,w) (by ext <;> dsimp; omega)).inv.app A ≫
          (biShiftAddIso (0,w) (0,-1) (0,w-1) (by ext <;> dsimp; omega)).inv.app (Smn 0 1) := by
      simpa only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl,
        Category.id_comp, Smn, A] using h₁.symm
    erw [← Category.assoc, h₁', Category.assoc, hl]
    simp only [Iso.inv_hom_id_app_assoc]
    have h₂' := congrArg
      (fun z => z ≫ (SyntheticCategory.biShift (0,w)).map (lambdaPow 1 (Smn (Syn := SyntheticSpectrum) 0 1))) h₂
    simpa only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl,
      Category.id_comp, Smn, A, Category.assoc] using h₂'
  unfold sphereProduct
  erw [reassoc_of% hp]
  simp only [lambdaMultiply, eqToHom_refl, Category.id_comp, Functor.map_comp, Category.assoc, A]
  rfl

private theorem sphere_two_product (w : ℤ) (y : BiHom 0 w (S_0_0 : SyntheticSpectrum)) :
    (biShiftAddIso (0,0) (0,w) (0,w) (by ext <;> dsimp; omega)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (0,w)).map Route.syntheticTwo ≫ y = (2 : ℕ) • y := by
  let coh := background.quotients.coherence
  letI := background.exactness.shiftAdditive (0,w)
  have hu := coh.left_unit (0,w) (S_0_0 : SyntheticSpectrum)
  change (biShiftAddIso (0,0) (0,w) (0,w) (by ext <;> dsimp; omega)).hom.app S_0_0 =
    (SyntheticCategory.biShift (0,w)).map (SyntheticCategory.biShift_zero.hom.app S_0_0) at hu
  dsimp only [Route.syntheticTwo]
  rw [Functor.map_comp, Functor.map_nsmul, CategoryTheory.Functor.map_id]
  erw [← hu]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Preadditive.nsmul_comp, Category.id_comp]

private theorem h0SquareLift_lambda :
    lambdaMultiply 1 h0SquareLift = (2 : ℕ) • KIP126.Literature.Standard.syntheticH0 := by
  have h := lambda_one_product_precomposition 1 KIP126.Literature.Standard.syntheticH0
    KIP126.Literature.Standard.syntheticH0
  rw [KIP126.Literature.Standard.lambdaMultiply_syntheticH0, sphere_two_product] at h
  convert h using 1
  simp [h0SquareLift, lambdaMultiply, biShiftAddIso]

private theorem h0CubeLift_lambda :
    lambdaMultiply 1 h0CubeLift = (2 : ℕ) • h0SquareLift := by
  have h := lambda_one_product_precomposition 2 KIP126.Literature.Standard.syntheticH0 h0SquareLift
  rw [KIP126.Literature.Standard.lambdaMultiply_syntheticH0, sphere_two_product] at h
  convert h using 1
  simp [h0CubeLift, lambdaMultiply, biShiftAddIso]


private theorem lambda_one_one_three {X : SyntheticSpectrum} (c : BiHom 0 3 X) :
    lambdaMultiply 1 (lambdaMultiply 1 c) = lambdaMultiply 2 c := by
  have ha := inverse_associativity background.quotients.coherence (0,3) (0,-1) (0,-1)
    (0,2) (0,-2) (0,1) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 1
    ((SyntheticCategory.biShift_comp (0,3) (0,-1)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 1 (lambdaPow 1 (Smn 0 3)))]
  erw [← Category.assoc, ← ha]
  erw [lambdaPow_add background.quotients.coherence 1 1 2 (by decide) (Smn 0 3)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl

private theorem h0CubeLift_lambda_two :
    lambdaMultiply 2 h0CubeLift = (4 : ℕ) • KIP126.Literature.Standard.syntheticH0 := by
  rw [← lambda_one_one_three, h0CubeLift_lambda]
  have hn : lambdaMultiply 1 ((2 : ℕ) • h0SquareLift) =
      (2 : ℕ) • lambdaMultiply 1 h0SquareLift := by
    simp only [lambdaMultiply, Preadditive.comp_nsmul]
  rw [hn, h0SquareLift_lambda, smul_smul]
  rfl

private def h0Nu : BiHom 0 1 (background.nu.functor.obj S) :=
  KIP126.Literature.Standard.syntheticH0 ≫ background.nu.unitIso.inv

private def h0SquareNu : BiHom 0 2 (background.nu.functor.obj S) :=
  h0SquareLift ≫ background.nu.unitIso.inv

private theorem h0SquareNu_label :
    h0SquareNu ≫ XModLambdaN.incl _ 1 = nativeFirstLabel .sphere 2 2 h0Square := by
  let Q := background.quotients.functoriality.functor 1
  apply (cancel_mono (Q.mapIso background.nu.unitIso).hom).mp
  apply (KIP126.Literature.sphereFirstQuotient background 2 2).injective
  change KIP126.Literature.sphereFirstQuotient background 2 2
      ((h0SquareNu ≫ XModLambdaN.incl _ 1) ≫ XModLambdaN.map background.nu.unitIso.hom 1) =
    KIP126.Literature.sphereFirstQuotient background 2 2
      (nativeFirstLabel .sphere 2 2 h0Square ≫ XModLambdaN.map background.nu.unitIso.hom 1)
  rw [sphere_native_quotient_label]
  have he : (h0SquareNu ≫ XModLambdaN.incl _ 1) ≫ Q.map background.nu.unitIso.hom =
      quotientClass 1 h0SquareLift := by
    change ((h0SquareLift ≫ background.nu.unitIso.inv) ≫ XModLambdaN.incl _ 1) ≫
        XModLambdaN.map background.nu.unitIso.hom 1 = h0SquareLift ≫ XModLambdaN.incl _ 1
    rw [Category.assoc, ← XModLambdaN.incl_naturality background.nu.unitIso.hom 1]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  exact he ▸ h0SquareLift_label

private theorem h0SquareNu_lambda :
    lambdaMultiply 1 h0SquareNu = (2 : ℕ) • h0Nu := by
  have h := congrArg (fun z => z ≫ background.nu.unitIso.inv) h0SquareLift_lambda
  simpa only [h0SquareNu, h0Nu, lambdaMultiply, Category.assoc, Preadditive.nsmul_comp] using h

private theorem h0CubeNu_lambda_two :
    lambdaMultiply 2 h0CubeNu = (4 : ℕ) • h0Nu := by
  have h := congrArg (fun z => z ≫ background.nu.unitIso.inv) h0CubeLift_lambda_two
  simpa only [h0CubeNu, h0Nu, lambdaMultiply, Category.assoc, Preadditive.nsmul_comp] using h

private theorem four_h0Nu_quotient_ne_zero :
    quotientClass 3 ((4 : ℕ) • h0Nu) ≠ 0 := by
  rw [← h0CubeNu_lambda_two]
  exact h0CubeNu_finite_lambda_ne_zero

end
end KIP126.ProofTools.Internal.CrossingCounterexample
