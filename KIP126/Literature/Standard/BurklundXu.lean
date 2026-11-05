module
import all KIP126.Literature.BocksteinOriginalSuccessor
import all KIP126.Literature.BocksteinComparisonInput
import all KIP126.Literature.BocksteinBoundaryInput
public import KIP126.AdamsSynthetic.Completed.Background
import KIP126.AdamsSynthetic.Completed.Filtration
import KIP126.AdamsSynthetic.Completed.Separation
import KIP126.AdamsSynthetic.Completed.ClassicalSupport
public import KIP126.Literature.ModelResults
import all KIP126.Literature.ModelResults
import all KIP126.Literature.Classical
import all KIP126.Literature.ClassicalRange
import all KIP126.Literature.EInfinity
import all KIP126.Literature.Triangles
import all KIP126.Literature.May

public import KIP126.AdamsSynthetic.Completed.SpectrumScope
public import KIP126.Literature.Standard.ClassicalInputs
import all KIP126.Literature.Standard.ClassicalInputs
public import KIP126.Literature.Standard.AdamsComparison
import all KIP126.Literature.Standard.AdamsComparison
public import KIP126.Literature.Standard.NormalizedTriangles
import all KIP126.Literature.Standard.NormalizedTriangles
public import KIP126.Literature.Standard.FiniteLift
import all KIP126.Literature.Standard.FiniteLift
public import KIP126.Literature.Standard.RealizationLifts
import all KIP126.Literature.Standard.RealizationLifts

/-! BurklundXu on the fixed literature background. -/

@[expose] section
set_option autoImplicit false
noncomputable section
set_option backward.privateInPublic true
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)

/-- Choose the synthetic θ₅ with its actual first-quotient label and doubling
relation. The existence of this common witness remains a source input. -/
private def syntheticTheta5Construction :
    { θ : BiHom 62 64 (S_0_0 : SyntheticSpectrum) //
      Theta5Detected background θ ∧ θ + θ = 0 } := by
  sorry

/-- The synthetic θ₅ selected by the common source witness. -/
public def syntheticTheta5 :
  BiHom 62 64 (S_0_0 : SyntheticSpectrum) :=
  syntheticTheta5Construction.val


public theorem eta_first_quotient_label :
  sphereFirstQuotient background 1 2 (quotientClass 1 eta) =
    background.standardClasses.standardHi 1 eta_detection._proof_2 := eta_label

/-- The first-quotient label of the synthetic θ₅ from the same witness. -/
public theorem syntheticTheta5_detected :
  Theta5Detected background syntheticTheta5 :=
  syntheticTheta5Construction.property.1

/-- The doubling relation of the synthetic θ₅ from the same witness. -/
public theorem syntheticTheta5_add_self :
  syntheticTheta5 + syntheticTheta5 = 0 :=
  syntheticTheta5Construction.property.2


public theorem h6_square_survives_iff_eta_theta_square_vanishes_mod_lambda :
  ∀ r : ℕ, 1 ≤ r →
    (SurvivesTo background.classical.sphere ((r : ℤ)+3) (2,128)
      background.standardClasses.standardH6Square ↔ quotientClass r (etaThetaSquare eta syntheticTheta5) = 0) := by
  sorry


public theorem delta_h6_square_eq_lambda_eta_syntheticTheta5_square :
  deltaH6Square background = lambdaEtaThetaSquare eta syntheticTheta5 := by
  sorry

section BxUntruncatedConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem sphereLiftIff (x : background.classical.sphere.Page 2 (2,128)) :
    ClassicalPermanentCycle background .sphere (2,128) x ↔
      ∃ a : BiHom 126 128 (S_0_0 : SyntheticSpectrum),
        sphereFirstQuotient background 2 128 (quotientClass 1 a) = x := by
  let e : nuZero background .sphere ≅ (S_0_0 : SyntheticSpectrum) :=
    SyntheticCategory.biShift_zero.app _ ≪≫ background.nu.unitIso
  constructor
  · intro hx
    obtain ⟨b,hb⟩ := (permanent_lift .sphere 2 128 x).mp hx
    let a := b ≫ e.hom
    have hq : quotientClass 1 a ≫ XModLambdaN.map e.inv 1 = quotientClass 1 b := by
      dsimp only [a, quotientClass]
      simp only [Category.assoc]
      rw [← XModLambdaN.incl_naturality]
      simp only [Iso.hom_inv_id_assoc]
    refine ⟨a, ?_⟩
    change (background.firstQuotient .sphere 0 2 128)
      (quotientClass 1 a ≫ XModLambdaN.map e.inv 1) = x
    rw [hq, hb]
    exact (background.firstQuotient .sphere 0 2 128).apply_symm_apply x
  · rintro ⟨a,ha⟩
    apply (permanent_lift .sphere 2 128 x).mpr
    refine ⟨a ≫ e.inv, ?_⟩
    have hq : quotientClass 1 (a ≫ e.inv) =
        quotientClass 1 a ≫ XModLambdaN.map e.inv 1 := by
      dsimp only [quotientClass]
      rw [Category.assoc, XModLambdaN.incl_naturality]
      simp only [Category.assoc]
    rw [hq]
    apply (background.firstQuotient .sphere 0 2 128).injective
    change (background.firstQuotient .sphere 0 2 128)
        (quotientClass 1 a ≫ XModLambdaN.map e.inv 1) =
      (background.firstQuotient .sphere 0 2 128)
        ((background.firstQuotient .sphere 0 2 128).symm x)
    rw [LinearEquiv.apply_symm_apply]
    exact ha

private theorem h6SquareNonzero : background.standardClasses.standardH6Square ≠ 0 := by
  obtain ⟨hdeg,xr,yr,_,hy,_,hne⟩ := adamsOneLine_d2 7 (by decide) (by decide)
  intro hz
  apply hne
  rw [←hy.eq_on_page_two]
  change background.sphereAlgebra.product (1,1) (2,128)
    (background.standardClasses.standardHi 0) background.standardClasses.standardH6Square = 0
  rw [hz, map_zero]

private theorem h6SquareNoIncoming (r : ℤ) (hr : 2 ≤ r) :
    background.classical.sphere.d r (((2:ℤ),128)-background.classical.sphere.diffDeg r) = 0 := by
  by_cases h2 : r = 2
  · subst r
    have hq : ((2:ℤ),128)-background.classical.sphere.diffDeg 2 = (0,127) := by
      rw [background.classical.differentialDegree]
      decide
    rw [hq]
    letI := KIP126.AdamsSynthetic.Completed.sphere_page_filtration_zero 2 127 (by decide)
    ext a
    have ha : a = 0 := Subsingleton.elim _ _
    simp only [ha, map_zero]
  · let q := ((2:ℤ),128)-background.classical.sphere.diffDeg r
    have hs : q.1 < 0 := by
      dsimp only [q]
      rw [background.classical.differentialDegree]
      change 2-r < 0
      omega
    letI : Subsingleton (background.classical.sphere.Page r q) :=
      KIP126.AdamsSynthetic.Completed.classical_page_negative .sphere r q.1 q.2 hs
    ext a
    have ha : a = 0 := Subsingleton.elim _ _
    simp only [ha, map_zero]

private theorem permanentIffSurvival :
    ClassicalPermanentCycle background .sphere (2,128) background.standardClasses.standardH6Square ↔
      background.H6SquarePermanent := by
  constructor
  · intro h
    exact KIP126.Literature.Standard.nonzeroSurvivalOfPermanentNoIncoming _ _ h
      h6SquareNonzero h6SquareNoIncoming
  · rintro ⟨z,hz,_⟩
    exact ⟨z,hz⟩

private theorem boundaryLiftIff :
    deltaH6Square background = 0 ↔
      ∃ a : BiHom 126 128 (S_0_0 : SyntheticSpectrum),
        sphereFirstQuotient background 2 128 (quotientClass 1 a) = background.standardClasses.standardH6Square := by
  let x := (sphereFirstQuotient background 2 128).symm background.standardClasses.standardH6Square
  have hboundary : deltaH6Square background = 0 ↔ x ≫ XModLambdaN.proj (S_0_0 : SyntheticSpectrum) 1 = 0 := by
    change (susp_invariance 125 129 1 (-1) (S_0_0 : SyntheticSpectrum)).symm
        (x ≫ sphereTotalBoundary) = 0 ↔ _
    have hz : (susp_invariance 125 129 1 (-1) (S_0_0 : SyntheticSpectrum)) 0 = 0 := by
      letI := background.exactness.shiftAdditive (1,-1)
      change (SyntheticCategory.biShift_comp (125,129) (1,-1)).inv.app
          (S_0_0 : SyntheticSpectrum) ≫
        (SyntheticCategory.biShift (1,-1)).map
          (0 : BiHom 125 129 (S_0_0 : SyntheticSpectrum)) ≫ 𝟙 _ = 0
      erw [Functor.map_zero, Category.comp_id, comp_zero]
    rw [Equiv.symm_apply_eq, hz]
    dsimp only [sphereTotalBoundary]
    constructor
    · intro h
      apply (cancel_mono ((SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).inv.app
        ((SyntheticCategory.biShift (0,-1)).obj S_0_0))).mp
      apply (cancel_mono ((SyntheticCategory.biShift_comp (0,-1) (1,0)).hom.app
        (S_0_0 : SyntheticSpectrum))).mp
      simpa only [Category.assoc, zero_comp] using h
    · intro h
      simp only [← Category.assoc, h, zero_comp]
  rw [hboundary]
  constructor
  · intro hx
    let T := XModLambdaN.cofiberTriangle (S_0_0 : SyntheticSpectrum) 1
    obtain ⟨a,ha⟩ := T.coyoneda_exact₃ (XModLambdaN.cofiberTriangle_distinguished _ _) x hx
    refine ⟨a, ?_⟩
    change x = a ≫ XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 1 at ha
    change sphereFirstQuotient background 2 128
      (a ≫ XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 1) = _
    rw [←ha]
    exact (sphereFirstQuotient background 2 128).apply_symm_apply _
  · rintro ⟨a,ha⟩
    have hx : quotientClass 1 a = x := by
      apply (sphereFirstQuotient background 2 128).injective
      rw [ha]
      exact ((sphereFirstQuotient background 2 128).apply_symm_apply _).symm
    rw [←hx]
    dsimp only [quotientClass]
    rw [Category.assoc, XModLambdaN.incl_comp_proj, comp_zero]

/-- The first λ-cofiber exact sequence identifies the total boundary obstruction
with a permanent lift. Nonzero survival follows from the independent one-line
differential and the absence of incoming classes. -/
public theorem h6_square_permanent_iff_lambda_eta_theta_square_eq_zero :
    background.H6SquarePermanent ↔ lambdaEtaThetaSquare eta syntheticTheta5 = 0 := by
  rw [←delta_h6_square_eq_lambda_eta_syntheticTheta5_square]
  exact permanentIffSurvival.symm.trans ((sphereLiftIff _).trans boundaryLiftIff.symm)

end BxUntruncatedConstruction

end KIP126.Literature.Standard
end
