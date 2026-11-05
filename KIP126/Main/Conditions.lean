module

public import KIP126.SSComputation

/-! Section 7 predicates on the fixed Adams and synthetic system. -/

@[expose] section
noncomputable section
namespace KIP126.Main
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Core.SpectralSequence KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)

public def H6SquareSupportsD12 : Prop :=
  HasNonzeroDifferential background.classical.sphere 12 (2,128) (14,139)
    background.standardClasses.standardH6Square KIP126.Computation.Standard.T

/-- A zero sixth differential includes an actual sixth-page representative. -/
public def Stem126D6Vanishes : Prop :=
  HasDifferential background.classical.sphere 6 (8,134) (14,139)
    KIP126.Computation.Standard.W 0

public def ThetaChoice (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) : Prop :=
  KIP126.Literature.Standard.Theta5Detected theta

/-- Nonzero detection of the square, retaining higher-filtration ambiguity. -/
public def Theta5SquareNonzeroDetectionAt (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) : Prop :=
  DetectsNonzero (background.convergence .sphere) (10,134,128)
    (background.comparison.sphereE2 10 134 6 KIP126.Computation.Standard.U)
    (sphereProduct theta theta)

public def Theta5SquareNonzeroDetection : Prop := ∃ theta, ThetaChoice theta ∧ Theta5SquareNonzeroDetectionAt theta

public def UChoice (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) : Prop :=
  DetectsNonzero (background.convergence .sphere) (10,134,134)
    (background.comparison.sphereE2 10 134 0 KIP126.Computation.Standard.U) u

/-- Associated-graded detection of the lambda-three eta product. -/
public def EtaExtensionDetectionAt (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) : Prop :=
  Detects (background.convergence .sphere) (14,139,133)
    (background.comparison.sphereE2 14 139 6 KIP126.Computation.Standard.T)
    (lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta u))

public def EtaExtensionDetection : Prop := ∃ u, UChoice u ∧ EtaExtensionDetectionAt u

/-- The endpoint keeps a common Z∞ representative and a nonzero E∞ image. -/
public abbrev H6SquarePermanent : Prop :=
  KIP126.AdamsSynthetic.Completed.H6SquarePermanent

end KIP126.Main
end
