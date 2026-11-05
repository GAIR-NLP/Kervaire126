module


/- Fixed literature objects and theorems with their mathematical range,
projectivity, completeness and detection conditions. Definitions and results
use the same specified objects and comparisons. -/

/- The specified realization is additive by its adjunction. -/

/- The filtration witness and cofiber-cell arguments use the fixed
homology-factorization comparison and exact tensor structure of the same
Adams model. -/
public import KIP126.Literature.Standard.ClassicalInputs
public import KIP126.Literature.Standard.AdamsComparison
public import KIP126.Literature.Standard.SyntheticAdamsTheorem
public import KIP126.Literature.Standard.NormalizedTriangles
public import KIP126.Literature.Standard.FiniteLift
public import KIP126.Literature.Standard.RealizationLifts
public import KIP126.Literature.Standard.BurklundXu
public import KIP126.Literature.Standard.Tensor
public import KIP126.Literature.Standard.Moss

/-! Literature statements organized by mathematical subject. -/

@[expose] section
set_option autoImplicit false
noncomputable section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)

public abbrev IsConnected := KIP126.Literature.IsConnected (C := Spectrum)

public abbrev ModTwoCohomology := KIP126.Literature.ModTwoCohomology background

public abbrev sphereFirstQuotient := KIP126.Literature.sphereFirstQuotient background

public abbrev h6FirstQuotient := KIP126.Literature.h6FirstQuotient background

public abbrev h6FirstQuotient_label := KIP126.Literature.h6FirstQuotient_label background

public abbrev Theta5Detected := KIP126.Literature.Theta5Detected background

public abbrev ClassicalTheta5Detected := KIP126.Literature.ClassicalTheta5Detected background

public abbrev ClassicalPermanentCycle := KIP126.Literature.ClassicalPermanentCycle background

public abbrev AdamsComparisonApplicability := KIP126.Literature.AdamsComparisonApplicability background

public abbrev FiniteLiftCriterion := KIP126.Literature.FiniteLiftCriterion background

public abbrev PermanentLiftAt := KIP126.Literature.PermanentLiftAt background

public abbrev FiltrationLambdaAt := KIP126.Literature.FiltrationLambdaAt background

public abbrev LambdaDivisible := KIP126.Literature.LambdaDivisible background

public abbrev nuZero := KIP126.Literature.nuZero background

public abbrev firstLabel := KIP126.Literature.firstLabel background

public abbrev bocksteinArrow := KIP126.Literature.bocksteinArrow background

public abbrev bocksteinLabel := KIP126.Literature.bocksteinLabel background

public abbrev oneLineTarget (j : ℕ) (hjBound : j ≤ 7 := by omega) :=
  KIP126.Literature.oneLineTarget background j hjBound

public abbrev classicalTwo := KIP126.Literature.classicalTwo (C := Spectrum)

public abbrev classicalSphereProduct := @KIP126.Literature.classicalSphereProduct Spectrum inferInstance

public abbrev etaThetaSquare := KIP126.Literature.etaThetaSquare eta

public abbrev lambdaEtaThetaSquare := KIP126.Literature.lambdaEtaThetaSquare eta

public abbrev deltaH6Square := KIP126.Literature.deltaH6Square background

public abbrev classicalDifferential := KIP126.Literature.classicalDifferential background

public abbrev syntheticDifferential := KIP126.Literature.syntheticDifferential background

public abbrev cycles := KIP126.Literature.cycles background

public abbrev boundaries := KIP126.Literature.boundaries background

public abbrev permanentCycles := KIP126.Literature.permanentCycles background

public abbrev CycleQuotient := KIP126.Literature.CycleQuotient background

public abbrev PermanentQuotient := KIP126.Literature.PermanentQuotient background

public abbrev quotientMap := @KIP126.Literature.quotientMap Spectrum inferInstance inferInstance SyntheticSpectrum inferInstance inferInstance background

public abbrev NuCofiberCriterion := KIP126.Literature.NuCofiberCriterion background

public abbrev SyntheticLiftComparison := KIP126.Literature.SyntheticLiftComparison background

public abbrev SyntheticTriangleLiftComparison := KIP126.Literature.SyntheticTriangleLiftComparison background

public abbrev NormalizedTriangleCompatible := KIP126.Literature.NormalizedTriangleCompatible background

public abbrev normalizedTriangle := KIP126.Literature.normalizedTriangle background

public abbrev normalizedNu := KIP126.Literature.normalizedNu background

public abbrev MossStatementAt := Moss.StatementAt mapping mappingComposition

public abbrev MossRelation := @Moss.PageMassey.Relation

public abbrev MossIndeterminacy := @Moss.PageMassey.Indeterminacy

public abbrev TripleToda := @Route.TripleToda

public abbrev TodaRelation := @KIP126.StableHomotopy.Toda.Relation

public abbrev toda_composable := @KIP126.StableHomotopy.Toda.composable

public abbrev toda_exists_relation := @KIP126.StableHomotopy.Toda.exists_relation

public abbrev toda_relation_iff_indeterminacy := @KIP126.StableHomotopy.Toda.relation_iff_indeterminacy

public abbrev toda_juggling := @KIP126.StableHomotopy.Toda.juggling

public abbrev toda_precompose := @KIP126.StableHomotopy.Toda.precompose

public abbrev toda_postcompose := @KIP126.StableHomotopy.Toda.postcompose

public abbrev toda_absorb_first := @KIP126.StableHomotopy.Toda.absorb_first

public abbrev toda_absorb_last := @KIP126.StableHomotopy.Toda.absorb_last

public abbrev toda_shuffle_iff := @KIP126.StableHomotopy.Toda.shuffle_iff

public abbrev toda_suspension_iff := @KIP126.StableHomotopy.Toda.suspension_iff

public abbrev toda_map := @KIP126.StableHomotopy.Toda.map

public abbrev toda_tensor_right := @KIP126.StableHomotopy.Toda.tensor_right

public abbrev toda_tensor_left := @KIP126.StableHomotopy.Toda.tensor_left

end KIP126.Literature.Standard
end
