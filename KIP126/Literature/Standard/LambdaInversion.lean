module

public import KIP126.Literature.Standard
public import KIP126.Literature.LambdaInversionAdams

/-! Comparison of Adams towers after lambda inversion, including stages,
cofibers, cycle and boundary maps, and E₂ calibration.
-/

@[expose] section
namespace KIP126.Literature.Standard
open KIP126.AdamsSynthetic.Completed (background)
noncomputable section

/-- The lambda-inversion comparison in the fixed realization coordinates,
using the selected coefficient towers and labels.
Source: Pstrągowski, Theorem 4.37, and BHS, Section 9 and Appendix A. -/
public def lambdaInversionAdamsComparison :
    KIP126.Literature.LambdaInversionAdamsComparison background realizationData := by
  sorry

end
end KIP126.Literature.Standard
