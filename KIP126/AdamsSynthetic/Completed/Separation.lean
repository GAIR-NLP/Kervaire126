module

public import KIP126.AdamsSynthetic.Completed.Background

/-! Separation of the fixed synthetic homotopy filtration on finite λ quotients.
The separation statement uses the actual λⁿ cofiber of each selected object,
with the same fixed tower and model. -/




@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open KIP126.Kervaire.Route

/-- The intersection of the nonnegative filtration levels is zero on each finite λⁿ
quotient. -/
public theorem synthetic_homotopy_separated (X : SyntheticObject) (n : ℕ) :
    KIP126.AdamsSynthetic.HomotopySeparated background.syntheticTower
      (KIP126.Synthetic.Context.XModLambdaN
        (X.obj background.nu background.auxiliary) n) := by
  sorry

end KIP126.AdamsSynthetic.Completed
