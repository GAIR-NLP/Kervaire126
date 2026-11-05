module

public import KIP126.AdamsSynthetic.Completed.Background
public import KIP126.AdamsSynthetic.ESSShift

/-! Compatibility of the fixed first-quotient comparison with positive weight
shift and classical suspension, on the specified model and quotient maps. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Kervaire.Route
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The first-quotient label commutes with the positive weight shift and
every quotient comparison satisfying the actual inclusion square. -/
public theorem firstQuotient_positive_shift
    (X : AdamsObject) (s t : ℤ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1))
    (hε : XModLambdaN.incl _ 1 ≫ ε.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ 1)) :
    homotopyRegrade (by simp) (by simp)
      (shiftHomotopyClass (0,1) (t-s,t)
        (homotopyRegrade rfl (by simp) ((background.firstQuotient X 0 s t).symm x) ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)) ≫ ε.inv =
        (background.firstQuotient X 1 s t).symm x := by
  sorry

/-- The first-quotient labels of a class and its actual classical suspension
agree after the fixed ν suspension and quotient comparisons. -/
public theorem firstQuotient_suspension
    (X : AdamsObject) (s t : ℤ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (sx : (background.classical.obj ((AdamsObject.shift 1 X).obj background.auxiliary)).Page 2 (s,t+1))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1))
    (hε : XModLambdaN.incl _ 1 ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 1))
    (hsx : (background.classicalSuspension X).DesuspendsClass s (t+1) sx (by simpa using x)) :
    (homotopyRegrade (w' := t+1) rfl (by simp)
        ((background.firstQuotient (.shift 1 X) 0 s (t+1)).symm sx) ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) ≫
      XModLambdaN.map (background.nu.suspensionIso (X.obj background.auxiliary)).hom 1 ≫ ε.hom =
    homotopyRegrade (by simp; omega) (by simp)
      (shiftHomotopyClass (1,1) (t-s,t)
        (homotopyRegrade rfl (by simp) ((background.firstQuotient X 0 s t).symm x) ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)) := by
  sorry

end
end KIP126.AdamsSynthetic.Completed
