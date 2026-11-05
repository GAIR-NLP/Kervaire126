module

public import KIP126.AdamsSynthetic.Completed.AdamsScope

/-! The selected objects lie in the general spectrum range by their
bounds and finite-type properties. The range definitions and base instances
are re-exported from SpectrumScope.Basic through AdamsScope. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy KIP126.Kervaire.Route
noncomputable section

/-- The original selected expressions are instances of the general shifted range. -/
public def ClassicalObject.adamsSpectrum (X : ClassicalObject) : AdamsSpectrum :=
  ⟨X.obj auxiliary, classicalObject_boundedBelow X, classicalObject_finite_modTwoHomology X⟩
end
end KIP126.AdamsSynthetic.Completed
