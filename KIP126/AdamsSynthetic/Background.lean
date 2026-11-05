module

public import KIP126.AdamsSynthetic.Context

/-! Additional background contracts on the same stable category. The chosen
closed structure and every shift comparison are explicit inputs. -/

@[expose] section
namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits MonoidalCategory Pretriangulated

universe u v
variable (C : Type u) [StableHomotopyCategory.{u, v} C]

/-- Closed symmetric tensor triangulated structure on this very background.
Exactness uses the supplied coherent comparisons of tensor and internal hom
with suspension. -/
public structure ClosedSymmetricTensorTriangulated where
  symmetric : SymmetricCategory C
  closed : MonoidalClosed C
  tensorShift : ∀ W : C, (tensorRight W).CommShift ℤ
  tensorExact : ∀ W : C,
    letI := tensorShift W
    (tensorRight W).IsTriangulated
  ihomShift : letI := closed
    ∀ W : C, (ihom W).CommShift ℤ
  ihomExact : letI := closed
    ∀ W : C,
    letI := ihomShift W
    (ihom W).IsTriangulated

variable {C}
namespace ClosedSymmetricTensorTriangulated

/-- Tensoring a shifted unit with an object is its actual integer shift.
This comparison is derived from the supplied tensor shift coherence. -/
public noncomputable def sphereTensorShift
    (B : ClosedSymmetricTensorTriangulated C) (n : ℤ) (X : C) :
    (Sphere n : C) ⊗ X ≅ (shiftFunctor C n).obj X := by
  letI := B.tensorShift X
  exact ((tensorRight X).commShiftIso n).app SphereSpectrum ≪≫
    (shiftFunctor C n).mapIso (λ_ X)

/-- The sphere product comparison determined by this background. -/
public noncomputable def smashSpheres
    (B : ClosedSymmetricTensorTriangulated C) (m n : ℤ) :
    (Sphere m : C) ⊗ Sphere n ≅ Sphere (m + n) :=
  B.sphereTensorShift m (Sphere n) ≪≫
    ((shiftFunctorAdd C n m).app SphereSpectrum).symm ≪≫
    eqToIso (congrArg (Sphere (C := C)) (add_comm n m))

end ClosedSymmetricTensorTriangulated

end KIP126.StableHomotopy
