module
public import KIP126.AdamsSynthetic.Completed.HomotopyCoproduct
public import KIP126.AdamsSynthetic.Ordinary.SphereCoproduct
import all KIP126.AdamsSynthetic.Source
import all KIP126.AdamsSynthetic.Internal.HInjective.SphereCoproductTransfer
import all KIP126.AdamsSynthetic.Internal.HInjective.ActualSphereWedgeColimit

/-! Small sphere coproducts and represented homotopy in the completed spectrum
localization. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Existence of a small coproduct of the actual degree-zero spheres. -/
public theorem smallSphereCoproduct (J : Type) :
    HasCoproduct (fun _ : J => Sphere (C := Spectrum) 0) :=
  by
    letI := smallSpectrumCoproducts
    infer_instance

/-- The actual sphere's negative-homotopy vanishing is preserved by its small
    coproducts; the result holds for any supplied choice of that coproduct. -/
public theorem smallSphereCoproduct_homotopy_vanishes (J : Type)
    [HasCoproduct (fun _ : J => Sphere (C := Spectrum) 0)]
    (hSphere : ∀ n : ℤ, n ≤ -1 → Subsingleton
      (HomotopyGroup n (SphereSpectrum (C := Spectrum))))
    (n : ℤ) (hn : n ≤ -1) :
    Subsingleton (HomotopyGroup n (∐ fun _ : J => Sphere (C := Spectrum) 0)) :=
  by sorry

end
end KIP126.AdamsSynthetic.Completed
end
