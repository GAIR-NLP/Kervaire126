module
public import KIP126.AdamsSynthetic.Ordinary.TopologicalComparison
import all KIP126.AdamsSynthetic.Source
import all KIP126.AdamsSynthetic.Internal.HInjective.SphereCoproductTransfer
import all KIP126.AdamsSynthetic.Internal.HInjective.ActualSphereWedgeColimit

/-! Small sphere coproducts and represented homotopy in the ordinary spectrum
localization. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Ordinary
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Existence of a small coproduct of the actual degree-zero spheres. -/
public theorem smallSphereCoproduct (J : Type) :
    HasCoproduct (fun _ : J => Sphere (C := Spectrum) 0) :=
  HasColimit.mk ⟨_, Source.recognizedSphereZeroCofan_isColimit sourceComparison J
    (Source.Prespectrum.actual_sphere_source_coproduct J)⟩

/-- The actual sphere's negative-homotopy vanishing is preserved by its small
    coproducts; the result holds for any supplied choice of that coproduct. -/
public theorem smallSphereCoproduct_homotopy_vanishes (J : Type)
    [HasCoproduct (fun _ : J => Sphere (C := Spectrum) 0)]
    (hSphere : ∀ n : ℤ, n ≤ -1 → Subsingleton
      (HomotopyGroup n (SphereSpectrum (C := Spectrum))))
    (n : ℤ) (hn : n ≤ -1) :
    Subsingleton (HomotopyGroup n (∐ fun _ : J => Sphere (C := Spectrum) 0)) :=
  Source.sphereCoproduct_connected_of_localized_strict_colimits
    sourceComparison hSphere
    (fun J => Source.Prespectrum.actual_sphere_source_coproduct J) J n hn

end
end KIP126.AdamsSynthetic.Ordinary
end
