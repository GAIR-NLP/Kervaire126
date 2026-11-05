module
public import KIP126.AdamsSynthetic.Completed.Source
public import KIP126.AdamsSynthetic.Ordinary.HomotopyCoproduct
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all KIP126.AdamsSynthetic.Internal.HInjective.WhiteheadMap

/-! Coproducts in completed spectra and the represented comparison for coproducts of
suspensions of HF₂. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
noncomputable section
public theorem smallSpectrumCoproducts : HasCoproducts.{0} Spectrum := by sorry
/-- A coproduct of HF₂ modules is already local. -/
public theorem homotopy_preserves_coefficient_coproduct {J : Type}
    (degrees : J → ℤ) [HasCoproducts.{0} Spectrum] (d : ℤ) :
    PreservesColimit (Discrete.functor (fun j => (shiftFunctor Spectrum (degrees j)).obj coefficients.object))
      (preadditiveCoyoneda.obj (Opposite.op (Sphere (C := Spectrum) d))) := by sorry
public theorem isIso_of_homotopy_bijective {X Y : Spectrum} (f : X ⟶ Y)
    (hf : ∀ n : ℤ, Function.Bijective (inducedMap f n)) : IsIso f :=
  completed_isIso_of_homotopy_bijective f hf
end
end KIP126.AdamsSynthetic.Completed
end
