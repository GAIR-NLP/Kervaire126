module
public import KIP126.AdamsSynthetic.Ordinary.TopologicalComparison
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all KIP126.AdamsSynthetic.Source
import all KIP126.AdamsSynthetic.Internal.HInjective.GeneralHomotopyCoproduct
import all KIP126.AdamsSynthetic.Ordinary.WhiteheadMap

/-! Small coproducts and homotopy detection in ordinary spectra. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Ordinary
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Arbitrary small families of the fixed ordinary spectra have coproducts. -/
public theorem smallSpectrumCoproducts : HasCoproducts.{0} Spectrum :=
  Source.recognizedSmallCoproducts sourceComparison

/-- The additive represented homotopy functor preserves the original small
    coproduct diagram, for every integer degree and every choice of coproducts. -/
public theorem homotopy_preserves_smallCoproduct {J : Type}
    (X : J → Spectrum) [HasCoproducts.{0} Spectrum] (d : ℤ) :
    PreservesColimit (Discrete.functor X)
      (preadditiveCoyoneda.obj (Opposite.op (Sphere (C := Spectrum) d))) :=
  Source.recognized_homotopy_preserves_coproduct sourceComparison X d

/-- Stable homotopy groups detect isomorphisms between arbitrary fixed spectra. -/
public theorem isIso_of_homotopy_bijective {X Y : Spectrum} (f : X ⟶ Y)
    (hf : ∀ n : ℤ, Function.Bijective (inducedMap f n)) : IsIso f :=
  ordinary_isIso_of_homotopy_bijective f hf

end
end KIP126.AdamsSynthetic.Ordinary
end
