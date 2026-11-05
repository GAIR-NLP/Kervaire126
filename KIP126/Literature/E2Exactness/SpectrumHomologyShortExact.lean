module
public import KIP126.AdamsSynthetic.Completed.Background
public import KIP126.AdamsSynthetic.Comparisons
import all KIP126.Literature.E2Exactness.Ordinary.ActualE2PageTwo

/-! The ordinary E₂ long exact sequence of an actual mod-two-homology
short exact distinguished triangle of arbitrary spectra. -/
namespace KIP126.Literature.Standard.E2Exactness
open CategoryTheory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Core.SpectralSequence
noncomputable section
set_option autoImplicit false

/-- The cochain-homology boundary in the original classical E₂ coordinates.
It has bidegree `(1,0)` and is defined for arbitrary spectra. -/
public def spectrumHomologyShortExactConnectingHom (U : Triangle Spectrum)
    (hU : U ∈ distTriang Spectrum) (hH : HomologyShortExact coefficients U) (s t : ℤ) :
    (classical.obj U.obj₃).Page 2 (s,t) →+ (classical.obj U.obj₁).Page 2 (s+1,t) :=
  ActualE2LES.spectrumHomologyShortExactConnectingHom U hU hH s t

/-- All three exactness positions for homology-short-exact triangles
and their classical page maps. -/
public theorem spectrumHomologyShortExactLongExactSequence (U : Triangle Spectrum)
    (hU : U ∈ distTriang Spectrum) (hH : HomologyShortExact coefficients U) (s t : ℤ) :
    (∀ y : (classical.obj U.obj₂).Page 2 (s,t),
      (classical.map U.mor₂).pageMap 2 (s,t) y = 0 ↔
        ∃ x, (classical.map U.mor₁).pageMap 2 (s,t) x = y) ∧
    (∀ z : (classical.obj U.obj₃).Page 2 (s,t),
      spectrumHomologyShortExactConnectingHom U hU hH s t z = 0 ↔
        ∃ y, (classical.map U.mor₂).pageMap 2 (s,t) y = z) ∧
    (∀ x : (classical.obj U.obj₁).Page 2 (s+1,t),
      (classical.map U.mor₁).pageMap 2 (s+1,t) x = 0 ↔
        ∃ z, spectrumHomologyShortExactConnectingHom U hU hH s t z = x) :=
  ActualE2LES.spectrumHomologyShortExactLongExactSequence U hU hH s t

end
end KIP126.Literature.Standard.E2Exactness
