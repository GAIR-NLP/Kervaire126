module
import all KIP126.Literature.E2Exactness.Ordinary.FixedTensorSES
import all KIP126.Literature.E2Exactness.Ordinary.FixedLayerAnnihilation
import all KIP126.Literature.E2Exactness.Ordinary.CochainLES

@[expose] section
namespace KIP126.Literature.Standard.FixedTensorE2
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated HomologicalComplex
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {X₀ : Spectrum} (T : AbstractAdamsTower coefficients.unit X₀)
  (t : ℤ) (U : Triangle Spectrum) (hU : U ∈ distTriang Spectrum)
  (hH : HomologyShortExact coefficients U)

include hU hH

private theorem tensorCochain_homologyShortExact (s : ℤ) :
    ((tensorCochainShortComplex T t U hU).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℤ) s)).ShortExact :=
  tensorCochain_degreewise_shortExact T t U hU
    (fun s => FixedLayerAnnihilation.shifted_layer_tensor_annihilates T s s U.mor₃
      (E2LayerSES.homologyShortExact_boundary_annihilated U hU hH)) s

private def tensorCochainBoundary (s : ℤ) :
    (tensorHomotopyCochain T t U.obj₃).homology s ⟶
      (tensorHomotopyCochain T t U.obj₁).homology (s+1) :=
  E2ComplexLES.δ (tensorCochainShortComplex T t U hU)
    (tensorCochain_homologyShortExact T t U hU hH) s

private theorem tensorCochain_les_exact (s : ℤ) :
    (ComposableArrows.mk₅
      (homologyMap (tensorHomotopyCochainMap T t U.mor₁) s)
      (homologyMap (tensorHomotopyCochainMap T t U.mor₂) s)
      (tensorCochainBoundary T t U hU hH s)
      (homologyMap (tensorHomotopyCochainMap T t U.mor₁) (s+1))
      (homologyMap (tensorHomotopyCochainMap T t U.mor₂) (s+1))).Exact :=
  E2ComplexLES.homology_les_exact (tensorCochainShortComplex T t U hU)
    (tensorCochain_homologyShortExact T t U hU hH) s

private theorem tensorCochain_range_eq_ker_middle (s : ℤ) :
    LinearMap.range (homologyMap (tensorHomotopyCochainMap T t U.mor₁) s).hom =
      LinearMap.ker (homologyMap (tensorHomotopyCochainMap T t U.mor₂) s).hom :=
  E2ComplexLES.homology_range_eq_ker_middle (tensorCochainShortComplex T t U hU)
    (tensorCochain_homologyShortExact T t U hU hH) s

private theorem tensorCochain_range_eq_ker_before_boundary (s : ℤ) :
    LinearMap.range (homologyMap (tensorHomotopyCochainMap T t U.mor₂) s).hom =
      LinearMap.ker (tensorCochainBoundary T t U hU hH s).hom :=
  E2ComplexLES.homology_range_eq_ker_before_δ (tensorCochainShortComplex T t U hU)
    (tensorCochain_homologyShortExact T t U hU hH) s

private theorem tensorCochain_range_eq_ker_after_boundary (s : ℤ) :
    LinearMap.range (tensorCochainBoundary T t U hU hH s).hom =
      LinearMap.ker (homologyMap (tensorHomotopyCochainMap T t U.mor₁) (s+1)).hom :=
  E2ComplexLES.homology_range_eq_ker_after_δ (tensorCochainShortComplex T t U hU)
    (tensorCochain_homologyShortExact T t U hU hH) s
end
end KIP126.Literature.Standard.FixedTensorE2
end
