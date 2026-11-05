module
import all KIP126.Literature.E2Exactness.Ordinary.FixedTensorComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] section
namespace KIP126.Literature.Standard.FixedTensorE2
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem triangle_homotopy_exact (U : Triangle Spectrum)
    (hU : U ∈ distTriang Spectrum) (d : ℤ) :
    Function.Exact (inducedMap U.mor₁ d) (inducedMap U.mor₂ d) := by
  intro a
  constructor
  · intro ha
    obtain ⟨b,hb⟩ := U.coyoneda_exact₂ hU a ha
    exact ⟨b,hb.symm⟩
  · rintro ⟨b,rfl⟩
    change (b ≫ U.mor₁) ≫ U.mor₂ = 0
    rw [Category.assoc, comp_distTriang_mor_zero₁₂ U hU, comp_zero]

private theorem triangle_homotopy_injective (U : Triangle Spectrum)
    (hU : U ∈ distTriang Spectrum) (hz : U.mor₃ = 0) (d : ℤ) :
    Function.Injective (inducedMap U.mor₁ d) := by
  letI : Mono U.mor₁ := U.mono₁ hU hz
  intro a b hab
  exact (cancel_mono U.mor₁).mp hab

private theorem triangle_homotopy_surjective (U : Triangle Spectrum)
    (hU : U ∈ distTriang Spectrum) (hz : U.mor₃ = 0) (d : ℤ) :
    Function.Surjective (inducedMap U.mor₂ d) := by
  intro a
  obtain ⟨b,hb⟩ := U.coyoneda_exact₃ hU a (by rw [hz, comp_zero])
  exact ⟨b,hb.symm⟩

variable {X₀ : Spectrum} (T : AbstractAdamsTower coefficients.unit X₀)

private def tensorCochainShortComplex (t : ℤ) (U : Triangle Spectrum)
    (hU : U ∈ distTriang Spectrum) : ShortComplex (CochainComplex (ModuleCat ℤ) ℤ) :=
  ShortComplex.mk (tensorHomotopyCochainMap T t U.mor₁)
    (tensorHomotopyCochainMap T t U.mor₂) (by
      ext s a
      change (a ≫ (T.layer s)⟦s⟧ ◁ U.mor₁) ≫ (T.layer s)⟦s⟧ ◁ U.mor₂ = 0
      rw [Category.assoc, ← whiskerLeft_comp, comp_distTriang_mor_zero₁₂ U hU]
      change a ≫ (tensorLeft ((T.layer s)⟦s⟧)).map 0 = 0
      rw [Functor.map_zero, comp_zero])

private theorem tensorCochain_degreewise_shortExact (t : ℤ) (U : Triangle Spectrum)
    (hU : U ∈ distTriang Spectrum)
    (hz : ∀ s : ℤ, (T.layer s)⟦s⟧ ◁ U.mor₃ = 0) (s : ℤ) :
    ((tensorCochainShortComplex T t U hU).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℤ) s)).ShortExact := by
  let K := (T.layer s)⟦s⟧
  let V := (tensorLeft K).mapTriangle.obj U
  have hV : V ∈ distTriang Spectrum := (tensorLeft K).map_distinguished U hU
  have hzero : V.mor₃ = 0 := by
    change K ◁ U.mor₃ ≫ _ = 0
    rw [hz s, zero_comp]
  apply ModuleCat.shortComplex_shortExact
  · exact triangle_homotopy_exact V hV t
  · exact triangle_homotopy_injective V hV hzero t
  · exact triangle_homotopy_surjective V hV hzero t

private theorem tensorCochain_shortExact (t : ℤ) (U : Triangle Spectrum)
    (hU : U ∈ distTriang Spectrum)
    (hz : ∀ s : ℤ, (T.layer s)⟦s⟧ ◁ U.mor₃ = 0) :
    (tensorCochainShortComplex T t U hU).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  exact tensorCochain_degreewise_shortExact T t U hU hz
end
end KIP126.Literature.Standard.FixedTensorE2
end
