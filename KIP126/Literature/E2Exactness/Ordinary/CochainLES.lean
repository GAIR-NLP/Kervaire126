module
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] section
namespace KIP126.Literature.Standard.E2ComplexLES
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
universe u
set_option autoImplicit false

variable (S : ShortComplex (CochainComplex (ModuleCat.{u} ℤ) ℤ))
    (hS : ∀ s : ℤ,
      (S.map (HomologicalComplex.eval (ModuleCat.{u} ℤ) (ComplexShape.up ℤ) s)).ShortExact)

include hS

/-- Degreewise short exactness gives short exactness of the same complex maps. -/
private theorem shortExact : S.ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact S hS

/-- The canonical snake-lemma boundary raises the cochain degree by one. -/
private def δ (s : ℤ) : S.X₃.homology s ⟶ S.X₁.homology (s+1) :=
  (shortExact S hS).δ s (s+1) (ComplexShape.up_mk _ _ rfl)

private theorem comp_δ (s : ℤ) :
    homologyMap S.g s ≫ δ S hS s = 0 :=
  (shortExact S hS).comp_δ s (s+1) (ComplexShape.up_mk _ _ rfl)

private theorem δ_comp (s : ℤ) :
    δ S hS s ≫ homologyMap S.f (s+1) = 0 :=
  (shortExact S hS).δ_comp s (s+1) (ComplexShape.up_mk _ _ rfl)

/-- Exactness at H^s(S.X₂), retaining homologyMap of S.f and S.g verbatim. -/
private theorem homology_exact_middle (s : ℤ) :
    (ShortComplex.mk (homologyMap S.f s) (homologyMap S.g s)
      (by rw [← homologyMap_comp, S.zero, homologyMap_zero])).Exact :=
  (shortExact S hS).homology_exact₂ s

/-- Exactness at H^s(S.X₃). -/
private theorem homology_exact_before_δ (s : ℤ) :
    (ShortComplex.mk (homologyMap S.g s) (δ S hS s) (comp_δ S hS s)).Exact :=
  (shortExact S hS).homology_exact₃ s (s+1) (ComplexShape.up_mk _ _ rfl)

/-- Exactness at H^(s+1)(S.X₁). -/
private theorem homology_exact_after_δ (s : ℤ) :
    (ShortComplex.mk (δ S hS s) (homologyMap S.f (s+1)) (δ_comp S hS s)).Exact :=
  (shortExact S hS).homology_exact₁ s (s+1) (ComplexShape.up_mk _ _ rfl)

/-- Six consecutive terms of the long exact sequence, with the exact original
homology maps on either side of the canonical boundary. -/
private theorem homology_les_exact (s : ℤ) :
    (ComposableArrows.mk₅ (homologyMap S.f s) (homologyMap S.g s) (δ S hS s)
      (homologyMap S.f (s+1)) (homologyMap S.g (s+1))).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact
    (shortExact S hS) s (s+1) (ComplexShape.up_mk _ _ rfl)

private theorem homology_range_eq_ker_middle (s : ℤ) :
    LinearMap.range (homologyMap S.f s).hom = LinearMap.ker (homologyMap S.g s).hom :=
  (homology_exact_middle S hS s).moduleCat_range_eq_ker

private theorem homology_range_eq_ker_before_δ (s : ℤ) :
    LinearMap.range (homologyMap S.g s).hom = LinearMap.ker (δ S hS s).hom :=
  (homology_exact_before_δ S hS s).moduleCat_range_eq_ker

private theorem homology_range_eq_ker_after_δ (s : ℤ) :
    LinearMap.range (δ S hS s).hom = LinearMap.ker (homologyMap S.f (s+1)).hom :=
  (homology_exact_after_δ S hS s).moduleCat_range_eq_ker

end
end KIP126.Literature.Standard.E2ComplexLES
end
