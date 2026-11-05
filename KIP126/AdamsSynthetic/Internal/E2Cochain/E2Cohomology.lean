module

import all KIP126.AdamsSynthetic.Internal.E2Cochain.E2Quotient
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

namespace KIP126.AdamsSynthetic.Internal.E2Cochain
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Core.SpectralSequence
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem shortComplex_rangeToCycles {R : Type w} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) :
    LinearMap.range S.moduleCatToCycles =
      (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype := by
  ext a
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b,hb⟩
    exact ⟨b, Subtype.ext hb⟩

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H} {X : C}
  {T : AbstractAdamsTower unit X}
  {D : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
  {δ : ∀ (r : ℤ) (p : ℤ × ℤ), (D p).page (↑(r-2).toNat : WithTop ℕ) ⟶
    (D (p+(r,r-1))).page (↑(r-2).toNat : WithTop ℕ)}

private def e2ShortComplexQuotientIso (P : TowerSequencePresentation unit T D δ) (t s : ℤ) :
    ((cochain T t).sc' (s-1) s (s+1)).moduleCatLeftHomologyData.H ≅ (D (s,t)).page 0 := by
  let S := (cochain T t).sc' (s-1) s (s+1)
  change ModuleCat.of ℤ ((LinearMap.ker S.g.hom) ⧸ LinearMap.range S.moduleCatToCycles) ≅ _
  refine (Submodule.quotEquivOfEq _ _ (shortComplex_rangeToCycles S)).toModuleIso ≪≫ ?_
  change ModuleCat.of ℤ ((LinearMap.ker ((cochain T t).d s (s+1)).hom) ⧸
    (LinearMap.range ((cochain T t).d (s-1) s).hom).comap
      (LinearMap.ker ((cochain T t).d s (s+1)).hom).subtype) ≅ _
  rw [cochain_d]
  exact (e2CochainQuotientEquiv P t s).toModuleIso

/-- Cohomology of the actual integer cochain complex is the supplied E₂ page. -/
private def e2CohomologyIso (P : TowerSequencePresentation unit T D δ) (t s : ℤ) :
    (cochain T t).homology s ≅ (D (s,t)).page 0 :=
  (cochain T t).homologyIsoSc' (s-1) s (s+1) (by simp) (by simp) ≪≫
    ((cochain T t).sc' (s-1) s (s+1)).moduleCatHomologyIso ≪≫
      e2ShortComplexQuotientIso P t s

end
end KIP126.AdamsSynthetic.Internal.E2Cochain
