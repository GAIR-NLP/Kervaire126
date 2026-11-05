module

import all KIP126.AdamsSynthetic.Internal.E2Cochain.AdamsCochain
import Mathlib.LinearAlgebra.Isomorphisms

namespace KIP126.AdamsSynthetic.Internal.E2Cochain
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Core.SpectralSequence
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H} {X : C}
  {T : AbstractAdamsTower unit X}
  {D : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
  {δ : ∀ (r : ℤ) (p : ℤ × ℤ), (D p).page (↑(r-2).toNat : WithTop ℕ) ⟶
    (D (p+(r,r-1))).page (↑(r-2).toNat : WithTop ℕ)}

/-- The original ambient identification, followed by the original page-zero quotient. -/
private def cyclesToPage (P : TowerSequencePresentation unit T D δ) (p : ℤ × ℤ) :
    T.cycles 2 (show 1 ≤ (2:ℕ) from one_le_two) p →ₗ[ℤ] (D p).page 0 :=
  (ambientToZeroPage (D p)).comp (P.ambient p).inv.hom

private theorem cyclesToPage_ambient (P : TowerSequencePresentation unit T D δ)
    (p : ℤ × ℤ) (a : (D p).V) :
    cyclesToPage P p ((P.ambient p).hom a) = ambientToZeroPage (D p) a := by
  change ambientToZeroPage (D p) ((P.ambient p).inv ((P.ambient p).hom a)) = _
  congr 1
  exact congrArg (fun f => f a) (P.ambient p).hom_inv_id

private theorem cyclesToPage_surjective (P : TowerSequencePresentation unit T D δ)
    (p : ℤ × ℤ) : Function.Surjective (cyclesToPage P p) := by
  intro a
  obtain ⟨b,hb⟩ := ambientToZeroPage_surjective (D p) a
  exact ⟨(P.ambient p).hom b, (cyclesToPage_ambient P p b).trans hb⟩

private theorem cyclesToPage_eq_zero_iff (P : TowerSequencePresentation unit T D δ)
    (p : ℤ × ℤ) (a : T.cycles 2 (show 1 ≤ (2:ℕ) from one_le_two) p) :
    cyclesToPage P p a = 0 ↔ a.val ∈ T.boundaries 2 (show 1 ≤ (2:ℕ) from one_le_two) p := by
  change ambientToZeroPage (D p) ((P.ambient p).inv a) = 0 ↔ _
  rw [ambientToZeroPage_eq_zero_iff]
  have h := P.boundaries p 0 ((P.ambient p).inv a)
  have ha : (P.ambient p).hom ((P.ambient p).inv a) = a :=
    congrArg (fun f => f a) (P.ambient p).inv_hom_id
  rw [ha] at h
  exact h

private def boundariesInCycles (T : AbstractAdamsTower unit X) (p : ℤ × ℤ) :
    Submodule ℤ (T.cycles 2 (show 1 ≤ (2:ℕ) from one_le_two) p) :=
  (T.boundaries 2 (show 1 ≤ (2:ℕ) from one_le_two) p).comap (T.cycles 2 (show 1 ≤ (2:ℕ) from one_le_two) p).subtype

private theorem cyclesToPage_ker (P : TowerSequencePresentation unit T D δ)
    (p : ℤ × ℤ) : LinearMap.ker (cyclesToPage P p) = boundariesInCycles T p := by
  ext a
  exact cyclesToPage_eq_zero_iff P p a

/-- E₂ is the actual cycle module modulo actual incoming boundaries. -/
private def e2CycleQuotientEquiv (P : TowerSequencePresentation unit T D δ) (p : ℤ × ℤ) :
    ((T.cycles 2 (show 1 ≤ (2:ℕ) from one_le_two) p) ⧸ boundariesInCycles T p) ≃ₗ[ℤ] (D p).page 0 :=
  (Submodule.quotEquivOfEq _ _ (cyclesToPage_ker P p).symm).trans
    ((cyclesToPage P p).quotKerEquivOfSurjective (cyclesToPage_surjective P p))

private theorem e2CycleQuotientEquiv_mk (P : TowerSequencePresentation unit T D δ)
    (p : ℤ × ℤ) (a : T.cycles 2 (show 1 ≤ (2:ℕ) from one_le_two) p) :
    e2CycleQuotientEquiv P p (Submodule.Quotient.mk a) = cyclesToPage P p a := rfl

/-- Representative compatibility with the supplied ambient object. -/
private theorem e2CycleQuotientEquiv_ambient (P : TowerSequencePresentation unit T D δ)
    (p : ℤ × ℤ) (a : (D p).V) :
    e2CycleQuotientEquiv P p (Submodule.Quotient.mk ((P.ambient p).hom a)) =
      ambientToZeroPage (D p) a :=
  cyclesToPage_ambient P p a

private def cochainCyclesToPage (P : TowerSequencePresentation unit T D δ) (t s : ℤ) :
    LinearMap.ker (cochainDifferential T t s) →ₗ[ℤ] (D (s,t)).page 0 :=
  (cyclesToPage P (s,t)).comp
    (LinearEquiv.ofEq _ _ (cycles2_eq_ker T t s).symm).toLinearMap

/-- Incoming image viewed inside the outgoing kernel of the actual complex. -/
private def cochainBoundaryInKernel (T : AbstractAdamsTower unit X) (t s : ℤ) :
    Submodule ℤ (LinearMap.ker (cochainDifferential T t s)) :=
  (LinearMap.range ((cochain T t).d (s-1) s).hom).comap
    (LinearMap.ker (cochainDifferential T t s)).subtype

private theorem cochainCyclesToPage_ker (P : TowerSequencePresentation unit T D δ)
    (t s : ℤ) : LinearMap.ker (cochainCyclesToPage P t s) = cochainBoundaryInKernel T t s := by
  ext a
  change cyclesToPage P (s,t) (LinearEquiv.ofEq _ _ (cycles2_eq_ker T t s).symm a) = 0 ↔ _
  rw [cyclesToPage_eq_zero_iff]
  change (a : T.FirstPage (s,t)) ∈ T.boundaries 2 _ (s,t) ↔
    (a : T.FirstPage (s,t)) ∈ LinearMap.range ((cochain T t).d (s-1) s).hom
  rw [boundaries2_eq_range]

private theorem cochainCyclesToPage_surjective (P : TowerSequencePresentation unit T D δ)
    (t s : ℤ) : Function.Surjective (cochainCyclesToPage P t s) :=
  (cyclesToPage_surjective P (s,t)).comp (LinearEquiv.ofEq _ _ (cycles2_eq_ker T t s).symm).surjective

/-- Explicit cochain cohomology quotient identified with the original E₂ page. -/
private def e2CochainQuotientEquiv (P : TowerSequencePresentation unit T D δ) (t s : ℤ) :
    ((LinearMap.ker (cochainDifferential T t s)) ⧸ cochainBoundaryInKernel T t s) ≃ₗ[ℤ]
      (D (s,t)).page 0 :=
  (Submodule.quotEquivOfEq _ _ (cochainCyclesToPage_ker P t s).symm).trans
    ((cochainCyclesToPage P t s).quotKerEquivOfSurjective (cochainCyclesToPage_surjective P t s))

private theorem e2CochainQuotientEquiv_mk (P : TowerSequencePresentation unit T D δ)
    (t s : ℤ) (a : LinearMap.ker (cochainDifferential T t s)) :
    e2CochainQuotientEquiv P t s (Submodule.Quotient.mk a) =
      cyclesToPage P (s,t) (LinearEquiv.ofEq _ _ (cycles2_eq_ker T t s).symm a) := rfl

end
end KIP126.AdamsSynthetic.Internal.E2Cochain
