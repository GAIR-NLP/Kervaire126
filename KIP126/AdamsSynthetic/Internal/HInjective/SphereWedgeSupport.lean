module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.StrictWedge
import Mathlib.Topology.Separation.Basic
import Mathlib.Logic.Relation

/-! Finite support specialized to the actual fixed source sphere.
The actual reduced-suspension quotients are T1-separated. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Source
open CategoryTheory Topology
open scoped unitInterval
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace BasedSpace
private theorem suspension_eq_iff (X : BasedSpace.{u}) (a b : X × I) :
    Quot.mk (SuspensionRelation X) a = Quot.mk (SuspensionRelation X) b ↔
      a = b ∨ (SuspensionCollapsed X a ∧ SuspensionCollapsed X b) := by
  constructor
  · intro h
    have hrel := Quot.eqvGen_exact h
    clear h
    induction hrel with
    | rel a b h => exact Or.inr h
    | refl a => exact Or.inl rfl
    | symm a b h ih => exact ih.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
    | trans a b c h k ih ik =>
      rcases ih with rfl | ⟨ha,hb⟩
      · exact ik
      rcases ik with rfl | ⟨_,hc⟩
      · exact Or.inr ⟨ha,hb⟩
      · exact Or.inr ⟨ha,hc⟩
  · rintro (rfl | h)
    · rfl
    · exact Quot.sound h

private theorem suspension_t1 (X : BasedSpace.{u}) [T1Space X] : T1Space X.suspension := by
  have hc : IsClosed {p : X × I | SuspensionCollapsed X p} := by
    exact (isClosed_singleton.preimage continuous_fst).union
      ((isClosed_singleton.preimage continuous_snd).union
        (isClosed_singleton.preimage continuous_snd))
  constructor
  intro x
  refine Quot.inductionOn x ?_
  intro a
  change IsClosed ({Quot.mk (SuspensionRelation X) a} : Set (Quot (SuspensionRelation X)))
  rw [← isQuotientMap_quot_mk.isClosed_preimage]
  by_cases ha : SuspensionCollapsed X a
  · have he : Quot.mk (SuspensionRelation X) ⁻¹' {Quot.mk (SuspensionRelation X) a} =
        {p : X × I | SuspensionCollapsed X p} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
        suspension_eq_iff]
      exact ⟨fun h => h.elim (fun h => h.symm ▸ ha) And.left, fun hp => Or.inr ⟨hp,ha⟩⟩
    rw [he]
    exact hc
  · have he : Quot.mk (SuspensionRelation X) ⁻¹' {Quot.mk (SuspensionRelation X) a} = {a} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, suspension_eq_iff, ha,
        and_false, or_false]
    rw [he]
    exact isClosed_singleton
end BasedSpace

namespace Prespectrum
private theorem sphere_level_t1 (n : ℕ) : T1Space (sphere.level n) := by
  change T1Space (sphereLevel n)
  induction n with
  | zero => exact inferInstanceAs (T1Space (Fin 2))
  | succ n ih =>
    letI := ih
    exact BasedSpace.suspension_t1 (sphereLevel n)

/-- No separation premise remains for the actual source sphere: every class
    of its strict small wedge comes from a finite subwedge via the same inclusions. -/
private theorem actual_sphere_strict_wedge_finite_support (J : Type) (d : ℤ)
    (a : StableHomotopy (strictWedge (fun _ : J => sphere)) d) :
    ∃ (s : Finset J)
      (b : StableHomotopy (strictWedge (fun _ : (s : Set J) => sphere)) d),
      stableHomotopyMap (strictWedgeSubfamily (fun _ : J => sphere) (s : Set J)) d b = a := by
  letI : ∀ (_ : J) (n : ℕ), T1Space (sphere.level n) := fun _ n => sphere_level_t1 n
  exact @strictWedge_stableHomotopy_finite_support _ (fun _ : J => sphere)
    (fun _ n => sphere_level_t1 n) d a

end Prespectrum
end
end KIP126.AdamsSynthetic.Source
end
