module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import Mathlib.Logic.Function.Iterate

@[expose] section

/-! Cofinal representatives and vanishing for the actual point-set stable
homotopy quotient. These arguments use only its displayed stabilization and
based-homotopy relations; no completion or spectrum-model input is used. -/

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open Topology
open scoped Topology.Homotopy unitInterval

universe u

variable {X : Prespectrum.{u}} {d : ℤ}

/-- The bonding map sends a constant cubical loop to a constant loop. -/
@[simp] theorem stabilizeLoop_const (n r : ℕ) :
    stabilizeLoop X n r GenLoop.const = GenLoop.const := by
  apply GenLoop.ext
  intro t
  exact X.bond_point n (t 0)

@[simp] theorem Representative.iterate_next_stage (a : Representative X d) (k : ℕ) :
    ((Representative.next^[k]) a).stage = a.stage + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change ((Representative.next^[k]) a).stage + 1 = _
    omega

/-- Any finite number of actual bonding maps preserves the stable class. -/
theorem Representative.class_eq_iterate_next (a : Representative X d) (k : ℕ) :
    (Quot.mk (StableRelation X d) a : StableHomotopy X d) =
      Quot.mk _ ((Representative.next^[k]) a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (Quot.sound (StableRelation.stabilization _))

theorem Representative.iterate_next_loop_const (a : Representative X d)
    (h : a.loop = GenLoop.const) (k : ℕ) :
    ((Representative.next^[k]) a).loop = GenLoop.const := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change stabilizeLoop X _ _ _ = _
    rw [ih, stabilizeLoop_const]
    rfl

/-- Based homotopies give equality of the displayed stable classes. -/
theorem loopClass_eq_of_homotopic (n r : ℕ) (hr : (r : ℤ) = d + n)
    (p q : GenLoop (Fin r) (X.level n) (X.level n).point)
    (h : GenLoop.Homotopic p q) : loopClass X d n r hr p = loopClass X d n r hr q :=
  Quot.sound (StableRelation.homotopy ⟨n, r, hr, p⟩ q h)

/-- Stabilization sends an actual based cubical homotopy to a based homotopy. -/
theorem stabilizeLoop_homotopic (P : Prespectrum.{u}) (n r : ℕ)
    (p q : GenLoop (Fin r) (P.level n) (P.level n).point) (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (stabilizeLoop P n r p) (stabilizeLoop P n r q) := by
  obtain ⟨H⟩ := h
  refine ⟨{ toFun := fun t => P.bond n (H (t.1,fun i => t.2 i.succ),t.2 0)
            continuous_toFun := (P.bond n).continuous.comp
              ((H.continuous.comp (continuous_fst.prodMk
                (continuous_pi fun i => (continuous_apply i.succ).comp continuous_snd))).prodMk
                  ((continuous_apply 0).comp continuous_snd))
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro t
    change P.bond n (H (0,_),_) = _
    rw [H.apply_zero]
    rfl
  · intro t
    change P.bond n (H (1,_),_) = _
    rw [H.apply_one]
    rfl
  · intro s t ht
    obtain ⟨i,hi⟩ := ht
    induction i using Fin.cases with
    | zero =>
      rcases hi with h | h
      · change P.bond n (H (s,_),t 0) = P.bond n (p _,t 0)
        rw [h,P.bond_zero,P.bond_zero]
      · change P.bond n (H (s,_),t 0) = P.bond n (p _,t 0)
        rw [h,P.bond_one,P.bond_one]
    | succ j =>
      change P.bond n (H (s,_),_) = P.bond n (p _,_)
      rw [H.eq_fst s ⟨j,hi⟩]
      rfl

end KIP126.AdamsSynthetic.Source.Prespectrum
