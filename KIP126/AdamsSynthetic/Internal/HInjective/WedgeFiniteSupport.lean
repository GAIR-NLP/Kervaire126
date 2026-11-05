module
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.DiscreteSubset

/-! Private finite-support slice. No actual-source coproduct or compactness premise is postulated. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Source.CompactWedge

universe u v

variable {J : Type u} (X : J → Type v) [∀ j, TopologicalSpace (X j)] (x₀ : ∀ j, X j)

/-- The actual disjoint union with one extra common basepoint. This also
specifies the empty wedge without a nonemptiness hypothesis on the index. -/
abbrev WedgeCarrier := (Σ j, X j) ⊕ PUnit

/-- Exactly the original basepoints and the extra point are collapsed. -/
def WedgeCollapsed : WedgeCarrier X → Prop
  | Sum.inl ⟨j,x⟩ => x = x₀ j
  | Sum.inr _ => True

/-- The equivalence relation for the actual wedge topology. -/
def wedgeSetoid : Setoid (WedgeCarrier X) where
  r a b := a = b ∨ (WedgeCollapsed X x₀ a ∧ WedgeCollapsed X x₀ b)
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
    trans := by
      intro a b c h k
      rcases h with rfl | ⟨ha,hb⟩
      · exact k
      rcases k with rfl | ⟨_,hc⟩
      · exact Or.inr ⟨ha,hb⟩
      · exact Or.inr ⟨ha,hc⟩ }

/-- The wedge has the genuine quotient topology of its disjoint union. -/
abbrev Wedge := Quotient (wedgeSetoid X x₀)

def wedgePoint : Wedge X x₀ := Quotient.mk' (s := wedgeSetoid X x₀) (Sum.inr PUnit.unit)

def wedgeInclusion (j : J) : C(X j,Wedge X x₀) :=
  ⟨fun x => Quotient.mk' (s := wedgeSetoid X x₀) (Sum.inl ⟨j,x⟩),
    continuous_quotient_mk'.comp (continuous_inl.comp continuous_sigmaMk)⟩

/-- Compatible continuous maps descend through the actual common-point
quotient. -/
def wedgeDesc {Y : Type*} [TopologicalSpace Y] (y₀ : Y)
    (f : ∀ j, C(X j,Y)) (hf : ∀ j, f j (x₀ j) = y₀) : C(Wedge X x₀,Y) := by
  let g : WedgeCarrier X → Y := Sum.elim (fun z => f z.1 z.2) (fun _ => y₀)
  have hpoint (z : WedgeCarrier X) (hz : WedgeCollapsed X x₀ z) : g z = y₀ := by
    cases z with
    | inl z => rcases z with ⟨j,x⟩; change x = x₀ j at hz; subst x; exact hf j
    | inr _ => rfl
  have hr : ∀ a b, (wedgeSetoid X x₀).r a b → g a = g b := by
    intro a b h
    rcases h with rfl | ⟨ha,hb⟩
    · rfl
    · exact (hpoint a ha).trans (hpoint b hb).symm
  exact ⟨Quotient.lift g hr,
    (continuous_sum_dom.mpr
      ⟨continuous_sigma (fun j => (f j).continuous),continuous_const⟩).quotient_lift hr⟩

end KIP126.AdamsSynthetic.Source.CompactWedge

namespace KIP126.AdamsSynthetic.Source.CompactWedge

open Set
universe u v
variable {J : Type u} {X : J → Type v} [∀ j, TopologicalSpace (X j)] {x₀ : ∀ j, X j}

@[simp] theorem wedgeInclusion_point (j : J) :
    wedgeInclusion X x₀ j (x₀ j) = wedgePoint X x₀ :=
  Quotient.sound (Or.inr ⟨rfl, trivial⟩)

@[simp] theorem wedgeInclusion_eq_point_iff (j : J) (x : X j) :
    wedgeInclusion X x₀ j x = wedgePoint X x₀ ↔ x = x₀ j := by
  constructor
  · intro h
    rcases Quotient.exact h with h | h
    · cases h
    · exact h.1
  · rintro rfl
    exact wedgeInclusion_point j

@[simp] theorem wedgeDesc_inclusion {Y : Type*} [TopologicalSpace Y] (y₀ : Y)
    (f : ∀ j, C(X j,Y)) (hf : ∀ j, f j (x₀ j) = y₀) (j : J) (x : X j) :
    wedgeDesc X x₀ y₀ f hf (wedgeInclusion X x₀ j x) = f j x := rfl

@[simp] theorem wedgeDesc_point {Y : Type*} [TopologicalSpace Y] (y₀ : Y)
    (f : ∀ j, C(X j,Y)) (hf : ∀ j, f j (x₀ j) = y₀) :
    wedgeDesc X x₀ y₀ f hf (wedgePoint X x₀) = y₀ := rfl

/-- Equality away from the common point identifies the actual summand. -/
theorem wedgeInclusion_eq_index {i j : J} {x : X i} {y : X j}
    (hx : x ≠ x₀ i) (h : wedgeInclusion X x₀ i x = wedgeInclusion X x₀ j y) : i = j := by
  rcases Quotient.exact h with h | h
  · exact congrArg Sigma.fst (Sum.inl.inj h)
  · exact False.elim (hx h.1)

/-- A selected nonbasepoint in each of any set of distinct summands forms
a closed subset of the actual wedge, provided each summand is T1. -/
theorem wedgeInclusion_selected_isClosed [∀ j, T1Space (X j)]
    (s : Set J) (x : ∀ j, X j) (hx : ∀ j ∈ s, x j ≠ x₀ j) :
    IsClosed ((fun j => wedgeInclusion X x₀ j (x j)) '' s) := by
  classical
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage]
  apply isClosed_sum_iff.mpr
  constructor
  · apply isClosed_sigma_iff.mpr
    intro i
    have he : (fun y : X i => Quotient.mk' (s := wedgeSetoid X x₀) (Sum.inl ⟨i,y⟩)) ⁻¹'
        ((fun j => wedgeInclusion X x₀ j (x j)) '' s) =
        if i ∈ s then {x i} else ∅ := by
      ext y
      classical
      by_cases hi : i ∈ s
      · simp only [hi,ite_true,mem_preimage,mem_image,mem_singleton_iff]
        constructor
        · rintro ⟨j,hj,h⟩
          have hji := wedgeInclusion_eq_index (hx j hj) h
          subst j
          rcases Quotient.exact h with h | h
          · exact (eq_of_heq (Sigma.mk.inj (Sum.inl.inj h)).2).symm
          · exact False.elim (hx i hi h.1)
        · rintro rfl
          exact ⟨i,hi,rfl⟩
      · simp only [hi,ite_false,mem_preimage,mem_image,mem_empty_iff_false,iff_false]
        rintro ⟨j,hj,h⟩
        exact hi ((wedgeInclusion_eq_index (hx j hj) h) ▸ hj)
    change IsClosed ((fun y : X i => Quotient.mk' (s := wedgeSetoid X x₀) (Sum.inl ⟨i,y⟩)) ⁻¹'
      ((fun j => wedgeInclusion X x₀ j (x j)) '' s))
    rw [he]
    split_ifs <;> simp
  · have he : (fun z : PUnit => Quotient.mk' (s := wedgeSetoid X x₀) (Sum.inr z)) ⁻¹'
        ((fun j => wedgeInclusion X x₀ j (x j)) '' s) = ∅ := by
      ext z
      simp only [mem_preimage,mem_image,mem_empty_iff_false,iff_false]
      rintro ⟨j,hj,h⟩
      exact hx j hj ((wedgeInclusion_eq_point_iff j (x j)).mp h)
    change IsClosed ((fun z : PUnit => Quotient.mk' (s := wedgeSetoid X x₀) (Sum.inr z)) ⁻¹'
      ((fun j => wedgeInclusion X x₀ j (x j)) '' s))
    rw [he]
    exact isClosed_empty

end KIP126.AdamsSynthetic.Source.CompactWedge

namespace KIP126.AdamsSynthetic.Source.CompactWedge

open Set
universe u v
variable {J : Type u} {X : J → Type v} [∀ j, TopologicalSpace (X j)] {x₀ : ∀ j, X j}

/-- Nonbasepoints selected in distinct summands form an actual discrete
subset of the quotient wedge. -/
theorem wedgeInclusion_selected_isDiscrete [∀ j, T1Space (X j)]
    (s : Set J) (x : ∀ j, X j) (hx : ∀ j ∈ s, x j ≠ x₀ j) :
    IsDiscrete ((fun j => wedgeInclusion X x₀ j (x j)) '' s) := by
  apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
  intro t ht
  let s' := {j | j ∈ s ∧ wedgeInclusion X x₀ j (x j) ∈ t}
  have he : (fun j => wedgeInclusion X x₀ j (x j)) '' s' = t := by
    apply Set.Subset.antisymm
    · rintro _ ⟨j,hj,rfl⟩
      exact hj.2
    · intro z hz
      obtain ⟨j,hj,rfl⟩ := ht hz
      exact ⟨j,⟨hj,hz⟩,rfl⟩
  refine ⟨t,?_,Set.inter_eq_left.mpr ht⟩
  rw [← he]
  exact wedgeInclusion_selected_isClosed s' x (fun j hj => hx j hj.1)

/-- A compact subset of the actual wedge meets only finitely many
summands away from the common basepoint. The T1 hypothesis is on the
original summands, and no local finiteness assumption is imposed. -/
theorem isCompact_wedge_finite_support [∀ j, T1Space (X j)]
    {K : Set (Wedge X x₀)} (hK : IsCompact K) :
    {j | ∃ x : X j, x ≠ x₀ j ∧ wedgeInclusion X x₀ j x ∈ K}.Finite := by
  classical
  let s : Set J := {j | ∃ x : X j, x ≠ x₀ j ∧ wedgeInclusion X x₀ j x ∈ K}
  let x (j : J) : X j := if h : j ∈ s then h.choose else x₀ j
  have hx (j : J) (hj : j ∈ s) : x j ≠ x₀ j ∧ wedgeInclusion X x₀ j (x j) ∈ K := by
    dsimp only [x]
    rw [dif_pos hj]
    exact hj.choose_spec
  let f (j : J) := wedgeInclusion X x₀ j (x j)
  have hclosed : IsClosed (f '' s) :=
    wedgeInclusion_selected_isClosed s x (fun j hj => (hx j hj).1)
  have hdisc : IsDiscrete (f '' s) :=
    wedgeInclusion_selected_isDiscrete s x (fun j hj => (hx j hj).1)
  have hsub : f '' s ⊆ K := by
    rintro _ ⟨j,hj,rfl⟩
    exact (hx j hj).2
  have hinj : Set.InjOn f s := fun i hi j _ hij =>
    wedgeInclusion_eq_index (hx i hi).1 hij
  exact ((hK.of_isClosed_subset hclosed hsub).finite hdisc).of_finite_image hinj

/-- Every continuous map from a compact space into the actual wedge has
only finitely many nonbasepoint summands in its image. -/
theorem continuousMap_wedge_finite_support [∀ j, T1Space (X j)]
    {A : Type*} [TopologicalSpace A] [CompactSpace A] (f : C(A,Wedge X x₀)) :
    {j | ∃ x : X j, x ≠ x₀ j ∧ wedgeInclusion X x₀ j x ∈ Set.range f}.Finite :=
  isCompact_wedge_finite_support (isCompact_range f.continuous)

end KIP126.AdamsSynthetic.Source.CompactWedge

namespace KIP126.AdamsSynthetic.Source.CompactWedge

open Set
universe u v
variable {J : Type u} (X : J → Type v) [∀ j, TopologicalSpace (X j)] (x₀ : ∀ j, X j)

/-- Include an actual subfamily wedge by the original summand maps. -/
def wedgeSubfamilyInclusion (s : Set J) :
    C(Wedge (fun j : s => X j.val) (fun j => x₀ j.val),Wedge X x₀) :=
  wedgeDesc _ _ (wedgePoint X x₀) (fun j => wedgeInclusion X x₀ j.val)
    (fun j => wedgeInclusion_point j.val)

/-- The continuous retraction which collapses every omitted summand to
the common point of the subfamily wedge. -/
noncomputable def wedgeSubfamilyRetraction (s : Set J) :
    C(Wedge X x₀,Wedge (fun j : s => X j.val) (fun j => x₀ j.val)) := by
  classical
  exact wedgeDesc X x₀ (wedgePoint (fun j : s => X j.val) (fun j => x₀ j.val))
    (fun j => if h : j ∈ s then
      wedgeInclusion (fun j : s => X j.val) (fun j => x₀ j.val) ⟨j,h⟩ else
        ContinuousMap.const _ (wedgePoint (fun j : s => X j.val) (fun j => x₀ j.val)))
    (fun j => by split_ifs <;> simp)

end KIP126.AdamsSynthetic.Source.CompactWedge

namespace KIP126.AdamsSynthetic.Source.CompactWedge

open Set
universe u v
variable {J : Type u} {X : J → Type v} [∀ j, TopologicalSpace (X j)] {x₀ : ∀ j, X j}

@[simp] theorem wedgeSubfamilyInclusion_point (s : Set J) :
    wedgeSubfamilyInclusion X x₀ s (wedgePoint _ _) = wedgePoint X x₀ := rfl

@[simp] theorem wedgeSubfamilyRetraction_point (s : Set J) :
    wedgeSubfamilyRetraction X x₀ s (wedgePoint X x₀) = wedgePoint _ _ := rfl

@[simp] theorem wedgeSubfamilyInclusion_inclusion (s : Set J) (j : s) (x : X j.val) :
    wedgeSubfamilyInclusion X x₀ s (wedgeInclusion _ _ j x) =
      wedgeInclusion X x₀ j.val x := rfl

@[simp] theorem wedgeSubfamilyRetraction_inclusion (s : Set J) (j : J)
    (hj : j ∈ s) (x : X j) :
    wedgeSubfamilyRetraction X x₀ s (wedgeInclusion X x₀ j x) =
      wedgeInclusion (fun j : s => X j.val) (fun j => x₀ j.val) ⟨j,hj⟩ x := by
  classical
  simp only [wedgeSubfamilyRetraction,wedgeDesc_inclusion,dif_pos hj]

/-- The displayed subfamily projection really retracts the actual
inclusion, including at the common point. -/
theorem wedgeSubfamilyRetraction_leftInverse (s : Set J) :
    Function.LeftInverse (wedgeSubfamilyRetraction X x₀ s)
      (wedgeSubfamilyInclusion X x₀ s) := by
  intro z
  refine Quotient.inductionOn z ?_
  rintro (⟨j,x⟩ | ⟨⟩)
  · exact wedgeSubfamilyRetraction_inclusion s j.val j.property x
  · rfl

/-- An inclusion followed by the actual subfamily retraction fixes every
point whose nonbasepoint summand belongs to the selected subfamily. -/
theorem wedgeSubfamilyInclusion_retraction_of_support (s : Set J) (z : Wedge X x₀)
    (hz : ∀ j (x : X j), x ≠ x₀ j → wedgeInclusion X x₀ j x = z → j ∈ s) :
    wedgeSubfamilyInclusion X x₀ s (wedgeSubfamilyRetraction X x₀ s z) = z := by
  classical
  induction z using Quotient.inductionOn with
  | h z =>
    rcases z with ⟨j,x⟩ | ⟨⟩
    · change wedgeSubfamilyInclusion X x₀ s
        (wedgeSubfamilyRetraction X x₀ s (wedgeInclusion X x₀ j x)) = wedgeInclusion X x₀ j x
      by_cases hx : x = x₀ j
      · subst x
        simp
      · rw [wedgeSubfamilyRetraction_inclusion s j (hz j x hx rfl)]
        rfl
    · rfl

/-- Every continuous compact-domain map into the actual wedge factors
continuously through the wedge of finitely many of the same summands. -/
theorem continuousMap_wedge_factor_finite [∀ j, T1Space (X j)]
    {A : Type*} [TopologicalSpace A] [CompactSpace A] (f : C(A,Wedge X x₀)) :
    ∃ (s : Finset J)
      (g : C(A,Wedge (fun j : (s : Set J) => X j.val) (fun j => x₀ j.val))),
      (wedgeSubfamilyInclusion X x₀ (s : Set J)).comp g = f := by
  classical
  let support := {j | ∃ x : X j, x ≠ x₀ j ∧ wedgeInclusion X x₀ j x ∈ Set.range f}
  have hs : support.Finite := continuousMap_wedge_finite_support f
  let s := hs.toFinset
  refine ⟨s,(wedgeSubfamilyRetraction X x₀ (s : Set J)).comp f,?_⟩
  apply ContinuousMap.ext
  intro a
  apply wedgeSubfamilyInclusion_retraction_of_support
  intro j x hx he
  change j ∈ hs.toFinset
  exact hs.mem_toFinset.mpr ⟨x,hx,⟨a,he.symm⟩⟩

end KIP126.AdamsSynthetic.Source.CompactWedge

end
