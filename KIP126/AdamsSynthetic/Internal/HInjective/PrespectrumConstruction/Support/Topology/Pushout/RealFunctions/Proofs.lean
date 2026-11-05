module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.Topology.Ball.HomotopyExtension.Proofs
import all KIP126.AdamsSynthetic.Internal.Topology.HomotopyExtension.Predicates
import all KIP126.AdamsSynthetic.Internal.Topology.SequentialColimit.Proofs
import Mathlib.Topology.UrysohnsLemma

@[expose] section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology Set

universe u

set_option backward.isDefEq.respectTransparency false

/-- Compatible real-valued functions glue over the actual topological
pushout, with equality on both constituent spaces. -/
theorem exists_real_map_of_pushout
    {S A B P : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (fa : C(A, ℝ)) (fb : C(B, ℝ))
    (he : ∀ s, fa (i s) = fb (f s)) :
    ∃ g : C(P, ℝ), (∀ x, g (a x) = fa x) ∧ (∀ y, g (b y) = fb y) := by
  let u : A ⟶ TopCat.of (ULift.{u} ℝ) :=
    TopCat.ofHom ⟨fun x => ULift.up (fa x), continuous_uliftUp.comp fa.continuous⟩
  let v : B ⟶ TopCat.of (ULift.{u} ℝ) :=
    TopCat.ofHom ⟨fun y => ULift.up (fb y), continuous_uliftUp.comp fb.continuous⟩
  have hw : i ≫ u = f ≫ v := by
    ext s
    exact he s
  let q := PushoutCocone.mk u v hw
  let d := h.isColimit.desc q
  refine ⟨⟨fun x => (d x).down, continuous_uliftDown.comp d.hom.continuous⟩,?_,?_⟩
  · intro x
    exact congrArg ULift.down (ConcreteCategory.congr_hom (h.isColimit.fac q .left) x)
  · intro y
    exact congrArg ULift.down (ConcreteCategory.congr_hom (h.isColimit.fac q .right) y)

/-- A point outside the attaching boundary can be separated from every
other point of the cell source by a real function on the actual pushout. -/
theorem pushout_distinct_cell_points_real_separation
    {S A B P : TopCat.{u}} [NormalSpace A] [T1Space A]
    {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (hi : IsClosedEmbedding i)
    (x y : A) (hx : x ∉ Set.range i) (hxy : x ≠ y) :
    ∃ g : C(P, ℝ), g (a x) ≠ g (a y) := by
  obtain ⟨fa,hfa0,hfa1,_⟩ := exists_continuous_zero_one_of_isClosed
    (hi.isClosed_range.union (isClosed_singleton (x := y)))
    (isClosed_singleton (x := x))
    (Set.disjoint_singleton_right.mpr (by simp only [Set.mem_union,Set.mem_singleton_iff,not_or]; exact ⟨hx,hxy⟩))
  obtain ⟨g,hga,hgb⟩ := exists_real_map_of_pushout h fa (ContinuousMap.const B 0)
    (fun s => hfa0 (Or.inl (Set.mem_range_self s)))
  have hgx : g (a x) = 1 := (hga x).trans (hfa1 (Set.mem_singleton x))
  have hgy : g (a y) = 0 := (hga y).trans (hfa0 (Or.inr (Set.mem_singleton y)))
  exact ⟨g,by rw [hgx,hgy]; exact one_ne_zero⟩

/-- Arbitrary disjoint unions of normal spaces are normal, so a whole
family of Euclidean cells is a valid source for the separation argument. -/
theorem normalSpace_sigma {ι : Type*} (A : ι → Type*)
    [∀ i, TopologicalSpace (A i)] [∀ i, NormalSpace (A i)] : NormalSpace (Σ i, A i) where
  normal S T hS hT hST := by
    have h (i : ι) : SeparatedNhds (Sigma.mk i ⁻¹' S) (Sigma.mk i ⁻¹' T) :=
      normal_separation (hS.preimage continuous_sigmaMk) (hT.preimage continuous_sigmaMk)
        (hST.preimage (Sigma.mk i))
    choose U V hU hV hSU hTV hUV using h
    refine ⟨{p | p.2 ∈ U p.1},{p | p.2 ∈ V p.1},
      isOpen_sigma_iff.mpr hU,isOpen_sigma_iff.mpr hV,?_,?_,?_⟩
    · intro p hp
      exact hSU p.1 hp
    · intro p hp
      exact hTV p.1 hp
    · exact Set.disjoint_left.mpr fun p hp hq => Set.disjoint_left.mp (hUV p.1) hp hq

end KIP126.Topology
