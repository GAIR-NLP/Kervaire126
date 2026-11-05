module

import all KIP126.SpectralSequence.Completion.UniversalProperty.Data

@[expose] section

/-!
# Universal property of completion
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasLimitsOfShape ℕᵒᵖ C]

set_option maxHeartbeats 8000000 in
lemma Filtration.completionLift_proj {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (T : C)
    (f : ∀ s₀ : ℤ, T ⟶ (fil.completionFiltration hbb).truncatedObj s₀ k)
    (hcompat : ∀ (s₀ s₁ : ℤ) (h : s₀ ≤ s₁),
      f s₁ ≫ (fil.completionFiltration hbb).truncationTransition h k = f s₀)
    (s₀ : ℤ) :
    fil.completionLift hbb k T f hcompat ≫
      (fil.completionFiltration hbb).truncationProj s₀ k = f s₀ := by
  apply (cancel_mono (fil.completionψ hbb k s₀)).mp
  rw [Category.assoc, fil.completionψ_factorization hbb k s₀]
  simp only [Filtration.completionProj', Filtration.completion,
    Filtration.completionFunctor]
  rw [← Category.assoc]
  simp only [Filtration.completionLift]
  erw [limit.lift_π]
  unfold Filtration.completionConeLeg
  rw [Category.assoc, Category.assoc]
  rw [fil.truncationTransition_comp
    (show s₀ + 1 ≤ hbb.lo k + ↑(s₀ + 1 - hbb.lo k).toNat by omega)
    (show hbb.lo k + ↑(s₀ + 1 - hbb.lo k).toNat ≤
      hbb.lo k + ↑(s₀ + 1 - hbb.lo k).toNat + 1 by omega)]
  rw [← fil.completionψ_naturality hbb k
    (show s₀ ≤ hbb.lo k + ↑(s₀ + 1 - hbb.lo k).toNat by omega)]
  rw [← Category.assoc, hcompat _ _
    (show s₀ ≤ hbb.lo k + ↑(s₀ + 1 - hbb.lo k).toNat by omega)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 32000000 in
lemma Filtration.completionLift_unique {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (T : C)
    (f : ∀ s₀ : ℤ, T ⟶ (fil.completionFiltration hbb).truncatedObj s₀ k)
    (hcompat : ∀ (s₀ s₁ : ℤ) (h : s₀ ≤ s₁),
      f s₁ ≫ (fil.completionFiltration hbb).truncationTransition h k = f s₀)
    (g' : T ⟶ fil.completion hbb k)
    (hg' : ∀ s₀ : ℤ, g' ≫ (fil.completionFiltration hbb).truncationProj s₀ k = f s₀) :
    g' = fil.completionLift hbb k T f hcompat := by
  apply limit.hom_ext
  intro ⟨n⟩
  simp only [Filtration.completionLift]
  erw [limit.lift_π]
  unfold Filtration.completionConeLeg
  have h_proj_eq_π : fil.completionProj' hbb k (hbb.lo k + ↑n) =
      limit.π (fil.completionFunctor hbb k) (Opposite.op n) := by
    unfold Filtration.completionProj' Filtration.completion Filtration.completionFunctor
    have hlef : n ≤ (hbb.lo k + ↑n - hbb.lo k).toNat := by omega
    have hw := limit.w (fil.completionFunctor hbb k) (homOfLE hlef).op
    exact hw
  rw [← h_proj_eq_π, ← fil.completionProj'_factor hbb k (hbb.lo k + ↑n),
    ← Category.assoc, ← fil.completionψ_factorization hbb k (hbb.lo k + ↑n),
    ← Category.assoc, hg' (hbb.lo k + ↑n), Category.assoc]

/-- The completion is complete with respect to its own filtration. -/
theorem Filtration.completion_isComplete {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) :
    (fil.completionFiltration hbb).IsComplete := by
  intro k T f hcompat
  exact ⟨fil.completionLift hbb k T f (fun s₀ s₁ h => hcompat h),
    fil.completionLift_proj hbb k T f (fun s₀ s₁ h => hcompat h),
    fun g' hg' => fil.completionLift_unique hbb k T f (fun s₀ s₁ h => hcompat h) g' hg'⟩

end KIP126.Core.SpectralSequence
