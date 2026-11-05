module

import all KIP126.SpectralSequence.Completion.Comparison.Data

@[expose] section

/-!
# Comparison proofs for the completed filtration
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasLimitsOfShape ℕᵒᵖ C]


lemma Filtration.completionProj'_general {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω)
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) :
    fil.completionProj' hbb k s₁ ≫ fil.truncationTransition h k =
    fil.completionProj' hbb k s₀ := by
  simp only [Filtration.completionProj', Filtration.completion,
    Filtration.completionFunctor]
  rw [Category.assoc, fil.truncationTransition_comp]
  have hw := limit.w (fil.completionFunctor hbb k)
    (homOfLE (show (s₀ - hbb.lo k).toNat ≤ (s₁ - hbb.lo k).toNat by omega)).op
  erw [← hw, Category.assoc, fil.truncationTransition_comp]
  all_goals simp only [Opposite.unop_op]
  · rfl
  · omega


lemma Filtration.completionψ_factorization {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (s₀ : ℤ) :
    (fil.completionFiltration hbb).truncationProj s₀ k ≫ fil.completionψ hbb k s₀ =
    fil.completionProj' hbb k (s₀ + 1) :=
  cokernel.π_desc _ _ _

noncomputable instance Filtration.completionψ_mono {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (s₀ : ℤ) :
    Mono (fil.completionψ hbb k s₀) := by
  have harr := (kernelSubobject_arrow (fil.completionProj' hbb k (s₀ + 1))).symm
  have key : fil.completionψ hbb k s₀ =
    (cokernelIsoOfEq harr).hom ≫
    (cokernelEpiComp (kernelSubobjectIso (fil.completionProj' hbb k (s₀ + 1))).hom
      (kernel.ι (fil.completionProj' hbb k (s₀ + 1)))).hom ≫
    (Abelian.coimageIsoImage' (fil.completionProj' hbb k (s₀ + 1))).hom ≫
    image.ι (fil.completionProj' hbb k (s₀ + 1)) := by
    apply (cancel_epi (cokernel.π
      ((kernelSubobject (fil.completionProj' hbb k (s₀ + 1))).arrow))).mp
    rw [Filtration.completionψ, cokernel.π_desc,
      π_comp_cokernelIsoOfEq_hom_assoc, cokernelEpiComp_hom, cokernel.π_desc_assoc,
      Abelian.coimageIsoImage'_hom, cokernel.π_desc_assoc, image.fac]
  rw [key]
  have : IsIso ((cokernelIsoOfEq harr).hom ≫
    (cokernelEpiComp (kernelSubobjectIso (fil.completionProj' hbb k (s₀ + 1))).hom
      (kernel.ι (fil.completionProj' hbb k (s₀ + 1)))).hom ≫
    (Abelian.coimageIsoImage' (fil.completionProj' hbb k (s₀ + 1))).hom) := by
    apply IsIso.comp_isIso
  exact mono_comp _ _

lemma Filtration.completionψ_naturality {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω)
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) :
    (fil.completionFiltration hbb).truncationTransition h k ≫ fil.completionψ hbb k s₀ =
    fil.completionψ hbb k s₁ ≫ fil.truncationTransition (show s₀ + 1 ≤ s₁ + 1 by omega) k := by
  haveI : Epi ((fil.completionFiltration hbb).truncationProj s₁ k) := by
    show Epi (cokernel.π _); infer_instance
  apply (cancel_epi ((fil.completionFiltration hbb).truncationProj s₁ k)).mp
  rw [← Category.assoc,
    (fil.completionFiltration hbb).truncationProj_transition h k,
    fil.completionψ_factorization,
    ← Category.assoc, fil.completionψ_factorization,
    fil.completionProj'_general hbb k (show s₀ + 1 ≤ s₁ + 1 by omega)]

set_option maxHeartbeats 8000000 in
lemma Filtration.completionConeLeg_naturality {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (T : C)
    (f : ∀ s₀ : ℤ, T ⟶ (fil.completionFiltration hbb).truncatedObj s₀ k)
    (hcompat : ∀ (s₀ s₁ : ℤ) (h : s₀ ≤ s₁),
      f s₁ ≫ (fil.completionFiltration hbb).truncationTransition h k = f s₀)
    (m n : ℕᵒᵖ) (φ : m ⟶ n) :
    fil.completionConeLeg hbb k T f n =
    fil.completionConeLeg hbb k T f m ≫ (fil.completionFunctor hbb k).map φ := by
  have hle : n.unop ≤ m.unop := leOfHom φ.unop
  unfold Filtration.completionConeLeg
  dsimp only [Filtration.completionFunctor]
  rw [Category.assoc, Category.assoc]
  conv_rhs => rw [fil.truncationTransition_comp
    (show hbb.lo k + ↑n.unop ≤ hbb.lo k + ↑m.unop by omega)
    (show hbb.lo k + ↑m.unop ≤ hbb.lo k + ↑m.unop + 1 by omega)]
  conv_rhs => rw [← fil.truncationTransition_comp
    (show hbb.lo k + ↑n.unop ≤ hbb.lo k + ↑n.unop + 1 by omega)
    (show hbb.lo k + ↑n.unop + 1 ≤ hbb.lo k + ↑m.unop + 1 by omega)]
  rw [← Category.assoc (fil.completionψ hbb k _)]
  rw [← fil.completionψ_naturality hbb k
    (show hbb.lo k + ↑n.unop ≤ hbb.lo k + ↑m.unop by omega)]
  have hc := hcompat _ _ (show hbb.lo k + ↑n.unop ≤ hbb.lo k + ↑m.unop by omega)
  slice_rhs 1 2 => rw [hc]
  simp only [Category.assoc]

end KIP126.Core.SpectralSequence
