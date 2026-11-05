module

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Module.ZMod
import Mathlib.CategoryTheory.Limits.Shapes.Products

namespace KIP126.AdamsSynthetic.HModuleDecomposition
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

private theorem zmodTwo_map_eq_smul
    {A V : Type} [AddCommGroup A] [AddCommGroup V] [Module (ZMod 2) V]
    (e : A ≃+ ZMod 2) (f : A →+ V) (b : V)
    (h : f (e.symm 1) = b) (a : A) : f a = e a • b := by
  have htwo : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
  rcases htwo (e a) with ha | ha
  · have hz : a = 0 := e.injective (by simpa using ha)
    simp [hz]
  · have hz : a = e.symm 1 := e.injective (by simpa using ha)
    rw [ha, one_smul, hz, h]

/-- A degreewise basis gives the original additive cofan, including all the
zero components in the other degrees. -/
private noncomputable def gradedBasisCofan_isColimit
    {D : Type} {J : D → Type} (d : D)
    (V : AddCommGrpCat.{0}) [Module (ZMod 2) V]
    (b : Module.Basis (J d) (ZMod 2) V)
    (A : (Σ n, J n) → AddCommGrpCat.{0})
    (e : ∀ j : J d, A ⟨d, j⟩ ≃+ ZMod 2)
    (hz : ∀ j : Σ n, J n, j.1 ≠ d → Subsingleton (A j))
    (ι : ∀ j, A j →+ V)
    (hι : ∀ (j : J d) (x : A ⟨d, j⟩), ι ⟨d, j⟩ x = e j x • b j) :
    IsColimit (Cofan.mk V (fun j => AddCommGrpCat.ofHom (ι j))) := by
  classical
  refine Cofan.IsColimit.mk _ (fun c => AddCommGrpCat.ofHom
    ((Finsupp.liftAddHom (fun j =>
      (c.inj ⟨d, j⟩).hom.comp (e j).symm.toAddMonoidHom)).comp
      b.repr.toAddMonoidHom)) ?_ ?_
  · rintro c ⟨n, j⟩
    apply AddCommGrpCat.ext
    intro x
    by_cases hn : n = d
    · subst n
      change Finsupp.liftAddHom _ (b.repr (ι ⟨d, j⟩ x)) = c.inj ⟨d, j⟩ x
      rw [hι, map_smul, b.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
        Finsupp.liftAddHom_apply_single]
      simp
    · letI := hz ⟨n, j⟩ hn
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
  · intro c m hm
    apply AddCommGrpCat.ext
    intro x
    obtain ⟨v, rfl⟩ := b.repr.symm.surjective x
    change m (b.repr.symm v) = Finsupp.liftAddHom
      (fun j => (c.inj ⟨d, j⟩).hom.comp (e j).symm.toAddMonoidHom)
      (b.repr (b.repr.symm v))
    rw [b.repr.apply_symm_apply]
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [map_add, hv, hw]
    | single j r =>
      rw [b.repr_symm_single, Finsupp.liftAddHom_apply_single]
      change m (r • b j) = c.inj ⟨d, j⟩ ((e j).symm r)
      have h := ConcreteCategory.congr_hom (hm ⟨d, j⟩) ((e j).symm r)
      change m (ι ⟨d, j⟩ ((e j).symm r)) = _ at h
      simpa only [hι, AddEquiv.apply_symm_apply] using h


end KIP126.AdamsSynthetic.HModuleDecomposition
