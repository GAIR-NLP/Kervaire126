module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.FiniteSupport.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory _root_.Topology
open scoped unitInterval

universe u

namespace BasedSpace

end BasedSpace

namespace Prespectrum

/-- At its generating stage the actual free prespectrum is its input space. -/
theorem free_level (n : ℕ) (A : BasedSpace.{u}) : (free n A).level n = A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((desuspension^[n+1]) (suspensionSpectrum A)).level (n+1) = A
    rw [Function.iterate_succ_apply']
    exact ih

/-- The chosen free/evaluation equivalence is natural for actual
prespectrum maps, as follows from its specified level formula. -/
theorem freeEvaluation_natural (n : ℕ) (A : BasedSpace.{u})
    {X Y : Prespectrum.{u}} (f : free n A ⟶ X) (g : X ⟶ Y) :
    freeEvaluation n A Y (f ≫ g) =
      freeEvaluation n A X f ≫ (⟨g.level n,g.point n⟩ : X.level n ⟶ Y.level n) := by
  apply BasedSpace.Hom.ext
  apply eq_of_heq
  have hf := (freeEvaluation_exists n A X).choose_spec f
  have hfg := (freeEvaluation_exists n A Y).choose_spec (f ≫ g)
  apply hfg.trans
  have hc {B : BasedSpace.{u}} (hB : B = A) (a : C(B,X.level n))
      (b : C(A,X.level n)) (hab : HEq a b) :
      HEq ((g.level n).comp a) ((g.level n).comp b) := by
    subst B
    rw [eq_of_heq hab]
  exact hc (free_level n A) (f.level n) (freeEvaluation n A X f).map hf.symm

/-- The actual induced free map has the expected evaluation formula after
composition with any actual prespectrum map. -/
theorem freeEvaluation_freeMap_comp (n : ℕ) {A B : BasedSpace.{u}}
    (f : A ⟶ B) {X : Prespectrum.{u}} (g : free n B ⟶ X) :
    freeEvaluation n A X (freeMap n f ≫ g) = f ≫ freeEvaluation n B X g := by
  rw [freeEvaluation_natural]
  simp only [freeMap, Equiv.apply_symm_apply, Category.assoc]
  have h := freeEvaluation_natural n B (𝟙 (free n B)) g
  rw [Category.id_comp] at h
  rw [← h]

end Prespectrum

end KIP126.AdamsSynthetic.Source
