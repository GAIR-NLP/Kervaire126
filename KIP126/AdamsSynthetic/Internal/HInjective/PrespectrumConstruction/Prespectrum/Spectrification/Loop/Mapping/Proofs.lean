module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Spectrification.Loop.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Replacement.Cubical.Mapping.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- After precomposition from the free-cell replacement, the loop replacement
preserves strict homotopy by lifting through the replaced constant-path map. -/
theorem loopSpectrification_pathHomotopic_precomp (A : Prespectrum.{u})
    {X Y : Prespectrum.{u}} [∀ n,T1Space (X.level n)] [∀ n,T1Space (Y.level n)]
    {f g : X ⟶ Y} (h : pathHomotopic f g)
    (a : cubicalReplacementFunctor.obj A ⟶ loopSpectrificationFunctor.obj X) :
    pathHomotopic (a ≫ loopSpectrificationFunctor.map f)
      (a ≫ loopSpectrificationFunctor.map g) := by
  obtain ⟨H⟩ := h
  letI (n : ℕ) : T1Space ((pathPrespectrum Y).level n) :=
    inferInstanceAs (T1Space C(unitInterval,Y.level n))
  obtain ⟨c,hc⟩ := cubicalReplacement_exists_pathHomotopic_lift A
    (loopSpectrificationFunctor.map (pathConstant Y))
    (fun n p r => loopSpectrificationFunctor_map_homotopy_bijective
      (pathConstant Y) (pathConstant_stableEquivalence Y) n r p)
    (a ≫ loopSpectrificationFunctor.map H.hom)
  have h0 := pathHomotopic_postcomp hc (loopSpectrificationFunctor.map (pathEvaluation Y 0))
  have h1 := pathHomotopic_postcomp hc (loopSpectrificationFunctor.map (pathEvaluation Y 1))
  have hs (s) : c ≫ loopSpectrificationFunctor.map (pathConstant Y) ≫
      loopSpectrificationFunctor.map (pathEvaluation Y s) = c := by
    rw [← Functor.map_comp,pathConstant_comp_evaluation,CategoryTheory.Functor.map_id,Category.comp_id]
  have hx : a ≫ loopSpectrificationFunctor.map H.hom ≫
      loopSpectrificationFunctor.map (pathEvaluation Y 0) = a ≫ loopSpectrificationFunctor.map f := by
    rw [← Functor.map_comp,H.zero]
  have hy : a ≫ loopSpectrificationFunctor.map H.hom ≫
      loopSpectrificationFunctor.map (pathEvaluation Y 1) = a ≫ loopSpectrificationFunctor.map g := by
    rw [← Functor.map_comp,H.one]
  simp only [Category.assoc,hs,hx,hy] at h0 h1
  exact pathHomotopic_trans (pathHomotopic_symm h0) h1

end KIP126.AdamsSynthetic.Source.Prespectrum
