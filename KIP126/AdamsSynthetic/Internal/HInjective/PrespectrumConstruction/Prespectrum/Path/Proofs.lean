module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.Prespectrum.Path.Data
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.FiniteSupport.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory _root_.Topology
open scoped unitInterval
universe u

@[simp] theorem pathConstant_comp_evaluation (X : Prespectrum.{u}) (s : I) :
    pathConstant X ≫ pathEvaluation X s = 𝟙 X := rfl

/-- Contracting the path parameter gives actual based cubical homotopies,
so constant paths induce bijections of every stable homotopy set. -/
theorem pathConstant_stableEquivalence (X : Prespectrum.{u}) :
    stableEquivalences (pathConstant X) := by
  intro d
  have hl (x : StableHomotopy X d) :
      stableHomotopyMap (pathEvaluation X 0) d (stableHomotopyMap (pathConstant X) d x) = x := by
    induction x using Quot.inductionOn with
    | h a => rfl
  have hr (x : StableHomotopy (pathPrespectrum X) d) :
      stableHomotopyMap (pathConstant X) d (stableHomotopyMap (pathEvaluation X 0) d x) = x := by
    induction x using Quot.inductionOn with
    | h a =>
      let p : GenLoop (Fin a.dimension) C(I,X.level a.stage) (ContinuousMap.const _ (X.level a.stage).point) := a.loop
      have H : GenLoop.Homotopic ((a.map (pathEvaluation X 0)).map (pathConstant X)).loop a.loop := by
        refine ⟨{
          toFun := fun z => ⟨fun t => p z.2 (z.1 * t),
            (p z.2).continuous.comp
              (((continuous_const : Continuous (fun _ : I => (z.1 : ℝ))).mul continuous_subtype_val).subtype_mk _)⟩
          continuous_toFun := ?_
          map_zero_left := ?_
          map_one_left := ?_
          prop' := ?_ }⟩
        · apply ContinuousMap.continuous_of_continuous_uncurry
          change Continuous (fun z : (I × (Fin a.dimension → I)) × I =>
            p z.1.2 (z.1.1 * z.2))
          exact (p.val.continuous.comp continuous_fst.snd).eval
            ((continuous_fst.fst.subtype_val.mul continuous_snd.subtype_val).subtype_mk _)
        · intro t
          apply ContinuousMap.ext
          intro s
          simp only [zero_mul]
          rfl
        · intro t
          apply ContinuousMap.ext
          intro s
          simp only [one_mul]
          rfl
        · intro s t ht
          apply ContinuousMap.ext
          intro v
          have hp := p.property t ht
          exact (congrArg (fun p : C(I,X.level a.stage) => p (s * v)) hp).trans
            (congrArg (fun p : C(I,X.level a.stage) => p 0) hp).symm
      change Quot.mk _ ((a.map (pathEvaluation X 0)).map (pathConstant X)) = Quot.mk _ a
      have he : { ((a.map (pathEvaluation X 0)).map (pathConstant X)) with loop := a.loop } = a := by
        cases a
        rfl
      have hs := Quot.sound (StableRelation.homotopy
        ((a.map (pathEvaluation X 0)).map (pathConstant X)) a.loop H)
      simpa only [he] using hs
  exact ⟨fun x y h => (hl x).symm.trans ((congrArg (stableHomotopyMap (pathEvaluation X 0) d) h).trans (hl y)),
    fun x => ⟨stableHomotopyMap (pathEvaluation X 0) d x,hr x⟩⟩

/-- All path evaluations agree after the actual stable localization. -/
theorem source_pathEvaluation_eq (X : Prespectrum.{u}) (s t : I) :
    sourceLocalization.map (pathEvaluation X s) = sourceLocalization.map (pathEvaluation X t) := by
  haveI : IsIso (sourceLocalization.map (pathConstant X)) :=
    stableEquivalences.Q_inverts _ (pathConstant_stableEquivalence X)
  apply (cancel_epi (sourceLocalization.map (pathConstant X))).mp
  rw [← Functor.map_comp, ← Functor.map_comp, pathConstant_comp_evaluation, pathConstant_comp_evaluation]

end KIP126.AdamsSynthetic.Source.Prespectrum
