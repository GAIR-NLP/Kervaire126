module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Suspension.Data
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u

/-- Levelwise bijectivity on based homotopy classes gives bijectivity on
the actual stable quotient. The chosen inverse loops respect stabilization
because the original strict map does. -/
theorem stableEquivalence_of_levelwise_loops {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hinj : ∀ n r (p q : GenLoop (Fin r) (X.level n) (X.level n).point),
      GenLoop.Homotopic
        (⟨(f.level n).comp p.val,fun t ht => (congrArg (f.level n) (p.property t ht)).trans (f.point n)⟩ :
          GenLoop (Fin r) (Y.level n) (Y.level n).point)
        ⟨(f.level n).comp q.val,fun t ht => (congrArg (f.level n) (q.property t ht)).trans (f.point n)⟩ →
      GenLoop.Homotopic p q)
    (hsurj : ∀ n r (p : GenLoop (Fin r) (Y.level n) (Y.level n).point),
      ∃ q : GenLoop (Fin r) (X.level n) (X.level n).point,
        GenLoop.Homotopic
          (⟨(f.level n).comp q.val,fun t ht => (congrArg (f.level n) (q.property t ht)).trans (f.point n)⟩ :
            GenLoop (Fin r) (Y.level n) (Y.level n).point) p) :
    stableEquivalences f := by
  classical
  let F (n r : ℕ) (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
      GenLoop (Fin r) (Y.level n) (Y.level n).point :=
    ⟨(f.level n).comp p.val,fun t ht => (congrArg (f.level n) (p.property t ht)).trans (f.point n)⟩
  choose L hL using hsurj
  have hnext (n r : ℕ) (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
      F (n+1) (r+1) (stabilizeLoop X n r p)=stabilizeLoop Y n r (F n r p) := by
    apply GenLoop.ext
    intro t
    exact f.bond n _ _
  intro d
  let R (a : Representative Y d) : Representative X d :=
    ⟨a.stage,a.dimension,a.degree,L a.stage a.dimension a.loop⟩
  have respects : ∀ a b, StableRelation Y d a b → Quot.mk (StableRelation X d) (R a)=Quot.mk _ (R b) := by
    intro a b hab
    cases hab with
    | homotopy p hp =>
      apply Quot.sound
      apply StableRelation.homotopy (R a)
      apply hinj
      exact (hL a.stage a.dimension a.loop).trans (hp.trans (hL a.stage a.dimension p).symm)
    | stabilization =>
      apply (Quot.sound (StableRelation.stabilization (R a))).trans
      have hh : GenLoop.Homotopic (stabilizeLoop X a.stage a.dimension (L _ _ a.loop))
          (L _ _ (stabilizeLoop Y a.stage a.dimension a.loop)) := by
        apply hinj
        change GenLoop.Homotopic (F _ _ (stabilizeLoop X _ _ (L _ _ a.loop))) _
        rw [hnext]
        exact (stabilizeLoop_homotopic Y _ _ _ _ (hL _ _ a.loop)).trans
          (hL _ _ (stabilizeLoop Y _ _ a.loop)).symm
      exact Quot.sound (StableRelation.homotopy (R a).next _ hh)
  let G : StableHomotopy Y d → StableHomotopy X d := Quot.lift (fun a => Quot.mk _ (R a)) respects
  have hGF : Function.LeftInverse G (stableHomotopyMap f d) := by
    intro a
    refine Quot.inductionOn a ?_
    intro a
    change Quot.mk _ (R (a.map f))=Quot.mk _ a
    have h : GenLoop.Homotopic (L a.stage a.dimension (F _ _ a.loop)) a.loop :=
      hinj _ _ _ _ (hL _ _ (F _ _ a.loop))
    exact Quot.sound (StableRelation.homotopy (R (a.map f)) _ h)
  have hFG : Function.RightInverse G (stableHomotopyMap f d) := by
    intro a
    refine Quot.inductionOn a ?_
    intro a
    change Quot.mk _ ((R a).map f)=Quot.mk _ a
    exact Quot.sound (StableRelation.homotopy ((R a).map f) _ (hL _ _ a.loop))
  exact ⟨hGF.injective,hFG.surjective⟩

end KIP126.AdamsSynthetic.Source.Prespectrum
