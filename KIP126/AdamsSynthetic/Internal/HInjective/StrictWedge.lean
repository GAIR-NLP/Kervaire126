module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.HInjective.WedgeFiniteSupport
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! Explicit strict wedges and finite support for the selected prespectra.
The construction uses the existing based levels, bonds, and cubical quotient. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Source
open CategoryTheory CategoryTheory.Limits Topology CompactWedge
open scoped unitInterval
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Prespectrum
variable {J : Type u} (X : J → Prespectrum.{u})

private def strictWedgeLevel (n : ℕ) : BasedSpace.{u} where
  space := TopCat.of (Wedge (fun j => (X j).level n) (fun j => ((X j).level n).point))
  point := wedgePoint _ _

private def strictWedgeBond (n : ℕ) :
    C(strictWedgeLevel X n × I, strictWedgeLevel X (n+1)) :=
  (wedgeDesc (fun j => (X j).level n) (fun j => ((X j).level n).point)
    (ContinuousMap.const I (wedgePoint _ _))
    (fun j => ((wedgeInclusion _ _ j).comp ((X j).bond n)).curry)
    (fun j => by
      apply ContinuousMap.ext
      intro t
      change wedgeInclusion (fun k => (X k).level (n+1)) (fun k => ((X k).level (n+1)).point) j ((X j).bond n (((X j).level n).point,t)) = _
      rw [(X j).bond_point, wedgeInclusion_point]
      rfl)).uncurry

private theorem strictWedgeBond_point (n : ℕ) (t : I) :
    strictWedgeBond X n ((strictWedgeLevel X n).point,t) =
      (strictWedgeLevel X (n+1)).point := rfl

private theorem strictWedgeBond_inclusion (n : ℕ) (j : J)
    (x : (X j).level n) (t : I) :
    strictWedgeBond X n (wedgeInclusion _ _ j x,t) =
      wedgeInclusion _ _ j ((X j).bond n (x,t)) := rfl

private theorem strictWedgeBond_zero (n : ℕ) (x : strictWedgeLevel X n) :
    strictWedgeBond X n (x,0) = (strictWedgeLevel X (n+1)).point := by
  refine Quotient.inductionOn x ?_
  rintro (⟨j,x⟩ | ⟨⟩)
  · change wedgeInclusion (fun k => (X k).level (n+1)) (fun k => ((X k).level (n+1)).point) j ((X j).bond n (x,0)) = _
    rw [(X j).bond_zero, wedgeInclusion_point]
    rfl
  · rfl

private theorem strictWedgeBond_one (n : ℕ) (x : strictWedgeLevel X n) :
    strictWedgeBond X n (x,1) = (strictWedgeLevel X (n+1)).point := by
  refine Quotient.inductionOn x ?_
  rintro (⟨j,x⟩ | ⟨⟩)
  · change wedgeInclusion (fun k => (X k).level (n+1)) (fun k => ((X k).level (n+1)).point) j ((X j).bond n (x,1)) = _
    rw [(X j).bond_one, wedgeInclusion_point]
    rfl
  · rfl

private def strictWedge : Prespectrum.{u} where
  level := strictWedgeLevel X
  bond := strictWedgeBond X
  bond_point := strictWedgeBond_point X
  bond_zero := strictWedgeBond_zero X
  bond_one := strictWedgeBond_one X

private def strictWedgeι (j : J) : X j ⟶ strictWedge X where
  level n := wedgeInclusion (fun k => (X k).level n) (fun k => ((X k).level n).point) j
  point _ := wedgeInclusion_point j
  bond n x t := (strictWedgeBond_inclusion X n j x t).symm

private def strictWedgeDesc {Y : Prespectrum.{u}} (f : ∀ j, X j ⟶ Y) :
    strictWedge X ⟶ Y where
  level n := wedgeDesc _ _ (Y.level n).point (fun j => (f j).level n)
    (fun j => (f j).point n)
  point _ := rfl
  bond n x t := by
    refine Quotient.inductionOn x ?_
    rintro (⟨j,x⟩ | ⟨⟩)
    · exact (f j).bond n x t
    · exact (Y.bond_point n t).symm

private theorem strictWedgeι_desc {Y : Prespectrum.{u}}
    (f : ∀ j, X j ⟶ Y) (j : J) :
    strictWedgeι X j ≫ strictWedgeDesc X f = f j := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  rfl

private theorem strictWedge_hom_ext {Y : Prespectrum.{u}}
    (f g : strictWedge X ⟶ Y)
    (h : ∀ j, strictWedgeι X j ≫ f = strictWedgeι X j ≫ g) : f = g := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  refine Quotient.inductionOn x ?_
  rintro (⟨j,x⟩ | ⟨⟩)
  · exact congrArg (fun a : X j ⟶ Y => a.level n x) (h j)
  · exact (f.point n).trans (g.point n).symm

/-- This is the actual coproduct of prespectra, before localization. -/
private def strictWedgeIsColimit :
    IsColimit (Cofan.mk (strictWedge X) (strictWedgeι X)) := by
  refine Cofan.IsColimit.mk _ (fun c => strictWedgeDesc X c.inj) ?_ ?_
  · intro c j
    exact strictWedgeι_desc X c.inj j
  · intro c f hf
    apply strictWedge_hom_ext X
    intro j
    exact (hf j).trans (strictWedgeι_desc X c.inj j).symm

private def strictWedgeSubfamily (s : Set J) :
    strictWedge (fun j : s => X j.val) ⟶ strictWedge X :=
  strictWedgeDesc _ (fun j => strictWedgeι X j.val)

private theorem strictWedgeSubfamily_level (s : Set J) (n : ℕ) :
    (strictWedgeSubfamily X s).level n =
      wedgeSubfamilyInclusion (fun j => (X j).level n)
        (fun j => ((X j).level n).point) s := rfl

private theorem strictWedgeSubfamily_injective (s : Set J) (n : ℕ) :
    Function.Injective ((strictWedgeSubfamily X s).level n) :=
  (wedgeSubfamilyRetraction_leftInverse (X := fun j => (X j).level n)
    (x₀ := fun j => ((X j).level n).point) s).injective

/-- Each class is represented in a finite strict subwedge of exactly the same
    prespectra, by factoring its actual compact cubical representative. -/
private theorem strictWedge_stableHomotopy_finite_support
    [∀ j n, T1Space ((X j).level n)] (d : ℤ)
    (a : StableHomotopy (strictWedge X) d) :
    ∃ (s : Finset J) (b : StableHomotopy (strictWedge (fun j : (s : Set J) => X j.val)) d),
      stableHomotopyMap (strictWedgeSubfamily X (s : Set J)) d b = a := by
  classical
  induction a using Quot.inductionOn with
  | h a =>
    letI (j : J) : T1Space ((X j).level a.stage) := inferInstance
    obtain ⟨s,g,hg⟩ := continuousMap_wedge_factor_finite a.loop.val
    let q := strictWedgeSubfamily X (s : Set J)
    let p : GenLoop (Fin a.dimension) ((strictWedge (fun j : (s : Set J) => X j.val)).level a.stage)
        ((strictWedge (fun j : (s : Set J) => X j.val)).level a.stage).point :=
      ⟨g,by
        intro z hz
        apply strictWedgeSubfamily_injective X (s : Set J) a.stage
        exact (congrArg (fun k => k z) hg).trans
          ((a.loop.property z hz).trans (q.point a.stage).symm)⟩
    refine ⟨s,loopClass _ d a.stage a.dimension a.degree p,?_⟩
    have hp : (⟨(q.level a.stage).comp p.val,by
        intro z hz
        exact (congrArg (q.level a.stage) (p.property z hz)).trans (q.point a.stage)⟩ :
          GenLoop (Fin a.dimension) ((strictWedge X).level a.stage)
            ((strictWedge X).level a.stage).point) = a.loop := by
      apply Subtype.ext
      exact hg
    change Quot.mk _ ⟨a.stage,a.dimension,a.degree,_⟩ = Quot.mk _ a
    rw [hp]

end Prespectrum
end
end KIP126.AdamsSynthetic.Source
end
