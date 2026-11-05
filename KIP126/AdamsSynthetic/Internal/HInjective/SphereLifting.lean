module

import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.FiniteSupport.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Zero.Proofs
import all KIP126.AdamsSynthetic.Internal.Topology.HomotopyLifting.Cube.Boundary.Predicates
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-! Direct lifting for the same actual sphere. The only selected point is a preimage of the degree-zero
non-basepoint; free evaluation extends it strictly. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory KIP126.Topology.HomotopyLifting
open scoped unitInterval

universe u
set_option backward.isDefEq.respectTransparency false

/-- The empty zero-dimensional cube boundary detects pointwise surjectivity. -/
private theorem level_surjective_of_cubeBoundaryLifting
    {E B : Prespectrum.{u}} (p : E ⟶ B)
    (hp : ∀ n, HasCubeBoundaryLifting (p.level n)) (n : ℕ) :
    Function.Surjective (p.level n) := by
  intro b
  obtain ⟨L, hL, _⟩ :=
    hp n 0
      (ContinuousMap.const _ (E.level n).point)
      (ContinuousMap.const _ b)
      (by
        intro z
        rcases z.property with ⟨i, hi⟩
        exact Fin.elim0 i)
  exact ⟨L (fun i : Fin 0 => Fin.elim0 i), hL _⟩

/-- Suspension of the actual level-zero two-point space is the fixed sphere. -/
private theorem suspensionSpectrum_sphereLevel_zero :
    suspensionSpectrum (sphereLevel 0) = sphere := by
  have h : BasedSpace.iterateSuspension (sphereLevel 0) = sphereLevel := by
    funext n
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg BasedSpace.suspension ih
  have ext (X Y : Prespectrum.{0}) (hlevel : X.level = Y.level)
      (hbond : ∀ n, HEq (X.bond n) (Y.bond n)) : X = Y := by
    cases X
    cases Y
    cases hlevel
    have hb := funext fun n => eq_of_heq (hbond n)
    cases hb
    rfl
  apply ext _ _ h
  intro n
  have hp (A B : BasedSpace.{0}) (hab : A = B) :
      HEq A.suspensionProjection B.suspensionProjection := by
    cases hab
    rfl
  exact hp _ _ (congrFun h n)

/-- A strict sphere map lifts as soon as the original degree-zero level map
is surjective. The specified sphere and its actual bonds are retained. -/
private theorem sphere_lift_of_level_zero_surjective
    {E B : Prespectrum.{0}} (p : E ⟶ B)
    (hp : Function.Surjective (p.level 0)) (f : sphere ⟶ B) :
    ∃ g : sphere ⟶ E, g ≫ p = f := by
  classical
  let e : free 0 (sphereLevel 0) ≅ sphere :=
    eqToIso suspensionSpectrum_sphereLevel_zero
  let f' : free 0 (sphereLevel 0) ⟶ B := e.hom ≫ f
  let a : sphereLevel 0 ⟶ B.level 0 := freeEvaluation 0 (sphereLevel 0) B f'
  obtain ⟨x, hx⟩ := hp (a.map (1 : Fin 2))
  letI : DiscreteTopology (sphereLevel 0) :=
    inferInstanceAs (DiscreteTopology (Fin 2))
  let a' : sphereLevel 0 ⟶ E.level 0 :=
    { map := ⟨fun i : Fin 2 => if i = 0 then (E.level 0).point else x,
        continuous_of_discreteTopology⟩
      point := by
        change (if (0 : Fin 2) = 0 then (E.level 0).point else x) = _
        rw [if_pos rfl] }
  have ha : a' ≫ (⟨p.level 0, p.point 0⟩ : E.level 0 ⟶ B.level 0) = a := by
    apply BasedSpace.Hom.ext
    apply ContinuousMap.ext
    intro i
    change Fin 2 at i
    fin_cases i
    · change p.level 0 (if (0 : Fin 2) = 0 then (E.level 0).point else x) = a.map (0 : Fin 2)
      rw [if_pos rfl, p.point]
      exact a.point.symm
    · change p.level 0 (if (1 : Fin 2) = 0 then (E.level 0).point else x) = a.map (1 : Fin 2)
      simpa using hx
  let g' : free 0 (sphereLevel 0) ⟶ E :=
    (freeEvaluation 0 (sphereLevel 0) E).symm a'
  have hg : g' ≫ p = f' := by
    apply (freeEvaluation 0 (sphereLevel 0) B).injective
    rw [freeEvaluation_natural]
    change freeEvaluation 0 (sphereLevel 0) E
      ((freeEvaluation 0 (sphereLevel 0) E).symm a') ≫ _ = a
    rw [Equiv.apply_symm_apply]
    exact ha
  refine ⟨e.inv ≫ g', ?_⟩
  rw [Category.assoc, hg]
  change e.inv ≫ (e.hom ≫ f) = f
  simp only [Iso.inv_hom_id_assoc]

/-- Every strict sphere map lifts through a map with actual full cube-boundary
lifting at every original level. -/
private theorem sphere_lift_of_level_cubeBoundary
    {E B : Prespectrum.{0}} (p : E ⟶ B)
    (hp : ∀ n, HasCubeBoundaryLifting (p.level n)) (f : sphere ⟶ B) :
    ∃ g : sphere ⟶ E, g ≫ p = f :=
  sphere_lift_of_level_zero_surjective p
    (level_surjective_of_cubeBoundaryLifting p hp 0) f

/-- The actual initial sphere inclusion has the full required lifting property. -/
private theorem sphere_initial_hasLiftingProperty_of_level
    {E B : Prespectrum.{0}} (p : E ⟶ B)
    (hp : ∀ n, HasCubeBoundaryLifting (p.level n)) :
    HasLiftingProperty (zeroMap zeroPrespectrum sphere) p := by
  constructor
  intro a f sq
  obtain ⟨g, hg⟩ := sphere_lift_of_level_cubeBoundary p hp f
  exact CommSq.HasLift.mk'
    { l := g
      fac_left := zeroPrespectrum_isZero.eq_of_src _ _
      fac_right := hg }


end KIP126.AdamsSynthetic.Source.Prespectrum
end
