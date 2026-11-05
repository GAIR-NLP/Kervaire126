module

public import KIP126.ProofTools.MahowaldLeibniz
public import KIP126.ProofTools.BlueprintTheorems
public import KIP126.Literature.E2Exactness
import all KIP126.ProofTools.MahowaldLeibniz.Filtration
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionClassLabels
import all KIP126.ProofTools.E2Boundary.HomologySES

/-! The actual E₂ connecting operation and its exactness.

The connecting operation is induced by the selected normalized map on the
first λ quotient. The kernel--image equation uses the same normalized
triangle, its signed quotient row, and the selected Adams suspension
comparison. The finite-layer composition theorem has this specified E₂
output and retains the actual HF₂ homology short exact sequence.
-/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Kervaire.Route KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The normalized first-quotient operation is an actual additive map. -/
public def cofiberFirstQuotientBoundaryHom
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ) :
    KIP126.ProofTools.Ambient background T.X (s,t) →+
      KIP126.ProofTools.Ambient background T.Y (s+1,t+1) :=
  KIP126.Literature.Standard.E2Exactness.e2ConnectingHom T hf s t

end
end KIP126.ProofTools.Standard


namespace KIP126.ProofTools.Internal.E2Boundary
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The tower comparison uniquely determines classical desuspension. -/
private def classicalDesuspensionHom (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ) :
    KIP126.ProofTools.Ambient background (.shift 1 X) (s,t) →+
      KIP126.ProofTools.Ambient background X (s,t-1) where
  toFun sx := Classical.choose (exists_desuspendsClass X s t sx)
  map_zero' := (desuspendsClass_eq_zero_iff X s t 0 _
    (Classical.choose_spec (exists_desuspendsClass X s t 0))).mp rfl
  map_add' sx sy := by
    exact (desuspendsClass_eq_iff X s t (sx+sy) (sx+sy) _ _
      (Classical.choose_spec (exists_desuspendsClass X s t (sx+sy)))
      (suspension_desuspends_add X s t sx sy _ _
        (Classical.choose_spec (exists_desuspendsClass X s t sx))
        (Classical.choose_spec (exists_desuspendsClass X s t sy)))).mp rfl

private theorem classicalDesuspensionHom_spec (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (sx : KIP126.ProofTools.Ambient background (.shift 1 X) (s,t)) :
    (background.classicalSuspension X).DesuspendsClass s t sx
      (classicalDesuspensionHom X s t sx) :=
  Classical.choose_spec (exists_desuspendsClass X s t sx)

/-- The ordinary h₂ map followed by actual classical desuspension. -/
private def classicalTriangleHMapHom
    (T : TriangleData background.auxiliary) (s t : ℤ) :
    KIP126.ProofTools.Ambient background T.Z (s,t) →+
      KIP126.ProofTools.Ambient background T.X (s,t-1) where
  toFun z := classicalDesuspensionHom T.X s t
    ((background.classical.map T.h).pageMap 2 (s,t) z)
  map_zero' := by rw [map_zero, map_zero]
  map_add' a b := by rw [map_add, map_add]

private theorem classicalTriangleHMapHom_spec
    (T : TriangleData background.auxiliary) (s t : ℤ)
    (z : KIP126.ProofTools.Ambient background T.Z (s,t)) :
    (background.classicalSuspension T.X).DesuspendsClass s t
      ((background.classical.map T.h).pageMap 2 (s,t) z)
      (classicalTriangleHMapHom T s t z) :=
  classicalDesuspensionHom_spec T.X s t _

end
end KIP126.ProofTools.Internal.E2Boundary


namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Kervaire.Route
noncomputable section

/-- The actual ordinary E₂ map of h followed by desuspension in the
selected classical Adams tower. -/
@[no_expose] public def classicalTriangleHMapHom
    (T : TriangleData background.auxiliary) (s t : ℤ) :
    Ambient background T.Z (s,t+1) →+ Ambient background T.X (s,t) := by
  exact (congrArg (fun u : ℤ => Ambient background T.Z (s,t+1) →+
      Ambient background T.X (s,u)) (show t+1-1=t by omega)).mp
    (Internal.E2Boundary.classicalTriangleHMapHom T s (t+1))

/-- Representative-level interpretation of the additive desuspension comparison. -/
private theorem classicalTriangleHMapHom_spec
    (T : TriangleData background.auxiliary) (s t : ℤ)
    (z : Ambient background T.Z (s,t+1)) :
    (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) z)
      (by simpa only [show t+1-1=t by omega] using classicalTriangleHMapHom T s t z) := by
  have undo (n n' : ℤ) (hn : n=n')
      (f : Ambient background T.Z (s,t+1) →+ Ambient background T.X (s,n)) :
      (congrArg (fun u : ℤ => (Ambient background T.X (s,u) : Type)) hn).mpr
        (((congrArg (fun u : ℤ => Ambient background T.Z (s,t+1) →+
          Ambient background T.X (s,u)) hn).mp f) z)=f z := by
    subst n'; rfl
  change (background.classicalSuspension T.X).DesuspendsClass s (t+1)
    ((background.classical.map T.h).pageMap 2 (s,t+1) z)
    ((congrArg (fun u : ℤ => (Ambient background T.X (s,u) : Type))
      (show t+1-1=t by omega)).mpr
      (((congrArg (fun u : ℤ => Ambient background T.Z (s,t+1) →+
        Ambient background T.X (s,u)) (show t+1-1=t by omega)).mp
        (Internal.E2Boundary.classicalTriangleHMapHom T s (t+1))) z))
  rw [undo (t+1-1) t (by omega)]
  exact Internal.E2Boundary.classicalTriangleHMapHom_spec T s (t+1) z

end
end KIP126.ProofTools.Standard

namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.E2Boundary
noncomputable section

/-- The E₂ kernel--image equation for the normalized quotient
operation induced by the compatible normalized triangle. -/
private theorem cofiberFirstQuotientBoundary_exact
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (s t : ℤ) :
    (cofiberFirstQuotientBoundaryHom T hf s t).ker=
      (classicalTriangleHMapHom T s t).range := by
  ext x
  change cofiberFirstQuotientBoundary T hf s t x=0 ↔
    ∃ z, classicalTriangleHMapHom T s t z=x
  refine (KIP126.Literature.Standard.E2Exactness.e2ExactAtX
    T hf hg hh s t x).trans ?_
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z, ?_⟩
    have cast_eq (n n' : ℤ) (hn : n=n')
        (a b : Ambient background T.X (s,n')) :
        (congrArg (fun u : ℤ => (Ambient background T.X (s,u) : Type)) hn).mpr a =
          (congrArg (fun u : ℤ => (Ambient background T.X (s,u) : Type)) hn).mpr b ↔
          a=b := by
      subst n'; rfl
    apply (cast_eq (t+1-1) t (by omega) _ _).mp
    exact (desuspendsClass_eq_iff T.X s (t+1) _ _ _ _
      (classicalTriangleHMapHom_spec T s t z) hz).mp rfl
  · rintro ⟨z,rfl⟩
    exact ⟨z,classicalTriangleHMapHom_spec T s t z⟩

/-- Exactness at the source of the specified E₂ connecting operation.
Its kernel is the image of the h page map followed by the selected
Adams desuspension. The operation has bidegree (1,1). -/
public theorem cofiberE2Boundary_exact
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t : ℤ) (x : Ambient background T.X (s,t)) :
    cofiberFirstQuotientBoundary T hf s t x=0 ↔
      ∃ z : Ambient background T.Z (s,t+1),
        (background.classicalSuspension T.X).DesuspendsClass s (t+1)
          ((background.classical.map T.h).pageMap 2 (s,t+1) z)
          (by simpa only [show t+1-1=t by omega] using x) := by
  exact KIP126.Literature.Standard.E2Exactness.e2ExactAtX T hf hg hh s t x

/-- Finite-layer-surjectivity composition using the E₂ connecting operation
of the normalized triangle. Positive Adams filtration supplies its HF₂
homology short exact sequence. The finite-layer, cycle, differential,
and triangle-compatibility inputs are those of the composition theorem. -/
public theorem finiteLayerSurjectivityMahowaldLeibnizE2
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (R K : ℕ) (hR : 2 ≤ R) (hK : 2 ≤ K) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (z : Ambient background T.Z (s+R,t+R))
    (v : Ambient background T.Y (s+R+K,t+R+K-1))
    (hx : IsCycle background T.X ((R:ℤ)-1) _ x)
    (hz : IsCycle background T.Z ((K:ℤ)-1) _ z)
    (hdx : ∃ u : Ambient background T.X (s+R,t+R-1),
      (background.classicalSuspension T.X).DesuspendsClass (s+R) (t+R)
        ((background.classical.functor.map T.h).pageMap 2 (s+R,t+R) z) u ∧
      DifferentialAt background T.X R (s,t) (s+R,t+R-1) x u)
    (hdz : DifferentialAt background T.Z K (s+R,t+R) (s+R+K,t+R+K-1) z
      ((background.classical.functor.map T.g).pageMap 2 (s+R+K,t+R+K-1) v))
    (hsurj : MahowaldLeibnizFiniteLayerSurjectivity T R K s t) :
    HomologyShortExact coefficients
        (CategoryTheory.Pretriangulated.Triangle.mk T.f T.g T.h).rotate ∧
      let y := cofiberFirstQuotientBoundary T hf s t x
      IsCycle background T.Y ((R:ℤ)+K-2) (s+1,t+1) y ∧
      DifferentialAt background T.Y ((R:ℤ)+K-1)
        (s+1,t+1) (s+R+K,t+R+K-1) y v := by
  exact ⟨HomologySES.positive_normalized_rotated_homology_short_exact T hf,
    finiteLayerSurjectivityMahowaldLeibniz T hf hg hh
      R K hR hK s t x z v hx hz hdx hdz hsurj⟩

end
end KIP126.ProofTools.Standard
