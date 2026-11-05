module

public import KIP126.ProofTools.Language

import all KIP126.ProofTools.GeneralizedLeibniz.Reverse
import all KIP126.ProofTools.GeneralizedMahowald.BoundaryDetection
import all KIP126.ProofTools.GeneralizedMahowald.ClassicalLift

/-! Specified-label finite Bockstein comparison in the selected model.
The lift and both of its labels are constructed from the given classical
differential; the reverse implication applies to that same lift.
 -/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/-- The native first-quotient sphere map after removing
the zero-shift comparison. -/
public def nativeFirstLabel (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (x : Ambient background X (s,t)) :
    BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1) :=
  firstLabel background X s t x ≫
    XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1

/-- The first-quotient label of the actual absolute boundary of a finite
lift, in the exact bidegree of its adjacent classical differential. -/
private def adjacentBoundaryLabel (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (s t : ℤ)
    (a : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q)) :
    BiHom ((t+q)-(s+q+1)) (t+q)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1) :=
  boundaryRepresentative X q s t a ≫ XModLambdaN.incl _ 1

/-- The selected adjacent finite-quotient boundary, with its ordinary
suspension and weight shift transported by the fixed comparison. -/
private def adjacentFiniteBoundary (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q)
    (s t : ℤ)
    (a : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q)) :
    BiHom ((t+q)-(s+q+1)) (t+q)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1) := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let δ : XModLambdaN A q ⟶
      ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧ := by
    simpa only [show q+1-q=1 by omega] using
      ((background.quotients.tower A).triangle hq (Nat.lt_succ_self q)).delta
  exact homotopyRegrade (by omega) rfl
    (biSuspensionHomEquiv (t-s) t q (XModLambdaN A 1) (a ≫ δ))

/-- The actual adjacent finite boundary agrees with the projected absolute
boundary on every specified lift; no choice of target label is involved. -/
private theorem adjacentFiniteBoundary_eq (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q)
    (s t : ℤ)
    (a : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q)) :
    adjacentFiniteBoundary X q hq s t a = adjacentBoundaryLabel X q s t a := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  have h := cofiber_boundary_projection X q (q+1) hq (Nat.lt_succ_self q) (t-s) t a
  have transport (n : ℕ) (hn : n=1)
      (δ : XModLambdaN A q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧)
      (he : (XModLambdaN A q ⟶
          ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧) =
        (XModLambdaN A q ⟶
          ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧))
      (hd : biSuspensionHomEquiv (t-s) t q (XModLambdaN A n) (a ≫ δ) =
        biSuspensionHomEquiv (t-s) t q A (a ≫ XModLambdaN.proj A q) ≫
          XModLambdaN.incl A n) :
      biSuspensionHomEquiv (t-s) t q (XModLambdaN A 1) (a ≫ he.mp δ) =
        biSuspensionHomEquiv (t-s) t q A (a ≫ XModLambdaN.proj A q) ≫
          XModLambdaN.incl A 1 := by
    subst n
    exact hd
  have hp := transport (q+1-q) (by omega) _ (by rw [show q+1-q=1 by omega]) h
  have hc := congrArg (homotopyRegrade (show t-s-1=(t+q)-(s+q+1) by omega) rfl) hp
  simpa only [adjacentFiniteBoundary,adjacentBoundaryLabel,boundaryRepresentative,
    regrade_precomp,Category.assoc] using hc

/-- A given classical differential is equivalent to the existence of one
finite lift with the specified source and target labels. The specified target
is retained exactly in Q₁, even when it is an earlier boundary. -/
private theorem differential_iff_specified_adjacent_lift
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background X (s+q+1,t+q)) :
    HasDifferential (background.classical.obj (X.obj background.auxiliary))
        (q+1) (s,t) (s+q+1,t+q) x y ↔
      ∃ a : BiHom (t-s) t
          (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q),
        a ≫ (background.quotients.tower _).rho 1 q hq = nativeFirstLabel X s t x ∧
        adjacentBoundaryLabel X q s t a = nativeFirstLabel X (s+q+1) (t+q) y := by
  constructor
  · intro hd
    obtain ⟨a,ha,hy⟩ := adjacent_absolute_boundary X q hq s t x y hd
    exact ⟨a,ha,hy⟩
  · rintro ⟨a,ha,hy⟩
    exact adjacent_boundary_differential X q hq s t x y a ha hy

/-- The complete adjacent finite-quotient Bockstein comparison, using the
actual finite delta map and both specified Q₁ labels. -/
private theorem differential_iff_specified_finite_lift
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background X (s+q+1,t+q)) :
    HasDifferential (background.classical.obj (X.obj background.auxiliary))
        (q+1) (s,t) (s+q+1,t+q) x y ↔
      ∃ a : BiHom (t-s) t
          (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q),
        a ≫ (background.quotients.tower _).rho 1 q hq = nativeFirstLabel X s t x ∧
        adjacentFiniteBoundary X q hq s t a = nativeFirstLabel X (s+q+1) (t+q) y := by
  simp only [adjacentFiniteBoundary_eq]
  exact differential_iff_specified_adjacent_lift X q hq s t x y

/-- The finite lift supplies the cycle qualification. -/
private theorem specified_adjacent_lift_cycles
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : Ambient background X (s,t))
    (a : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : a ≫ (background.quotients.tower _).rho 1 q hq = nativeFirstLabel X s t x) :
    IsCycle background X q (s,t) x := by
  exact ⟨by omega, first_label_lift_cycles X q hq s t x a ha⟩

/-- At the last finite layer, a representative with the specified label
vanishes precisely when its label belongs to `B_q`. -/
private theorem finite_top_detected_zero_iff_boundary
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (y : Ambient background X (s,t))
    (b : BiHom (t-s) (t-(q-1:ℕ))
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (hb : Detects (background.convergence (.quotient q (.nu X))) (s,t,t-(q-1:ℕ))
      (finiteTargetLabel background X q s t (q-1) y) b) :
    b = 0 ↔ y ∈ boundaries background X q (s,t) := by
  have hycycle : IsCycle background X 1 (s,t) y := by
    exact (isCycle_iff_reaches background X 2 (by decide) (s,t) y).mpr
      ⟨y,represents_two_self y⟩
  let yc : cycles background X ((q:ℤ)-t+(t-(q-1:ℕ))) (s,t) := ⟨y,by
    have hi : (q:ℤ)-t+(t-(q-1:ℕ)) = 1 := by omega
    rw [hi]
    exact hycycle.2⟩
  constructor
  · intro hz
    have hb0 : Detects (background.convergence (.quotient q (.nu X))) (s,t,t-(q-1:ℕ))
        (finiteTargetLabel background X q s t (q-1) y) 0 := by simpa only [hz] using hb
    have he := detected_zero_infinity (.quotient q (.nu X)) (s,t,t-(q-1:ℕ)) _ hb0
    have hw := (finite_target_label_iff X q hq s t (q-1) (by omega) yc 0).mp he
    rw [map_zero] at hw
    have hmem := (CrossingLabels.subquotient_zero_iff _ _ yc).mp hw.symm
    have hi : 1+t-(t-(q-1:ℕ)) = (q:ℤ) := by omega
    simpa only [hi] using hmem
  · intro hy
    exact finite_top_detection_unique X q hq s t (t-(q-1:ℕ)) (by omega)
      _ b 0 hb (finite_top_boundary_detects_zero X q hq s t y hy)

/-- Equality of two specified highest-layer representatives is precisely
congruence of their classical labels modulo B_q. -/
private theorem finite_top_detected_eq_iff_boundary
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (y z : Ambient background X (s,t))
    (b c : BiHom (t-s) (t-(q-1:ℕ))
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (hb : Detects (background.convergence (.quotient q (.nu X))) (s,t,t-(q-1:ℕ))
      (finiteTargetLabel background X q s t (q-1) y) b)
    (hc : Detects (background.convergence (.quotient q (.nu X))) (s,t,t-(q-1:ℕ))
      (finiteTargetLabel background X q s t (q-1) z) c) :
    b = c ↔ y-z ∈ boundaries background X q (s,t) := by
  have hsub := detects_sub (.quotient q (.nu X)) (s,t,t-(q-1:ℕ)) hb hc
  rw [←finiteTargetLabel_sub] at hsub
  exact sub_eq_zero.symm.trans
    (finite_top_detected_zero_iff_boundary X q hq s t (y-z) (b-c) hsub)

/-- The exact terminal boundary comparison preserves the specified output
of an adjacent classical differential. -/
private theorem differential_of_equal_top_representatives
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : Ambient background X (s,t)) (y z : Ambient background X (s+q+1,t+q))
    (hd : HasDifferential (background.classical.obj (X.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) x z)
    (b c : BiHom ((t+q)-(s+q+1)) ((t+q)-(q-1:ℕ))
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (hb : Detects (background.convergence (.quotient q (.nu X)))
      (s+q+1,t+q,(t+q)-(q-1:ℕ))
      (finiteTargetLabel background X q (s+q+1) (t+q) (q-1) y) b)
    (hc : Detects (background.convergence (.quotient q (.nu X)))
      (s+q+1,t+q,(t+q)-(q-1:ℕ))
      (finiteTargetLabel background X q (s+q+1) (t+q) (q-1) z) c)
    (heq : b=c) :
    HasDifferential (background.classical.obj (X.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) x y := by
  have hcong := (finite_top_detected_eq_iff_boundary X q hq
    (s+q+1) (t+q) y z b c hb hc).mp heq
  exact (differentialAt_of_congruent background X
    (⟨by omega,hd⟩ : DifferentialAt background X (q+1) (s,t) (s+q+1,t+q) x z)
    ⟨by omega,by simpa only [add_sub_cancel_right] using hcong⟩).2

/-- In the retained finite window, detection of the projection of an actual
full class reflects to detection of that same full class. Permanence of the
specified label is derived from its actual full lift. -/
private theorem finite_projection_detects_reflect
    (X : AdamsObject (coefficients := background.coefficients)) (N : ℕ) (hN : 0 < N) (s t w : ℤ)
    (hw : 0 ≤ t-w ∧ t-w < N) (y : Ambient background X (s,t))
    (β : BiHom (t-s) w (background.nu.functor.obj (X.obj background.auxiliary)))
    (hfinite : Detects (background.convergence (.quotient N (.nu X))) (s,t,w)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) N).pageMap
        2 (s,t,w) (nuWeightLabel background X s t w (by omega) y))
      (β ≫ XModLambdaN.incl _ N)) :
    Detects (background.convergence (.nu X)) (s,t,w)
      (nuWeightLabel background X s t w (by omega) y) β := by
  have hp := KIP126.ProofTools.finite_target_from_full_lift_is_permanent
    X N hN s t w hw y β hfinite
  have hfull := KIP126.ProofTools.full_projection_reflects_filtration
    X N hN s (t-s) w (by omega) β
    (detects_filtration (.quotient N (.nu X)) (s,t,w) _ _ hfinite)
  let e := (KIP126.Literature.Standard.infinityNuWindow X (s,t) w (by omega)).symm
    (subquotientClass (permanentCycles background X (s,t))
      (boundaries background X (1+t-w) (s,t)) ⟨y,hp⟩)
  have he : HasInfinityRepresentative _ 2 (s,t,w)
      (nuWeightLabel background X s t w (by omega) y) e := by
    apply (KIP126.Literature.Standard.eInfinity_nu_labels X s t w (by omega) y e).mpr
    exact ⟨hp,(KIP126.Literature.Standard.infinityNuWindow X (s,t) w (by omega)).apply_symm_apply _⟩
  exact detects_reflect (.nu X) (.quotient N (.nu X)) (XModLambdaN.incl _ N)
    (s,t,w) (KIP126.ProofTools.Internal.Leibniz.nu_projection_infinity_injective
      X N hN s t w hw) _ e he β hfull hfinite

/-- Finite detection of the absolute boundary gives the specified
classical differential with its finite-window boundary denominator. -/
private theorem finite_boundary_detects_differential
    (X : AdamsObject (coefficients := background.coefficients)) (i k N : ℕ) (hi : 0 < i) (hik : i ≤ k)
    (hN : 0 < N) (hwindow : k-i < N) (s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background X (s+k+1,t+k))
    (a : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) i))
    (ha : a ≫ (background.quotients.tower _).rho 1 i hi = nativeFirstLabel X s t x)
    (hy : Detects (background.convergence (.quotient N (.nu X))) (s+k+1,t+k,t+i)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) N).pageMap
        2 (s+k+1,t+k,t+i)
        (nuWeightLabel background X (s+k+1) (t+k) (t+i) (by omega) y))
      ((homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv (t-s) t i (background.nu.functor.obj (X.obj background.auxiliary))
          (a ≫ XModLambdaN.proj _ i))) ≫ XModLambdaN.incl _ N)) :
    HasDifferential (background.classical.obj (X.obj background.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y := by
  exact boundary_detects_differential X i k hi hik s t x y a ha
    (finite_projection_detects_reflect X N hN (s+k+1) (t+k) (t+i)
      (by omega) y _ hy)


/-- The actual boundary of the finite tower triangle Qi → Q(i+N), in
unsuspended sphere coordinates. -/
private def finiteTowerBoundary (X : AdamsObject (coefficients := background.coefficients)) (i N : ℕ)
    (hi : 0 < i) (hN : 0 < N) (s t : ℤ)
    (a : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) i)) :
    BiHom (t-s-1) (t+i)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N) := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let δ : XModLambdaN A i ⟶
      ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A N))⟦(1:ℤ)⟧ := by
    simpa only [show i+N-i=N by omega] using
      ((background.quotients.tower A).triangle hi (show i < i + N by omega)).delta
  exact biSuspensionHomEquiv (t-s) t i (XModLambdaN A N) (a ≫ δ)

/-- The chosen finite delta equals the actual absolute boundary followed
by the chosen projection to the complementary finite quotient. -/
private theorem finiteTowerBoundary_eq (X : AdamsObject (coefficients := background.coefficients)) (i N : ℕ)
    (hi : 0 < i) (hN : 0 < N) (s t : ℤ)
    (a : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) i)) :
    finiteTowerBoundary X i N hi hN s t a =
      biSuspensionHomEquiv (t-s) t i (background.nu.functor.obj (X.obj background.auxiliary))
        (a ≫ XModLambdaN.proj _ i) ≫ XModLambdaN.incl _ N := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  have h := cofiber_boundary_projection X i (i+N) hi (by omega) (t-s) t a
  have transport (n : ℕ) (hn : n=N)
      (δ : XModLambdaN A i ⟶
        ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧)
      (he : (XModLambdaN A i ⟶
          ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧) =
        (XModLambdaN A i ⟶
          ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A N))⟦(1:ℤ)⟧))
      (hd : biSuspensionHomEquiv (t-s) t i (XModLambdaN A n) (a ≫ δ) =
        biSuspensionHomEquiv (t-s) t i A (a ≫ XModLambdaN.proj A i) ≫
          XModLambdaN.incl A n) :
      biSuspensionHomEquiv (t-s) t i (XModLambdaN A N) (a ≫ he.mp δ) =
        biSuspensionHomEquiv (t-s) t i A (a ≫ XModLambdaN.proj A i) ≫
          XModLambdaN.incl A N := by
    subst n
    exact hd
  exact transport (i+N-i) (by omega) _ (by rw [show i+N-i=N by omega]) h

/-- The finite tower Bockstein detects the classical target exactly when
its projected absolute boundary does; its leading term gives the
classical differential. -/
private theorem finiteTowerBoundary_detects_differential
    (X : AdamsObject (coefficients := background.coefficients)) (i k N : ℕ) (hi : 0 < i) (hik : i ≤ k)
    (hN : 0 < N) (hwindow : k-i < N) (s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background X (s+k+1,t+k))
    (a : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) i))
    (ha : a ≫ (background.quotients.tower _).rho 1 i hi = nativeFirstLabel X s t x)
    (hy : Detects (background.convergence (.quotient N (.nu X))) (s+k+1,t+k,t+i)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) N).pageMap
        2 (s+k+1,t+k,t+i)
        (nuWeightLabel background X (s+k+1) (t+k) (t+i) (by omega) y))
      (homotopyRegrade (by dsimp; omega) rfl
        (finiteTowerBoundary X i N hi hN s t a))) :
    HasDifferential (background.classical.obj (X.obj background.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y := by
  apply finite_boundary_detects_differential X i k N hi hik hN hwindow s t x y a ha
  simpa only [finiteTowerBoundary_eq,regrade_precomp,Category.assoc] using hy

/-- Complete terminal decoder. The equality δ₁,ₚ₊₁(x)=b, with b carrying
the specified highest-layer label y, forces both x∈Zp and dₚ₊₁x=y. The
nontrivial highest-layer denominator is Bp, as calculated above. -/
private theorem finite_bockstein_terminal_decode
    (X : AdamsObject (coefficients := background.coefficients)) (p : ℕ) (hp : 0 < p) (s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background X (s+p+1,t+p))
    (b : BiHom ((t+p)-(s+p+1)) (t+(1:ℕ))
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) p))
    (hb : Detects (background.convergence (.quotient p (.nu X))) (s+p+1,t+p,t+(1:ℕ))
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) p).pageMap
        2 (s+p+1,t+p,t+(1:ℕ))
        (nuWeightLabel background X (s+p+1) (t+p) (t+(1:ℕ)) (by omega) y)) b)
    (heq : homotopyRegrade (by omega) rfl
      (finiteTowerBoundary X 1 p (by decide) hp s t (nativeFirstLabel X s t x)) = b) :
    IsCycle background X p (s,t) x ∧
      HasDifferential (background.classical.obj (X.obj background.auxiliary))
        (p+1) (s,t) (s+p+1,t+p) x y := by
  have hd : HasDifferential (background.classical.obj (X.obj background.auxiliary))
      (p+1) (s,t) (s+p+1,t+p) x y := by
    apply finiteTowerBoundary_detects_differential X 1 p p (by decide) (by omega)
      hp (by omega) s t x y (nativeFirstLabel X s t x)
    · simp only [(background.quotients.tower _).rho_id,Category.comp_id]
    · simpa only [heq] using hb
  refine ⟨?_,hd⟩
  obtain ⟨_,a,_,ha,_,_⟩ := hd
  have hx := (isCycle_iff_reaches background X (p+1) (by omega) (s,t) x).mpr ⟨a,ha⟩
  simpa only [add_sub_cancel_right] using hx


/-- The classical differential `d_R x=u` gives a finite connecting
representative of weight difference `R−2`, with `k=R−1`.
Its adjacent Bockstein lift makes the target permanent. -/
private theorem differential_detects_first_finite_boundary
    (X : AdamsObject (coefficients := background.coefficients)) (k N : ℕ) (hk : 0 < k) (hN : 0 < N) (s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background X (s+k+1,t+k))
    (hd : HasDifferential (background.classical.obj (X.obj background.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y) :
    Detects (background.convergence (.quotient N (.nu X))) (s+k+1,t+k,t+(1:ℕ))
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) N).pageMap
        2 (s+k+1,t+k,t+(1:ℕ))
        (nuWeightLabel background X (s+k+1) (t+k) (t+(1:ℕ)) (by omega) y))
      (homotopyRegrade (by dsimp; omega) rfl
        (finiteTowerBoundary X 1 N (by decide) hN s t (nativeFirstLabel X s t x))) := by
  obtain ⟨a,_,hay⟩ := adjacent_absolute_boundary X k hk s t x y hd
  have hy := first_label_lift_permanent X (s+k+1) (t+k) y
    (boundaryRepresentative X k s t a) hay
  obtain ⟨b,hb,hbd⟩ := differential_absolute_boundary X 1 k (by decide) (by omega)
    s t x y hd hy
  have hb' : b = nativeFirstLabel X s t x := by
    simpa only [nativeFirstLabel,(background.quotients.tower _).rho_id,Category.comp_id] using hb
  have hf := detects_map (.nu X) (.quotient N (.nu X)) (XModLambdaN.incl _ N)
    (s+k+1,t+k,t+(1:ℕ)) _ _ hbd
  change Detects (background.convergence (.quotient N (.nu X))) (s+k+1,t+k,t+(1:ℕ))
    ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) N).pageMap
      2 (s+k+1,t+k,t+(1:ℕ))
      (nuWeightLabel background X (s+k+1) (t+k) (t+(1:ℕ)) (by omega) y))
    ((homotopyRegrade (by dsimp; omega) rfl
      (biSuspensionHomEquiv (t-s) t (1:ℕ) (background.nu.functor.obj (X.obj background.auxiliary))
        (b ≫ XModLambdaN.proj _ 1))) ≫ XModLambdaN.incl _ N) at hf
  simpa only [finiteTowerBoundary_eq,regrade_precomp,Category.assoc,hb'] using hf

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
