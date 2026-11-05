module

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.BottomFiniteLift
import all KIP126.ProofTools.SyntheticCoverage.SelectiveDifferential

/-! Final positive-first specialization of the selective differential criterion.
The actual adjacent source is retained by the bottom coefficient extension. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

private theorem positive_finite_image_native_first
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (s t : ℤ) (x : Ambient background T.X (s,t)) :
    homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
      (positiveFiniteImage T hf 1 (levelQuotientShiftIso T.X 1 1) (t-s) t
        (nativeFirstLabel T.X s t x))=
      nativeFirstLabel T.Y (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) := by
  have hs := KIP126.ProofTools.Internal.LastLayerComparison.shifted_first_label_uncast
    T.X 1 rfl s t x (levelQuotientShiftIso T.X 1 1) (level_quotient_shift_incl T.X 1 1)
  have hs' : homotopyRegrade (m':=t-s) (w':=t+1) (by dsimp; omega) rfl
      (shiftHomotopyClass (0,1) (t-s,t) (nativeFirstLabel T.X s t x)) ≫
        (levelQuotientShiftIso T.X 1 1).inv=(background.firstQuotient T.X 1 s t).symm x := by
    simpa only [oneQuotientUncast,oneQuotientCast,regrade_comp] using hs
  dsimp only [positiveFiniteImage]
  rw [hs']
  exact normalizedFirstMap_boundary T hf s t x

/-- The restricted-middle differential criterion for the positive first arrow:
all middle conditions are restricted to the inverse images of the chosen permanent-cycle spaces. -/
public theorem differential_of_selective_middle_and_candidate_kernel_first
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (L q : ℕ) (hL : 0<L) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u : Ambient background T.X (s+L+1,t+L))
    (z : Ambient background T.Z (s+L+1,(t+L)+1))
    (v : Ambient background T.Y ((s+L+1)+q+1,((t+L)+1)+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+L+1) ((t+L)+1)
      ((background.classical.map T.h).pageMap 2 (s+L+1,(t+L)+1) z) (by simpa using u))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (s,t) (s+L+1,t+L) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+L+1,(t+L)+1) ((s+L+1)+q+1,((t+L)+1)+q) z
      ((background.classical.map T.g).pageMap 2 ((s+L+1)+q+1,((t+L)+1)+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      permanentCycles background T.Y ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ a : Ambient background T.X ((s+L+1)+j,(t+L)+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf
          ((s+L+1)+j) ((t+L)+j) a ∈ Pm j →
        ∃ z' : Ambient background T.Z ((s+L+1)+j,(t+L)+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T
            ((s+L+1)+j) ((t+L)+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) ((s+L+1)+j,(t+L)+j))
    (P : Submodule ℤ (Ambient background T.Y ((s+L+1)+q+1,((t+L)+1)+q)))
    (hP : permanentCycles background T.Y ((s+L+1)+q+1,((t+L)+1)+q) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ a ∈ P,
      (background.classical.map T.g).pageMap 2 ((s+L+1)+q+1,((t+L)+1)+q) a=0 →
      a ∈ boundaries background T.Y (L+q) ((s+L+1)+q+1,((t+L)+1)+q)) :
    let y := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x
    IsCycle background T.Y (L+q) (s+1,t+1) y ∧
      IsCycle background T.Y (L+q) ((s+L+1)+q+1,((t+L)+1)+q) v ∧
      DifferentialAt background T.Y (L+q+1) (s+1,t+1)
        ((s+L+1)+q+1,((t+L)+1)+q) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨ζ,hζ,hbζ⟩ := adjacent_absolute_boundary T.X L hL s t x u hdx
  have hbζ' : adjacentBoundaryLabel T.X L s t ζ=nativeFirstLabel T.X (s+L+1) (t+L) u := by
    simpa only [adjacentBoundaryLabel,boundaryRepresentative,nativeFirstLabel,regrade_precomp,
      ←Category.assoc,eqToHom_trans] using hbζ
  obtain ⟨η,wv,e,error,herror,hη,hwv,hwp,herr⟩ :=
    positive_bottom_finite_lift_of_selective_middle T he hT hf hg hh L q hL hq s t u z v hu hdz
      Pm hPm hmid ζ hbζ'
  let N := L+(0+q)
  have hN : 0<N := by dsimp [N]; omega
  let y := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x
  let a := homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl η
  have ha : a ≫ (background.quotients.tower _).rho 1 N (by omega)=nativeFirstLabel T.Y (s+1) (t+1) y := by
    dsimp only [a]
    rw [←regrade_comp,←(background.quotients.tower _).rho_comp hL (show L≤N by dsimp [N];omega),
      ←Category.assoc,hη,positive_finite_image_restriction T hf 1 L (by decide) hL,hζ]
    exact positive_finite_image_native_first T hf s t x
  let w' : Ambient background T.Y ((s+1)+N+1,(t+1)+N) :=
    topClassicalRegrade (show ((s+L+1)+q+1,((t+L)+1)+q)=((s+1)+N+1,(t+1)+N) by
      ext <;> dsimp [N] <;> omega) wv
  have hw' : HEq w' wv := top_classical_regrade_heq _ _
  have hb := congrArg (homotopyRegrade
    (show (((t+L)+1)+q)-((s+L+1)+q+1)=((t+1)+N)-((s+1)+N+1) by dsimp [N];omega)
    (show ((t+L)+1)+q=(t+1)+N by dsimp [N];omega)) hwv
  rw [source_native_label_transport T.Y ((s+L+1)+q+1) (((t+L)+1)+q)
    ((s+1)+N+1) ((t+1)+N) (by dsimp [N];omega) (by dsimp [N];omega) wv w' hw'] at hb
  have hba : boundaryRepresentative T.Y N (s+1) (t+1) a ≫ XModLambdaN.incl _ 1=
      nativeFirstLabel T.Y ((s+1)+N+1) ((t+1)+N) w' := by
    simpa only [a,boundaryRepresentative,source_boundary_regrade,regrade_comp,last_layer_regrade_trans] using hb
  have hd0 : DifferentialAt background T.Y (N+1) (s+1,t+1) ((s+1)+N+1,(t+1)+N) y w' :=
    ⟨by omega,adjacent_boundary_differential T.Y N hN (s+1) (t+1) y w' a ha hba⟩
  have hd := classical_differential_heq T.Y (N+1) rfl
    (show ((s+1)+N+1,(t+1)+N)=((s+L+1)+q+1,((t+L)+1)+q) by ext <;> dsimp [N] <;> omega)
    y y w' wv HEq.rfl hw' hd0
  have heG : (background.classical.map T.g).pageMap 2 ((s+L+1)+q+1,((t+L)+1)+q) error=0 := by
    have hb := (KIP126.Literature.Standard.E2Exactness.e2ExactAtY T hf hg hh
      ((s+L+1)+q) ((t+L)+q)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+L+1)+q) ((t+L)+q) e)).mpr ⟨e,rfl⟩
    have transport (p p' : ℤ×ℤ) (hp : p=p')
        (a : Ambient background T.Y p) (b : Ambient background T.Y p') (hab : HEq a b)
        (hb : (background.classical.map T.g).pageMap 2 p' b=0) :
        (background.classical.map T.g).pageMap 2 p a=0 := by
      subst p'; simpa only [eq_of_heq hab] using hb
    exact transport _ _ (by congr 1;omega) _ _ herror hb
  have hd' := differential_target_of_permanent_candidate_kernel T.Y T.Z T.g (N+1)
    (s+1,t+1) ((s+L+1)+q+1,((t+L)+1)+q) y wv v error P hP hd hv
    (boundaries_monotone background T.Y _ (by dsimp [N];omega) herr) heG
    (by simpa only [N,Nat.cast_add,Nat.cast_zero,zero_add,add_sub_cancel_right] using hker)
  have hc := cycles_of_differential T.Y (N+1) _ _ y v hd'
  refine ⟨?_,?_,?_⟩
  · simpa only [N,Nat.cast_add,Nat.cast_zero,zero_add,add_sub_cancel_right] using hc.1
  · simpa only [N,Nat.cast_add,Nat.cast_zero,zero_add,add_sub_cancel_right] using hc.2
  · simpa only [N,Nat.cast_add,Nat.cast_zero,zero_add,add_sub_cancel_right] using hd'

end
end KIP126.ProofTools.Internal.SyntheticCoverage
