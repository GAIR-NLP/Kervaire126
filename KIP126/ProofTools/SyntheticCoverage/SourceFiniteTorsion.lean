module

import all KIP126.ProofTools.SyntheticCoverage.SourceFiniteBottom
import all KIP126.ProofTools.SyntheticCoverage.PositiveTorsionDifferential

/-! Finite-torsion refinement of the lower comparison in the original
source-finite differential criterion. Only the lower candidate bound changes:
it contains true B_<r+j+1. The complete upper middle conditions, the whole
upper correction image's later survival, and the final entire-kernel condition
remain unchanged. The lower extension preserves the actual original source. -/

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

/-- Original source-finite criterion, positive-first exponent, with only the
lower candidate spaces tightened by the actual main boundary's finite torsion.
Here r=L+1, K₁=a+1, K₂=b+1, and D=L+b-a+1. -/
private theorem source_finite_differential_positive_first_torsion_bottom
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (a b L : ℕ) (ha : 0 < a) (hb : 0 < b) (haL : a+1 ≤ L) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (u : Ambient background T.X (s+L+1,t+L))
    (z₁ : Ambient background T.Z (s,t+1))
    (y : Ambient background T.Y (s+a+1,(t+1)+a))
    (z₂ : Ambient background T.Z (s+L+1,(t+L)+1))
    (v : Ambient background T.Y ((s+L+1)+b+1,((t+L)+1)+b))
    (_hFx : KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x = 0)
    (hxz : (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) z₁) (by simpa using x))
    (huz : (background.classicalSuspension T.X).DesuspendsClass (s+L+1) ((t+L)+1)
      ((background.classical.map T.h).pageMap 2 (s+L+1,(t+L)+1) z₂) (by simpa using u))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (s,t) (s+L+1,t+L) x u)
    (hdz₁ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (a+1) (s,t+1) (s+a+1,(t+1)+a) z₁
      ((background.classical.map T.g).pageMap 2 (s+a+1,(t+1)+a) y))
    (hdz₂ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (b+1) (s+L+1,(t+L)+1) ((s+L+1)+b+1,((t+L)+1)+b) z₂
      ((background.classical.map T.g).pageMap 2 ((s+L+1)+b+1,((t+L)+1)+b) v))
    (htop : ∀ j : ℕ, 1 ≤ j → j < (a+1)-1 →
      ∀ x' : Ambient background T.X (s+j,t+j),
        x' ∈ cycles background T.X (((a+1:ℕ):ℤ)-j) (s+j,t+j) →
        ∃ z' : Ambient background T.Z (s+j,t+j+1),
          z' ∈ cycles background T.Z (((a+1:ℕ):ℤ)-j) (s+j,t+j+1) ∧
          x'-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+j) (t+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (s+j,t+j))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hPm : ∀ j : ℕ, 1 ≤ j → j < (b+1)-1 →
      boundaries background T.Y ((L:ℤ)+j+1) ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j)
    (hbottom : ∀ j : ℕ, 1 ≤ j → j < (b+1)-1 →
      ∀ x' : Ambient background T.X ((s+L+1)+j,(t+L)+j),
        x' ∈ cycles background T.X (((b+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf
          ((s+L+1)+j) ((t+L)+j) x' ∈ Pm j →
        ∃ z' : Ambient background T.Z ((s+L+1)+j,(t+L)+j+1),
          z' ∈ cycles background T.Z (((b+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j+1) ∧
          x'-KIP126.ProofTools.Standard.classicalTriangleHMapHom T
            ((s+L+1)+j) ((t+L)+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) ((s+L+1)+j,(t+L)+j))
    (himage : ∀ e : Ambient background T.X (s+a,t+a),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+a) (t+a) e ∈
        cycles background T.Y ((L+b-a:ℕ)+1) (s+a+1,(t+a)+1))
    (P : Submodule ℤ (Ambient background T.Y ((s+L+1)+b+1,((t+L)+1)+b)))
    (hP : permanentCycles background T.Y ((s+L+1)+b+1,((t+L)+1)+b) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ z ∈ P,
      (background.classical.map T.g).pageMap 2 ((s+L+1)+b+1,((t+L)+1)+b) z = 0 →
      z ∈ boundaries background T.Y (L+b-a:ℕ) ((s+L+1)+b+1,((t+L)+1)+b)) :
    IsCycle background T.Y (L+b-a:ℕ) (s+a+1,(t+1)+a) y ∧
      IsCycle background T.Y (L+b-a:ℕ) ((s+L+1)+b+1,((t+L)+1)+b) v ∧
      DifferentialAt background T.Y ((L+b-a:ℕ)+1) (s+a+1,(t+1)+a)
        ((s+L+1)+b+1,((t+L)+1)+b) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X L (by omega)
    s t x u).mp hdx
  obtain ⟨η,wv,e,error,herror,hη,hboundary,hperm,herr⟩ :=
    torsion_positive_bottom_finite_lift_of_selective_middle T he hT hf hg hh L b (by omega) hb
      s t u z₂ v huz hdz₂ Pm hPm hbottom ζ hU
  let N := L+(0+b)
  have hG : (background.classical.map T.g).pageMap 2 ((s+L+1)+b+1,((t+L)+1)+b) error = 0 := by
    have hz := (KIP126.Literature.Standard.E2Exactness.e2ExactAtY T hf hg hh
      ((s+L+1)+b) ((t+L)+b)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf
        ((s+L+1)+b) ((t+L)+b) e)).mpr ⟨e,rfl⟩
    have transport (p p' : ℤ × ℤ) (hp : p=p')
        (a : Ambient background T.Y p) (a' : Ambient background T.Y p') (ha : HEq a a')
        (hz : (background.classical.map T.g).pageMap 2 p' a' = 0) :
        (background.classical.map T.g).pageMap 2 p a = 0 := by
      subst p'; cases eq_of_heq ha; exact hz
    exact transport _ _ (by congr 1; omega) error _ herror hz
  have herrorP : error ∈ P := by
    have hB := hP (boundary_mem_permanent_cycles T.Y (b+1) _ (wv-v-error) herr)
    have h := P.sub_mem (P.sub_mem (hP hperm) hv) hB
    convert h using 1; abel
  have htarget : wv-v ∈ boundaries background T.Y (L+b-a:ℕ)
      ((s+L+1)+b+1,((t+L)+1)+b) := by
    have h := (boundaries background T.Y (L+b-a:ℕ) _).add_mem
      (boundaries_monotone background T.Y _ (by omega) herr) (hker error herrorP hG)
    simpa only [sub_add_cancel] using h
  let w₀ : Ambient background T.Y ((s+N+1)+1,(t+N)+1) :=
    topClassicalRegrade (show ((s+L+1)+b+1,((t+L)+1)+b)=((s+N+1)+1,(t+N)+1) by
      ext <;> dsimp [N] <;> omega) wv
  let v₀ : Ambient background T.Y ((s+N+1)+1,(t+N)+1) :=
    topClassicalRegrade (show ((s+L+1)+b+1,((t+L)+1)+b)=((s+N+1)+1,(t+N)+1) by
      ext <;> dsimp [N] <;> omega) v
  have hw₀ : HEq w₀ wv := top_classical_regrade_heq _ _
  have hv₀ : HEq v₀ v := top_classical_regrade_heq _ _
  have hsub : HEq (w₀-v₀) (wv-v) := by
    have transport (p p' : ℤ × ℤ) (hp : p=p')
        (a b : Ambient background T.Y p) (a' b' : Ambient background T.Y p')
        (ha : HEq a' a) (hb : HEq b' b) : HEq (a'-b') (a-b) := by
      subst p'; cases eq_of_heq ha; cases eq_of_heq hb; rfl
    exact transport _ _ (by ext <;> dsimp [N] <;> omega) wv v w₀ v₀ hw₀ hv₀
  have htarget₀ : w₀-v₀ ∈ boundaries background T.Y (N-a:ℕ) ((s+N+1)+1,(t+N)+1) := by
    exact classical_boundary_heq T.Y (N-a:ℕ)
      (show ((s+L+1)+b+1,((t+L)+1)+b)=((s+N+1)+1,(t+N)+1) by
        ext <;> dsimp [N] <;> omega) (wv-v) (w₀-v₀) hsub.symm
      (by simpa only [N,Nat.zero_add] using htarget)
  have hboundary₀ := congrArg (homotopyRegrade
    (show (((t+L)+1)+b)-((s+L+1)+b+1)=((t+N)+1)-((s+N+1)+1) by dsimp [N]; omega)
    (show ((t+L)+1)+b=(t+N)+1 by dsimp [N]; omega)) hboundary
  rw [source_native_label_transport T.Y ((s+L+1)+b+1) (((t+L)+1)+b)
    ((s+N+1)+1) ((t+N)+1) (by dsimp [N]; omega) (by dsimp [N]; omega) wv w₀ hw₀]
    at hboundary₀
  have hresult := source_finite_differential_of_retained_lift T he hT hf hg hh
    a L N ha haL (by dsimp [N]; omega) s t x z₁ y w₀ v₀ hxz hdz₁ htop
    (fun e => by simpa only [N,Nat.zero_add] using himage e) ζ hζ η hη
    (by simpa only [regrade_comp,last_layer_regrade_trans] using hboundary₀) htarget₀
  have hvcycle := classical_cycle_heq T.Y (N-a:ℕ)
    (show ((s+N+1)+1,(t+N)+1)=((s+L+1)+b+1,((t+L)+1)+b) by
      ext <;> dsimp [N] <;> omega) v₀ v hv₀ hresult.2.1
  have hdiff := classical_differential_heq T.Y ((N-a:ℕ)+1) rfl
    (show ((s+N+1)+1,(t+N)+1)=((s+L+1)+b+1,((t+L)+1)+b) by
      ext <;> dsimp [N] <;> omega) y y v₀ v HEq.rfl hv₀ hresult.2.2
  exact ⟨by simpa only [N,Nat.zero_add] using hresult.1,
    by simpa only [N,Nat.zero_add] using hvcycle,
    by simpa only [N,Nat.zero_add] using hdiff⟩


end
end KIP126.ProofTools.Internal.SyntheticCoverage
