module

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.SourceFiniteDifferential
import all KIP126.ProofTools.SyntheticCoverage.BottomFiniteLift

/-! Composition of the two finite ends of the finite-source differential criterion.
The long target representative retains the prescribed image of the original
source lift. Its actual absolute boundary is used to decode the output
differential. The final theorem closes the positive-first-arrow case with
both finite ends and the original selective middle condition at the lower
end; the preceding full-middle theorem remains as a specialization.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000

/-- Apply the source-finite criterion to a retained long target lift,
combining the upper E₂ hypotheses with the lower-lift data. -/
private theorem source_finite_differential_of_retained_lift
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q L N : ℕ) (hq : 0 < q) (hqL : q+1 ≤ L) (hLN : L ≤ N) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (z : Ambient background T.Z (s,t+1))
    (y : Ambient background T.Y (s+q+1,(t+1)+q))
    (wᵥ v : Ambient background T.Y ((s+N+1)+1,(t+N)+1))
    (hxz : (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) z) (by simpa using x))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t+1) (s+q+1,(t+1)+q) z
      ((background.classical.map T.g).pageMap 2 (s+q+1,(t+1)+q) y))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X (s+j,t+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (s+j,t+j) →
        ∃ z' : Ambient background T.Z (s+j,t+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (s+j,t+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+j) (t+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (s+j,t+j))
    (himage : ∀ e : Ambient background T.X (s+q,t+q),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+q) (t+q) e ∈
        cycles background T.Y ((N-q:ℕ)+1) (s+q+1,(t+q)+1))
    (ζ : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) L))
    (hζ : ζ ≫ (background.quotients.tower _).rho 1 L (by omega) = nativeFirstLabel T.X s t x)
    (η : BiHom (t-s) (t+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N))
    (hη : η ≫ (background.quotients.tower _).rho L N hLN =
      positiveFiniteImage T hf L (levelQuotientShiftIso T.X 1 L) (t-s) t ζ)
    (hboundary : homotopyRegrade
        (show (t-s)-1=((t+N)+1)-((s+N+1)+1) by omega)
        (show (t+1)+N=(t+N)+1 by omega)
        (biSuspensionHomEquiv (t-s) (t+1) N
          (background.nu.functor.obj (T.Y.obj background.auxiliary)) (η ≫ XModLambdaN.proj _ N)) ≫
        XModLambdaN.incl _ 1 = nativeFirstLabel T.Y ((s+N+1)+1) ((t+N)+1) wᵥ)
    (htarget : wᵥ-v ∈ boundaries background T.Y (N-q:ℕ) ((s+N+1)+1,(t+N)+1)) :
    IsCycle background T.Y (N-q:ℕ) (s+q+1,(t+1)+q) y ∧
      IsCycle background T.Y (N-q:ℕ) ((s+N+1)+1,(t+N)+1) v ∧
      DifferentialAt background T.Y ((N-q:ℕ)+1) (s+q+1,(t+1)+q)
        ((s+N+1)+1,(t+N)+1) y v := by
  obtain ⟨e,error,herror,htop⟩ := positive_source_finite_top_restriction
    T he hT hf hg hh q L hq hqL s t x z y hxz hdz hmid ζ hζ
  let S := s+q+1
  let V := (t+1)+q
  let d : ℕ := 0+q
  let w' : Ambient background T.Y (S+(N-d:ℕ)+1,V+(N-d:ℕ)) :=
    topClassicalRegrade (show ((s+N+1)+1,(t+N)+1)=(S+(N-d:ℕ)+1,V+(N-d:ℕ)) by
      ext <;> dsimp [S,V,d] <;> omega) wᵥ
  have hw' : HEq w' wᵥ := top_classical_regrade_heq _ _
  let a : BiHom (V-S) (t+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N) :=
    homotopyRegrade (show t-s=V-S by dsimp [S,V]; omega) rfl η
  have ha : a ≫ (background.quotients.tower _).rho (0+(q+1)) N (by omega) =
      finiteTopLabelAtWeight T.Y d (by dsimp [d]; omega) (0+(q+1)) (by dsimp [d]; omega)
        S V (t+1) (by dsimp [V,d]; omega) (y+error) := by
    dsimp only [a]
    rw [←regrade_comp,←(background.quotients.tower _).rho_comp (show 0+(q+1)≤L by omega) hLN,
      ←Category.assoc,hη]
    exact htop
  have hb := congrArg (homotopyRegrade
    (show ((t+N)+1)-((s+N+1)+1)=(V+(N-d:ℕ))-(S+(N-d:ℕ)+1) by dsimp [S,V,d]; omega)
    (show (t+N)+1=V+(N-d:ℕ) by dsimp [V,d]; omega)) hboundary
  rw [source_native_label_transport T.Y ((s+N+1)+1) ((t+N)+1)
    (S+(N-d:ℕ)+1) (V+(N-d:ℕ)) (by dsimp [S,d]; omega) (by dsimp [V,d]; omega) wᵥ w' hw'] at hb
  have hba : homotopyRegrade (by omega) (by omega)
      (biSuspensionHomEquiv (V-S) (t+1) N (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (a ≫ XModLambdaN.proj _ N)) ≫ XModLambdaN.incl _ 1 =
      nativeFirstLabel T.Y (S+(N-d:ℕ)+1) (V+(N-d:ℕ)) w' := by
    simpa only [a,source_boundary_regrade,regrade_comp,last_layer_regrade_trans] using hb
  have hd := finite_source_differential_of_top_at_weight T.Y d N (0+(q+1))
    (by dsimp [d]; omega) (by dsimp [d]; omega) (by dsimp [d]; omega)
    S V (t+1) (by dsimp [V,d]; omega) (y+error) w' a ha hba
  have hecycle : error ∈ cycles background T.Y ((N-d:ℕ)+1) (S,V) := by
    have h := classical_cycle_heq T.Y ((N-d:ℕ)+1)
      (show (s+q+1,(t+q)+1)=(S,V) by dsimp [S,V]; congr 1; omega)
      _ error herror.symm ⟨by omega,by simpa only [d,Nat.zero_add] using himage e⟩
    exact h.2
  have hdactual := classical_differential_heq T.Y ((N-d:ℕ)+1) rfl
    (show (S+(N-d:ℕ)+1,V+(N-d:ℕ))=((s+N+1)+1,(t+N)+1) by
      ext <;> dsimp [S,V,d] <;> omega) (y+error) (y+error) w' wᵥ HEq.rfl hw' hd
  have hfinal := differential_of_source_correction T.Y ((N-d:ℕ)+1) (q+1)
    (S,V) ((s+N+1)+1,(t+N)+1) (y+error) y error wᵥ v hdactual
    (by have hz : (y+error)-y-error=0 := by abel
        rw [hz]; exact (boundaries background T.Y (q+1) (S,V)).zero_mem)
    hecycle (by simpa only [d,Nat.zero_add,add_sub_cancel_right] using htarget)
  simpa only [d,Nat.zero_add,add_sub_cancel_right] using hfinal

/-- The two-ended source-finite differential with full middle image
conditions at both ends and an arbitrary terminal candidate space.
Here `r=L+1`, `K₁=a+1`, `K₂=b+1`, so `D=L+b-a+1`.
The lower full-M condition is a specialization of the selective M_P
condition in the finite-source differential criterion; the candidate
space itself is unrestricted apart from the original permanence and kernel requirements. -/
private theorem source_finite_differential_positive_first_full_middle
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
    (hbottom : ∀ j : ℕ, 1 ≤ j → j < (b+1)-1 →
      ∀ x' : Ambient background T.X ((s+L+1)+j,(t+L)+j),
        x' ∈ cycles background T.X (((b+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j) →
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
    positive_bottom_finite_lift_of_middle_images T he hT hf hg hh L b (by omega) hb
      s t u z₂ v huz hdz₂ hbottom ζ hU
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

/-- The finite-source differential criterion with its selective bottom condition.
The specified main source lift is retained through both finite constructions;
only the original full upper image control removes the source correction. -/
public theorem source_finite_differential_positive_first_selective_bottom
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
      permanentCycles background T.Y ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j)
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
    positive_bottom_finite_lift_of_selective_middle T he hT hf hg hh L b (by omega) hb
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
