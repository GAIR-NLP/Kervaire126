module

public import KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch

public import KIP126.ProofTools.MahowaldLeibniz.PositiveBranches

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.KnownSourceSurvival
import all KIP126.ProofTools.SyntheticCoverage.OrdinarySourceFinite
import all KIP126.ProofTools.SyntheticCoverage.SourceFiniteDivision

/-! Ordinary first-arrow corrections with a fixed known finite source.
Independent survival of its first label supplies the exact early-boundary
gate for every actual residual head. Each correction preserves the same
full image and all original restricted cycle hypotheses. -/

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
set_option maxHeartbeats 2500000

private theorem known_source_ordinary_finite_head
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N k L : ℕ) (hk : 0<k) (hkN : k<N) (hL : 0<L)
    (s t A B D : ℤ) (hA : s=A+(L+k:ℕ)+1) (hB : t=B+(L+k:ℕ))
    (hD : (L:ℤ)+k+1<D)
    (y : Ambient background Y (A,B))
    (η₀ : BiHom (B-A) B (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel Y A B y)
    (hy : y ∈ cycles background Y (D-1) (A,B))
    (a : BiHom (t-s) (t-k) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (ha : FiltrationAtLeast background.syntheticTower s a)
    (β : BiHom (t-s) (t-k) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (hβ : β=homotopyRegrade (show (B-A)-1=t-s by omega) (show B+L=t-k by omega)
      (biSuspensionHomEquiv (B-A) B L (background.nu.functor.obj (Y.obj background.auxiliary))
        (η₀ ≫ XModLambdaN.proj _ L)))
    (v : BiHom (t-s) (t-k) (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (hv : FiltrationAtLeast background.syntheticTower (s+1) v)
    (himage : a ≫ XModLambdaN.map (background.nu.functor.map f) N =
      β ≫ XModLambdaN.incl _ N-v) :
    ∃ x : Ambient background X (s,t),
      x ∈ cycles background X (N-k:ℕ) (s,t) ∧
      Detects (background.convergence (.quotient N (.nu X))) (s,t,t-k)
        (finiteTargetLabel background X N s t k x) a ∧
      (background.classical.map f).pageMap 2 (s,t) x ∈ boundaries background Y ((L+k:ℕ):ℤ) (s,t) := by
  obtain ⟨x,hx,hxa⟩ := middle_finite_filtration_label X N k hkN s t a ha
  refine ⟨x,hx,hxa,?_⟩
  have hmap := detects_map (.quotient N (.nu X)) (.quotient N (.nu Y))
    (XModLambdaN.map (background.nu.functor.map f) N) (s,t,t-k) _ a hxa
  erw [←middle_finite_label_as_weight,finite_weight_label_natural X Y f N s t (t-k) (by omega) x,
    middle_finite_label_as_weight] at hmap
  apply known_source_finite_label_boundary_at_degree Y L k N hL hk hkN
    A B s t D hA hB hD y η₀ hη hy β hβ _ _ hmap
  rw [himage]
  simpa only [sub_sub_cancel] using hv

private theorem known_source_positive_h_native_step
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (k q L : ℕ) (hk : 0<k) (hq : 0<q) (hL : 0<L) (s t A B D : ℤ)
    (hA : s+1=A+(L+k:ℕ)+1) (hB : t=B+(L+k:ℕ))
    (hD : (L:ℤ)+k+1<D)
    (y : Ambient background T.Y (A,B))
    (η₀ : BiHom (B-A) B (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y A B y)
    (hy : y ∈ cycles background T.Y (D-1) (A,B))
    (P : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (hP : boundaries background T.Y ((L+k:ℕ):ℤ) (s+1,t) ≤ P)
    (hmid : ∀ x : Ambient background T.X (s+1,t), x ∈ cycles background T.X q (s+1,t) →
      (background.classical.map T.f).pageMap 2 (s+1,t) x ∈ P →
      ∃ z : Ambient background T.Z (s,t), z ∈ cycles background T.Z q (s,t) ∧
      ∃ u : Ambient background T.X (s+1,t),
        (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
          (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
          (by simpa only [add_sub_cancel_right] using u) ∧
        x-u ∈ boundaries background T.X (k+1) (s+1,t))
    (a : BiHom (t-(s+1)) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)))
    (ha : FiltrationAtLeast background.syntheticTower (s+1) a)
    (β : BiHom (t-(s+1)) (t-k) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hβ : β=homotopyRegrade (show (B-A)-1=t-(s+1) by omega) (show B+L=t-k by omega)
      (biSuspensionHomEquiv (B-A) B L (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (η₀ ≫ XModLambdaN.proj _ L)))
    (v : BiHom (t-(s+1)) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (k+q)))
    (hv : FiltrationAtLeast background.syntheticTower (s+2) v)
    (himage : a ≫ XModLambdaN.map (background.nu.functor.map T.f) (k+q)=
      β ≫ XModLambdaN.incl _ (k+q)-v) :
    ∃ b : BiHom (t-(s+1)) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)),
      FiltrationAtLeast background.syntheticTower (s+2) b ∧
      b ≫ XModLambdaN.map (background.nu.functor.map T.f) (k+q)=
      a ≫ XModLambdaN.map (background.nu.functor.map T.f) (k+q) := by
  obtain ⟨x,hxc,hxd,hxp⟩ := known_source_ordinary_finite_head T.X T.Y T.f
    (k+q) k L hk (by omega) hL (s+1) t A B D hA hB hD y η₀ hη hy
    a ha β hβ v (by simpa only [show s+1+1=s+2 by omega] using hv) himage
  obtain ⟨z,hz,u,hu,hxu⟩ := hmid x (by simpa only [Nat.add_sub_cancel_left] using hxc) (hP hxp)
  obtain ⟨b,hb,hbz⟩ := middle_positive_h_native_cycle_image T he hf hg hh hT
    k q hq s t z hz u hu
  have hnext := middle_finite_congruent_difference T.X (k+q) k (by omega)
    (s+1) t x u hxu a b hxd hb
  refine ⟨a-b,?_,?_⟩
  · simpa only [show s+1+1=s+2 by omega] using hnext
  · rw [Preadditive.sub_comp,hbz,sub_zero]

/-- Coordinate-only wrapper for a fixed finite representative. -/
private theorem known_source_positive_h_native_step_regraded
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (N k q L : ℕ) (hk : 0<k) (hq : 0<q) (hL : 0<L) (hN : N=k+q) (s t m w A B D : ℤ)
    (hA : s+1=A+(L+k:ℕ)+1) (hB : t=B+(L+k:ℕ))
    (hD : (L:ℤ)+k+1<D)
    (y : Ambient background T.Y (A,B))
    (η₀ : BiHom (B-A) B (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y A B y)
    (hy : y ∈ cycles background T.Y (D-1) (A,B))
    (hm : m=t-(s+1)) (hw : w=t-k)
    (P : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (hP : boundaries background T.Y ((L+k:ℕ):ℤ) (s+1,t) ≤ P)
    (hmid : ∀ x : Ambient background T.X (s+1,t), x ∈ cycles background T.X q (s+1,t) →
      (background.classical.map T.f).pageMap 2 (s+1,t) x ∈ P →
      ∃ z : Ambient background T.Z (s,t), z ∈ cycles background T.Z q (s,t) ∧
      ∃ u : Ambient background T.X (s+1,t),
        (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
          (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
          (by simpa only [add_sub_cancel_right] using u) ∧
        x-u ∈ boundaries background T.X (k+1) (s+1,t))
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (ha : FiltrationAtLeast background.syntheticTower (s+1) a)
    (β : BiHom m w (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hβ : β=homotopyRegrade (show (B-A)-1=m by omega) (show B+L=w by omega)
      (biSuspensionHomEquiv (B-A) B L (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (η₀ ≫ XModLambdaN.proj _ L)))
    (v : BiHom m w (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N))
    (hv : FiltrationAtLeast background.syntheticTower (s+2) v)
    (himage : a ≫ XModLambdaN.map (background.nu.functor.map T.f) N=
      β ≫ XModLambdaN.incl _ N-v) :
    ∃ b : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower (s+2) b ∧
      b ≫ XModLambdaN.map (background.nu.functor.map T.f) N=
      a ≫ XModLambdaN.map (background.nu.functor.map T.f) N := by
  subst N; subst m; subst w
  exact known_source_positive_h_native_step T he hf hg hh hT k q L hk hq hL s t A B D hA hB hD y η₀ hη hy P hP hmid a ha β hβ v hv himage


/-- Repeated restricted positive-H corrections keep the same full image
and produce a last-layer residual. The spaces P_j are used only after
membership of the actual residual head has been established. -/
private theorem known_source_positive_h_native_residual_same_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (c K L : ℕ) (hK : 2≤K) (hL : 0<L) (S V A₀ B₀ D : ℤ)
    (hA : S=A₀+(L+c:ℕ)+1) (hB : V=B₀+(L+c:ℕ))
    (hD : (L:ℤ)+c+K≤D)
    (y : Ambient background T.Y (A₀,B₀))
    (η₀ : BiHom (B₀-A₀) B₀ (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y A₀ B₀ y)
    (hy : y ∈ cycles background T.Y (D-1) (A₀,B₀))
    (P : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j-1+1,V+j)))
    (hP : ∀ j : ℕ, 1≤j → j<K-1 → boundaries background T.Y ((L:ℤ)+c+j) (S+j-1+1,V+j) ≤ P j)
    (hmid : ∀ j : ℕ, 1≤j → j<K-1 →
      ∀ x : Ambient background T.X (S+j-1+1,V+j),
        x ∈ cycles background T.X ((K:ℤ)-j) (S+j-1+1,V+j) →
        (background.classical.map T.f).pageMap 2 (S+j-1+1,V+j) x ∈ P j →
        ∃ z : Ambient background T.Z (S+j-1,V+j),
          z ∈ cycles background T.Z ((K:ℤ)-j) (S+j-1,V+j) ∧
        ∃ u : Ambient background T.X (S+j-1+1,V+j),
          (background.classicalSuspension T.X).DesuspendsClass (S+j-1+1) (V+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              (S+j-1) (V+j) z) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((c:ℤ)+j+1) (S+j-1+1,V+j))
    (a : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)))
    (ha : FiltrationAtLeast background.syntheticTower (S+1) a)
    (β : BiHom (V-S) (V-c) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hβ : β=homotopyRegrade (show (B₀-A₀)-1=V-S by omega) (show B₀+L=V-c by omega)
      (biSuspensionHomEquiv (B₀-A₀) B₀ L (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (η₀ ≫ XModLambdaN.proj _ L)))
    (v : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (c+K)))
    (hv : FiltrationAtLeast background.syntheticTower (S+K-1) v)
    (himage : a ≫ XModLambdaN.map (background.nu.functor.map T.f) (c+K)=
      β ≫ XModLambdaN.incl _ (c+K)-v) :
    ∃ e : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)),
      FiltrationAtLeast background.syntheticTower (S+K-1) e ∧
      e ≫ XModLambdaN.map (background.nu.functor.map T.f) (c+K)=
      a ≫ XModLambdaN.map (background.nu.functor.map T.f) (c+K) := by
  let A := XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)
  let f := XModLambdaN.map (background.nu.functor.map T.f) (c+K)
  have hstep (j : ℕ) (hj : 1≤j) (hjK : j<K-1)
      (b : BiHom (V-S) (V-c) A)
      (hb : FiltrationAtLeast background.syntheticTower (S+j) b)
      (hi : b≫f=a≫f) :
      ∃ b' : BiHom (V-S) (V-c) A,
        FiltrationAtLeast background.syntheticTower (S+(j+1:ℕ)) b' ∧ b'≫f=b≫f := by
    have H := known_source_positive_h_native_step_regraded T he hf hg hh hT
      (c+K) (c+j) (K-j) L (by omega) (by omega) hL (by omega)
      (S+j-1) (V+j) (V-S) (V-c) A₀ B₀ D (by omega) (by omega) (by omega)
      y η₀ hη hy (by omega) (by omega)
      (P j) (by simpa only [Nat.cast_add,add_assoc] using hP j hj hjK)
      (by simpa only [Nat.cast_sub (show j≤K by omega),Nat.cast_add,Nat.cast_one] using hmid j hj hjK)
      b (by simpa only [sub_add_cancel] using hb) β hβ v
      (background.syntheticTower.filtrationSubmodule_antitone _ _ (by omega) hv)
      (hi.trans himage)
    obtain ⟨b',hb',hi'⟩ := H
    refine ⟨b',?_,hi'⟩
    convert hb' using 1
    omega
  have hrec (j : ℕ) (hj : 1≤j) (hjK : j≤K-1)
      (b : BiHom (V-S) (V-c) A)
      (hb : FiltrationAtLeast background.syntheticTower (S+j) b)
      (hi : b≫f=a≫f) :
      ∃ e : BiHom (V-S) (V-c) A,
        FiltrationAtLeast background.syntheticTower (S+K-1) e ∧ e≫f=a≫f := by
    induction hlen : K-1-j using Nat.strong_induction_on generalizing j b with
    | h n ih =>
      by_cases hend : K-1≤j
      · refine ⟨b,?_,hi⟩
        convert hb using 1
        omega
      · obtain ⟨b',hb',hi'⟩ := hstep j hj (by omega) b hb hi
        exact ih (K-1-(j+1)) (by omega) (j+1) (by omega) (by omega) b' hb' (hi'.trans hi) rfl
  exact hrec 1 (by omega) (by omega) a (by simpa only [Nat.cast_one] using ha) rfl


/-- The positive-G branch needs only the restricted source condition for
its actual residual head. The image remains the same actual νf-image. -/
private theorem known_source_positive_g_native_step
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (k q L : ℕ) (hk : 0<k) (hq : 0<q) (hL : 0<L) (s t A B D : ℤ)
    (hA : s+1=A+(L+k:ℕ)+1) (hB : t=B+(L+k:ℕ))
    (hD : (L:ℤ)+k+1<D)
    (y : Ambient background T.Y (A,B))
    (η₀ : BiHom (B-A) B (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y A B y)
    (hy : y ∈ cycles background T.Y (D-1) (A,B))
    (P : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (hP : boundaries background T.Y ((L+k:ℕ):ℤ) (s+1,t) ≤ P)
    (hmid : ∀ x : Ambient background T.X (s+1,t), x ∈ cycles background T.X q (s+1,t) →
      (background.classical.map T.f).pageMap 2 (s+1,t) x ∈ P →
      ∃ z : Ambient background T.Z (s+1,t+1), z ∈ cycles background T.Z q (s+1,t+1) ∧
      ∃ u : Ambient background T.X (s+1,t),
        (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
          ((background.classical.map T.h).pageMap 2 (s+1,t+1) z)
          (by simpa only [add_sub_cancel_right] using u) ∧
        x-u ∈ boundaries background T.X (k+1) (s+1,t))
    (a : BiHom (t-(s+1)) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)))
    (ha : FiltrationAtLeast background.syntheticTower (s+1) a)
    (β : BiHom (t-(s+1)) (t-k) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hβ : β=homotopyRegrade (show (B-A)-1=t-(s+1) by omega) (show B+L=t-k by omega)
      (biSuspensionHomEquiv (B-A) B L (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (η₀ ≫ XModLambdaN.proj _ L)))
    (v : BiHom (t-(s+1)) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (k+q)))
    (hv : FiltrationAtLeast background.syntheticTower (s+2) v)
    (himage : a ≫ XModLambdaN.map (background.nu.functor.map T.f) (k+q)=
      β ≫ XModLambdaN.incl _ (k+q)-v) :
    ∃ b : BiHom (t-(s+1)) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)),
      FiltrationAtLeast background.syntheticTower (s+2) b ∧
      b ≫ XModLambdaN.map (background.nu.functor.map T.f) (k+q)=
      a ≫ XModLambdaN.map (background.nu.functor.map T.f) (k+q) := by
  obtain ⟨x,hxc,hxd,hxp⟩ := known_source_ordinary_finite_head T.X T.Y T.f
    (k+q) k L hk (by omega) hL (s+1) t A B D hA hB hD y η₀ hη hy
    a ha β hβ v (by simpa only [show s+1+1=s+2 by omega] using hv) himage
  obtain ⟨z,hz,u,hu,hxu⟩ := hmid x (by simpa only [Nat.add_sub_cancel_left] using hxc) (hP hxp)
  obtain ⟨b,hb,hbz⟩ := selective_positive_g_native_cycle_image T he hf hg hh hT
    k q hq s t z hz u hu
  have hnext := middle_finite_congruent_difference T.X (k+q) k (by omega)
    (s+1) t x u hxu a b hxd hb
  refine ⟨a-b,?_,?_⟩
  · simpa only [show s+1+1=s+2 by omega] using hnext
  · rw [Preadditive.sub_comp,hbz,sub_zero]

/-- Coordinate-only wrapper for a fixed finite representative. -/
private theorem known_source_positive_g_native_step_regraded
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (N k q L : ℕ) (hk : 0<k) (hq : 0<q) (hL : 0<L) (hN : N=k+q) (s t m w A B D : ℤ)
    (hA : s+1=A+(L+k:ℕ)+1) (hB : t=B+(L+k:ℕ))
    (hD : (L:ℤ)+k+1<D)
    (y : Ambient background T.Y (A,B))
    (η₀ : BiHom (B-A) B (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y A B y)
    (hy : y ∈ cycles background T.Y (D-1) (A,B))
    (hm : m=t-(s+1)) (hw : w=t-k)
    (P : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (hP : boundaries background T.Y ((L+k:ℕ):ℤ) (s+1,t) ≤ P)
    (hmid : ∀ x : Ambient background T.X (s+1,t), x ∈ cycles background T.X q (s+1,t) →
      (background.classical.map T.f).pageMap 2 (s+1,t) x ∈ P →
      ∃ z : Ambient background T.Z (s+1,t+1), z ∈ cycles background T.Z q (s+1,t+1) ∧
      ∃ u : Ambient background T.X (s+1,t),
        (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
          ((background.classical.map T.h).pageMap 2 (s+1,t+1) z)
          (by simpa only [add_sub_cancel_right] using u) ∧
        x-u ∈ boundaries background T.X (k+1) (s+1,t))
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (ha : FiltrationAtLeast background.syntheticTower (s+1) a)
    (β : BiHom m w (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hβ : β=homotopyRegrade (show (B-A)-1=m by omega) (show B+L=w by omega)
      (biSuspensionHomEquiv (B-A) B L (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (η₀ ≫ XModLambdaN.proj _ L)))
    (v : BiHom m w (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N))
    (hv : FiltrationAtLeast background.syntheticTower (s+2) v)
    (himage : a ≫ XModLambdaN.map (background.nu.functor.map T.f) N=
      β ≫ XModLambdaN.incl _ N-v) :
    ∃ b : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower (s+2) b ∧
      b ≫ XModLambdaN.map (background.nu.functor.map T.f) N=
      a ≫ XModLambdaN.map (background.nu.functor.map T.f) N := by
  subst N; subst m; subst w
  exact known_source_positive_g_native_step T he hf hg hh hT k q L hk hq hL s t A B D hA hB hD y η₀ hη hy P hP hmid a ha β hβ v hv himage


/-- Repeated restricted positive-G corrections keep the same full image
and produce a last-layer residual. The spaces P_j are used only after
membership of the actual residual head has been established. -/
private theorem known_source_positive_g_native_residual_same_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (c K L : ℕ) (hK : 2≤K) (hL : 0<L) (S V A₀ B₀ D : ℤ)
    (hA : S=A₀+(L+c:ℕ)+1) (hB : V=B₀+(L+c:ℕ))
    (hD : (L:ℤ)+c+K≤D)
    (y : Ambient background T.Y (A₀,B₀))
    (η₀ : BiHom (B₀-A₀) B₀ (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y A₀ B₀ y)
    (hy : y ∈ cycles background T.Y (D-1) (A₀,B₀))
    (P : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j-1+1,V+j)))
    (hP : ∀ j : ℕ, 1≤j → j<K-1 → boundaries background T.Y ((L:ℤ)+c+j) (S+j-1+1,V+j) ≤ P j)
    (hmid : ∀ j : ℕ, 1≤j → j<K-1 →
      ∀ x : Ambient background T.X (S+j-1+1,V+j),
        x ∈ cycles background T.X ((K:ℤ)-j) (S+j-1+1,V+j) →
        (background.classical.map T.f).pageMap 2 (S+j-1+1,V+j) x ∈ P j →
        ∃ z : Ambient background T.Z (S+j-1+1,V+j+1),
          z ∈ cycles background T.Z ((K:ℤ)-j) (S+j-1+1,V+j+1) ∧
        ∃ u : Ambient background T.X (S+j-1+1,V+j),
          (background.classicalSuspension T.X).DesuspendsClass (S+j-1+1) (V+j+1)
            ((background.classical.map T.h).pageMap 2 (S+j-1+1,V+j+1) z) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((c:ℤ)+j+1) (S+j-1+1,V+j))
    (a : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)))
    (ha : FiltrationAtLeast background.syntheticTower (S+1) a)
    (β : BiHom (V-S) (V-c) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hβ : β=homotopyRegrade (show (B₀-A₀)-1=V-S by omega) (show B₀+L=V-c by omega)
      (biSuspensionHomEquiv (B₀-A₀) B₀ L (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (η₀ ≫ XModLambdaN.proj _ L)))
    (v : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (c+K)))
    (hv : FiltrationAtLeast background.syntheticTower (S+K-1) v)
    (himage : a ≫ XModLambdaN.map (background.nu.functor.map T.f) (c+K)=
      β ≫ XModLambdaN.incl _ (c+K)-v) :
    ∃ e : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)),
      FiltrationAtLeast background.syntheticTower (S+K-1) e ∧
      e ≫ XModLambdaN.map (background.nu.functor.map T.f) (c+K)=
      a ≫ XModLambdaN.map (background.nu.functor.map T.f) (c+K) := by
  let A := XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)
  let f := XModLambdaN.map (background.nu.functor.map T.f) (c+K)
  have hstep (j : ℕ) (hj : 1≤j) (hjK : j<K-1)
      (b : BiHom (V-S) (V-c) A)
      (hb : FiltrationAtLeast background.syntheticTower (S+j) b)
      (hi : b≫f=a≫f) :
      ∃ b' : BiHom (V-S) (V-c) A,
        FiltrationAtLeast background.syntheticTower (S+(j+1:ℕ)) b' ∧ b'≫f=b≫f := by
    have H := known_source_positive_g_native_step_regraded T he hf hg hh hT
      (c+K) (c+j) (K-j) L (by omega) (by omega) hL (by omega)
      (S+j-1) (V+j) (V-S) (V-c) A₀ B₀ D (by omega) (by omega) (by omega)
      y η₀ hη hy (by omega) (by omega)
      (P j) (by simpa only [Nat.cast_add,add_assoc] using hP j hj hjK)
      (by simpa only [Nat.cast_sub (show j≤K by omega),Nat.cast_add,Nat.cast_one] using hmid j hj hjK)
      b (by simpa only [sub_add_cancel] using hb) β hβ v
      (background.syntheticTower.filtrationSubmodule_antitone _ _ (by omega) hv)
      (hi.trans himage)
    obtain ⟨b',hb',hi'⟩ := H
    refine ⟨b',?_,hi'⟩
    convert hb' using 1
    omega
  have hrec (j : ℕ) (hj : 1≤j) (hjK : j≤K-1)
      (b : BiHom (V-S) (V-c) A)
      (hb : FiltrationAtLeast background.syntheticTower (S+j) b)
      (hi : b≫f=a≫f) :
      ∃ e : BiHom (V-S) (V-c) A,
        FiltrationAtLeast background.syntheticTower (S+K-1) e ∧ e≫f=a≫f := by
    induction hlen : K-1-j using Nat.strong_induction_on generalizing j b with
    | h n ih =>
      by_cases hend : K-1≤j
      · refine ⟨b,?_,hi⟩
        convert hb using 1
        omega
      · obtain ⟨b',hb',hi'⟩ := hstep j hj (by omega) b hb hi
        exact ih (K-1-(j+1)) (by omega) (j+1) (by omega) (by omega) b' hb' (hi'.trans hi) rfl
  exact hrec 1 (by omega) (by omega) a (by simpa only [Nat.cast_one] using ha) rfl


/-- The known surviving source narrows the actual intermediate heads. -/
private theorem known_source_ordinary_full_image_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q L : ℕ) (hq : 0 < q) (hL : 0<L) (B W A₀ B₀ D : ℤ)
    (hA : B=A₀+L) (hB : W=B₀+L) (hD : (L:ℤ)+(q+1:ℕ)≤D)
    (y : Ambient background T.Y (A₀,B₀))
    (η₀ : BiHom (B₀-A₀) B₀ (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y A₀ B₀ y)
    (hy : y ∈ cycles background T.Y (D-1) (A₀,B₀))
    (u : Ambient background T.X (B+1,W)) (z : Ambient background T.Z (B+1,W+1))
    (v : Ambient background T.Y (B+q+1,W+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      ((background.classical.map T.h).pageMap 2 (B+1,W+1) z) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (B+1,W+1) ((B+q+1)+1,(W+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (B+q+1) (W+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((B+1)+j-1+1,W+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → boundaries background T.Y ((L:ℤ)+j) ((B+1)+j-1+1,W+j) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ x : Ambient background T.X ((B+1)+j-1+1,W+j),
        x ∈ cycles background T.X (((q+1):ℤ)-j) ((B+1)+j-1+1,W+j) →
        (background.classical.map T.f).pageMap 2 ((B+1)+j-1+1,W+j) x ∈ Pm j →
        ∃ z : Ambient background T.Z ((B+1)+j-1+1,W+j+1),
          z ∈ cycles background T.Z (((q+1):ℤ)-j) ((B+1)+j-1+1,W+j+1) ∧
        ∃ u : Ambient background T.X ((B+1)+j-1+1,W+j),
          (background.classicalSuspension T.X).DesuspendsClass ((B+1)+j-1+1) (W+j+1)
            ((background.classical.map T.h).pageMap 2 ((B+1)+j-1+1,W+j+1) z) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((0:ℤ)+j+1) ((B+1)+j-1+1,W+j))
    (U : BiHom (W-(B+1)) W (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X (B+1) W u)
    (hboundary : U ≫ background.nu.functor.map T.f =
      homotopyRegrade (show (B₀-A₀)-1=W-(B+1) by omega) (show B₀+L=W by omega)
        (biSuspensionHomEquiv (B₀-A₀) B₀ L (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (η₀ ≫ XModLambdaN.proj _ L))) :
    ∃ e₂ : Ambient background T.X (B+q+1,W+q),
      homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
        ((U ≫ background.nu.functor.map T.f) ≫ XModLambdaN.incl _ (q+1)) =
      finiteTopLabelAtWeight T.Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega)
        (v+(background.classical.map T.f).pageMap 2 (B+q+1,W+q) e₂) := by
  obtain ⟨a,ha,hi⟩ := finite_common_lift_positive_g
    T he hT hf hg hh q hq B W z u v hu hdz
  let a₀ := U ≫ XModLambdaN.incl _ (q+1)
  have ha₀ : a₀ ≫ (background.quotients.tower _).rho 1 (q+1) (by omega) =
      nativeFirstLabel T.X (B+1) W u := by
    dsimp only [a₀]
    rw [Category.assoc,(background.quotients.tower _).rho_quotient,hU]
  have hdet := first_label_detects_unshifted T.X (q+1) (by omega) (B+1) W u a₀ ha₀
  have hdet' := first_label_detects_unshifted T.X (q+1) (by omega) (B+1) W u a ha
  have hres := detects_sub_filtration (background.convergence (.quotient (q+1) (.nu T.X)))
    (B+1,W,W) hdet hdet'
  have hvfil : FiltrationAtLeast background.syntheticTower (B+q+1)
      (a ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1)) := by
    rw [hi]
    apply (regrade_filtration_iff _ _ _ _).mpr
    exact detects_filtration (.quotient (q+1) (.nu T.Y)) (B+q+1,W+q,(W+q)-q) _ _
      (finiteTopLabel_detects T.Y q hq (B+q+1) (W+q) v)
  have H := known_source_positive_g_native_residual_same_image T he hf hg hh hT
    0 (q+1) L (by omega) hL (B+1) W A₀ B₀ D (by omega) (by omega) (by omega)
    y η₀ hη hy Pm (by simpa only [Nat.cast_zero,add_zero] using hPm) hmid
  have transport (N : ℕ) (w : ℤ) (hN : 0+(q+1)=N) (hw : W-(0:ℕ)=w) :
      ∀ r : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+1) r →
      ∀ β : BiHom (W-(B+1)) w (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      β=homotopyRegrade (show (B₀-A₀)-1=W-(B+1) by omega) (show B₀+L=w by omega)
        (biSuspensionHomEquiv (B₀-A₀) B₀ L (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (η₀ ≫ XModLambdaN.proj _ L)) →
      ∀ v : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+(q+1:ℕ)-1) v →
      r ≫ XModLambdaN.map (background.nu.functor.map T.f) N = β ≫ XModLambdaN.incl _ N-v →
      ∃ e : BiHom (W-(B+1)) w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
        FiltrationAtLeast background.syntheticTower ((B+1)+(q+1:ℕ)-1) e ∧
        e ≫ XModLambdaN.map (background.nu.functor.map T.f) N =
          r ≫ XModLambdaN.map (background.nu.functor.map T.f) N := by
    subst N; subst w; exact H
  have H' := transport (q+1) W (by omega) (by omega)
  obtain ⟨e,hefil,heimage⟩ := H' (a₀-a) hres (U ≫ background.nu.functor.map T.f) hboundary
    (a ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1))
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hvfil)
    (by dsimp only [a₀]; rw [Preadditive.sub_comp,Category.assoc,
          ←XModLambdaN.incl_naturality,←Category.assoc])
  exact ordinary_full_source_top_of_residual T.X T.Y T.f q hq B W U a e v hi
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hefil) heimage

/-- The specified full source image under the original restricted middle condition. -/
private theorem known_source_ordinary_full_image_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
    (q L : ℕ) (hq : 0 < q) (hL : 0<L) (B W A₀ B₀ D : ℤ)
    (hA : B=A₀+L) (hB : W=B₀+L) (hD : (L:ℤ)+(q+1:ℕ)≤D)
    (y : Ambient background T.Y (A₀,B₀))
    (η₀ : BiHom (B₀-A₀) B₀ (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y A₀ B₀ y)
    (hy : y ∈ cycles background T.Y (D-1) (A₀,B₀))
    (u : Ambient background T.X (B+1,W)) (z : Ambient background T.Z (B,W))
    (v : Ambient background T.Y (B+q+1,W+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) B W z)
      (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (B,W) (B+q+1,W+q) z
      ((background.classical.map T.g).pageMap 2 (B+q+1,W+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((B+1)+j-1+1,W+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → boundaries background T.Y ((L:ℤ)+j) ((B+1)+j-1+1,W+j) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ x : Ambient background T.X ((B+1)+j-1+1,W+j),
        x ∈ cycles background T.X (((q+1):ℤ)-j) ((B+1)+j-1+1,W+j) →
        (background.classical.map T.f).pageMap 2 ((B+1)+j-1+1,W+j) x ∈ Pm j →
        ∃ z : Ambient background T.Z ((B+1)+j-1,W+j),
          z ∈ cycles background T.Z (((q+1):ℤ)-j) ((B+1)+j-1,W+j) ∧
        ∃ u : Ambient background T.X ((B+1)+j-1+1,W+j),
          (background.classicalSuspension T.X).DesuspendsClass ((B+1)+j-1+1) (W+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              ((B+1)+j-1) (W+j) z) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((0:ℤ)+j+1) ((B+1)+j-1+1,W+j))
    (U : BiHom (W-(B+1)) W (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X (B+1) W u)
    (hboundary : U ≫ background.nu.functor.map T.f =
      homotopyRegrade (show (B₀-A₀)-1=W-(B+1) by omega) (show B₀+L=W by omega)
        (biSuspensionHomEquiv (B₀-A₀) B₀ L (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (η₀ ≫ XModLambdaN.proj _ L))) :
    ∃ e₂ : Ambient background T.X (B+q+1,W+q),
      homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
        ((U ≫ background.nu.functor.map T.f) ≫ XModLambdaN.incl _ (q+1)) =
      finiteTopLabelAtWeight T.Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega)
        (v+(background.classical.map T.f).pageMap 2 (B+q+1,W+q) e₂) := by
  obtain ⟨a,ha,hi⟩ := finite_common_lift_positive_h
    T he hT hf hg hh q hq B W z u v hu hdz
  let a₀ := U ≫ XModLambdaN.incl _ (q+1)
  have ha₀ : a₀ ≫ (background.quotients.tower _).rho 1 (q+1) (by omega) =
      nativeFirstLabel T.X (B+1) W u := by
    dsimp only [a₀]
    rw [Category.assoc,(background.quotients.tower _).rho_quotient,hU]
  have hdet := first_label_detects_unshifted T.X (q+1) (by omega) (B+1) W u a₀ ha₀
  have hdet' := first_label_detects_unshifted T.X (q+1) (by omega) (B+1) W u a ha
  have hres := detects_sub_filtration (background.convergence (.quotient (q+1) (.nu T.X)))
    (B+1,W,W) hdet hdet'
  have hvfil : FiltrationAtLeast background.syntheticTower (B+q+1)
      (a ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1)) := by
    rw [hi]
    apply (regrade_filtration_iff _ _ _ _).mpr
    exact detects_filtration (.quotient (q+1) (.nu T.Y)) (B+q+1,W+q,(W+q)-q) _ _
      (finiteTopLabel_detects T.Y q hq (B+q+1) (W+q) v)
  have H := known_source_positive_h_native_residual_same_image T he hf hg hh hT
    0 (q+1) L (by omega) hL (B+1) W A₀ B₀ D (by omega) (by omega) (by omega)
    y η₀ hη hy Pm (by simpa only [Nat.cast_zero,add_zero] using hPm) hmid
  have transport (N : ℕ) (w : ℤ) (hN : 0+(q+1)=N) (hw : W-(0:ℕ)=w) :
      ∀ r : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+1) r →
      ∀ β : BiHom (W-(B+1)) w (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      β=homotopyRegrade (show (B₀-A₀)-1=W-(B+1) by omega) (show B₀+L=w by omega)
        (biSuspensionHomEquiv (B₀-A₀) B₀ L (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (η₀ ≫ XModLambdaN.proj _ L)) →
      ∀ v : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+(q+1:ℕ)-1) v →
      r ≫ XModLambdaN.map (background.nu.functor.map T.f) N = β ≫ XModLambdaN.incl _ N-v →
      ∃ e : BiHom (W-(B+1)) w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
        FiltrationAtLeast background.syntheticTower ((B+1)+(q+1:ℕ)-1) e ∧
        e ≫ XModLambdaN.map (background.nu.functor.map T.f) N =
          r ≫ XModLambdaN.map (background.nu.functor.map T.f) N := by
    subst N; subst w; exact H
  have H' := transport (q+1) W (by omega) (by omega)
  obtain ⟨e,hefil,heimage⟩ := H' (a₀-a) hres (U ≫ background.nu.functor.map T.f) hboundary
    (a ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1))
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hvfil)
    (by dsimp only [a₀]; rw [Preadditive.sub_comp,Category.assoc,
          ←XModLambdaN.incl_naturality,←Category.assoc])
  exact ordinary_full_source_top_of_residual T.X T.Y T.f q hq B W U a e v hi
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hefil) heimage


private theorem known_source_ordinary_bottom_differential_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q L : ℕ) (hq : 0 < q) (hL : 0<L) (B W A₀ B₀ D : ℤ)
    (hA : B=A₀+L) (hB : W=B₀+L) (hD : (L:ℤ)+(q+1:ℕ)≤D)
    (y : Ambient background T.Y (A₀,B₀))
    (η₀ : BiHom (B₀-A₀) B₀ (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y A₀ B₀ y)
    (hy : y ∈ cycles background T.Y (D-1) (A₀,B₀))
    (u : Ambient background T.X (B+1,W)) (z : Ambient background T.Z (B+1,W+1))
    (v : Ambient background T.Y (B+q+1,W+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      ((background.classical.map T.h).pageMap 2 (B+1,W+1) z) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (B+1,W+1) ((B+q+1)+1,(W+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (B+q+1) (W+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((B+1)+j-1+1,W+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → boundaries background T.Y ((L:ℤ)+j) ((B+1)+j-1+1,W+j) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ x : Ambient background T.X ((B+1)+j-1+1,W+j),
        x ∈ cycles background T.X (((q+1):ℤ)-j) ((B+1)+j-1+1,W+j) →
        (background.classical.map T.f).pageMap 2 ((B+1)+j-1+1,W+j) x ∈ Pm j →
        ∃ z : Ambient background T.Z ((B+1)+j-1+1,W+j+1),
          z ∈ cycles background T.Z (((q+1):ℤ)-j) ((B+1)+j-1+1,W+j+1) ∧
        ∃ u : Ambient background T.X ((B+1)+j-1+1,W+j),
          (background.classicalSuspension T.X).DesuspendsClass ((B+1)+j-1+1) (W+j+1)
            ((background.classical.map T.h).pageMap 2 ((B+1)+j-1+1,W+j+1) z) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((0:ℤ)+j+1) ((B+1)+j-1+1,W+j))
    (U : BiHom (W-(B+1)) W (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X (B+1) W u)
    (hboundary : U ≫ background.nu.functor.map T.f =
      homotopyRegrade (show (B₀-A₀)-1=W-(B+1) by omega) (show B₀+L=W by omega)
        (biSuspensionHomEquiv (B₀-A₀) B₀ L (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (η₀ ≫ XModLambdaN.proj _ L)))
    (P : Submodule ℤ (Ambient background T.Y (B+q+1,W+q)))
    (hP : permanentCycles background T.Y (B+q+1,W+q) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ a ∈ P, positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) (B+q+1) (W+q) a=0 →
      a ∈ boundaries background T.Y (L+q) (B+q+1,W+q)) :
    IsCycle background T.Y (L+q) (A₀,B₀) y ∧
      IsCycle background T.Y (L+q) (B+q+1,W+q) v ∧
      DifferentialAt background T.Y (L+q+1) (A₀,B₀) (B+q+1,W+q) y v := by
  obtain ⟨e,htop⟩ := known_source_ordinary_full_image_second
    T he hT hf hg hh q L hq hL B W A₀ B₀ D hA hB hD y η₀ hη hy
    u z v hu hdz Pm hPm hmid U hU hboundary
  let error := (background.classical.map T.f).pageMap 2 (B+q+1,W+q) e
  rw [hboundary,←regrade_comp,normalized_homotopy_regrade_trans] at htop
  obtain ⟨η,wv,hρ,hwv,hwp,herr⟩ := finite_extension_of_boundary_top_at_weight
    T.Y L q (q+1) hL hq rfl (B₀-A₀) B₀ (B+q+1) (W+q) W
      (by omega) (by omega) (by omega) η₀ (v+error) htop
  let N := L+q
  have hN : 0<N := by dsimp [N]; omega
  have ha : η ≫ (background.quotients.tower _).rho 1 N (by omega)=nativeFirstLabel T.Y A₀ B₀ y := by
    rw [←(background.quotients.tower _).rho_comp hL (show L≤N by dsimp [N];omega),
      ←Category.assoc,hρ,hη]
  let w' : Ambient background T.Y (A₀+N+1,B₀+N) :=
    topClassicalRegrade (show (B+q+1,W+q)=(A₀+N+1,B₀+N) by ext <;> dsimp [N] <;> omega) wv
  have hw' : HEq w' wv := top_classical_regrade_heq _ _
  have hb := congrArg (homotopyRegrade
    (show (W+q)-(B+q+1)=(B₀+N)-(A₀+N+1) by dsimp [N];omega)
    (show W+q=B₀+N by dsimp [N];omega)) hwv
  rw [source_native_label_transport T.Y (B+q+1) (W+q)
    (A₀+N+1) (B₀+N) (by dsimp [N];omega) (by dsimp [N];omega) wv w' hw'] at hb
  have hba : boundaryRepresentative T.Y N A₀ B₀ η ≫ XModLambdaN.incl _ 1=
      nativeFirstLabel T.Y (A₀+N+1) (B₀+N) w' := by
    simpa only [boundaryRepresentative,regrade_comp,last_layer_regrade_trans] using hb
  have hd0 : DifferentialAt background T.Y (N+1) (A₀,B₀) (A₀+N+1,B₀+N) y w' :=
    ⟨by omega,adjacent_boundary_differential T.Y N hN A₀ B₀ y w' η ha hba⟩
  have hd := classical_differential_heq T.Y (N+1) rfl
    (show (A₀+N+1,B₀+N)=(B+q+1,W+q) by ext <;> dsimp [N] <;> omega)
    y y w' wv HEq.rfl hw' hd0
  have heG : positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) (B+q+1) (W+q) error=0 := by
    exact positive_second_triangle_composite_zero T hf hg hh hT (B+q+1) (W+q) e
  have herr' : wv-v-error ∈ boundaries background T.Y (q+1) (B+q+1,W+q) := by
    have heq : wv-v-error=wv-(v+error) := by abel
    simpa only [heq] using herr
  have hd' := differential_target_of_positive_candidate_kernel T hg (N+1)
    (A₀,B₀) (B+q+1) (W+q) y wv v error P hP hd hv
    (boundaries_monotone background T.Y _ (by dsimp [N];omega) herr') heG
    (by simpa only [N,Nat.cast_add,add_sub_cancel_right] using hker)
  have hc := cycles_of_differential T.Y (N+1) _ _ y v hd'
  refine ⟨?_,?_,?_⟩
  · simpa only [N,Nat.cast_add,add_sub_cancel_right] using hc.1
  · simpa only [N,Nat.cast_add,add_sub_cancel_right] using hc.2
  · simpa only [N,Nat.cast_add,add_sub_cancel_right] using hd'


private theorem known_source_ordinary_bottom_differential_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
    (q L : ℕ) (hq : 0 < q) (hL : 0<L) (B W A₀ B₀ D : ℤ)
    (hA : B=A₀+L) (hB : W=B₀+L) (hD : (L:ℤ)+(q+1:ℕ)≤D)
    (y : Ambient background T.Y (A₀,B₀))
    (η₀ : BiHom (B₀-A₀) B₀ (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L))
    (hη : η₀ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel T.Y A₀ B₀ y)
    (hy : y ∈ cycles background T.Y (D-1) (A₀,B₀))
    (u : Ambient background T.X (B+1,W)) (z : Ambient background T.Z (B,W))
    (v : Ambient background T.Y (B+q+1,W+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) B W z)
      (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (B,W) (B+q+1,W+q) z
      ((background.classical.map T.g).pageMap 2 (B+q+1,W+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((B+1)+j-1+1,W+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → boundaries background T.Y ((L:ℤ)+j) ((B+1)+j-1+1,W+j) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ x : Ambient background T.X ((B+1)+j-1+1,W+j),
        x ∈ cycles background T.X (((q+1):ℤ)-j) ((B+1)+j-1+1,W+j) →
        (background.classical.map T.f).pageMap 2 ((B+1)+j-1+1,W+j) x ∈ Pm j →
        ∃ z : Ambient background T.Z ((B+1)+j-1,W+j),
          z ∈ cycles background T.Z (((q+1):ℤ)-j) ((B+1)+j-1,W+j) ∧
        ∃ u : Ambient background T.X ((B+1)+j-1+1,W+j),
          (background.classicalSuspension T.X).DesuspendsClass ((B+1)+j-1+1) (W+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              ((B+1)+j-1) (W+j) z) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((0:ℤ)+j+1) ((B+1)+j-1+1,W+j))
    (U : BiHom (W-(B+1)) W (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X (B+1) W u)
    (hboundary : U ≫ background.nu.functor.map T.f =
      homotopyRegrade (show (B₀-A₀)-1=W-(B+1) by omega) (show B₀+L=W by omega)
        (biSuspensionHomEquiv (B₀-A₀) B₀ L (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (η₀ ≫ XModLambdaN.proj _ L)))
    (P : Submodule ℤ (Ambient background T.Y (B+q+1,W+q)))
    (hP : permanentCycles background T.Y (B+q+1,W+q) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ a ∈ P, (background.classical.map T.g).pageMap 2 (B+q+1,W+q) a=0 →
      a ∈ boundaries background T.Y (L+q) (B+q+1,W+q)) :
    IsCycle background T.Y (L+q) (A₀,B₀) y ∧
      IsCycle background T.Y (L+q) (B+q+1,W+q) v ∧
      DifferentialAt background T.Y (L+q+1) (A₀,B₀) (B+q+1,W+q) y v := by
  obtain ⟨e,htop⟩ := known_source_ordinary_full_image_third
    T he hT hf hg hh q L hq hL B W A₀ B₀ D hA hB hD y η₀ hη hy
    u z v hu hdz Pm hPm hmid U hU hboundary
  let error := (background.classical.map T.f).pageMap 2 (B+q+1,W+q) e
  rw [hboundary,←regrade_comp,normalized_homotopy_regrade_trans] at htop
  obtain ⟨η,wv,hρ,hwv,hwp,herr⟩ := finite_extension_of_boundary_top_at_weight
    T.Y L q (q+1) hL hq rfl (B₀-A₀) B₀ (B+q+1) (W+q) W
      (by omega) (by omega) (by omega) η₀ (v+error) htop
  let N := L+q
  have hN : 0<N := by dsimp [N]; omega
  have ha : η ≫ (background.quotients.tower _).rho 1 N (by omega)=nativeFirstLabel T.Y A₀ B₀ y := by
    rw [←(background.quotients.tower _).rho_comp hL (show L≤N by dsimp [N];omega),
      ←Category.assoc,hρ,hη]
  let w' : Ambient background T.Y (A₀+N+1,B₀+N) :=
    topClassicalRegrade (show (B+q+1,W+q)=(A₀+N+1,B₀+N) by ext <;> dsimp [N] <;> omega) wv
  have hw' : HEq w' wv := top_classical_regrade_heq _ _
  have hb := congrArg (homotopyRegrade
    (show (W+q)-(B+q+1)=(B₀+N)-(A₀+N+1) by dsimp [N];omega)
    (show W+q=B₀+N by dsimp [N];omega)) hwv
  rw [source_native_label_transport T.Y (B+q+1) (W+q)
    (A₀+N+1) (B₀+N) (by dsimp [N];omega) (by dsimp [N];omega) wv w' hw'] at hb
  have hba : boundaryRepresentative T.Y N A₀ B₀ η ≫ XModLambdaN.incl _ 1=
      nativeFirstLabel T.Y (A₀+N+1) (B₀+N) w' := by
    simpa only [boundaryRepresentative,regrade_comp,last_layer_regrade_trans] using hb
  have hd0 : DifferentialAt background T.Y (N+1) (A₀,B₀) (A₀+N+1,B₀+N) y w' :=
    ⟨by omega,adjacent_boundary_differential T.Y N hN A₀ B₀ y w' η ha hba⟩
  have hd := classical_differential_heq T.Y (N+1) rfl
    (show (A₀+N+1,B₀+N)=(B+q+1,W+q) by ext <;> dsimp [N] <;> omega)
    y y w' wv HEq.rfl hw' hd0
  have heG : (background.classical.map T.g).pageMap 2 (B+q+1,W+q) error=0 := by
    exact ordinary_triangle_composite_zero T (B+q+1) (W+q) e
  have herr' : wv-v-error ∈ boundaries background T.Y (q+1) (B+q+1,W+q) := by
    have heq : wv-v-error=wv-(v+error) := by abel
    simpa only [heq] using herr
  have hd' := differential_target_of_permanent_candidate_kernel T.Y T.Z T.g (N+1)
    (A₀,B₀) (B+q+1,W+q) y wv v error P hP hd hv
    (boundaries_monotone background T.Y _ (by dsimp [N];omega) herr') heG
    (by simpa only [N,Nat.cast_add,add_sub_cancel_right] using hker)
  have hc := cycles_of_differential T.Y (N+1) _ _ y v hd'
  refine ⟨?_,?_,?_⟩
  · simpa only [N,Nat.cast_add,add_sub_cancel_right] using hc.1
  · simpa only [N,Nat.cast_add,add_sub_cancel_right] using hc.2
  · simpa only [N,Nat.cast_add,add_sub_cancel_right] using hd'


/-- The original known-source differential criterion for this ordinary-first exponent branch. -/
public theorem known_source_differential_ordinary_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (a b L : ℕ) (ha : 0 < a) (hb : 0 < b) (haL : a+1 ≤ L) (B W : ℤ)
    (x : Ambient background T.X (B+1,W)) (z₁ : Ambient background T.Z (B+1,W+1))
    (y : Ambient background T.Y (B+a+1,W+a))
    (hxz : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      ((background.classical.map T.h).pageMap 2 (B+1,W+1) z₁) (by simpa using x))
    (hdz₁ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (a+1) (B+1,W+1) ((B+a+1)+1,(W+a)+1) z₁
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (B+a+1) (W+a) y))
    (htop : ∀ j : ℕ, 1 ≤ j → j < (a+1)-1 →
      ∀ x' : Ambient background T.X (B+1+j,W+j),
        x' ∈ cycles background T.X (((a+1:ℕ):ℤ)-j) (B+1+j,W+j) →
        ∃ z₁' : Ambient background T.Z (B+1+j,W+j+1),
          z₁' ∈ cycles background T.Z (((a+1:ℕ):ℤ)-j) (B+1+j,W+j+1) ∧
          x'-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (B+1+j) (W+j) z₁' ∈
            boundaries background T.X ((j:ℤ)+1) (B+1+j,W+j))
    (u : Ambient background T.X ((B+1)+L+1,W+L))
    (_hFx : (background.classical.map T.f).pageMap 2 (B+1,W) x = 0)
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (B+1,W) ((B+1)+L+1,W+L) x u)
    (z₂ : Ambient background T.Z (((B+1)+L)+1,(W+L)+1))
    (v : Ambient background T.Y (((B+1)+L)+b+1,(W+L)+b))
    (huz : (background.classicalSuspension T.X).DesuspendsClass (((B+1)+L)+1) ((W+L)+1)
      ((background.classical.map T.h).pageMap 2 (((B+1)+L)+1,(W+L)+1) z₂) (by simpa using u))
    (hdz₂ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (b+1) (((B+1)+L)+1,(W+L)+1) ((((B+1)+L)+b+1)+1,((W+L)+b)+1) z₂
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (((B+1)+L)+b+1) ((W+L)+b) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((((B+1)+L)+1)+j-1+1,(W+L)+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(b+1)-1 → boundaries background T.Y ((L-a:ℕ)+j) ((((B+1)+L)+1)+j-1+1,(W+L)+j) ≤ Pm j)
    (hbottom : ∀ j : ℕ, 1≤j → j<(b+1)-1 →
      ∀ x : Ambient background T.X ((((B+1)+L)+1)+j-1+1,(W+L)+j),
        x ∈ cycles background T.X (((b+1):ℤ)-j) ((((B+1)+L)+1)+j-1+1,(W+L)+j) →
        (background.classical.map T.f).pageMap 2 ((((B+1)+L)+1)+j-1+1,(W+L)+j) x ∈ Pm j →
        ∃ z₂ : Ambient background T.Z ((((B+1)+L)+1)+j-1+1,(W+L)+j+1),
          z₂ ∈ cycles background T.Z (((b+1):ℤ)-j) ((((B+1)+L)+1)+j-1+1,(W+L)+j+1) ∧
        ∃ u : Ambient background T.X ((((B+1)+L)+1)+j-1+1,(W+L)+j),
          (background.classicalSuspension T.X).DesuspendsClass ((((B+1)+L)+1)+j-1+1) ((W+L)+j+1)
            ((background.classical.map T.h).pageMap 2 ((((B+1)+L)+1)+j-1+1,(W+L)+j+1) z₂) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((0:ℤ)+j+1) ((((B+1)+L)+1)+j-1+1,(W+L)+j))
    (himage : ∀ e : Ambient background T.X (B+a+1,W+a),
      (background.classical.map T.f).pageMap 2 (B+a+1,W+a) e ∈
        cycles background T.Y ((L+b-a:ℕ)+1) (B+a+1,W+a))
    (hy : y ∈ cycles background T.Y (L+b-a:ℕ) (B+a+1,W+a))
    (P : Submodule ℤ (Ambient background T.Y ((((B+1)+L)+b+1),((W+L)+b))))
    (hP : permanentCycles background T.Y ((((B+1)+L)+b+1),((W+L)+b)) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ z ∈ P, positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (((B+1)+L)+b+1) ((W+L)+b) z = 0 →
      z ∈ boundaries background T.Y (L+b-a:ℕ) ((((B+1)+L)+b+1),((W+L)+b))) :
    IsCycle background T.Y (L+b-a:ℕ) (B+a+1,W+a) y ∧
      IsCycle background T.Y (L+b-a:ℕ) ((((B+1)+L)+b+1),((W+L)+b)) v ∧
      DifferentialAt background T.Y ((L+b-a:ℕ)+1) (B+a+1,W+a) ((((B+1)+L)+b+1),((W+L)+b)) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X L (by omega)
    (B+1) W x u).mp hdx
  obtain ⟨e,η₀,wy,hinsert,hfirst,hboundary,hcong,hwy,_⟩ :=
    ordinary_source_finite_division_producer_second T he hT hf hg hh
      a L ha haL B W (L+b-a:ℕ) x z₁ y hxz hdz₁ htop ζ hζ hy
      (fun e => cycles_antitone background T.Y _ (by omega) (himage e))
  let U := boundaryRepresentative T.X L (B+1) W ζ
  have hlen : ((L-(0+a):ℕ):ℤ)+b=((L+b-a:ℕ):ℤ) := by omega
  have hbot := known_source_ordinary_bottom_differential_second T he hT hf hg hh
    b (L-(0+a)) hb (by omega) ((B+1)+L) (W+L) (B+a+1) (W+a)
    ((L+b-a:ℕ)+1) (by omega) (by omega) (by omega) wy η₀ hfirst
    (by simpa only [add_sub_cancel_right] using hwy)
    u z₂ v huz hdz₂ Pm
    (by simpa only [Nat.zero_add] using hPm) hbottom U hU hboundary P hP hv
    (by simpa only [hlen] using hker)
  rw [hlen] at hbot
  simpa only [add_sub_cancel_right] using
    differential_of_source_correction T.Y ((L+b-a:ℕ)+1) ((0+a:ℕ)+1)
      (B+a+1,W+a) ((((B+1)+L)+b+1),((W+L)+b))
      wy y ((background.classical.map T.f).pageMap 2 (B+a+1,W+a) e) v v
      hbot.2.2 hcong (himage e)
      (by rw [sub_self]; exact (boundaries background T.Y _ _).zero_mem)


/-- The original known-source differential criterion for this ordinary-first exponent branch. -/
public theorem known_source_differential_ordinary_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
    (a b L : ℕ) (ha : 0 < a) (hb : 0 < b) (haL : a+1 ≤ L) (B W : ℤ)
    (x : Ambient background T.X (B+1,W)) (z₁ : Ambient background T.Z (B,W))
    (y : Ambient background T.Y (B+a+1,W+a))
    (hxz : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) B W z₁)
      (by simpa using x))
    (hdz₁ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (a+1) (B,W) (B+a+1,W+a) z₁
      ((background.classical.map T.g).pageMap 2 (B+a+1,W+a) y))
    (htop : ∀ j : ℕ, 1 ≤ j → j < (a+1)-1 →
      ∀ x' : Ambient background T.X ((B+1)+j-1+1,W+j),
        x' ∈ cycles background T.X (((a+1:ℕ):ℤ)-j) ((B+1)+j-1+1,W+j) →
        ∃ z₁' : Ambient background T.Z ((B+1)+j-1,W+j),
          z₁' ∈ cycles background T.Z (((a+1:ℕ):ℤ)-j) ((B+1)+j-1,W+j) ∧
        ∃ u' : Ambient background T.X ((B+1)+j-1+1,W+j),
          (background.classicalSuspension T.X).DesuspendsClass ((B+1)+j-1+1) (W+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              ((B+1)+j-1) (W+j) z₁') (by simpa only [add_sub_cancel_right] using u') ∧
          x'-u' ∈ boundaries background T.X ((j:ℤ)+1) ((B+1)+j-1+1,W+j))
    (u : Ambient background T.X ((B+1)+L+1,W+L))
    (_hFx : (background.classical.map T.f).pageMap 2 (B+1,W) x = 0)
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (B+1,W) ((B+1)+L+1,W+L) x u)
    (z₂ : Ambient background T.Z (((B+1)+L),(W+L)))
    (v : Ambient background T.Y (((B+1)+L)+b+1,(W+L)+b))
    (huz : (background.classicalSuspension T.X).DesuspendsClass (((B+1)+L)+1) ((W+L)+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) ((B+1)+L) (W+L) z₂)
      (by simpa using u))
    (hdz₂ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (b+1) (((B+1)+L),(W+L)) (((B+1)+L)+b+1,(W+L)+b) z₂
      ((background.classical.map T.g).pageMap 2 (((B+1)+L)+b+1,(W+L)+b) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((((B+1)+L)+1)+j-1+1,(W+L)+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(b+1)-1 → boundaries background T.Y ((L-a:ℕ)+j) ((((B+1)+L)+1)+j-1+1,(W+L)+j) ≤ Pm j)
    (hbottom : ∀ j : ℕ, 1≤j → j<(b+1)-1 →
      ∀ x : Ambient background T.X ((((B+1)+L)+1)+j-1+1,(W+L)+j),
        x ∈ cycles background T.X (((b+1):ℤ)-j) ((((B+1)+L)+1)+j-1+1,(W+L)+j) →
        (background.classical.map T.f).pageMap 2 ((((B+1)+L)+1)+j-1+1,(W+L)+j) x ∈ Pm j →
        ∃ z₂ : Ambient background T.Z ((((B+1)+L)+1)+j-1,(W+L)+j),
          z₂ ∈ cycles background T.Z (((b+1):ℤ)-j) ((((B+1)+L)+1)+j-1,(W+L)+j) ∧
        ∃ u : Ambient background T.X ((((B+1)+L)+1)+j-1+1,(W+L)+j),
          (background.classicalSuspension T.X).DesuspendsClass ((((B+1)+L)+1)+j-1+1) ((W+L)+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              ((((B+1)+L)+1)+j-1) ((W+L)+j) z₂) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((0:ℤ)+j+1) ((((B+1)+L)+1)+j-1+1,(W+L)+j))
    (himage : ∀ e : Ambient background T.X (B+a+1,W+a),
      (background.classical.map T.f).pageMap 2 (B+a+1,W+a) e ∈
        cycles background T.Y ((L+b-a:ℕ)+1) (B+a+1,W+a))
    (hy : y ∈ cycles background T.Y (L+b-a:ℕ) (B+a+1,W+a))
    (P : Submodule ℤ (Ambient background T.Y ((((B+1)+L)+b+1),((W+L)+b))))
    (hP : permanentCycles background T.Y ((((B+1)+L)+b+1),((W+L)+b)) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ z ∈ P, (background.classical.map T.g).pageMap 2 ((((B+1)+L)+b+1),((W+L)+b)) z = 0 →
      z ∈ boundaries background T.Y (L+b-a:ℕ) ((((B+1)+L)+b+1),((W+L)+b))) :
    IsCycle background T.Y (L+b-a:ℕ) (B+a+1,W+a) y ∧
      IsCycle background T.Y (L+b-a:ℕ) ((((B+1)+L)+b+1),((W+L)+b)) v ∧
      DifferentialAt background T.Y ((L+b-a:ℕ)+1) (B+a+1,W+a) ((((B+1)+L)+b+1),((W+L)+b)) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X L (by omega)
    (B+1) W x u).mp hdx
  obtain ⟨e,η₀,wy,hinsert,hfirst,hboundary,hcong,hwy,_⟩ :=
    ordinary_source_finite_division_producer_third T he hT hf hg hh
      a L ha haL B W (L+b-a:ℕ) x z₁ y hxz hdz₁ htop ζ hζ hy
      (fun e => cycles_antitone background T.Y _ (by omega) (himage e))
  let U := boundaryRepresentative T.X L (B+1) W ζ
  have hlen : ((L-(0+a):ℕ):ℤ)+b=((L+b-a:ℕ):ℤ) := by omega
  have hbot := known_source_ordinary_bottom_differential_third T he hT hf hg hh
    b (L-(0+a)) hb (by omega) ((B+1)+L) (W+L) (B+a+1) (W+a)
    ((L+b-a:ℕ)+1) (by omega) (by omega) (by omega) wy η₀ hfirst
    (by simpa only [add_sub_cancel_right] using hwy)
    u z₂ v huz hdz₂ Pm
    (by simpa only [Nat.zero_add] using hPm) hbottom U hU hboundary P hP hv
    (by simpa only [hlen] using hker)
  rw [hlen] at hbot
  simpa only [add_sub_cancel_right] using
    differential_of_source_correction T.Y ((L+b-a:ℕ)+1) ((0+a:ℕ)+1)
      (B+a+1,W+a) ((((B+1)+L)+b+1),((W+L)+b))
      wy y ((background.classical.map T.f).pageMap 2 (B+a+1,W+a) e) v v
      hbot.2.2 hcong (himage e)
      (by rw [sub_self]; exact (boundaries background T.Y _ _).zero_mem)

end
end KIP126.ProofTools.Internal.SyntheticCoverage
