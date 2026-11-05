module

import all KIP126.ProofTools.SyntheticCoverage.SelectiveDifferential
import all KIP126.ProofTools.SyntheticCoverage.SelectiveTorsion
import all KIP126.ProofTools.SyntheticCoverage.BoundaryPermanence

/-! Restricted middle corrections using the actual full image's finite
lambda-torsion bound. The candidate spaces need contain only the indicated
true early boundaries, not every permanent cycle. -/

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

private theorem lambda_torsion_postcomp {A B : SyntheticSpectrum}
    {m w : ℤ} (k : ℕ) (a : BiHom m w A) (f : A ⟶ B)
    (ha : lambdaMultiply k a=0) : lambdaMultiply k (a≫f)=0 := by
  have h := congrArg (fun b => b≫f) ha
  simpa only [lambdaMultiply,Category.assoc,zero_comp] using h

private theorem torsion_selective_ordinary_finite_head
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N k l : ℕ) (hkN : k<N) (hl : 0<l) (s t : ℤ)
    (a : BiHom (t-s) (t-k) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (ha : FiltrationAtLeast background.syntheticTower s a)
    (β : BiHom (t-s) (t-k) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (v : BiHom (t-s) (t-k) (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (hv : FiltrationAtLeast background.syntheticTower (s+1) v)
    (himage : a ≫ XModLambdaN.map (background.nu.functor.map f) N =
      β ≫ XModLambdaN.incl _ N-v)
    (ht : lambdaMultiply l β=0) :
    ∃ x : Ambient background X (s,t),
      x ∈ cycles background X (N-k:ℕ) (s,t) ∧
      Detects (background.convergence (.quotient N (.nu X))) (s,t,t-k)
        (finiteTargetLabel background X N s t k x) a ∧
      (background.classical.map f).pageMap 2 (s,t) x ∈ boundaries background Y ((k:ℤ)+l+1) (s,t) := by
  obtain ⟨x,hx,hxa⟩ := middle_finite_filtration_label X N k hkN s t a ha
  refine ⟨x,hx,hxa,?_⟩
  have hmap := detects_map (.quotient N (.nu X)) (.quotient N (.nu Y))
    (XModLambdaN.map (background.nu.functor.map f) N) (s,t,t-k) _ a hxa
  erw [←middle_finite_label_as_weight,finite_weight_label_natural X Y f N s t (t-k) (by omega) x,
    middle_finite_label_as_weight] at hmap
  apply finite_torsion_label_boundary_of_next_filtration Y N k l hkN hl s t _ _ β hmap ?_ ht
  rw [himage]
  simpa only [sub_sub_cancel] using hv

private theorem torsion_selective_positive_h_native_step
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (k q l : ℕ) (hq : 0<q) (hl : 0<l) (s t : ℤ)
    (P : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (hP : boundaries background T.Y ((k:ℤ)+l+1) (s+1,t) ≤ P)
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
    (v : BiHom (t-(s+1)) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (k+q)))
    (hv : FiltrationAtLeast background.syntheticTower (s+2) v)
    (himage : a ≫ XModLambdaN.map (background.nu.functor.map T.f) (k+q)=
      β ≫ XModLambdaN.incl _ (k+q)-v)
    (ht : lambdaMultiply l β=0) :
    ∃ b : BiHom (t-(s+1)) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)),
      FiltrationAtLeast background.syntheticTower (s+2) b ∧
      b ≫ XModLambdaN.map (background.nu.functor.map T.f) (k+q)=
      a ≫ XModLambdaN.map (background.nu.functor.map T.f) (k+q) := by
  obtain ⟨x,hxc,hxd,hxp⟩ := torsion_selective_ordinary_finite_head T.X T.Y T.f
    (k+q) k l (by omega) hl (s+1) t a ha β v (by simpa only [show s+1+1=s+2 by omega] using hv) himage ht
  obtain ⟨z,hz,u,hu,hxu⟩ := hmid x (by simpa only [Nat.add_sub_cancel_left] using hxc) (hP hxp)
  obtain ⟨b,hb,hbz⟩ := middle_positive_h_native_cycle_image T he hf hg hh hT
    k q hq s t z hz u hu
  have hnext := middle_finite_congruent_difference T.X (k+q) k (by omega)
    (s+1) t x u hxu a b hxd hb
  refine ⟨a-b,?_,?_⟩
  · simpa only [show s+1+1=s+2 by omega] using hnext
  · rw [Preadditive.sub_comp,hbz,sub_zero]

/-- Coordinate-only wrapper for a fixed finite representative. -/
private theorem torsion_selective_positive_h_native_step_regraded
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (N k q l : ℕ) (hq : 0<q) (hl : 0<l) (hN : N=k+q) (s t m w : ℤ)
    (hm : m=t-(s+1)) (hw : w=t-k)
    (P : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (hP : boundaries background T.Y ((k:ℤ)+l+1) (s+1,t) ≤ P)
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
    (v : BiHom m w (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N))
    (hv : FiltrationAtLeast background.syntheticTower (s+2) v)
    (himage : a ≫ XModLambdaN.map (background.nu.functor.map T.f) N=
      β ≫ XModLambdaN.incl _ N-v)
    (ht : lambdaMultiply l β=0) :
    ∃ b : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower (s+2) b ∧
      b ≫ XModLambdaN.map (background.nu.functor.map T.f) N=
      a ≫ XModLambdaN.map (background.nu.functor.map T.f) N := by
  subst N; subst m; subst w
  exact torsion_selective_positive_h_native_step T he hf hg hh hT k q l hq hl s t P hP hmid a ha β v hv himage ht


/-- Repeated restricted positive-H corrections keep the same full image
and produce a last-layer residual. The spaces P_j are used only after
membership of the actual residual head has been established. -/
private theorem torsion_selective_positive_h_native_residual_same_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (c K l : ℕ) (hK : 2≤K) (hl : 0<l) (S V : ℤ)
    (P : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j-1+1,V+j)))
    (hP : ∀ j : ℕ, 1≤j → j<K-1 → boundaries background T.Y ((c:ℤ)+j+l+1) (S+j-1+1,V+j) ≤ P j)
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
    (v : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (c+K)))
    (hv : FiltrationAtLeast background.syntheticTower (S+K-1) v)
    (himage : a ≫ XModLambdaN.map (background.nu.functor.map T.f) (c+K)=
      β ≫ XModLambdaN.incl _ (c+K)-v)
    (ht : lambdaMultiply l β=0) :
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
    have H := torsion_selective_positive_h_native_step_regraded T he hf hg hh hT
      (c+K) (c+j) (K-j) l (by omega) hl (by omega)
      (S+j-1) (V+j) (V-S) (V-c) (by omega) (by omega)
      (P j) (by simpa only [Nat.cast_add] using hP j hj hjK)
      (by simpa only [Nat.cast_sub (show j≤K by omega),Nat.cast_add,Nat.cast_one] using hmid j hj hjK)
      b (by simpa only [sub_add_cancel] using hb) β v
      (background.syntheticTower.filtrationSubmodule_antitone _ _ (by omega) hv)
      (hi.trans himage) ht
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
private theorem torsion_selective_positive_g_native_step
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (k q l : ℕ) (hq : 0<q) (hl : 0<l) (s t : ℤ)
    (P : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (hP : boundaries background T.Y ((k:ℤ)+l+1) (s+1,t) ≤ P)
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
    (v : BiHom (t-(s+1)) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (k+q)))
    (hv : FiltrationAtLeast background.syntheticTower (s+2) v)
    (himage : a ≫ XModLambdaN.map (background.nu.functor.map T.f) (k+q)=
      β ≫ XModLambdaN.incl _ (k+q)-v)
    (ht : lambdaMultiply l β=0) :
    ∃ b : BiHom (t-(s+1)) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)),
      FiltrationAtLeast background.syntheticTower (s+2) b ∧
      b ≫ XModLambdaN.map (background.nu.functor.map T.f) (k+q)=
      a ≫ XModLambdaN.map (background.nu.functor.map T.f) (k+q) := by
  obtain ⟨x,hxc,hxd,hxp⟩ := torsion_selective_ordinary_finite_head T.X T.Y T.f
    (k+q) k l (by omega) hl (s+1) t a ha β v (by simpa only [show s+1+1=s+2 by omega] using hv) himage ht
  obtain ⟨z,hz,u,hu,hxu⟩ := hmid x (by simpa only [Nat.add_sub_cancel_left] using hxc) (hP hxp)
  obtain ⟨b,hb,hbz⟩ := selective_positive_g_native_cycle_image T he hf hg hh hT
    k q hq s t z hz u hu
  have hnext := middle_finite_congruent_difference T.X (k+q) k (by omega)
    (s+1) t x u hxu a b hxd hb
  refine ⟨a-b,?_,?_⟩
  · simpa only [show s+1+1=s+2 by omega] using hnext
  · rw [Preadditive.sub_comp,hbz,sub_zero]

/-- Coordinate-only wrapper for a fixed finite representative. -/
private theorem torsion_selective_positive_g_native_step_regraded
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (N k q l : ℕ) (hq : 0<q) (hl : 0<l) (hN : N=k+q) (s t m w : ℤ)
    (hm : m=t-(s+1)) (hw : w=t-k)
    (P : Submodule ℤ (Ambient background T.Y (s+1,t)))
    (hP : boundaries background T.Y ((k:ℤ)+l+1) (s+1,t) ≤ P)
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
    (v : BiHom m w (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N))
    (hv : FiltrationAtLeast background.syntheticTower (s+2) v)
    (himage : a ≫ XModLambdaN.map (background.nu.functor.map T.f) N=
      β ≫ XModLambdaN.incl _ N-v)
    (ht : lambdaMultiply l β=0) :
    ∃ b : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower (s+2) b ∧
      b ≫ XModLambdaN.map (background.nu.functor.map T.f) N=
      a ≫ XModLambdaN.map (background.nu.functor.map T.f) N := by
  subst N; subst m; subst w
  exact torsion_selective_positive_g_native_step T he hf hg hh hT k q l hq hl s t P hP hmid a ha β v hv himage ht


/-- Repeated restricted positive-G corrections keep the same full image
and produce a last-layer residual. The spaces P_j are used only after
membership of the actual residual head has been established. -/
private theorem torsion_selective_positive_g_native_residual_same_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (c K l : ℕ) (hK : 2≤K) (hl : 0<l) (S V : ℤ)
    (P : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j-1+1,V+j)))
    (hP : ∀ j : ℕ, 1≤j → j<K-1 → boundaries background T.Y ((c:ℤ)+j+l+1) (S+j-1+1,V+j) ≤ P j)
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
    (v : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (c+K)))
    (hv : FiltrationAtLeast background.syntheticTower (S+K-1) v)
    (himage : a ≫ XModLambdaN.map (background.nu.functor.map T.f) (c+K)=
      β ≫ XModLambdaN.incl _ (c+K)-v)
    (ht : lambdaMultiply l β=0) :
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
    have H := torsion_selective_positive_g_native_step_regraded T he hf hg hh hT
      (c+K) (c+j) (K-j) l (by omega) hl (by omega)
      (S+j-1) (V+j) (V-S) (V-c) (by omega) (by omega)
      (P j) (by simpa only [Nat.cast_add] using hP j hj hjK)
      (by simpa only [Nat.cast_sub (show j≤K by omega),Nat.cast_add,Nat.cast_one] using hmid j hj hjK)
      b (by simpa only [sub_add_cancel] using hb) β v
      (background.syntheticTower.filtrationSubmodule_antitone _ _ (by omega) hv)
      (hi.trans himage) ht
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


private theorem ordinary_boundary_native_full_projection_torsion
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (N : ℕ) (hN : 0<N) (c k : ℕ) (hc : (c:ℤ)=k-1) (s t : ℤ)
    (ex : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ N ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ N))
    (x : Ambient background T.X (s,t)) :
    ∃ U : BiHom ((t+k)-((s+k)+1)) (t+k-c) (background.nu.functor.obj (T.X.obj background.auxiliary)),
      positiveHSourceDesuspend T he hf N c (s+k) (t+k) ε
        (homotopyRegrade (by omega) (by omega)
          (ordinaryNormalizedFirstFiniteBoundary T he hf N hN s t ex x))=
        U ≫ XModLambdaN.incl _ N ∧ lambdaMultiply 1 U=0 := by
  let U := biSuspensionHomEquiv (t-s) t (1:ℕ)
    (background.nu.functor.obj (T.X.obj background.auxiliary))
    (nativeFirstLabel T.X s t x ≫ XModLambdaN.proj _ 1)
  refine ⟨homotopyRegrade (show t-s-1=(t+k)-((s+k)+1) by omega)
    (show t+(1:ℕ)=t+k-c by omega) U,?_,?_⟩
  · have heq := ordinary_normalized_boundary_desuspend_eq T he hf N hN s t ex hex ε hε x
    have hr := quotient_unshift_regrade T.X (1,0) (t-s-1,t+(1:ℕ))
      ((t+k)-((s+k)+1),t+k-c) N ε (by dsimp; omega) (by dsimp; omega)
      (homotopyRegrade (by dsimp; omega) (by simp)
        (ordinaryNormalizedFirstFiniteBoundary T he hf N hN s t ex x ≫
          XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom N))
    dsimp only [positiveHSourceDesuspend]
    simp only [homotopyRegrade_comp,normalized_homotopy_regrade_trans] at hr heq ⊢
    rw [hr,heq,finiteTowerBoundary_eq,regrade_comp]

  · rw [lambda_regrade]
    have hz := absolute_boundary_lambda_zero (background.nu.functor.obj (T.X.obj background.auxiliary))
      (t-s) t 1 (nativeFirstLabel T.X s t x)
    simp only [U,hz,regrade_precomp,comp_zero]

/-- Finite-torsion variant of the original restricted middle criterion. -/
private theorem differential_of_torsion_selective_middle_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u : Ambient background T.X ((s+(c+1))+1,t+(c+1)))
    (z : Ambient background T.Z (s+(c+1),t+(c+1)))
    (v : Ambient background T.Y ((s+(c+1))+q+1,(t+(c+1))+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass ((s+(c+1))+1) ((t+(c+1))+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
        (s+(c+1)) (t+(c+1)) z) (by simpa using u))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      ((c+1)+1) (s,t) ((s+(c+1))+1,t+(c+1)) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+(c+1),t+(c+1)) ((s+(c+1))+q+1,(t+(c+1))+q) z
      ((background.classical.map T.g).pageMap 2 ((s+(c+1))+q+1,(t+(c+1))+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y
      (((s+(c+1))+1)+j-1+1,(t+(c+1))+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → boundaries background T.Y ((c:ℤ)+j+2)
      (((s+(c+1))+1)+j-1+1,(t+(c+1))+j) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ a : Ambient background T.X (((s+(c+1))+1)+j-1+1,(t+(c+1))+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j)
          (((s+(c+1))+1)+j-1+1,(t+(c+1))+j) →
        (background.classical.map T.f).pageMap 2
          (((s+(c+1))+1)+j-1+1,(t+(c+1))+j) a ∈ Pm j →
        ∃ z' : Ambient background T.Z (((s+(c+1))+1)+j-1,(t+(c+1))+j),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j)
            (((s+(c+1))+1)+j-1,(t+(c+1))+j) ∧
        ∃ u' : Ambient background T.X (((s+(c+1))+1)+j-1+1,(t+(c+1))+j),
          (background.classicalSuspension T.X).DesuspendsClass
            (((s+(c+1))+1)+j-1+1) ((t+(c+1))+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              (((s+(c+1))+1)+j-1) ((t+(c+1))+j) z')
            (by simpa only [add_sub_cancel_right] using u') ∧
          a-u' ∈ boundaries background T.X ((j:ℤ)+1)
            (((s+(c+1))+1)+j-1+1,(t+(c+1))+j))
    (P : Submodule ℤ (Ambient background T.Y ((s+(c+1))+q+1,(t+(c+1))+q)))
    (hP : permanentCycles background T.Y ((s+(c+1))+q+1,(t+(c+1))+q) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ a ∈ P,
      (background.classical.map T.g).pageMap 2 ((s+(c+1))+q+1,(t+(c+1))+q) a=0 →
      a ∈ boundaries background T.Y (c+(q+1))
        ((s+(c+1))+q+1,(t+(c+1))+q)) :
    let y := (background.classical.map T.f).pageMap 2 (s,t) x
    IsCycle background T.Y (c+(q+1)) (s,t) y ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s,t)
        ((s+(c+1))+q+1,(t+(c+1))+q) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  let N := c+(q+1)
  have hN : 0<N := by dsimp [N]; omega
  let B := s+(c+1)
  let W := t+(c+1)
  obtain ⟨ex,hex⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.X.obj background.auxiliary)) N
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) (q+1)
  obtain ⟨eY,heY⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) N
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) N
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  let d := homotopyRegrade (show t-s=W-B by dsimp [B,W]; omega)
    (show t+1=W-c by dsimp [W]; omega)
    (ordinaryNormalizedFirstFiniteBoundary T he hf N hN s t ex x)
  have hd := ordinary_first_finite_boundary_source_detects T he hf (c+1) N c
    (by omega) hN (by omega) s t x u hdx ex hex ε hε
  obtain ⟨a,ha,hi,_,_⟩ := positive_third_finite_core T he hT hf hg hh
    c q hq B W z u v hu hdz ey hey ε hε
  have hdiff := detects_sub_filtration
    (background.convergence (.quotient N (.nu T.X))) (B+1,W,W-c) hd ha
  change FiltrationAtLeast background.syntheticTower ((B+1)+1)
    (positiveHSourceDesuspend T he hf N c B W ε d -
      positiveHSourceDesuspend T he hf N c B W ε a) at hdiff
  rw [←positive_h_source_desuspend_sub] at hdiff
  let dn := positiveHSourceDesuspend T he hf N c B W ε d
  let an := positiveHSourceDesuspend T he hf N c B W ε a
  have hcommon := congrArg (fun k => k ≫ eY.hom) hi
  have htop := finite_may_signed_target_eq_top_at_level T.Y c q hq B W v ey eY hey heY
  have hcommon' : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N ≫ eY.hom =
      ordinarySuspendedRepresentative _ (W-B) (W-c) (finiteMayTopLabel T.Y c q hq B W v) := by
    simpa only [Category.assoc] using hcommon.trans htop
  have hnativeCommon := ordinary_suspended_representative_injective _ (W-B) (W-c)
    ((native_ordinary_image_eq_raw_image T he hf N c hN B W ε hε eY heY a).symm.trans hcommon')
  have hvfil : FiltrationAtLeast background.syntheticTower (B+q+1)
      (an ≫ XModLambdaN.map (background.nu.functor.map T.f) N) := by
    apply (regrade_filtration_iff (show W-(B+1)=(W-B)-1 by omega) rfl (B+q+1) _).mp
    rw [show homotopyRegrade (show W-(B+1)=(W-B)-1 by omega) rfl
      (an ≫ XModLambdaN.map (background.nu.functor.map T.f) N)=finiteMayTopLabel T.Y c q hq B W v
      from hnativeCommon]
    exact (regrade_filtration_iff _ _ _ _).mp (detects_filtration
      (.quotient N (.nu T.Y)) (B+q+1,W+q,W-c) _ _
      (finite_may_top_label_detects T.Y c q hq B W v))
  obtain ⟨U,hU,hUt⟩ := ordinary_boundary_native_full_projection_torsion T he hf N hN c (c+1)
    (by omega) s t ex hex ε hε x
  change dn=U ≫ XModLambdaN.incl _ N at hU
  have hdnimage : dn ≫ XModLambdaN.map (background.nu.functor.map T.f) N=
      (U ≫ background.nu.functor.map T.f) ≫ XModLambdaN.incl _ N := by
    rw [hU,Category.assoc]
    erw [←XModLambdaN.incl_naturality (background.nu.functor.map T.f) N]
    exact (Category.assoc _ _ _).symm
  have hdiff' : FiltrationAtLeast background.syntheticTower ((B+1)+1) (dn-an) := by
    simpa only [dn,an,positive_h_source_desuspend_sub] using hdiff
  obtain ⟨en,hefil,heimage⟩ := torsion_selective_positive_h_native_residual_same_image
    T he hf hg hh hT c (q+1) 1 (by omega) (by omega) (B+1) W Pm
    (fun j hj hjq => by simpa only [Nat.cast_one,show (c:ℤ)+j+1+1=c+j+2 by omega] using hPm j hj hjq)
    (fun j hj hjq b hb hbp => by
      obtain ⟨z',hz',u',hu',hbu⟩ := hmid j hj hjq b hb hbp
      exact ⟨z',hz',u',hu',boundaries_monotone background T.X _ (by omega) hbu⟩)
    (dn-an) hdiff' (U ≫ background.nu.functor.map T.f)
    (an ≫ XModLambdaN.map (background.nu.functor.map T.f) N)
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hvfil)
    (by rw [Preadditive.sub_comp,hdnimage])
    (by exact lambda_torsion_postcomp 1 U (background.nu.functor.map T.f) hUt)
  have hefil' : FiltrationAtLeast background.syntheticTower (B+q+1) en := by
    simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hefil
  obtain ⟨e₂,herrorTop⟩ := last_layer_ordinary_image_eq_finite_may_top
    T.X T.Y T.f c q hq B W en hefil'
  let error := (background.classical.map T.f).pageMap 2 (B+q+1,W+q) e₂
  have hnativeSum : homotopyRegrade (show W-(B+1)=(W-B)-1 by omega) rfl
      (dn ≫ XModLambdaN.map (background.nu.functor.map T.f) N)=
      finiteMayTopLabel T.Y c q hq B W (v+error) := by
    have hsum : dn ≫ XModLambdaN.map (background.nu.functor.map T.f) N=
        an ≫ XModLambdaN.map (background.nu.functor.map T.f) N+
          en ≫ XModLambdaN.map (background.nu.functor.map T.f) N := by
      rw [heimage,Preadditive.sub_comp]
      abel
    rw [hsum,regrade_add,hnativeCommon,herrorTop,finite_may_top_label_add]
  let f := XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
    (normalizedTriangle background T he).mor₁) N ≫ eY.hom
  have himage : d ≫ f = ordinarySuspendedRepresentative _ (W-B) (W-c)
      (finiteMayTopLabel T.Y c q hq B W (v+error)) := by
    have hraw := native_ordinary_image_eq_raw_image T he hf N c hN B W ε hε eY heY d
    rw [show homotopyRegrade (show W-(B+1)=(W-B)-1 by omega) rfl
      (positiveHSourceDesuspend T he hf N c B W ε d ≫ XModLambdaN.map (background.nu.functor.map T.f) N)=
      finiteMayTopLabel T.Y c q hq B W (v+error) from hnativeSum] at hraw
    simpa only [f,Category.assoc] using hraw
  have hdecoded : IsCycle background T.Y (c+(q+1)) (s,t)
      ((background.classical.map T.f).pageMap 2 (s,t) x) ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s,t) (B+q+1,W+q)
        ((background.classical.map T.f).pageMap 2 (s,t) x) (v+error) := by
    apply ordinary_boundary_image_decode_coordinates T he hf N hN s t (B+q+1) (W+q)
      (W-B) (W-c) (by dsimp [B,N]; omega) (by dsimp [W,N]; omega)
      (by dsimp [B,W]; omega) (by dsimp [W]; omega) x (v+error) ex eY hex heY
      (finiteMayTopLabel T.Y c q hq B W (v+error))
      (finite_may_top_label_detects T.Y c q hq B W (v+error))
    apply homotopy_regrade_injective (show t-s=W-B by dsimp [B,W]; omega)
      (show t+1=W-c by dsimp [W]; omega)
    simpa only [d,f,regrade_comp,regrade_transitive,positive_g_regrade_self,Category.assoc] using himage
  refine ⟨hdecoded.1,?_⟩
  exact differential_target_of_permanent_candidate_kernel T.Y T.Z T.g (c+(q+1)+1)
    (s,t) (B+q+1,W+q) _ (v+error) v error P hP hdecoded.2 hv
    (by have hz : (v+error)-v-error=0 := by abel
        rw [hz]
        exact (boundaries background T.Y (c+(q+1)+1-1) _).zero_mem)
    (ordinary_triangle_composite_zero T (B+q+1) (W+q) e₂)
    (by simpa only [add_sub_cancel_right] using hker)


/-- Finite-torsion variant of the original restricted middle criterion. -/
private theorem differential_of_torsion_selective_middle_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u : Ambient background T.X ((s+(c+1))+1,t+(c+1)))
    (z : Ambient background T.Z ((s+(c+1))+1,(t+(c+1))+1))
    (v : Ambient background T.Y ((s+(c+1))+q+1,(t+(c+1))+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass ((s+(c+1))+1) ((t+(c+1))+1)
      ((background.classical.map T.h).pageMap 2 ((s+(c+1))+1,(t+(c+1))+1) z) (by simpa using u))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      ((c+1)+1) (s,t) ((s+(c+1))+1,t+(c+1)) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) ((s+(c+1))+1,(t+(c+1))+1)
      (((s+(c+1))+q+1)+1,((t+(c+1))+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        ((s+(c+1))+q+1) ((t+(c+1))+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y
      (((s+(c+1))+1)+j-1+1,(t+(c+1))+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → boundaries background T.Y ((c:ℤ)+j+2)
      (((s+(c+1))+1)+j-1+1,(t+(c+1))+j) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ a : Ambient background T.X (((s+(c+1))+1)+j-1+1,(t+(c+1))+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j)
          (((s+(c+1))+1)+j-1+1,(t+(c+1))+j) →
        (background.classical.map T.f).pageMap 2
          (((s+(c+1))+1)+j-1+1,(t+(c+1))+j) a ∈ Pm j →
        ∃ z' : Ambient background T.Z (((s+(c+1))+1)+j-1+1,(t+(c+1))+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j)
            (((s+(c+1))+1)+j-1+1,(t+(c+1))+j+1) ∧
        ∃ u' : Ambient background T.X (((s+(c+1))+1)+j-1+1,(t+(c+1))+j),
          (background.classicalSuspension T.X).DesuspendsClass
            (((s+(c+1))+1)+j-1+1) ((t+(c+1))+j+1)
            ((background.classical.map T.h).pageMap 2
              (((s+(c+1))+1)+j-1+1,(t+(c+1))+j+1) z')
            (by simpa only [add_sub_cancel_right] using u') ∧
          a-u' ∈ boundaries background T.X ((j:ℤ)+1)
            (((s+(c+1))+1)+j-1+1,(t+(c+1))+j))
    (P : Submodule ℤ (Ambient background T.Y ((s+(c+1))+q+1,(t+(c+1))+q)))
    (hP : permanentCycles background T.Y ((s+(c+1))+q+1,(t+(c+1))+q) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ a ∈ P,
      positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        ((s+(c+1))+q+1) ((t+(c+1))+q) a=0 →
      a ∈ boundaries background T.Y (c+(q+1))
        ((s+(c+1))+q+1,(t+(c+1))+q)) :
    let y := (background.classical.map T.f).pageMap 2 (s,t) x
    IsCycle background T.Y (c+(q+1)) (s,t) y ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s,t)
        ((s+(c+1))+q+1,(t+(c+1))+q) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  let N := c+(q+1)
  have hN : 0<N := by dsimp [N]; omega
  let B := s+(c+1)
  let W := t+(c+1)
  obtain ⟨ex,hex⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.X.obj background.auxiliary)) N
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) (q+1)
  obtain ⟨eY,heY⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) N
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) N
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  let d := homotopyRegrade (show t-s=W-B by dsimp [B,W]; omega)
    (show t+1=W-c by dsimp [W]; omega)
    (ordinaryNormalizedFirstFiniteBoundary T he hf N hN s t ex x)
  have hd := ordinary_first_finite_boundary_source_detects T he hf (c+1) N c
    (by omega) hN (by omega) s t x u hdx ex hex ε hε
  obtain ⟨_,a,ha,hi,_⟩ := positive_second_finite_core T he hT hf hg hh
    c q hq B W z u v hu hdz ey hey ε hε
  have hdiff := detects_sub_filtration
    (background.convergence (.quotient N (.nu T.X))) (B+1,W,W-c) hd ha
  change FiltrationAtLeast background.syntheticTower ((B+1)+1)
    (positiveHSourceDesuspend T he hf N c B W ε d -
      positiveHSourceDesuspend T he hf N c B W ε a) at hdiff
  rw [←positive_h_source_desuspend_sub] at hdiff
  let dn := positiveHSourceDesuspend T he hf N c B W ε d
  let an := positiveHSourceDesuspend T he hf N c B W ε a
  have hcommon := congrArg (fun k => k ≫ eY.hom) hi
  have htop := finite_may_signed_target_eq_top_at_level T.Y c q hq B W v ey eY hey heY
  have hcommon' : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N ≫ eY.hom =
      ordinarySuspendedRepresentative _ (W-B) (W-c) (finiteMayTopLabel T.Y c q hq B W v) := by
    simpa only [Category.assoc] using hcommon.trans htop
  have hnativeCommon := ordinary_suspended_representative_injective _ (W-B) (W-c)
    ((native_ordinary_image_eq_raw_image T he hf N c hN B W ε hε eY heY a).symm.trans hcommon')
  have hvfil : FiltrationAtLeast background.syntheticTower (B+q+1)
      (an ≫ XModLambdaN.map (background.nu.functor.map T.f) N) := by
    apply (regrade_filtration_iff (show W-(B+1)=(W-B)-1 by omega) rfl (B+q+1) _).mp
    rw [show homotopyRegrade (show W-(B+1)=(W-B)-1 by omega) rfl
      (an ≫ XModLambdaN.map (background.nu.functor.map T.f) N)=finiteMayTopLabel T.Y c q hq B W v
      from hnativeCommon]
    exact (regrade_filtration_iff _ _ _ _).mp (detects_filtration
      (.quotient N (.nu T.Y)) (B+q+1,W+q,W-c) _ _
      (finite_may_top_label_detects T.Y c q hq B W v))
  obtain ⟨U,hU,hUt⟩ := ordinary_boundary_native_full_projection_torsion T he hf N hN c (c+1)
    (by omega) s t ex hex ε hε x
  change dn=U ≫ XModLambdaN.incl _ N at hU
  have hdnimage : dn ≫ XModLambdaN.map (background.nu.functor.map T.f) N=
      (U ≫ background.nu.functor.map T.f) ≫ XModLambdaN.incl _ N := by
    rw [hU,Category.assoc]
    erw [←XModLambdaN.incl_naturality (background.nu.functor.map T.f) N]
    exact (Category.assoc _ _ _).symm
  have hdiff' : FiltrationAtLeast background.syntheticTower ((B+1)+1) (dn-an) := by
    simpa only [dn,an,positive_h_source_desuspend_sub] using hdiff
  obtain ⟨en,hefil,heimage⟩ := torsion_selective_positive_g_native_residual_same_image
    T he hf hg hh hT c (q+1) 1 (by omega) (by omega) (B+1) W Pm
    (fun j hj hjq => by simpa only [Nat.cast_one,show (c:ℤ)+j+1+1=c+j+2 by omega] using hPm j hj hjq)
    (fun j hj hjq b hb hbp => by
      obtain ⟨z',hz',u',hu',hbu⟩ := hmid j hj hjq b hb hbp
      exact ⟨z',hz',u',hu',boundaries_monotone background T.X _ (by omega) hbu⟩)
    (dn-an) hdiff' (U ≫ background.nu.functor.map T.f)
    (an ≫ XModLambdaN.map (background.nu.functor.map T.f) N)
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hvfil)
    (by rw [Preadditive.sub_comp,hdnimage])
    (by exact lambda_torsion_postcomp 1 U (background.nu.functor.map T.f) hUt)
  have hefil' : FiltrationAtLeast background.syntheticTower (B+q+1) en := by
    simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hefil
  obtain ⟨e₂,herrorTop⟩ := last_layer_ordinary_image_eq_finite_may_top
    T.X T.Y T.f c q hq B W en hefil'
  let error := (background.classical.map T.f).pageMap 2 (B+q+1,W+q) e₂
  have hnativeSum : homotopyRegrade (show W-(B+1)=(W-B)-1 by omega) rfl
      (dn ≫ XModLambdaN.map (background.nu.functor.map T.f) N)=
      finiteMayTopLabel T.Y c q hq B W (v+error) := by
    have hsum : dn ≫ XModLambdaN.map (background.nu.functor.map T.f) N=
        an ≫ XModLambdaN.map (background.nu.functor.map T.f) N+
          en ≫ XModLambdaN.map (background.nu.functor.map T.f) N := by
      rw [heimage,Preadditive.sub_comp]
      abel
    rw [hsum,regrade_add,hnativeCommon,herrorTop,finite_may_top_label_add]
  let f := XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
    (normalizedTriangle background T he).mor₁) N ≫ eY.hom
  have himage : d ≫ f = ordinarySuspendedRepresentative _ (W-B) (W-c)
      (finiteMayTopLabel T.Y c q hq B W (v+error)) := by
    have hraw := native_ordinary_image_eq_raw_image T he hf N c hN B W ε hε eY heY d
    rw [show homotopyRegrade (show W-(B+1)=(W-B)-1 by omega) rfl
      (positiveHSourceDesuspend T he hf N c B W ε d ≫ XModLambdaN.map (background.nu.functor.map T.f) N)=
      finiteMayTopLabel T.Y c q hq B W (v+error) from hnativeSum] at hraw
    simpa only [f,Category.assoc] using hraw
  have hdecoded : IsCycle background T.Y (c+(q+1)) (s,t)
      ((background.classical.map T.f).pageMap 2 (s,t) x) ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s,t) (B+q+1,W+q)
        ((background.classical.map T.f).pageMap 2 (s,t) x) (v+error) := by
    apply ordinary_boundary_image_decode_coordinates T he hf N hN s t (B+q+1) (W+q)
      (W-B) (W-c) (by dsimp [B,N]; omega) (by dsimp [W,N]; omega)
      (by dsimp [B,W]; omega) (by dsimp [W]; omega) x (v+error) ex eY hex heY
      (finiteMayTopLabel T.Y c q hq B W (v+error))
      (finite_may_top_label_detects T.Y c q hq B W (v+error))
    apply homotopy_regrade_injective (show t-s=W-B by dsimp [B,W]; omega)
      (show t+1=W-c by dsimp [W]; omega)
    simpa only [d,f,regrade_comp,regrade_transitive,positive_g_regrade_self,Category.assoc] using himage
  refine ⟨hdecoded.1,?_⟩
  exact differential_target_of_positive_candidate_kernel T hg (c+(q+1)+1)
    (s,t) (B+q+1) (W+q) _ (v+error) v error P hP hdecoded.2 hv
    (by have hz : (v+error)-v-error=0 := by abel
        rw [hz]
        exact (boundaries background T.Y (c+(q+1)+1-1) _).zero_mem)
    (positive_second_triangle_composite_zero T hf hg hh hT (B+q+1) (W+q) e₂)
    (by simpa only [add_sub_cancel_right] using hker)


end
end KIP126.ProofTools.Internal.SyntheticCoverage
