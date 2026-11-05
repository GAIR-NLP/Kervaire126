module

public import KIP126.ProofTools.SyntheticCoverage.BoundaryPermanence

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.SelectiveBoundaryDifferential
import all KIP126.ProofTools.SyntheticCoverage.SelectiveDifferentialMain
import all KIP126.ProofTools.SyntheticCoverage.HigherEarlyDifferential
import all KIP126.ProofTools.SyntheticCoverage.LambdaTranslate

/-! Positive-source finite-torsion refinements of the restricted middle
criterion and the earlier-boundary target comparison. -/

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

private theorem torsion_selective_positive_f_finite_head
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N k l : ℕ) (hk : 0<k) (hkN : k<N) (hl : 0<l) (s t : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ N))
    (a : BiHom (t-s) (t-k) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (ha : FiltrationAtLeast background.syntheticTower s a)
    (β : BiHom (t-s) ((t-k)+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (v : BiHom (t-s) ((t-k)+1) (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N))
    (hv : FiltrationAtLeast background.syntheticTower (s+2) v)
    (himage : positiveFiniteImage T hf N ε (t-s) (t-k) a=β ≫ XModLambdaN.incl _ N-v)
    (ht : lambdaMultiply l β=0) :
    ∃ x : Ambient background T.X (s,t),
      x ∈ cycles background T.X (N-k:ℕ) (s,t) ∧
      Detects (background.convergence (.quotient N (.nu T.X))) (s,t,t-k)
        (finiteTargetLabel background T.X N s t k x) a ∧
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈
        boundaries background T.Y ((k:ℤ)+l+1) (s+1,t+1) := by
  obtain ⟨x,hx,hxa⟩ := middle_finite_filtration_label T.X N k hkN s t a ha
  refine ⟨x,hx,hxa,?_⟩
  have hmap := selective_positive_image_detects T hf N k hk hkN s t ε hε x a hxa
  let β' := homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
    (show (t-k)+1=(t+1)-k by omega) β
  apply finite_torsion_label_boundary_of_next_filtration T.Y N k l hkN hl (s+1) (t+1) _ _ β' hmap ?_ ?_
  · have h := congrArg (homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
      (show (t-k)+1=(t+1)-k by omega)) himage
    erw [h]
    simp only [β',regrade_precomp,Preadditive.comp_sub,Category.assoc,sub_sub_cancel]
    have hv' := (regrade_filtration_iff (show t-s=(t+1)-(s+1) by omega)
      (show (t-k)+1=(t+1)-k by omega) (s+2) v).mpr hv
    simpa only [regrade_precomp,show s+1+1=s+2 by omega] using hv'
  · dsimp only [β']
    rw [lambda_regrade,ht,regrade_zero]

/-- A single genuinely restricted positive-F correction of the actual
head, through the ordinary H-image, preserves its exact positive image. -/
private theorem torsion_selective_positive_f_native_step
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (k q l : ℕ) (hk : 0<k) (hq : 0<q) (hl : 0<l) (s t : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (k+q) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)))
    (hε : XModLambdaN.incl _ (k+q) ≫ ε.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (k+q)))
    (P : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (hP : boundaries background T.Y ((k:ℤ)+l+1) (s+1,t+1) ≤ P)
    (hmid : ∀ x : Ambient background T.X (s,t), x ∈ cycles background T.X q (s,t) →
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈ P →
      ∃ z : Ambient background T.Z (s,t+1), z ∈ cycles background T.Z q (s,t+1) ∧
      ∃ u : Ambient background T.X (s,t),
        (background.classicalSuspension T.X).DesuspendsClass s (t+1)
          ((background.classical.map T.h).pageMap 2 (s,t+1) z)
          (by simpa only [add_sub_cancel_right] using u) ∧
        x-u ∈ boundaries background T.X (k+1) (s,t))
    (a : BiHom (t-s) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)))
    (ha : FiltrationAtLeast background.syntheticTower s a)
    (β : BiHom (t-s) ((t-k)+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (v : BiHom (t-s) ((t-k)+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (k+q)))
    (hv : FiltrationAtLeast background.syntheticTower (s+2) v)
    (himage : positiveFiniteImage T hf (k+q) ε (t-s) (t-k) a=β ≫ XModLambdaN.incl _ (k+q)-v)
    (ht : lambdaMultiply l β=0) :
    ∃ b : BiHom (t-s) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)),
      FiltrationAtLeast background.syntheticTower (s+1) b ∧
      positiveFiniteImage T hf (k+q) ε (t-s) (t-k) b=
      positiveFiniteImage T hf (k+q) ε (t-s) (t-k) a := by
  obtain ⟨x,hxc,hxd,hxp⟩ := torsion_selective_positive_f_finite_head T hf
    (k+q) k l hk (by omega) hl s t ε hε a ha β v hv himage ht
  obtain ⟨z,hz,u,hu,hxu⟩ := hmid x (by simpa only [Nat.add_sub_cancel_left] using hxc) (hP hxp)
  obtain ⟨b,hb,hbz⟩ := selective_positive_f_native_cycle_image T he hf hg hh hT
    k q hq s t ε hε z hz u hu
  have hnext := middle_finite_congruent_difference T.X (k+q) k (by omega)
    s t x u hxu a b hxd hb
  refine ⟨a-b,hnext,?_⟩
  rw [positiveFiniteImage_sub,hbz,sub_zero]


private theorem torsion_selective_positive_f_native_step_regraded
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (N k q l : ℕ) (hk : 0<k) (hq : 0<q) (hl : 0<l) (hN : N=k+q) (s t m w : ℤ)
    (hm : m=t-s) (hw : w=t-k)
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ N))
    (P : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (hP : boundaries background T.Y ((k:ℤ)+l+1) (s+1,t+1) ≤ P)
    (hmid : ∀ x : Ambient background T.X (s,t), x ∈ cycles background T.X q (s,t) →
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈ P →
      ∃ z : Ambient background T.Z (s,t+1), z ∈ cycles background T.Z q (s,t+1) ∧
      ∃ u : Ambient background T.X (s,t),
        (background.classicalSuspension T.X).DesuspendsClass s (t+1)
          ((background.classical.map T.h).pageMap 2 (s,t+1) z)
          (by simpa only [add_sub_cancel_right] using u) ∧
        x-u ∈ boundaries background T.X (k+1) (s,t))
    (a : BiHom m w
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (ha : FiltrationAtLeast background.syntheticTower s a)
    (β : BiHom m (w+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (v : BiHom m (w+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N))
    (hv : FiltrationAtLeast background.syntheticTower (s+2) v)
    (himage : positiveFiniteImage T hf N ε m w a=β ≫ XModLambdaN.incl _ N-v)
    (ht : lambdaMultiply l β=0) :
    ∃ b : BiHom m w
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower (s+1) b ∧
      positiveFiniteImage T hf N ε m w b=
      positiveFiniteImage T hf N ε m w a := by
  subst N; subst m; subst w
  exact torsion_selective_positive_f_native_step T he hf hg hh hT k q l hk hq hl s t ε hε P hP hmid a ha β v hv himage ht


/-- Restricted middle elimination for the actual positive finite image.
The same fixed full image is used at every stage. -/
private theorem torsion_selective_positive_f_native_residual_same_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (c K l : ℕ) (hK : 2≤K) (hl : 0<l) (S V : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+K) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)))
    (hε : XModLambdaN.incl _ (c+K) ≫ ε.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (c+K)))
    (P : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j+1,V+j+1)))
    (hP : ∀ j : ℕ, 1≤j → j<K-1 → boundaries background T.Y ((c:ℤ)+j+l+1) (S+j+1,V+j+1) ≤ P j)
    (hmid : ∀ j : ℕ, 1≤j → j<K-1 →
      ∀ x : Ambient background T.X (S+j,V+j),
        x ∈ cycles background T.X ((K:ℤ)-j) (S+j,V+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+j) (V+j) x ∈ P j →
        ∃ z : Ambient background T.Z (S+j,V+j+1),
          z ∈ cycles background T.Z ((K:ℤ)-j) (S+j,V+j+1) ∧
          x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z ∈
            boundaries background T.X ((c:ℤ)+j+1) (S+j,V+j))
    (a : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)))
    (ha : FiltrationAtLeast background.syntheticTower (S+1) a)
    (β : BiHom (V-S) ((V-c)+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (v : BiHom (V-S) ((V-c)+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (c+K)))
    (hv : FiltrationAtLeast background.syntheticTower (S+K) v)
    (himage : positiveFiniteImage T hf (c+K) ε (V-S) (V-c) a=
      β ≫ XModLambdaN.incl _ (c+K)-v)
    (ht : lambdaMultiply l β=0) :
    ∃ e : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)),
      FiltrationAtLeast background.syntheticTower (S+K-1) e ∧
      positiveFiniteImage T hf (c+K) ε (V-S) (V-c) e=
      positiveFiniteImage T hf (c+K) ε (V-S) (V-c) a := by
  let A := XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)
  let f := positiveFiniteImage T hf (c+K) ε (V-S) (V-c)
  have hstep (j : ℕ) (hj : 1≤j) (hjK : j<K-1)
      (b : BiHom (V-S) (V-c) A)
      (hb : FiltrationAtLeast background.syntheticTower (S+j) b)
      (hi : f b=f a) :
      ∃ b' : BiHom (V-S) (V-c) A,
        FiltrationAtLeast background.syntheticTower (S+(j+1:ℕ)) b' ∧ f b'=f b := by
    have H := torsion_selective_positive_f_native_step_regraded T he hf hg hh hT
      (c+K) (c+j) (K-j) l (by omega) (by omega) hl (by omega)
      (S+j) (V+j) (V-S) (V-c) (by omega) (by omega) ε hε
      (P j) (by simpa only [Nat.cast_add] using hP j hj hjK)
      (fun x hx hxp => by
        obtain ⟨z,hz,hxz⟩ := hmid j hj hjK x
          (by simpa only [Nat.cast_sub (show j≤K by omega)] using hx) hxp
        refine ⟨z,?_,_,KIP126.ProofTools.Standard.classicalTriangleHMapHom_spec T (S+j) (V+j) z,?_⟩
        · simpa only [Nat.cast_sub (show j≤K by omega)] using hz
        · simpa only [Nat.cast_add,Nat.cast_one] using hxz)
      b hb β v (background.syntheticTower.filtrationSubmodule_antitone _ _ (by omega) hv)
      (hi.trans himage) ht
    obtain ⟨b',hb',hi'⟩ := H
    refine ⟨b',?_,hi'⟩
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hb'
  have hrec (j : ℕ) (hj : 1≤j) (hjK : j≤K-1)
      (b : BiHom (V-S) (V-c) A)
      (hb : FiltrationAtLeast background.syntheticTower (S+j) b)
      (hi : f b=f a) :
      ∃ e : BiHom (V-S) (V-c) A,
        FiltrationAtLeast background.syntheticTower (S+K-1) e ∧ f e=f a := by
    induction hlen : K-1-j using Nat.strong_induction_on generalizing j b with
    | h n ih =>
      by_cases hend : K-1≤j
      · refine ⟨b,?_,hi⟩
        convert hb using 1
        omega
      · obtain ⟨b',hb',hi'⟩ := hstep j hj (by omega) b hb hi
        exact ih (K-1-(j+1)) (by omega) (j+1) (by omega) (by omega) b' hb' (hi'.trans hi) rfl
  exact hrec 1 (by omega) (by omega) a (by simpa only [Nat.cast_one] using ha) rfl



/-- Lambda torsion of the same full class survives its actual positive image. -/
private theorem lambda_torsion_positive_full_image
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (l : ℕ) (m w : ℤ)
    (a : BiHom m w (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (ha : lambdaMultiply l a=0) :
    lambdaMultiply l (verticalTranslate _ 1 m w a≫lastLayerNormalizedMap T hf)=0 := by
  apply lambda_torsion_postcomp l _ _
  apply homotopy_regrade_injective (rfl : m=m)
    (show (w+1)-(l:ℤ)=(w-(l:ℤ))+1 by omega)
  rw [lambda_multiply_vertical_translate_comm,ha]
  simp only [map_zero,regrade_zero]

private theorem torsion_positive_full_image_of_selective_middle
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q l : ℕ) (hq : 0 < q) (hl : 0<l) (S V : ℤ)
    (u : Ambient background T.X (S,V)) (z : Ambient background T.Z (S,V+1))
    (v : Ambient background T.Y (S+q+1,(V+1)+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass S (V+1)
      ((background.classical.map T.h).pageMap 2 (S,V+1) z) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (S,V+1) (S+q+1,(V+1)+q) z
      ((background.classical.map T.g).pageMap 2 (S+q+1,(V+1)+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j+1,V+j+1)))
    (hPm : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      boundaries background T.Y ((l:ℤ)+j+1) (S+j+1,V+j+1) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ x : Ambient background T.X (S+j,V+j),
        x ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (S+j,V+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+j) (V+j) x ∈ Pm j →
        ∃ z' : Ambient background T.Z (S+j,V+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (S+j,V+j+1) ∧
          x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (S+j,V+j))
    (U : BiHom (V-S) V (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X S V u)
    (hUt : lambdaMultiply l U=0) :
    ∃ e : Ambient background T.X (S+q,V+q),
    ∃ error : Ambient background T.Y (S+q+1,(V+1)+q),
      HEq error (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
        T hf (S+q) (V+q) e) ∧
      homotopyRegrade (show V-S=((V+1)+q)-(S+q+1) by omega) rfl
        ((verticalTranslate _ 1 (V-S) V U ≫ lastLayerNormalizedMap T hf) ≫
          XModLambdaN.incl _ (0+(q+1))) =
        finiteTopLabelAtWeight T.Y (0+q) (by omega) (0+(q+1)) (by omega)
          (S+q+1) ((V+1)+q) (V+1) (by omega) (v+error) := by
  let N := 0+(q+1)
  let ε := levelQuotientShiftIso T.X 1 N
  have hε := level_quotient_shift_incl T.X 1 N
  let a₀ : BiHom (V-S) (V-(0:ℕ))
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N) :=
    homotopyRegrade rfl (by omega) (U ≫ XModLambdaN.incl _ N)
  have hfirst : (U ≫ XModLambdaN.incl _ N) ≫
      (background.quotients.tower _).rho 1 N (by dsimp [N]; omega) =
      nativeFirstLabel T.X S V u := by
    rw [Category.assoc,(background.quotients.tower _).rho_quotient,hU]
  have hdet := first_label_detects_unshifted T.X N (by dsimp [N]; omega)
    S V u _ hfirst
  rw [←zero_weight_label] at hdet
  have ha₀ := finite_weight_detection_regrade T.X N S V V (V-(0:ℕ))
    (by omega) (by dsimp [N]; omega) (by dsimp [N]; omega) u _ hdet
  rw [finite_coefficient_weight_label] at ha₀
  obtain ⟨a,ha,hai⟩ := positive_finite_common_native_source
    T he hT hf hg hh 0 q hq S V u z v hu hdz ε hε
  have hres := detects_sub_filtration (background.convergence (.quotient N (.nu T.X)))
    (S,V,V-(0:ℕ)) ha₀ ha
  let f := positiveFiniteImage T hf N ε (V-S) (V-(0:ℕ))
  let β := homotopyRegrade (rfl : V-S=V-S) (show V+1=(V-(0:ℕ))+1 by omega)
    (verticalTranslate _ 1 (V-S) V U ≫ lastLayerNormalizedMap T hf)
  have hfull : f a₀ = β ≫ XModLambdaN.incl _ N := by
    dsimp only [f,a₀,β,ε]
    rw [←positiveFiniteImage_regrade,positive_finite_image_full_projection,regrade_comp]
  have hvfil : FiltrationAtLeast background.syntheticTower (S+(q+1)) (f a) := by
    apply (regrade_filtration_iff _ _ (S+(q+1)) (f a)).mp
    rw [show homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
      (show (V-(0:ℕ))+1=(V+1)-(0:ℕ) by omega) (f a) =
      finiteMayTopLabel T.Y 0 q hq S (V+1) v from hai]
    have hvd := finite_may_top_label_detects T.Y 0 q hq S (V+1) v
    have hvf := (regrade_filtration_iff _ _ (S+q+1) _).mp (detects_filtration
      (.quotient N (.nu T.Y)) (S+q+1,(V+1)+q,(V+1)-(0:ℕ)) _ _ hvd)
    simpa only [Nat.cast_add,Nat.cast_one,Int.add_assoc] using hvf
  obtain ⟨e,hefil,hei⟩ := torsion_selective_positive_f_native_residual_same_image
    T he hf hg hh hT 0 (q+1) l (by omega) hl S V ε hε Pm
    (fun j hj hjq => by simpa only [Nat.cast_zero,zero_add,add_comm,add_left_comm,add_assoc] using hPm j hj hjq)
    (by simpa only [Nat.cast_zero,zero_add] using hmid) (a₀-a) hres β (f a) hvfil
    (by rw [positiveFiniteImage_sub]; exact congrArg (fun z => z-f a) hfull)
    (by dsimp only [β]; rw [lambda_regrade,lambda_torsion_positive_full_image T hf l (V-S) V U hUt,regrade_zero])
  have hefil' : FiltrationAtLeast background.syntheticTower (S+q) e := by
    simpa only [Nat.cast_add,Nat.cast_one,show S+((q:ℤ)+1)-1=S+q by omega] using hefil
  obtain ⟨e₂,error,herror,heiTop⟩ := last_layer_positive_image_eq_finite_may_top
    T hf 0 q hq S V ε hε e hefil'
  have hsum : f a₀=f a+f e := by
    change f e=f (a₀-a) at hei
    dsimp only [f] at hei ⊢
    rw [positiveFiniteImage_sub] at hei
    rw [hei]; abel
  have htop : homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
      (show (V-(0:ℕ))+1=(V+1)-(0:ℕ) by omega) (f a₀) =
      finiteMayTopLabel T.Y 0 q hq S (V+1) (v+error) := by
    rw [hsum,regrade_add,hai,heiTop,finite_may_top_label_add]
  rw [hfull] at htop
  have ht := congrArg (homotopyRegrade
    (show ((V+1)-S)-1=((V+1)+q)-(S+q+1) by omega)
    (show (V+1)-(0:ℕ)=V+1 by omega)) htop
  refine ⟨e₂,error,herror,?_⟩
  simp only [β,←regrade_comp,finiteMayTopLabel,last_layer_regrade_trans] at ht
  rw [top_label_at_weight_output_regrade] at ht
  simpa only [top_target_regrade_self] using ht

private theorem torsion_positive_bottom_finite_lift_of_selective_middle
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (L q : ℕ) (hL : 0<L) (hq : 0<q) (s t : ℤ)
    (u : Ambient background T.X (s+L+1,t+L))
    (z : Ambient background T.Z (s+L+1,(t+L)+1))
    (v : Ambient background T.Y ((s+L+1)+q+1,((t+L)+1)+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+L+1) ((t+L)+1)
      ((background.classical.map T.h).pageMap 2 (s+L+1,(t+L)+1) z) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+L+1,(t+L)+1) ((s+L+1)+q+1,((t+L)+1)+q) z
      ((background.classical.map T.g).pageMap 2 ((s+L+1)+q+1,((t+L)+1)+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hPm : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      boundaries background T.Y ((L:ℤ)+j+1) ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X ((s+L+1)+j,(t+L)+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf
          ((s+L+1)+j) ((t+L)+j) a ∈ Pm j →
        ∃ z' : Ambient background T.Z ((s+L+1)+j,(t+L)+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T
            ((s+L+1)+j) ((t+L)+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) ((s+L+1)+j,(t+L)+j))
    (ζ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) L))
    (hζ : adjacentBoundaryLabel T.X L s t ζ = nativeFirstLabel T.X (s+L+1) (t+L) u) :
    ∃ η : BiHom (t-s) (t+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (L+(0+q))),
    ∃ wv : Ambient background T.Y ((s+L+1)+q+1,((t+L)+1)+q),
    ∃ e : Ambient background T.X ((s+L+1)+q,(t+L)+q),
    ∃ error : Ambient background T.Y ((s+L+1)+q+1,((t+L)+1)+q),
      HEq error (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
        T hf ((s+L+1)+q) ((t+L)+q) e) ∧
      η ≫ (background.quotients.tower _).rho L (L+(0+q)) (by omega) =
        positiveFiniteImage T hf L (levelQuotientShiftIso T.X 1 L) (t-s) t ζ ∧
      homotopyRegrade
          (show (t-s)-1=(((t+L)+1)+q)-((s+L+1)+q+1) by omega)
          (show (t+1)+(L+(0+q):ℕ)=((t+L)+1)+q by omega)
          (biSuspensionHomEquiv (t-s) (t+1) ((L+(0+q):ℕ):ℤ)
            (background.nu.functor.obj (T.Y.obj background.auxiliary))
            (η ≫ XModLambdaN.proj _ (L+(0+q)))) ≫ XModLambdaN.incl _ 1 =
        nativeFirstLabel T.Y ((s+L+1)+q+1) (((t+L)+1)+q) wv ∧
      wv ∈ permanentCycles background T.Y ((s+L+1)+q+1,((t+L)+1)+q) ∧
      wv-v-error ∈ boundaries background T.Y (q+1) ((s+L+1)+q+1,((t+L)+1)+q) := by
  let U := positiveAdjustedBoundary T.X L s t ζ
  have hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X (s+L+1) (t+L) u :=
    (positive_adjusted_boundary_first T.X L s t ζ).trans hζ
  obtain ⟨e,error,herror,htop⟩ := torsion_positive_full_image_of_selective_middle
    T he hT hf hg hh q L hq hL (s+L+1) (t+L) u z v hu hdz Pm hPm hmid U hU (positive_adjusted_boundary_torsion T.X L s t ζ)
  let aY := positiveFiniteImage T hf L (levelQuotientShiftIso T.X 1 L) (t-s) t ζ
  have hboundary := positive_finite_image_absolute_boundary T hf L s t ζ
  have hboundaryTop := congrArg (fun b => b ≫ XModLambdaN.incl
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) (0+(q+1))) hboundary
  have htopY : homotopyRegrade
      (show (t-s)-1=(((t+L)+1)+q)-((s+L+1)+q+1) by omega)
      (show (t+1)+L=(t+L)+1 by omega)
      (biSuspensionHomEquiv (t-s) (t+1) L (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (aY ≫ XModLambdaN.proj _ L) ≫ XModLambdaN.incl _ (0+(q+1))) =
      finiteTopLabelAtWeight T.Y (0+q) (by omega) (0+(q+1)) (by omega)
        ((s+L+1)+q+1) (((t+L)+1)+q) ((t+L)+1) (by omega) (v+error) := by
    have h := congrArg (homotopyRegrade
      (show (t+L)-(s+L+1)=(((t+L)+1)+q)-((s+L+1)+q+1) by omega)
      (rfl : (t+L)+1=(t+L)+1)) hboundaryTop
    rw [←regrade_comp,normalized_homotopy_regrade_trans] at h
    exact h.trans htop
  obtain ⟨η,wv,hη,hwv,hp,herr⟩ := finite_extension_of_boundary_top_at_weight
    T.Y L (0+q) (0+(q+1)) hL (by omega) (by omega) (t-s) (t+1)
    ((s+L+1)+q+1) (((t+L)+1)+q) ((t+L)+1) (by omega) (by omega) (by omega)
    aY (v+error) htopY
  refine ⟨η,wv,e,error,herror,hη,hwv,hp,?_⟩
  have hid : wv-v-error=wv-(v+error) := by abel
  simpa only [hid,Nat.cast_add,Nat.cast_zero,zero_add] using herr

/-- The restricted-middle differential criterion in the positive-first branch
with genuine finite-torsion candidate bounds. -/
private theorem differential_of_torsion_selective_middle_first
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
      boundaries background T.Y ((L:ℤ)+j+1) ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j)
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
    torsion_positive_bottom_finite_lift_of_selective_middle T he hT hf hg hh L q hL hq s t u z v hu hdz
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

private theorem finite_boundaries_le_permanent (X : (AdamsObject (coefficients := background.coefficients))) (p : Bidegree) (r : ℤ) :
    boundaries background X r p ≤ permanentCycles background X p :=
  (boundaries_le_finalBoundaries X p r).trans (finalBoundaries_le_permanentCycles X p)

private theorem torsion_early_positive_selective_top
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q l : ℕ) (hq : 0 < q) (hl : 0<l) (S V : ℤ)
    (u : Ambient background T.X (S,V))
    (v : Ambient background T.Y (S+q+1,(V+1)+q))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j+1,V+j+1)))
    (hPm : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      boundaries background T.Y ((l:ℤ)+j+1) (S+j+1,V+j+1) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ x : Ambient background T.X (S+j,V+j),
        x ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (S+j,V+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+j) (V+j) x ∈ Pm j →
        ∃ z' : Ambient background T.Z (S+j,V+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (S+j,V+j+1) ∧
          x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (S+j,V+j))
    (U : BiHom (V-S) V (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X S V u)
    (cA : BiHom (V-S) (V-(0:ℕ))
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (0+(q+1))))
    (hcA : cA ≫ (background.quotients.tower _).rho 1 (0+(q+1)) (by omega) =
      homotopyRegrade rfl (by omega) (nativeFirstLabel T.X S V u))
    (W : BiHom (V-S) (V+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hcAi : homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
        (show (V-(0:ℕ))+1=(V+1)-(0:ℕ) by omega)
        (positiveFiniteImage T hf (0+(q+1)) (levelQuotientShiftIso T.X 1 (0+(q+1)))
          (V-S) (V-(0:ℕ)) cA) =
      homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
        (show V+1=(V+1)-(0:ℕ) by omega) (W ≫ XModLambdaN.incl _ (0+(q+1))) +
        finiteMayTopLabel T.Y 0 q hq S (V+1) v)
    (ht : lambdaMultiply l (verticalTranslate _ 1 (V-S) V U≫lastLayerNormalizedMap T hf-W)=0) :
    ∃ e : Ambient background T.X (S+q,V+q),
    ∃ error : Ambient background T.Y (S+q+1,(V+1)+q),
      HEq error (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
        T hf (S+q) (V+q) e) ∧
      homotopyRegrade (show V-S=((V+1)+q)-(S+q+1) by omega) rfl
        ((verticalTranslate _ 1 (V-S) V U ≫ lastLayerNormalizedMap T hf-W) ≫
          XModLambdaN.incl _ (0+(q+1))) =
        finiteTopLabelAtWeight T.Y (0+q) (by omega) (0+(q+1)) (by omega)
          (S+q+1) ((V+1)+q) (V+1) (by omega) (v+error) := by
  let N := 0+(q+1)
  let ε := levelQuotientShiftIso T.X 1 N
  have hε := level_quotient_shift_incl T.X 1 N
  let a₀ : BiHom (V-S) (V-(0:ℕ))
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N) :=
    homotopyRegrade rfl (by omega) (U ≫ XModLambdaN.incl _ N)
  have hfirst : (U ≫ XModLambdaN.incl _ N) ≫
      (background.quotients.tower _).rho 1 N (by dsimp [N]; omega) =
      nativeFirstLabel T.X S V u := by
    rw [Category.assoc,(background.quotients.tower _).rho_quotient,hU]
  have hdet := first_label_detects_unshifted T.X N (by dsimp [N]; omega)
    S V u _ hfirst
  rw [←zero_weight_label] at hdet
  have ha₀ := finite_weight_detection_regrade T.X N S V V (V-(0:ℕ))
    (by omega) (by dsimp [N]; omega) (by dsimp [N]; omega) u _ hdet
  rw [finite_coefficient_weight_label] at ha₀
  let a := cA
  have hafirst : homotopyRegrade rfl (show V-(0:ℕ)=V by omega) cA ≫
      (background.quotients.tower _).rho 1 N (by dsimp [N]; omega) = nativeFirstLabel T.X S V u := by
    rw [←regrade_comp,hcA,normalized_homotopy_regrade_trans,top_target_regrade_self]
  have hadet := first_label_detects_unshifted T.X N (by dsimp [N]; omega)
    S V u _ hafirst
  rw [←zero_weight_label] at hadet
  have ha := finite_weight_detection_regrade T.X N S V V (V-(0:ℕ))
    (by omega) (by dsimp [N]; omega) (by dsimp [N]; omega) u _ hadet
  rw [finite_coefficient_weight_label,normalized_homotopy_regrade_trans,top_target_regrade_self] at ha
  have hres := detects_sub_filtration (background.convergence (.quotient N (.nu T.X)))
    (S,V,V-(0:ℕ)) ha₀ ha
  let f := positiveFiniteImage T hf N ε (V-S) (V-(0:ℕ))
  let W' := homotopyRegrade (rfl : V-S=V-S) (show V+1=(V-(0:ℕ))+1 by omega) W
  let β := homotopyRegrade (rfl : V-S=V-S) (show V+1=(V-(0:ℕ))+1 by omega)
    (verticalTranslate _ 1 (V-S) V U ≫ lastLayerNormalizedMap T hf-W)
  let top := f a-W' ≫ XModLambdaN.incl _ N
  have htopv : homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
      (show (V-(0:ℕ))+1=(V+1)-(0:ℕ) by omega) top =
      finiteMayTopLabel T.Y 0 q hq S (V+1) v := by
    dsimp only [top,f,a,ε,W']
    rw [early_regrade_sub,←regrade_comp,normalized_homotopy_regrade_trans,hcAi,add_sub_cancel_left]
  have hfull : f a₀-W' ≫ XModLambdaN.incl _ N = β ≫ XModLambdaN.incl _ N := by
    dsimp only [f,a₀,β,ε,W']
    rw [←positiveFiniteImage_regrade,positive_finite_image_full_projection,regrade_comp,
      early_regrade_sub,Preadditive.sub_comp,regrade_comp]
  have hvfil : FiltrationAtLeast background.syntheticTower (S+(q+1)) top := by
    apply (regrade_filtration_iff _ _ (S+(q+1)) top).mp
    rw [htopv]
    have hvd := finite_may_top_label_detects T.Y 0 q hq S (V+1) v
    have hvf := (regrade_filtration_iff _ _ (S+q+1) _).mp (detects_filtration
      (.quotient N (.nu T.Y)) (S+q+1,(V+1)+q,(V+1)-(0:ℕ)) _ _ hvd)
    simpa only [Nat.cast_add,Nat.cast_one,Int.add_assoc] using hvf
  obtain ⟨e,hefil,hei⟩ := torsion_selective_positive_f_native_residual_same_image
    T he hf hg hh hT 0 (q+1) l (by omega) hl S V ε hε Pm
    (fun j hj hjq => by simpa only [Nat.cast_zero,zero_add,add_comm,add_left_comm,add_assoc] using hPm j hj hjq)
    (by simpa only [Nat.cast_zero,zero_add] using hmid) (a₀-a) hres β top hvfil
    (by rw [positiveFiniteImage_sub,←hfull]; dsimp only [top]; abel)
    (by dsimp only [β]; rw [lambda_regrade,ht,regrade_zero])
  have hefil' : FiltrationAtLeast background.syntheticTower (S+q) e := by
    simpa only [Nat.cast_add,Nat.cast_one,show S+((q:ℤ)+1)-1=S+q by omega] using hefil
  obtain ⟨e₂,error,herror,heiTop⟩ := last_layer_positive_image_eq_finite_may_top
    T hf 0 q hq S V ε hε e hefil'
  have hsum : β ≫ XModLambdaN.incl _ N=top+f e := by
    change f e=f (a₀-a) at hei
    have hei' : f e=f a₀-f a := by simpa only [f,positiveFiniteImage_sub] using hei
    rw [←hfull,hei']
    dsimp only [top]
    abel
  have htop : homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
      (show (V-(0:ℕ))+1=(V+1)-(0:ℕ) by omega) (β ≫ XModLambdaN.incl _ N) =
      finiteMayTopLabel T.Y 0 q hq S (V+1) (v+error) := by
    rw [hsum,regrade_add,htopv,heiTop,finite_may_top_label_add]
  have ht := congrArg (homotopyRegrade
    (show ((V+1)-S)-1=((V+1)+q)-(S+q+1) by omega)
    (show (V+1)-(0:ℕ)=V+1 by omega)) htop
  refine ⟨e₂,error,herror,?_⟩
  simp only [β,←regrade_comp,finiteMayTopLabel,last_layer_regrade_trans] at ht
  rw [top_label_at_weight_output_regrade] at ht
  simpa only [top_target_regrade_self] using ht

private theorem torsion_early_positive_selective_top_at_degree
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q N l : ℕ) (hq : 0 < q) (hl : 0<l) (hN : N=0+(q+1)) (S V A B : ℤ)
    (hA : A=S+q+1) (hB : B=(V+1)+q)
    (u : Ambient background T.X (S,V))
    (v : Ambient background T.Y (A,B))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y (S+j+1,V+j+1)))
    (hPm : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      boundaries background T.Y ((l:ℤ)+j+1) (S+j+1,V+j+1) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ x : Ambient background T.X (S+j,V+j),
        x ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (S+j,V+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+j) (V+j) x ∈ Pm j →
        ∃ z' : Ambient background T.Z (S+j,V+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (S+j,V+j+1) ∧
          x-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (S+j,V+j))
    (U : BiHom (V-S) V (background.nu.functor.obj (T.X.obj background.auxiliary)))
    (hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X S V u)
    (cA : BiHom (V-S) V
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hcA : cA ≫ (background.quotients.tower _).rho 1 N (by omega) = nativeFirstLabel T.X S V u)
    (W : BiHom (V-S) (V+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hcAi : positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (V-S) V cA =
      W ≫ XModLambdaN.incl _ N +
        homotopyRegrade (show B-A=V-S by omega) rfl
          (finiteTopLabelAtWeight T.Y q hq N (by omega) A B (V+1) (by omega) v))
    (ht : lambdaMultiply l (verticalTranslate _ 1 (V-S) V U≫lastLayerNormalizedMap T hf-W)=0) :
    ∃ e : Ambient background T.X (S+q,V+q),
    ∃ error : Ambient background T.Y (A,B),
      HEq error (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
        T hf (S+q) (V+q) e) ∧
      homotopyRegrade (show V-S=B-A by omega) rfl
        ((verticalTranslate _ 1 (V-S) V U ≫ lastLayerNormalizedMap T hf-W) ≫
          XModLambdaN.incl _ N) =
        finiteTopLabelAtWeight T.Y q hq N (by omega) A B (V+1) (by omega) (v+error) := by
  subst N; subst A; subst B
  let cA' := homotopyRegrade (rfl : V-S=V-S) (show V=V-(0:ℕ) by omega) cA
  have hcA' : cA' ≫ (background.quotients.tower _).rho 1 (0+(q+1)) (by omega) =
      homotopyRegrade rfl (by omega) (nativeFirstLabel T.X S V u) := by
    dsimp only [cA']
    rw [←regrade_comp,hcA]
  have hcAi' : homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
        (show (V-(0:ℕ))+1=(V+1)-(0:ℕ) by omega)
        (positiveFiniteImage T hf (0+(q+1)) (levelQuotientShiftIso T.X 1 (0+(q+1)))
          (V-S) (V-(0:ℕ)) cA') =
      homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
        (show V+1=(V+1)-(0:ℕ) by omega) (W ≫ XModLambdaN.incl _ (0+(q+1))) +
        finiteMayTopLabel T.Y 0 q hq S (V+1) v := by
    dsimp only [cA']
    rw [←positiveFiniteImage_regrade,normalized_homotopy_regrade_trans,hcAi,regrade_add,
      normalized_homotopy_regrade_trans]
    unfold finiteMayTopLabel
    apply congrArg (fun z => homotopyRegrade
      (show V-S=((V+1)-S)-1 by omega) (show V+1=(V+1)-(0:ℕ) by omega)
      (W ≫ XModLambdaN.incl _ (0+(q+1))) + z)
    exact early_top_at_weight_congr T.Y q (0+q) (0+(q+1)) hq (by omega)
      (by omega) (by omega) (by omega) (S+q+1) ((V+1)+q) (V+1) ((V+1)-(0:ℕ))
      (((V+1)-S)-1) ((V+1)-(0:ℕ)) (by omega) (by omega) (by omega) (by omega) rfl v
  obtain ⟨e,error,he,ht⟩ := torsion_early_positive_selective_top T he hT hf hg hh q l hq hl S V u v
    Pm hPm hmid U hU cA' hcA' W hcAi' ht
  exact ⟨e,error,he,by simpa only [Nat.zero_add] using ht⟩

/-- Original early-boundary torsion corollary: intersect the original permanent candidate with a true-boundary upper bound. -/
private theorem differential_of_torsion_early_boundary_positive
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (L d : ℕ) (hL : 2≤L) (hd : 0<d) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u : Ambient background T.X (s+L+1,t+L))
    (c : Ambient background T.Y (s+L,t+L))
    (v : Ambient background T.Y ((s+L)+(d+1)+1,(t+L)+(d+1)))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (s,t) (s+L+1,t+L) x u)
    (hd₂ : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      2 (s+L,t+L) ((s+L)+1+1,(t+L)+1) c
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+L+1) (t+L) u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((d+1)+1) (s+L,t+L) ((s+L)+(d+1)+1,(t+L)+(d+1))
      ((background.classical.map T.g).pageMap 2 (s+L,t+L) c)
      ((background.classical.map T.g).pageMap 2 ((s+L)+(d+1)+1,(t+L)+(d+1)) v))
    (hH : ∀ z : Ambient background T.Z (s+L+1,(t+L)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+L+1) (t+L) z ∈
        boundaries background T.X 2 (s+L+1,t+L))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hPm : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      permanentCycles background T.Y ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j)
    (Qm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hQm : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      boundaries background T.Y ((L:ℤ)+j+1) ((s+L+1)+j+1,(t+L)+j+1) ≤ Qm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      ∀ a : Ambient background T.X ((s+L+1)+j,(t+L)+j),
        a ∈ cycles background T.X (((d+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+L+1)+j) ((t+L)+j) a ∈ Pm j ⊓ Qm j →
        ∃ z : Ambient background T.Z ((s+L+1)+j,(t+L)+j+1),
          z ∈ cycles background T.Z (((d+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T ((s+L+1)+j) ((t+L)+j) z ∈
            boundaries background T.X ((j:ℤ)+1) ((s+L+1)+j,(t+L)+j))
    (P : Submodule ℤ (Ambient background T.Y ((s+L)+(d+1)+1,(t+L)+(d+1))))
    (hP : permanentCycles background T.Y ((s+L)+(d+1)+1,(t+L)+(d+1)) ≤ P)
    (hv : v∈P)
    (hker : ∀ a∈P, (background.classical.map T.g).pageMap 2 ((s+L)+(d+1)+1,(t+L)+(d+1)) a=0 →
      a∈boundaries background T.Y (L+d) ((s+L)+(d+1)+1,(t+L)+(d+1))) :
    IsCycle background T.Y (L+d) (s+1,t+1)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) ∧
    IsCycle background T.Y (L+d) ((s+L)+(d+1)+1,(t+L)+(d+1)) v ∧
    DifferentialAt background T.Y (L+d+1) (s+1,t+1) ((s+L)+(d+1)+1,(t+L)+(d+1))
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨cA,u',aHat,W,hcA,hu',hW,_,hcAi⟩ := early_positive_compatible_finite_lift
    T he hT hf hg hh (d+1) (by omega) (s+L) (t+L) c u v hdz hH hd₂
  obtain ⟨ζ,hζ,hU,ξ,hξ,hξb⟩ := early_positive_corrected_source T hf L hL s t x u u' hdx hu' aHat W hW
  have hΔ : lambdaMultiply L
      (verticalTranslate _ 1 ((t+L)-(s+L+1)) (t+L)
        (positiveAdjustedBoundary T.X L s t ζ)≫lastLayerNormalizedMap T hf-W)=0 := by
    rw [←hξb,lambda_regrade,absolute_boundary_lambda_zero,regrade_zero]
  have hCand (j : ℕ) (hj : 1≤j) (hjd : j<(d+1)-1) :
      boundaries background T.Y ((L:ℤ)+j+1) ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j ⊓ Qm j := by
    intro b hb
    exact ⟨hPm j hj hjd (finite_boundaries_le_permanent T.Y _ _ hb),hQm j hj hjd hb⟩
  obtain ⟨e,error,herror,htop⟩ := torsion_early_positive_selective_top_at_degree T he hT hf hg hh
    d (((d+1)+1)-1) L hd (by omega) (by omega) (s+L+1) (t+L)
    ((s+L)+(d+1)+1) ((t+L)+(d+1)) (by omega) (by omega) u' v
    (fun j => Pm j ⊓ Qm j) hCand hmid (positiveAdjustedBoundary T.X L s t ζ) hU cA hcA W hcAi hΔ
  have heG : (background.classical.map T.g).pageMap 2 ((s+L)+(d+1)+1,(t+L)+(d+1)) error=0 := by
    have hgF := (KIP126.Literature.Standard.E2Exactness.e2ExactAtY
      T hf hg hh ((s+L+1)+d) ((t+L)+d)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+L+1)+d) ((t+L)+d) e)).mpr ⟨e,rfl⟩
    have transport (p p' : ℤ×ℤ) (hp : p=p')
        (a : Ambient background T.Y p) (b : Ambient background T.Y p') (hab : HEq a b)
        (hb : (background.classical.map T.g).pageMap 2 p' b=0) :
        (background.classical.map T.g).pageMap 2 p a=0 := by
      subst p'
      simpa only [eq_of_heq hab] using hb
    exact transport _ _ (by ext <;> dsimp <;> omega) _ _ herror hgF
  let ξY := homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl ξ
  have hξY : ξY ≫ (background.quotients.tower _).rho 1 L (by omega)=
      nativeFirstLabel T.Y (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) := by
    simpa only [ξY,←regrade_comp] using hξ
  have hfinalTop : homotopyRegrade
      (show ((t+1)-(s+1))-1=((t+L)+(d+1))-((s+L)+(d+1)+1) by omega)
      (show (t+1)+L=((t+L)+(d+1))-d by omega)
      (biSuspensionHomEquiv ((t+1)-(s+1)) (t+1) L
        (background.nu.functor.obj (T.Y.obj background.auxiliary)) (ξY ≫ XModLambdaN.proj _ L) ≫
          XModLambdaN.incl _ (d+1)) =
      finiteTopLabel T.Y d hd ((s+L)+(d+1)+1) ((t+L)+(d+1)) (v+error) := by
    have hb := congrArg (fun b => b ≫ XModLambdaN.incl
      (background.nu.functor.obj (T.Y.obj background.auxiliary)) (((d+1)+1)-1)) hξb
    have hb' := congrArg (homotopyRegrade
      (show (t+L)-(s+L+1)=((t+L)+(d+1))-((s+L)+(d+1)+1) by omega) rfl) hb
    rw [←regrade_comp,normalized_homotopy_regrade_trans] at hb'
    have ht := hb'.trans htop
    have ht' := congrArg (homotopyRegrade (rfl :
        ((t+L)+(d+1))-((s+L)+(d+1)+1)=((t+L)+(d+1))-((s+L)+(d+1)+1))
      (show (t+L)+1=((t+L)+(d+1))-d by omega)) ht
    convert ht' using 1 <;>
      simp only [ξY,←regrade_comp,early_bi_susp_regrade,normalized_homotopy_regrade_trans,
        finiteTopLabelAtWeight,top_target_regrade_self,Nat.add_sub_cancel]
    all_goals rfl
  exact early_target_of_retained_boundary_top_at_degree T.Y T.Z T.g L d (by omega) hd
    (s+1) (t+1) ((s+L)+(d+1)+1) ((t+L)+(d+1)) (by omega) (by omega)
    (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) v error P hP hv hker heG ξY hξY hfinalTop

/-- The complete displayed-page-source form of the target early-boundary
differential criterion for α=1.
The equation F_r[x]=[y] is expressed by its exact E₂ representatives modulo
B_{<r}; both asserted output cycles are derived. -/
private theorem differential_of_torsion_early_boundary_positive_page_source
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (L d : ℕ) (hL : 2≤L) (hd : 0<d) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (y : Ambient background T.Y (s+1,t+1))
    (u : Ambient background T.X (s+L+1,t+L))
    (c : Ambient background T.Y (s+L,t+L))
    (v : Ambient background T.Y ((s+L)+(d+1)+1,(t+L)+(d+1)))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (s,t) (s+L+1,t+L) x u)
    (hd₂ : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      2 (s+L,t+L) ((s+L)+1+1,(t+L)+1) c
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+L+1) (t+L) u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((d+1)+1) (s+L,t+L) ((s+L)+(d+1)+1,(t+L)+(d+1))
      ((background.classical.map T.g).pageMap 2 (s+L,t+L) c)
      ((background.classical.map T.g).pageMap 2 ((s+L)+(d+1)+1,(t+L)+(d+1)) v))
    (hH : ∀ z : Ambient background T.Z (s+L+1,(t+L)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+L+1) (t+L) z ∈
        boundaries background T.X 2 (s+L+1,t+L))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hPm : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      permanentCycles background T.Y ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j)
    (Qm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hQm : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      boundaries background T.Y ((L:ℤ)+j+1) ((s+L+1)+j+1,(t+L)+j+1) ≤ Qm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      ∀ a : Ambient background T.X ((s+L+1)+j,(t+L)+j),
        a ∈ cycles background T.X (((d+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+L+1)+j) ((t+L)+j) a ∈ Pm j ⊓ Qm j →
        ∃ z : Ambient background T.Z ((s+L+1)+j,(t+L)+j+1),
          z ∈ cycles background T.Z (((d+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T ((s+L+1)+j) ((t+L)+j) z ∈
            boundaries background T.X ((j:ℤ)+1) ((s+L+1)+j,(t+L)+j))
    (P : Submodule ℤ (Ambient background T.Y ((s+L)+(d+1)+1,(t+L)+(d+1))))
    (hP : permanentCycles background T.Y ((s+L)+(d+1)+1,(t+L)+(d+1)) ≤ P)
    (hv : v∈P)
    (hker : ∀ a∈P, (background.classical.map T.g).pageMap 2 ((s+L)+(d+1)+1,(t+L)+(d+1)) a=0 →
      a∈boundaries background T.Y (L+d) ((s+L)+(d+1)+1,(t+L)+(d+1)))
    (hy : y-KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈
      boundaries background T.Y L (s+1,t+1)) :
    IsCycle background T.Y (L+d) (s+1,t+1) y ∧
    IsCycle background T.Y (L+d) ((s+L)+(d+1)+1,(t+L)+(d+1)) v ∧
    DifferentialAt background T.Y (L+d+1) (s+1,t+1) ((s+L)+(d+1)+1,(t+L)+(d+1))
      y v := by
  have hd' := differential_of_torsion_early_boundary_positive T he hf hg hh L d hL hd s t
    x u c v hdx hd₂ hdz hH Pm hPm Qm hQm hmid P hP hv hker
  have hh' := early_target_of_page_source T.Y (L+d+1) L (s+1,t+1)
    ((s+L)+(d+1)+1,(t+L)+(d+1)) (by omega)
    (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) y v hd'.2.2 hy
  simpa only [add_sub_cancel_right] using hh'

/-- Original early-boundary torsion corollary: intersect the original permanent candidate with a true-boundary upper bound. -/
private theorem differential_of_torsion_higher_early_boundary_positive
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (L i d : ℕ) (hi : 0 < i) (hiL : i<L) (hd : 0<d) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u : Ambient background T.X (s+L+1,t+L))
    (c : Ambient background T.Y ((s+L+1-i),(t+L+1-i)))
    (v : Ambient background T.Y ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (s,t) (s+L+1,t+L) x u)
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) ((s+L+1-i),(t+L+1-i)) ((s+L+1-i)+i+1,(t+L+1-i)+i) c
      (boundaryLabelRegrade (show (s+L+1)+1=(s+L+1-i)+i+1 by omega)
        (show (t+L)+1=(t+L+1-i)+i by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+L+1) (t+L) u)))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((i+d)+1) ((s+L+1-i),(t+L+1-i)) ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d))
      ((background.classical.map T.g).pageMap 2 ((s+L+1-i),(t+L+1-i)) c)
      ((background.classical.map T.g).pageMap 2 ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) v))
    (hR : ∀ p : ℤ, (s+L+1-i)+1≤p → p<(s+L+1-i)+(i+1)-1 →
      ∀ z : Ambient background T.Z (p,(t+L+1-i)-(s+L+1-i)+p), z ∈ cycles background T.Z ((i+1)-(p-(s+L+1-i)).toNat:ℕ) (p,(t+L+1-i)-(s+L+1-i)+p) →
      ∃ y : Ambient background T.Y (p,(t+L+1-i)-(s+L+1-i)+p), y ∈ cycles background T.Y ((i+1)-(p-(s+L+1-i)).toNat:ℕ) (p,(t+L+1-i)-(s+L+1-i)+p) ∧
      ∃ k : Ambient background T.Z (p,(t+L+1-i)-(s+L+1-i)+p), k ∈ cycles background T.Z ((i+d)+1-(p-(s+L+1-i)).toNat:ℕ) (p,(t+L+1-i)-(s+L+1-i)+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,(t+L+1-i)-(s+L+1-i)+p) y-k ∈
          boundaries background T.Z ((p-(s+L+1-i)).toNat+1) (p,(t+L+1-i)-(s+L+1-i)+p))
    (hH : ∀ z : Ambient background T.Z (s+L+1,(t+L)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+L+1) (t+L) z ∈
        boundaries background T.X (i+1) (s+L+1,t+L))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hPm : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      permanentCycles background T.Y ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j)
    (Qm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hQm : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      boundaries background T.Y ((L:ℤ)+j+1) ((s+L+1)+j+1,(t+L)+j+1) ≤ Qm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      ∀ a : Ambient background T.X ((s+L+1)+j,(t+L)+j),
        a ∈ cycles background T.X (((d+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+L+1)+j) ((t+L)+j) a ∈ Pm j ⊓ Qm j →
        ∃ z : Ambient background T.Z ((s+L+1)+j,(t+L)+j+1),
          z ∈ cycles background T.Z (((d+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T ((s+L+1)+j) ((t+L)+j) z ∈
            boundaries background T.X ((j:ℤ)+1) ((s+L+1)+j,(t+L)+j))
    (P : Submodule ℤ (Ambient background T.Y ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d))))
    (hP : permanentCycles background T.Y ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) ≤ P)
    (hv : v∈P)
    (hker : ∀ a∈P, (background.classical.map T.g).pageMap 2 ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) a=0 →
      a∈boundaries background T.Y (L+d) ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d))) :
    IsCycle background T.Y (L+d) (s+1,t+1)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) ∧
    IsCycle background T.Y (L+d) ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) v ∧
    DifferentialAt background T.Y (L+d+1) (s+1,t+1) ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d))
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨cA,u',aHat,W,hcA,hu',hW,_,hcAi⟩ := higher_positive_compatible_finite_lift_at
    T he hT hf hg hh i d hi hd (s+L+1-i) (t+L+1-i) (s+L+1) (t+L) (by omega) (by omega)
    c u v hdz hearly hR hH
  obtain ⟨ζ,hζ,hU,ξ,hξ,hξb⟩ := higher_positive_corrected_source T hf L i hi hiL s t x u u' hdx hu' aHat W hW
  have hΔ : lambdaMultiply L
      (verticalTranslate _ 1 ((t+L)-(s+L+1)) (t+L)
        (positiveAdjustedBoundary T.X L s t ζ)≫lastLayerNormalizedMap T hf-W)=0 := by
    rw [←hξb,lambda_regrade,absolute_boundary_lambda_zero,regrade_zero]
  have hCand (j : ℕ) (hj : 1≤j) (hjd : j<(d+1)-1) :
      boundaries background T.Y ((L:ℤ)+j+1) ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j ⊓ Qm j := by
    intro b hb
    exact ⟨hPm j hj hjd (finite_boundaries_le_permanent T.Y _ _ hb),hQm j hj hjd hb⟩
  obtain ⟨e,error,herror,htop⟩ := torsion_early_positive_selective_top_at_degree T he hT hf hg hh
    d (d+1) L hd (by omega) (by omega) (s+L+1) (t+L)
    ((s+L+1-i)+(i+d)+1) ((t+L+1-i)+(i+d)) (by omega) (by omega) u' v
    (fun j => Pm j ⊓ Qm j) hCand hmid (positiveAdjustedBoundary T.X L s t ζ) hU cA hcA W hcAi hΔ
  have heG : (background.classical.map T.g).pageMap 2 ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) error=0 := by
    have hgF := (KIP126.Literature.Standard.E2Exactness.e2ExactAtY
      T hf hg hh ((s+L+1)+d) ((t+L)+d)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+L+1)+d) ((t+L)+d) e)).mpr ⟨e,rfl⟩
    have transport (p p' : ℤ×ℤ) (hp : p=p')
        (a : Ambient background T.Y p) (b : Ambient background T.Y p') (hab : HEq a b)
        (hb : (background.classical.map T.g).pageMap 2 p' b=0) :
        (background.classical.map T.g).pageMap 2 p a=0 := by
      subst p'
      simpa only [eq_of_heq hab] using hb
    exact transport _ _ (by ext <;> dsimp <;> omega) _ _ herror hgF
  let ξY := homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl ξ
  have hξY : ξY ≫ (background.quotients.tower _).rho 1 L (by omega)=
      nativeFirstLabel T.Y (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) := by
    simpa only [ξY,←regrade_comp] using hξ
  have hfinalTop : homotopyRegrade
      (show ((t+1)-(s+1))-1=((t+L+1-i)+(i+d))-((s+L+1-i)+(i+d)+1) by omega)
      (show (t+1)+L=((t+L+1-i)+(i+d))-d by omega)
      (biSuspensionHomEquiv ((t+1)-(s+1)) (t+1) L
        (background.nu.functor.obj (T.Y.obj background.auxiliary)) (ξY ≫ XModLambdaN.proj _ L) ≫
          XModLambdaN.incl _ (d+1)) =
      finiteTopLabel T.Y d hd ((s+L+1-i)+(i+d)+1) ((t+L+1-i)+(i+d)) (v+error) := by
    have hb := congrArg (fun b => b ≫ XModLambdaN.incl
      (background.nu.functor.obj (T.Y.obj background.auxiliary)) (d+1)) hξb
    have hb' := congrArg (homotopyRegrade
      (show (t+L)-(s+L+1)=((t+L+1-i)+(i+d))-((s+L+1-i)+(i+d)+1) by omega) rfl) hb
    rw [←regrade_comp,normalized_homotopy_regrade_trans] at hb'
    have ht := hb'.trans htop
    have ht' := congrArg (homotopyRegrade (rfl :
        ((t+L+1-i)+(i+d))-((s+L+1-i)+(i+d)+1)=((t+L+1-i)+(i+d))-((s+L+1-i)+(i+d)+1))
      (show (t+L)+1=((t+L+1-i)+(i+d))-d by omega)) ht
    convert ht' using 1 <;>
      simp only [ξY,←regrade_comp,early_bi_susp_regrade,normalized_homotopy_regrade_trans,
        finiteTopLabelAtWeight,top_target_regrade_self]
  exact early_target_of_retained_boundary_top_at_degree T.Y T.Z T.g L d (by omega) hd
    (s+1) (t+1) ((s+L+1-i)+(i+d)+1) ((t+L+1-i)+(i+d)) (by omega) (by omega)
    (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) v error P hP hv hker heG ξY hξY hfinalTop


/-- Original displayed-page-source form of the higher early-boundary target theorem. The original F_r[x]=[y] relation is retained as the exact B_<r coset, and both output cycle statements are derived. -/
public theorem differential_of_torsion_higher_early_boundary_positive_page_source
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (L i d : ℕ) (hi : 0 < i) (hiL : i<L) (hd : 0<d) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (y : Ambient background T.Y (s+1,t+1))
    (u : Ambient background T.X (s+L+1,t+L))
    (c : Ambient background T.Y ((s+L+1-i),(t+L+1-i)))
    (v : Ambient background T.Y ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (s,t) (s+L+1,t+L) x u)
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) ((s+L+1-i),(t+L+1-i)) ((s+L+1-i)+i+1,(t+L+1-i)+i) c
      (boundaryLabelRegrade (show (s+L+1)+1=(s+L+1-i)+i+1 by omega)
        (show (t+L)+1=(t+L+1-i)+i by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+L+1) (t+L) u)))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((i+d)+1) ((s+L+1-i),(t+L+1-i)) ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d))
      ((background.classical.map T.g).pageMap 2 ((s+L+1-i),(t+L+1-i)) c)
      ((background.classical.map T.g).pageMap 2 ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) v))
    (hR : ∀ p : ℤ, (s+L+1-i)+1≤p → p<(s+L+1-i)+(i+1)-1 →
      ∀ z : Ambient background T.Z (p,(t+L+1-i)-(s+L+1-i)+p), z ∈ cycles background T.Z ((i+1)-(p-(s+L+1-i)).toNat:ℕ) (p,(t+L+1-i)-(s+L+1-i)+p) →
      ∃ y : Ambient background T.Y (p,(t+L+1-i)-(s+L+1-i)+p), y ∈ cycles background T.Y ((i+1)-(p-(s+L+1-i)).toNat:ℕ) (p,(t+L+1-i)-(s+L+1-i)+p) ∧
      ∃ k : Ambient background T.Z (p,(t+L+1-i)-(s+L+1-i)+p), k ∈ cycles background T.Z ((i+d)+1-(p-(s+L+1-i)).toNat:ℕ) (p,(t+L+1-i)-(s+L+1-i)+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,(t+L+1-i)-(s+L+1-i)+p) y-k ∈
          boundaries background T.Z ((p-(s+L+1-i)).toNat+1) (p,(t+L+1-i)-(s+L+1-i)+p))
    (hH : ∀ z : Ambient background T.Z (s+L+1,(t+L)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+L+1) (t+L) z ∈
        boundaries background T.X (i+1) (s+L+1,t+L))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hPm : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      permanentCycles background T.Y ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j)
    (Qm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hQm : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      boundaries background T.Y ((L:ℤ)+j+1) ((s+L+1)+j+1,(t+L)+j+1) ≤ Qm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      ∀ a : Ambient background T.X ((s+L+1)+j,(t+L)+j),
        a ∈ cycles background T.X (((d+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+L+1)+j) ((t+L)+j) a ∈ Pm j ⊓ Qm j →
        ∃ z : Ambient background T.Z ((s+L+1)+j,(t+L)+j+1),
          z ∈ cycles background T.Z (((d+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T ((s+L+1)+j) ((t+L)+j) z ∈
            boundaries background T.X ((j:ℤ)+1) ((s+L+1)+j,(t+L)+j))
    (P : Submodule ℤ (Ambient background T.Y ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d))))
    (hP : permanentCycles background T.Y ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) ≤ P)
    (hv : v∈P)
    (hker : ∀ a∈P, (background.classical.map T.g).pageMap 2 ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) a=0 →
      a∈boundaries background T.Y (L+d) ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)))
    (hy : y-KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈
      boundaries background T.Y L (s+1,t+1)) :
    IsCycle background T.Y (L+d) (s+1,t+1)
      y ∧
    IsCycle background T.Y (L+d) ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) v ∧
    DifferentialAt background T.Y (L+d+1) (s+1,t+1) ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d))
      y v := by
  have hdiff := differential_of_torsion_higher_early_boundary_positive T he hf hg hh L i d hi hiL hd s t
    x u c v hdx hearly hdz hR hH Pm hPm Qm hQm hmid P hP hv hker
  have hfinal := early_target_of_page_source T.Y (L+d+1) L (s+1,t+1)
    ((s+L+1-i)+(i+d)+1,(t+L+1-i)+(i+d)) (by omega)
    (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) y v hdiff.2.2 hy
  simpa only [add_sub_cancel_right] using hfinal

/-- The displayed original page source is retained under the finite-torsion refinement. -/
private theorem differential_of_torsion_selective_middle_first_page_source
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (L q : ℕ) (hL : 0<L) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (y : Ambient background T.Y (s+1,t+1))
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
      boundaries background T.Y ((L:ℤ)+j+1) ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j)
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
      a ∈ boundaries background T.Y (L+q) ((s+L+1)+q+1,((t+L)+1)+q))
    (hy : y-KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈
      boundaries background T.Y L (s+1,t+1)) :
    IsCycle background T.Y (L+q) (s+1,t+1) y ∧
      IsCycle background T.Y (L+q) ((s+L+1)+q+1,((t+L)+1)+q) v ∧
      DifferentialAt background T.Y (L+q+1) (s+1,t+1)
        ((s+L+1)+q+1,((t+L)+1)+q) y v := by
  have h := differential_of_torsion_selective_middle_first T he hf hg hh L q hL hq s t
    x u z v hu hdx hdz Pm hPm hmid P hP hv hker
  have hfinal := early_target_of_page_source T.Y (L+q+1) L (s+1,t+1)
    ((s+L+1)+q+1,((t+L)+1)+q) (by omega)
    (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) y v h.2.2 hy
  simpa only [add_sub_cancel_right] using hfinal

end
end KIP126.ProofTools.Internal.SyntheticCoverage
