module

import all KIP126.ProofTools.LevelLanguage
import all KIP126.ProofTools.GeneralizedLeibniz.RightEdge

/-! Label transport for the finite-quotient Mahowald theorem.
Restriction by rho reflects the specified label in the visible window;
normalization uses the quotient-shift comparison of
the level-indexed Leibniz language. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option Elab.async false

/-- A common representative whose rho image has the visible label lambda^K x
has that same label in the strong quotient, and the original x is a later
classical cycle.  The zero-label case is included. -/
private theorem finite_rho_lift_label_and_cycles (X : AdamsObject (coefficients := background.coefficients))
    (A N K : ℕ) (hAN : A ≤ N) (hKA : K < A) (s t : ℤ)
    (x : Ambient background X (s,t))
    (a : BiHom (t-s) (t-K)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) A))
    (ha : Detects (background.convergence (.quotient A (.nu X))) (s,t,t-K)
      (finiteTargetLabel background X A s t K x) a)
    (c : BiHom (t-s) (t-K)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (hc : c ≫ (background.quotients.tower _).rho A N hAN = a) :
    Detects (background.convergence (.quotient N (.nu X))) (s,t,t-K)
      (finiteTargetLabel background X N s t K x) c ∧
      x ∈ cycles background X ((N:ℤ)-K) (s,t) := by
  have hlabel (q : ℕ) :
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap
        2 (s,t,t-K) (nuWeightLabel background X s t (t-K) (by omega) x)) =
        finiteTargetLabel background X q s t K x := by
    have hk : (t-(t-K)).toNat = K := by omega
    have hn : nuWeightLabel background X s t (t-K) (by omega) x =
        targetNuLabel background X s t K x := by
      unfold nuWeightLabel
      have transport (k k' : ℕ) (h : k=k') (hp : (s,t,t-k)=(s,t,t-k')) :
          regradeE2 hp (targetNuLabel background X s t k x) =
            targetNuLabel background X s t k' x := by
        subst k'
        rfl
      exact transport _ K hk _
    rw [hn]
    rfl
  have ha' := ha
  rw [←hlabel A] at ha'
  have hdet := rho_lift_detects X A N (by omega) hAN s t (t-K)
    (by constructor <;> omega) x a ha' c hc
  have hcyc := rho_lift_detected_cycles X A N (by omega) hAN s t (t-K)
    (by constructor <;> omega) x a ha' c hc
  rw [hlabel N] at hdet
  refine ⟨hdet,?_⟩
  convert hcyc using 1
  congr 1
  omega

/-- The normalized representative in the actual quotient of the shifted
source, using the fixed comparison that defines the intrinsic source label. -/
private def finiteLevelNormalizedRepresentative (X : AdamsObject (coefficients := background.coefficients))
    (e : ℤ) (N K : ℕ) (s t : ℤ)
    (c : BiHom (t-s) (t-K)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    BiHom (t-s) (t+e-K)
      ((SyntheticObject.quotient N (.shift (0,e) (.nu X))).obj
        background.nu background.auxiliary) :=
  homotopyRegrade (by simp) (by dsimp; omega)
    (shiftHomotopyClass (0,e) (t-s,t-K) c) ≫ (levelQuotientShiftIso X e N).inv

/-- Normalization preserves the actual detection of the intrinsic finite
source label at every level. -/
private theorem finite_level_normalized_representative_detects
    (X : AdamsObject (coefficients := background.coefficients)) (e : ℤ) (N K : ℕ) (s t : ℤ)
    (x : Ambient background X (s,t))
    (c : BiHom (t-s) (t-K)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (hc : Detects (background.convergence (.quotient N (.nu X))) (s,t,t-K)
      (finiteTargetLabel background X N s t K x) c) :
    Detects (background.convergence (.quotient N (.shift (0,e) (.nu X))))
      (s,(t-s)+s,t+e-K)
      (KIP126.ProofTools.Standard.levelFiniteSourceLabel X N e s t K x)
      (homotopyRegrade (by dsimp; omega) rfl
        (finiteLevelNormalizedRepresentative X e N K s t c)) := by
  let A : SyntheticObject (coefficients := background.coefficients) := .quotient N (.nu X)
  let p : ℤ×ℤ := (t-s,t-K)
  let δ : ℤ×ℤ := (0,e)
  have h0 : (s,t,t-K)=(s,p.1+s,p.2) := by simp [p]
  have hN : (s,(p+δ).1+s,(p+δ).2)=(s,(t-s)+s,t+e-K) := by
    ext <;> dsimp [p,δ] <;> omega
  have hc0 := detects_transport h0 _ _ hc
  have hc0' : Detects (background.convergence A) (s,p.1+s,p.2)
      (regradeE2 h0 (finiteTargetLabel background X N s t K x))
      (homotopyRegrade (by dsimp [p]; omega) rfl c) := by
    convert hc0 using 1
  have hs := detects_shift A δ p s _ c hc0'
  have ht := detects_transport hN _ _ hs
  have hm := detects_map (.shift δ A) (.quotient N (.shift (0,e) (.nu X)))
    (levelQuotientShiftIso X e N).inv (s,(t-s)+s,t+e-K) _ _ ht
  convert hm using 1
  · rfl
  · simp only [finiteLevelNormalizedRepresentative,regrade_precomp,←Category.assoc,
      eqToHom_trans]
    rfl

/-- The target level is forced by the same actual source weight; this
comparison preserves the specified y. -/
private theorem finite_level_target_label (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N K J : ℕ) (n s t : ℤ)
    (hn : (normalizedExponent background.classicalTower f : ℤ) ≤ n)
    (hJ : (J:ℤ) = K+n-normalizedExponent background.classicalTower f)
    (y : Ambient background Y (s+n,t+n)) :
    regradeE2 (by ext <;> dsimp <;> omega)
      (finiteTargetLabel background Y N (s+n) (t+n) J y) =
      levelFiniteTargetLabel X Y f N K n s t hn y := by
  have hpow : ((t+n)-(t+normalizedExponent background.classicalTower f-K)).toNat=J := by
    omega
  unfold levelFiniteTargetLabel finiteTargetLabel nuWeightLabel
  change regradeE2 _ (familyPageMap background.family (XModLambdaN.incl _ N) 2 _ _) =
    regradeE2 _ (familyPageMap background.family (XModLambdaN.incl _ N) 2 _ (regradeE2 _ _))
  simp only [page_regrade,normalized_regrade_trans]
  have labels (k k' : ℕ) (hk : k=k') (p : Tridegree)
      (h₁ : (s+n,t+n,t+n-k)=p) (h₂ : (s+n,t+n,t+n-k')=p) :
      regradeE2 h₁ (targetNuLabel background Y (s+n) (t+n) k y) =
        regradeE2 h₂ (targetNuLabel background Y (s+n) (t+n) k' y) := by
    subst k'
    rfl
  exact congrArg (familyPageMap background.family (XModLambdaN.incl _ N) 2
    (s+n,(t-s)+(s+n),t+normalizedExponent background.classicalTower f-K))
      (labels _ _ hpow.symm _ _ _)

/-- Actual detected representatives for the same normalized finite map give
the complete level-extension witness, with arbitrary target object Y. -/
private theorem finite_level_extension_of_detected_pair
    (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page K J : ℕ) (n s t : ℤ) (hpage : 2 ≤ page)
    (hn : (normalizedExponent background.classicalTower f : ℤ) ≤ n)
    (hnUpper : n ≤ (page:ℤ)-2+normalizedExponent background.classicalTower f)
    (hJ : (J:ℤ) = K+n-normalizedExponent background.classicalTower f)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n))
    (a : BiHom (t-s) (t+normalizedExponent background.classicalTower f-K)
      ((SyntheticObject.quotient (page+K-1) (extensionSourceObject background X Y f)).obj
        background.nu background.auxiliary))
    (ha : Detects (background.convergence
      (.quotient (page+K-1) (extensionSourceObject background X Y f)))
      (s,(t-s)+s,t+normalizedExponent background.classicalTower f-K)
      (KIP126.ProofTools.Standard.levelFiniteSourceLabel X (page+K-1)
        (normalizedExponent background.classicalTower f) s t K x)
      (homotopyRegrade (by dsimp; omega) rfl a))
    (hb : Detects (background.convergence (.quotient (page+K-1) (.nu Y)))
      (s+n,t+n,t+n-J)
      (finiteTargetLabel background Y (page+K-1) (s+n) (t+n) J y)
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (a ≫ finiteExtensionMap background X Y f (page+K-1)))) :
    KIP126.ProofTools.Standard.LevelFiniteExtension X Y f page K n s t x y := by
  have hp : (s+n,t+n,t+n-J)=
      (s+n,(t-s)+(s+n),t+normalizedExponent background.classicalTower f-K) := by
    ext <;> dsimp <;> omega
  have hb' := detects_transport hp _ _ hb
  rw [finite_level_target_label X Y f (page+K-1) K J n s t hn hJ y] at hb'
  obtain ⟨source,target,hs,ht,heq⟩ := extension_equation_of_detected_pair
    (background.convergentMap
      (.quotient (page+K-1) (extensionSourceObject background X Y f))
      (.quotient (page+K-1) (.nu Y)) (finiteExtensionMap background X Y f (page+K-1)))
    (t-s,t+normalizedExponent background.classicalTower f-K) s n
    (by have := normalizedExponent_le_one background.classicalTower f; omega)
    _ _ a (a ≫ finiteExtensionMap background X Y f (page+K-1)) ha
    (by simpa only [regrade_precomp,←Category.assoc,eqToHom_trans] using hb') rfl
  exact ⟨hpage,hn,hnUpper,source,target,hs,ht,heq⟩

/-- A native common representative and its actual normalized f image give
the level extension in the full quotient N.  The effective classical page
is N-K+1, and J<N is exactly its target visibility bound. -/
private theorem finite_level_extension_of_native_representative
    (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N K J : ℕ) (hKN : K < N) (hJN : J < N) (n s t : ℤ)
    (hn : (normalizedExponent background.classicalTower f : ℤ) ≤ n)
    (hJ : (J:ℤ) = K+n-normalizedExponent background.classicalTower f)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n))
    (c : BiHom (t-s) (t-K)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (hc : Detects (background.convergence (.quotient N (.nu X))) (s,t,t-K)
      (finiteTargetLabel background X N s t K x) c)
    (hf : Detects (background.convergence (.quotient N (.nu Y)))
      (s+n,t+n,t+n-J) (finiteTargetLabel background Y N (s+n) (t+n) J y)
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (finiteLevelNormalizedRepresentative X (normalizedExponent background.classicalTower f)
          N K s t c ≫ finiteExtensionMap background X Y f N))) :
    KIP126.ProofTools.Standard.LevelFiniteExtension X Y f (N-K+1) K n s t x y := by
  have hq : (N-K+1)+K-1=N := by omega
  have ha := finite_level_normalized_representative_detects X
    (normalizedExponent background.classicalTower f) N K s t x c hc
  have result := finite_level_extension_of_detected_pair X Y f (N-K+1) K J n s t
    (by omega) hn (by omega) hJ x y
  rw [hq] at result
  exact result (finiteLevelNormalizedRepresentative X
    (normalizedExponent background.classicalTower f) N K s t c) ha hf

/-- The complete common-representative label assembly: rho fixes the source
label and its higher-cycle qualification, while the actual f image fixes
the target label in the same strong quotient. -/
private theorem finite_level_extension_of_common_representative
    (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (A N K J : ℕ) (hAN : A ≤ N) (hKA : K < A) (hJN : J < N)
    (n s t : ℤ)
    (hn : (normalizedExponent background.classicalTower f : ℤ) ≤ n)
    (hJ : (J:ℤ) = K+n-normalizedExponent background.classicalTower f)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n))
    (a : BiHom (t-s) (t-K)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) A))
    (ha : Detects (background.convergence (.quotient A (.nu X))) (s,t,t-K)
      (finiteTargetLabel background X A s t K x) a)
    (c : BiHom (t-s) (t-K)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (hρ : c ≫ (background.quotients.tower _).rho A N hAN = a)
    (hf : Detects (background.convergence (.quotient N (.nu Y)))
      (s+n,t+n,t+n-J) (finiteTargetLabel background Y N (s+n) (t+n) J y)
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (finiteLevelNormalizedRepresentative X (normalizedExponent background.classicalTower f)
          N K s t c ≫ finiteExtensionMap background X Y f N))) :
    x ∈ cycles background X ((N:ℤ)-K) (s,t) ∧
      KIP126.ProofTools.Standard.LevelFiniteExtension X Y f (N-K+1) K n s t x y := by
  obtain ⟨hc,hx⟩ := finite_rho_lift_label_and_cycles X A N K hAN hKA s t x a ha c hρ
  exact ⟨hx,finite_level_extension_of_native_representative X Y f N K J (by omega)
    hJN n s t hn hJ x y c hc hf⟩

end
end KIP126.ProofTools.Internal.Mahowald
