module

public import KIP126.ProofTools.MahowaldLeibniz
public import KIP126.ProofTools.GeneralizedMahowald.Coherence
public import KIP126.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.ProofTools.MahowaldLeibniz.CommonCore
import all KIP126.ProofTools.MahowaldLeibniz.ClassicalComposition
import all KIP126.ProofTools.MahowaldLeibniz.TopTarget

import all KIP126.ProofTools.MahowaldLeibniz.FiniteCore
import all KIP126.ProofTools.MahowaldLeibniz.CoreAtLevel
import all KIP126.ProofTools.MahowaldLeibniz.PositiveBranches
import all KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch
import all KIP126.ProofTools.MahowaldLeibniz.ClassicalStatements
import all KIP126.ProofTools.GeneralizedMahowald.Coherence

/-!
# Public finite-quotient and classical composition theorems

The finite core retains the three exhaustive normalization coordinates of
one selected triangle, its quotient representatives, and their images.
The auxiliary coordinate maps are defined by the fixed model.
-/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000

/-- The additive criterion for lifting a member of the specified correction family. -/
public theorem representativeFamilyLift_iff
    {D A C : Type*} [AddCommGroup D] [AddCommGroup A] [AddCommGroup C]
    (q : D →+ A) (δ : A →+ C)
    (hexact : ∀ a : A, δ a = 0 ↔ ∃ d : D, q d = a)
    (V : AddSubgroup A) (a₀ : A) :
    (∃ v : A, v ∈ V ∧ ∃ d : D, q d = a₀ + v) ↔ δ a₀ ∈ V.map δ :=
  representative_family_has_lift_iff_boundary_mem q δ hexact V a₀

/-- Surjectivity of the actual graded h-maps through every higher layer
annihilates the entire ambiguity subgroup. The H filtration records the
actual normalized h shift. -/
public theorem finiteSurjectiveAmbiguityZero
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B)
    (E : ℤ → AddSubgroup A) (L : ℤ → AddSubgroup H)
    (hL : Antitone L) (hfh : ∀ b : H, f (h b) = 0)
    (S eₕ : ℤ) (K : ℕ) (hK : 2 ≤ K)
    (hsurj : ∀ j : ℤ, 1 ≤ j → j < K → ∀ a : A, a ∈ E (S+j) →
      ∃ b : H, b ∈ L (S+j-eₕ) ∧ a-h b ∈ E (S+j+1))
    (hend : E (S+K) = ⊥) :
    ∀ a : A, a ∈ E (S+1) → f a = 0 := by
  intro a ha
  have hi := finite_level_surjectivity_image_eq h f E (fun k => L (k-eₕ))
    (fun i j hij => hL (by omega)) hfh S K hK hsurj hend a 0
    (by simpa only [sub_zero] using ha)
  simpa only [map_zero] using hi

/-- Collapse of the intermediate grades and zero action on the entire
last grade annihilate the ambiguity. The last source grade is allowed
to be nonzero and need not be an h-image. -/
public theorem finiteCollapsedAmbiguityZero
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (E : ℤ → AddSubgroup A) (F : ℤ → AddSubgroup B)
    (S e_f : ℤ) (K : ℕ) (hK : 2 ≤ K)
    (hcollapse : ∀ j : ℤ, 1 ≤ j → j < (K:ℤ)-1 →
      E (S+j) ≤ E (S+j+1))
    (hlast : ∀ a : A, a ∈ E (S+K-1) → f a ∈ F (S+e_f+K))
    (htarget : F (S+e_f+K) = ⊥) :
    ∀ a : A, a ∈ E (S+1) → f a = 0 := by
  intro a ha
  have hi := finite_level_collapsed_image_eq (0 : ℤ →+ A) f E
    (fun _ => (⊥ : AddSubgroup ℤ)) (fun _ _ _ => le_rfl)
    (fun _ => by simp) S K hK hcollapse
    (fun b hb => by simpa only [htarget, AddSubgroup.mem_bot] using hlast b hb) a 0
    (by simpa only [sub_zero] using ha)
  simpa only [map_zero] using hi

public def FiniteQuotientFirstCoreStatement
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (_hg : normalizedExponent background.classicalTower T.g = 0)
    (_hh : normalizedExponent background.classicalTower T.h = 0) : Prop :=
  let biSuspensionHomEquiv (n w q : ℤ) (Q : SyntheticSpectrum) :
      BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) ≃
        BiHom (n - 1) (w + q) Q := by
    let e : BiHom (n - 1) (w + q) Q ≃
        BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) := by
      simpa only [sub_add_cancel, add_neg_cancel_right] using
        ((susp_invariance (n - 1) (w + q) 1 (-q) Q).trans
          (Iso.homCongr (Iso.refl _) (biSuspensionIso q Q)))
    exact e.symm
  let nativeFirstLabel (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
      (x : Ambient background X (s,t)) :
      BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1) :=
    firstLabel background X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1
  let finiteCoefficientShiftClass (A : SyntheticSpectrum)
      (N c : ℕ) (hcN : c<N) (m w : ℤ)
      (a : BiHom m w (XModLambdaN A (N-c))) :
      BiHom m (w-c) (XModLambdaN A N) := by
    by_cases hc : c=0
    · subst c
      exact homotopyRegrade rfl (by simp) a
    · exact homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
        (shiftHomotopyClass (0,-(c:ℤ)) (m,w) a) ≫
        ((background.quotients.tower A).triangle (show 0<c by omega) hcN).lambdaMap
  let finiteCoefficientInsert (A : SyntheticSpectrum)
      (c K : ℕ) (hK : 0<K) (m w : ℤ)
      (a : BiHom m w (XModLambdaN A K)) :
      BiHom m (w-c) (XModLambdaN A (c+K)) :=
    finiteCoefficientShiftClass A (c+K) c (by omega) m w
      (by simpa only [Nat.add_sub_cancel_left,SyntheticObject.obj] using a)
  let quotientUnshift (X : AdamsObject (coefficients := background.coefficients)) (δ p : ℤ × ℤ) (q : ℕ)
      (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
          (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
        (SyntheticCategory.biShift δ).obj
          (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
      (a : BiHom (p+δ).1 (p+δ).2 (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q)) :
      BiHom p.1 p.2 (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q) :=
    (SyntheticCategory.biShift_fullyFaithful δ).preimage
      ((SyntheticCategory.biShift_comp p δ).hom.app S_0_0 ≫ a ≫ ε.hom)
  let normalizedSuspensionNativeIso
      (T : TriangleData background.auxiliary)
      (he : (normalizedExponent background.classicalTower T.f : ℤ) +
        normalizedExponent background.classicalTower T.g +
        normalizedExponent background.classicalTower T.h = 1)
      (hf : normalizedExponent background.classicalTower T.f = 1) :
      ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) ≅
        background.nu.functor.obj ((AdamsObject.shift 1 T.X).obj background.auxiliary) :=
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
      (SyntheticCategory.biShift_comp
        (0,(normalizedExponent background.classicalTower T.f:ℤ)) (1,0)).app _ ≪≫
      eqToIso (congrArg (fun p : ℤ×ℤ => (SyntheticCategory.biShift p).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary)))
        (show (0,(normalizedExponent background.classicalTower T.f:ℤ))+(1,0)=(1,1)
          by ext <;> dsimp <;> omega)) ≪≫
      (background.nu.suspensionIso (T.X.obj background.auxiliary)).symm
  let rawMaySourceDesuspend
      (T : TriangleData background.auxiliary)
      (he : (normalizedExponent background.classicalTower T.f : ℤ) +
        normalizedExponent background.classicalTower T.g +
        normalizedExponent background.classicalTower T.h = 1)
      (hf : normalizedExponent background.classicalTower T.f = 1)
      (N c : ℕ) (S V : ℤ)
      (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
        (SyntheticCategory.biShift (1,1)).obj
          (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
      (a : BiHom (V-S+1) (V-c+1)
        (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N)) :
      BiHom (V-S) (V-c) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N) :=
    quotientUnshift T.X (1,1) (V-S,V-c) N ε
      (homotopyRegrade rfl rfl
        (a ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N ≫
          XModLambdaN.map (background.nu.suspensionIso (T.X.obj background.auxiliary)).hom N))
  ∀ (c q : ℕ) (hq : 0<q) (S V : ℤ)
    (u : Ambient background T.X (S,V)) (z : Ambient background T.Z (S,V+1))
    (v : Ambient background T.Y (S+q+1,(V+1)+q)),
    (background.classicalSuspension T.X).DesuspendsClass S (V+1)
      ((background.classical.map T.h).pageMap 2 (S,V+1) z) (by simpa using u) →
    HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (S,V+1) (S+q+1,(V+1)+q) z
      ((background.classical.map T.g).pageMap 2 (S+q+1,(V+1)+q) v) →
    ∀ (ey : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ (q+1))⟦(1:ℤ)⟧),
    XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)) →
    ∀ (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1)))),
    XModLambdaN.incl _ (c+(q+1)) ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (c+(q+1))) →
    let N := normalizedTriangle background T he
    let b := (biSuspensionHomEquiv ((V+1)-S) (V+1) (q:ℤ)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1)).symm
        (homotopyRegrade (show ((V+1)+q)-(S+q+1)=((V+1)-S)-1 by omega) rfl
          (nativeFirstLabel T.Y (S+q+1) ((V+1)+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN N.obj₂ 1) ⟶
        XModLambdaN N.obj₂ (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((background.quotients.tower N.obj₂).triangle hq (Nat.lt_succ_self q)).lambdaMap
    let target :=
      homotopyRegrade (show (V+1)-S=V-S+1 by omega) (show (V+1)-c=V-c+1 by omega)
        (finiteCoefficientInsert (N.obj₂⟦(1:ℤ)⟧) c (q+1) (by omega) ((V+1)-S) (V+1)
          ((-(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly)) ≫ ey.inv))
    (∃ a : BiHom (V-S+1) (V-c+1) (XModLambdaN (N.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      Detects (background.convergence (.quotient (c+(q+1)) (.nu T.X)))
        (S,V,V-c) (finiteTargetLabel background T.X (c+(q+1)) S V c u)
        (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε a) ∧
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁)
        (c+(q+1)) = target ∧
      IsCycle background T.X (q+1) (S,V) u) ∧
    ((∀ a : BiHom (V-S+1) (V-c+1) (XModLambdaN (N.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      FiltrationAtLeast background.syntheticTower (S+1)
        (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε a) →
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁)
        (c+(q+1)) = 0) →
      ∀ d : BiHom (V-S+1) (V-c+1) (XModLambdaN (N.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      Detects (background.convergence (.quotient (c+(q+1)) (.nu T.X)))
        (S,V,V-c) (finiteTargetLabel background T.X (c+(q+1)) S V c u)
        (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε d) →
      d ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁)
        (c+(q+1)) = target)

public def FiniteQuotientSecondCoreStatement
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (_hh : normalizedExponent background.classicalTower T.h=0) : Prop :=
  let biSuspensionHomEquiv (n w q : ℤ) (Q : SyntheticSpectrum) :
      BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) ≃
        BiHom (n - 1) (w + q) Q := by
    let e : BiHom (n - 1) (w + q) Q ≃
        BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) := by
      simpa only [sub_add_cancel, add_neg_cancel_right] using
        ((susp_invariance (n - 1) (w + q) 1 (-q) Q).trans
          (Iso.homCongr (Iso.refl _) (biSuspensionIso q Q)))
    exact e.symm
  let nativeFirstLabel (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
      (x : Ambient background X (s,t)) :
      BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1) :=
    firstLabel background X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1
  let finiteCoefficientShiftClass (A : SyntheticSpectrum)
      (N c : ℕ) (hcN : c<N) (m w : ℤ)
      (a : BiHom m w (XModLambdaN A (N-c))) :
      BiHom m (w-c) (XModLambdaN A N) := by
    by_cases hc : c=0
    · subst c
      exact homotopyRegrade rfl (by simp) a
    · exact homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
        (shiftHomotopyClass (0,-(c:ℤ)) (m,w) a) ≫
        ((background.quotients.tower A).triangle (show 0<c by omega) hcN).lambdaMap
  let finiteCoefficientInsert (A : SyntheticSpectrum)
      (c K : ℕ) (hK : 0<K) (m w : ℤ)
      (a : BiHom m w (XModLambdaN A K)) :
      BiHom m (w-c) (XModLambdaN A (c+K)) :=
    finiteCoefficientShiftClass A (c+K) c (by omega) m w
      (by simpa only [Nat.add_sub_cancel_left,SyntheticObject.obj] using a)
  let positiveFirstQuotientOperation (X Y : AdamsObject (coefficients := background.coefficients))
      (F : (SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
          background.nu.functor.obj (Y.obj background.auxiliary))
      (s t : ℤ) (x : Ambient background X (s,t)) : Ambient background Y (s+1,t+1) :=
    background.firstQuotient Y 0 (s+1) (t+1)
      (homotopyRegrade (by omega) (by omega)
        ((background.firstQuotient X 1 s t).symm x ≫ XModLambdaN.map F 1 ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) 1))
  let zero_positive_iso (A : SyntheticSpectrum) (k : ℕ) (hk : k=0) :
      (SyntheticCategory.biShift (0,(k:ℤ))).obj A ≅ A :=
    eqToIso (congrArg (fun j : ℕ => (SyntheticCategory.biShift (0,(j:ℤ))).obj A) hk) ≪≫
      SyntheticCategory.biShift_zero.app A
  let normalizedSuspensionZeroIso (T : TriangleData background.auxiliary)
      (he : (normalizedExponent background.classicalTower T.f : ℤ)+
        normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
      (hf : normalizedExponent background.classicalTower T.f=0) :
      ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) ≅
        (SyntheticCategory.biShift (1,0)).obj (background.nu.functor.obj (T.X.obj background.auxiliary)) :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      (zero_positive_iso (background.nu.functor.obj (T.X.obj background.auxiliary)) _ hf) ≪≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _
  let quotientUnshift (X : AdamsObject (coefficients := background.coefficients)) (δ p : ℤ × ℤ) (q : ℕ)
      (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
          (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
        (SyntheticCategory.biShift δ).obj
          (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
      (a : BiHom (p+δ).1 (p+δ).2 (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q)) :
      BiHom p.1 p.2 (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q) :=
    (SyntheticCategory.biShift_fullyFaithful δ).preimage
      ((SyntheticCategory.biShift_comp p δ).hom.app S_0_0 ≫ a ≫ ε.hom)
  let positiveHSourceDesuspend
      (T : TriangleData background.auxiliary)
      (he : (normalizedExponent background.classicalTower T.f : ℤ)+
        normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
      (hf : normalizedExponent background.classicalTower T.f=0)
      (N c : ℕ) (s t : ℤ)
      (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
        (SyntheticCategory.biShift (1,0)).obj
          (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
      (a : BiHom (t-s) (t-c)
        (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N)) :
      BiHom (t-(s+1)) (t-c) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N) :=
    quotientUnshift T.X (1,0) (t-(s+1),t-c) N ε
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom N))
  let normalizedSecondPositiveMap
      (T : TriangleData background.auxiliary)
      (hg : normalizedExponent background.classicalTower T.g = 1) :
      (SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.Y.obj background.auxiliary)) ⟶
          background.nu.functor.obj (T.Z.obj background.auxiliary) :=
    eqToHom (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
      (background.nu.functor.obj (T.Y.obj background.auxiliary))) hg.symm) ≫
      (background.normalizedMap T.Y T.Z T.g).map
  ∀ (c q : ℕ) (_hq : 0<q) (s t : ℤ)
    (z : Ambient background T.Z (s+1,t+1)) (u : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+q+1,t+q)),
    (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((background.classical.map T.h).pageMap 2 (s+1,t+1) z) (by simpa using u) →
    HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+1,t+1) ((s+q+1)+1,(t+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (s+q+1) (t+q) v) →
    ∀ (ey : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ (q+1))⟦(1:ℤ)⟧),
    XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)) →
    ∀ (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1)))),
    XModLambdaN.incl _ (c+(q+1)) ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (c+(q+1))) →
    let V := normalizedTriangle background T he
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel T.Y (s+q+1) (t+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN V.obj₂ 1) ⟶
        XModLambdaN V.obj₂ (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((background.quotients.tower V.obj₂).triangle _hq (Nat.lt_succ_self q)).lambdaMap
    let target := finiteCoefficientInsert (V.obj₂⟦(1:ℤ)⟧) c (q+1) (by omega) (t-s) t
      ((-(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly)) ≫ ey.inv)
    IsCycle background T.X (q+1) (s+1,t) u ∧
    ∃ a : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      Detects (background.convergence (.quotient (c+(q+1)) (.nu T.X)))
        (s+1,t,t-c) (finiteTargetLabel background T.X (c+(q+1)) (s+1) t c u)
        (positiveHSourceDesuspend T he hf (c+(q+1)) c s t ε a) ∧
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁)
        (c+(q+1)) = target ∧
      ((∀ d : BiHom (t-(s+1)) (t-c)
          (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))),
        FiltrationAtLeast background.syntheticTower (s+2) d →
          d ≫ XModLambdaN.map (background.nu.functor.map T.f) (c+(q+1)) = 0) →
        ∀ d : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
        Detects (background.convergence (.quotient (c+(q+1)) (.nu T.X)))
          (s+1,t,t-c) (finiteTargetLabel background T.X (c+(q+1)) (s+1) t c u)
          (positiveHSourceDesuspend T he hf (c+(q+1)) c s t ε d) →
        d ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁)
          (c+(q+1)) = target)

public def FiniteQuotientThirdCoreStatement
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (_hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
 : Prop :=
  let biSuspensionHomEquiv (n w q : ℤ) (Q : SyntheticSpectrum) :
      BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) ≃
        BiHom (n - 1) (w + q) Q := by
    let e : BiHom (n - 1) (w + q) Q ≃
        BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) := by
      simpa only [sub_add_cancel, add_neg_cancel_right] using
        ((susp_invariance (n - 1) (w + q) 1 (-q) Q).trans
          (Iso.homCongr (Iso.refl _) (biSuspensionIso q Q)))
    exact e.symm
  let nativeFirstLabel (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
      (x : Ambient background X (s,t)) :
      BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1) :=
    firstLabel background X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1
  let finiteCoefficientShiftClass (A : SyntheticSpectrum)
      (N c : ℕ) (hcN : c<N) (m w : ℤ)
      (a : BiHom m w (XModLambdaN A (N-c))) :
      BiHom m (w-c) (XModLambdaN A N) := by
    by_cases hc : c=0
    · subst c
      exact homotopyRegrade rfl (by simp) a
    · exact homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
        (shiftHomotopyClass (0,-(c:ℤ)) (m,w) a) ≫
        ((background.quotients.tower A).triangle (show 0<c by omega) hcN).lambdaMap
  let finiteCoefficientInsert (A : SyntheticSpectrum)
      (c K : ℕ) (hK : 0<K) (m w : ℤ)
      (a : BiHom m w (XModLambdaN A K)) :
      BiHom m (w-c) (XModLambdaN A (c+K)) :=
    finiteCoefficientShiftClass A (c+K) c (by omega) m w
      (by simpa only [Nat.add_sub_cancel_left,SyntheticObject.obj] using a)
  let positiveFirstQuotientOperation (X Y : AdamsObject (coefficients := background.coefficients))
      (F : (SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
          background.nu.functor.obj (Y.obj background.auxiliary))
      (s t : ℤ) (x : Ambient background X (s,t)) : Ambient background Y (s+1,t+1) :=
    background.firstQuotient Y 0 (s+1) (t+1)
      (homotopyRegrade (by omega) (by omega)
        ((background.firstQuotient X 1 s t).symm x ≫ XModLambdaN.map F 1 ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) 1))
  let zero_positive_iso (A : SyntheticSpectrum) (k : ℕ) (hk : k=0) :
      (SyntheticCategory.biShift (0,(k:ℤ))).obj A ≅ A :=
    eqToIso (congrArg (fun j : ℕ => (SyntheticCategory.biShift (0,(j:ℤ))).obj A) hk) ≪≫
      SyntheticCategory.biShift_zero.app A
  let normalizedSuspensionZeroIso (T : TriangleData background.auxiliary)
      (he : (normalizedExponent background.classicalTower T.f : ℤ)+
        normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
      (hf : normalizedExponent background.classicalTower T.f=0) :
      ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) ≅
        (SyntheticCategory.biShift (1,0)).obj (background.nu.functor.obj (T.X.obj background.auxiliary)) :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      (zero_positive_iso (background.nu.functor.obj (T.X.obj background.auxiliary)) _ hf) ≪≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _
  let quotientUnshift (X : AdamsObject (coefficients := background.coefficients)) (δ p : ℤ × ℤ) (q : ℕ)
      (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
          (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
        (SyntheticCategory.biShift δ).obj
          (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
      (a : BiHom (p+δ).1 (p+δ).2 (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q)) :
      BiHom p.1 p.2 (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q) :=
    (SyntheticCategory.biShift_fullyFaithful δ).preimage
      ((SyntheticCategory.biShift_comp p δ).hom.app S_0_0 ≫ a ≫ ε.hom)
  let positiveHSourceDesuspend
      (T : TriangleData background.auxiliary)
      (he : (normalizedExponent background.classicalTower T.f : ℤ)+
        normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
      (hf : normalizedExponent background.classicalTower T.f=0)
      (N c : ℕ) (s t : ℤ)
      (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
        (SyntheticCategory.biShift (1,0)).obj
          (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
      (a : BiHom (t-s) (t-c)
        (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N)) :
      BiHom (t-(s+1)) (t-c) (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N) :=
    quotientUnshift T.X (1,0) (t-(s+1),t-c) N ε
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom N))
  let positiveHMap (T : TriangleData background.auxiliary)
      (hh : normalizedExponent background.classicalTower T.h=1) :
      (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (T.Z.obj background.auxiliary)) ⟶
        background.nu.functor.obj ((AdamsObject.shift 1 T.X).obj background.auxiliary) := by
    simpa only [hh,Nat.cast_one] using (background.normalizedMap T.Z (.shift 1 T.X) T.h).map
  ∀ (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient background T.Z (s,t)) (u : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using u))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z
      ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
    (ey : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ (q+1))⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)))
    (εN : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (hεN : XModLambdaN.incl _ (c+(q+1)) ≫ εN.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (c+(q+1)))),
    let V := normalizedTriangle background T he
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel T.Y (s+q+1) (t+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN V.obj₂ 1) ⟶
        XModLambdaN V.obj₂ (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((background.quotients.tower V.obj₂).triangle hq (Nat.lt_succ_self q)).lambdaMap
    ∃ a : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      Detects (background.convergence (.quotient (c+(q+1)) (.nu T.X)))
        (s+1,t,t-c) (finiteTargetLabel background T.X (c+(q+1)) (s+1) t c u)
        (positiveHSourceDesuspend T he hf (c+(q+1)) c s t εN a) ∧
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (c+(q+1)) =
        finiteCoefficientInsert (V.obj₂⟦(1:ℤ)⟧) c (q+1) (by omega) (t-s) t
          ((-(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly)) ≫ ey.inv) ∧
      IsCycle background T.X (q+1) (s+1,t) u ∧
      ((∀ e : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
        FiltrationAtLeast background.syntheticTower ((s+1)+1)
          (positiveHSourceDesuspend T he hf (c+(q+1)) c s t εN e) →
        e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (c+(q+1))=0) →
        ∀ d : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
          Detects (background.convergence (.quotient (c+(q+1)) (.nu T.X)))
            (s+1,t,t-c) (finiteTargetLabel background T.X (c+(q+1)) (s+1) t c u)
            (positiveHSourceDesuspend T he hf (c+(q+1)) c s t εN d) →
          d ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (c+(q+1)) =
            a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (c+(q+1)))

/-- The finite-quotient core in all three exponent positions, identifying
each signed coefficient output with the highest-layer inclusion.
The statement quantifies every level, coherent shift comparison, and label. -/
public def FiniteQuotientMahowaldLeibnizCoreStatement
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1) : Prop :=
  let exactTopTarget : Prop :=
    let biSuspensionHomEquiv (n w q : ℤ) (Q : SyntheticSpectrum) :
        BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) ≃
          BiHom (n - 1) (w + q) Q := by
      let e : BiHom (n - 1) (w + q) Q ≃
          BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) := by
        simpa only [sub_add_cancel, add_neg_cancel_right] using
          ((susp_invariance (n - 1) (w + q) 1 (-q) Q).trans
            (Iso.homCongr (Iso.refl _) (biSuspensionIso q Q)))
      exact e.symm
    let nativeFirstLabel (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
        (x : Ambient background X (s,t)) :
        BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1) :=
      firstLabel background X s t x ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1
    let finiteCoefficientShiftClass (A : SyntheticSpectrum)
        (N c : ℕ) (hcN : c<N) (m w : ℤ)
        (a : BiHom m w (XModLambdaN A (N-c))) :
        BiHom m (w-c) (XModLambdaN A N) := by
      by_cases hc : c=0
      · subst c
        exact homotopyRegrade rfl (by simp) a
      · exact homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
          (shiftHomotopyClass (0,-(c:ℤ)) (m,w) a) ≫
          ((background.quotients.tower A).triangle (show 0<c by omega) hcN).lambdaMap
    let finiteCoefficientInsert (A : SyntheticSpectrum)
        (c K : ℕ) (hK : 0<K) (m w : ℤ)
        (a : BiHom m w (XModLambdaN A K)) :
        BiHom m (w-c) (XModLambdaN A (c+K)) :=
      finiteCoefficientShiftClass A (c+K) c (by omega) m w
        (by simpa only [Nat.add_sub_cancel_left,SyntheticObject.obj] using a)
    let oneInclusionCast (A B : SyntheticSpectrum) (d n : ℕ) (hn : n=1)
        (l : (SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A n) ⟶ B) :
        (SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A 1) ⟶ B := hn ▸ l
    let finiteTopInclusion (A : SyntheticSpectrum) (d : ℕ) (hd : 0 < d) :
        (SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A 1) ⟶
          XModLambdaN A (d+1) :=
      oneInclusionCast A _ d ((d+1)-d) (by omega)
        ((background.quotients.tower A).triangle hd (Nat.lt_succ_self d)).lambdaMap
    let finiteTopOfFirst (A : SyntheticSpectrum) (d : ℕ) (hd : 0 < d)
        (m w : ℤ) (a : BiHom m w (XModLambdaN A 1)) :
        BiHom m (w-d) (XModLambdaN A (d+1)) :=
      homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
        (shiftHomotopyClass (0,-(d:ℤ)) (m,w) a) ≫ finiteTopInclusion A d hd
    let finiteTopLabel (X : AdamsObject (coefficients := background.coefficients)) (d : ℕ) (hd : 0 < d)
        (s t : ℤ) (x : Ambient background X (s,t)) :
        BiHom (t-s) (t-d)
          (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)) :=
      finiteTopOfFirst _ d hd (t-s) t (nativeFirstLabel X s t x)
    let finiteTopLabelAtWeight (X : AdamsObject (coefficients := background.coefficients)) (d : ℕ) (hd : 0<d)
        (N : ℕ) (hN : d+1=N) (s t w : ℤ) (hw : t-d=w)
        (x : Ambient background X (s,t)) :
        BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N) :=
      hN ▸ homotopyRegrade rfl hw (finiteTopLabel X d hd s t x)
    let finiteMayTopLabel (X : AdamsObject (coefficients := background.coefficients)) (c q : ℕ) (hq : 0<q)
        (s t : ℤ) (v : Ambient background X (s+q+1,t+q)) :
        BiHom ((t-s)-1) (t-c)
          (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (c+(q+1))) :=
      homotopyRegrade (by omega) rfl
        (finiteTopLabelAtWeight X (c+q) (by omega) (c+(q+1)) (by omega)
          (s+q+1) (t+q) (t-c) (by omega) v)
    let ordinarySuspendedRepresentative (A : SyntheticSpectrum) (m w : ℤ)
        (a : BiHom (m-1) w A) : BiHom m w (A⟦(1:ℤ)⟧) :=
      homotopyRegrade (by dsimp; omega) (by simp)
        (shiftHomotopyClass (1,0) (m-1,w) a) ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app A
    ∀ (X : AdamsObject (coefficients := background.coefficients)) (c q : ℕ) (hq : 0<q) (s t : ℤ)
      (v : Ambient background X (s+q+1,t+q))
      (en : XModLambdaN ((background.nu.functor.obj (X.obj background.auxiliary))⟦(1:ℤ)⟧) (q+1) ≅
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q+1))⟦(1:ℤ)⟧)
      (eN : XModLambdaN ((background.nu.functor.obj (X.obj background.auxiliary))⟦(1:ℤ)⟧) (c+(q+1)) ≅
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (c+(q+1)))⟦(1:ℤ)⟧)
      (hen : XModLambdaN.incl _ (q+1)≫en.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)))
      (heN : XModLambdaN.incl _ (c+(q+1))≫eN.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (c+(q+1)))),
      let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1)).symm
          (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
            (nativeFirstLabel X (s+q+1) (t+q) v))
      let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj
          (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1) ⟶
          XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q+1) := by
        simpa only [show q.succ-q=1 by omega] using
          ((background.quotients.tower _).triangle hq (Nat.lt_succ_self q)).lambdaMap
      finiteCoefficientInsert _ c (q+1) (by omega) (t-s) t
          ((-(b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map ly))≫en.inv)≫eN.hom =
        ordinarySuspendedRepresentative _ (t-s) (t-c) (finiteMayTopLabel X c q hq s t v)
  ((∀ hf hg hh, FiniteQuotientFirstCoreStatement T he hf hg hh) ∧
  (∀ hf hg hh, FiniteQuotientSecondCoreStatement T he hf hg hh) ∧
  (∀ hf hg hh, FiniteQuotientThirdCoreStatement T he hf hg hh)) ∧ exactTopTarget

/-- The common finite-quotient Mahowald theorem at every lambda level.
Its hypotheses are the actual classical differential and triangle
compatibility; its conclusion includes the original source cycle and
exact image of every same-label representative under ambiguity annihilation. -/
public theorem finiteQuotientMahowaldLeibnizCore
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1) :
    FiniteQuotientMahowaldLeibnizCoreStatement T he := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  refine ⟨finite_quotient_mahowald_leibniz_core T he hT, ?_⟩
  exact finite_may_signed_target_eq_top_at_level

public def normalizedClassicalOperation (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t : ℤ) (x : Ambient background X (s,t)) :
    Ambient background Y (s+normalizedExponent background.classicalTower f,
      t+normalizedExponent background.classicalTower f) :=
  background.firstQuotient Y 0
    (s+normalizedExponent background.classicalTower f)
    (t+normalizedExponent background.classicalTower f)
    (homotopyRegrade (by omega) (by omega)
      ((background.firstQuotient X (normalizedExponent background.classicalTower f) s t).symm x ≫
        XModLambdaN.map (background.normalizedMap X Y f).map 1 ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) 1))

public def ClassicalNCCompositionStatement
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1) : Prop :=
  let classicalLabelRegrade {X : AdamsObject (coefficients := background.coefficients)} {p q : ℤ×ℤ}
      (h : p=q) (x : Ambient background X p) : Ambient background X q := h ▸ x
  let ef := normalizedExponent background.classicalTower T.f
  let eg := normalizedExponent background.classicalTower T.g
  let eh := normalizedExponent background.classicalTower T.h
  ∀ (R K : ℕ), 2 ≤ R → 2 ≤ K → ∀ (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (z : Ambient background T.Z (s+R-eh,t+R-eh))
    (v : Ambient background T.Y (s+R+ef+K-1,t+R+ef+K-2)),
    IsCycle background T.X ((R:ℤ)-1) (s,t) x →
    IsCycle background T.Z ((K:ℤ)-1) (s+R-eh,t+R-eh) z →
    (∃ u : Ambient background T.X (s+R,t+R-1),
      (background.classicalSuspension T.X).DesuspendsClass (s+R) (t+R)
        (classicalLabelRegrade (X := .shift 1 T.X) (q := (s+R,t+R))
          (by dsimp only [eh]; ext <;> dsimp only [Prod.fst,Prod.snd] <;> omega)
          (normalizedClassicalOperation T.Z (.shift 1 T.X) T.h
            (s+R-eh) (t+R-eh) z)) u ∧
      DifferentialAt background T.X R (s,t) (s+R,t+R-1) x u) →
    DifferentialAt background T.Z K (s+R-eh,t+R-eh)
      (s+R-eh+K,t+R-eh+K-1) z
      (classicalLabelRegrade (X := T.Z) (q := (s+R-eh+K,t+R-eh+K-1)) (by
          dsimp only [ef,eg,eh]
          ext <;> dsimp only [Prod.fst,Prod.snd] <;> omega)
        (normalizedClassicalOperation T.Y T.Z T.g
          (s+R+ef+K-1) (t+R+ef+K-2) v)) →
    (∀ j : ℕ, 1 ≤ j → j < K-1 →
      cycles background T.X ((K:ℤ)-j) (s+R+j,t+R+j-1) ≤
        boundaries background T.X ((R:ℤ)+j-1) (s+R+j,t+R+j-1)) →
    (∀ a : Ambient background T.X (s+R+K-1,t+R+K-2),
      normalizedClassicalOperation T.X T.Y T.f
        (s+R+K-1) (t+R+K-2) a ∈
      boundaries background T.Y ((R:ℤ)+K-2)
        ((s+R+K-1)+ef,(t+R+K-2)+ef)) →
    let y := normalizedClassicalOperation T.X T.Y T.f s t x
    IsCycle background T.Y ((R:ℤ)+K-2) (s+ef,t+ef) y ∧
      DifferentialAt background T.Y ((R:ℤ)+K-1) (s+ef,t+ef)
        (s+R+ef+K-1,t+R+ef+K-2) y v

/-- The NC1/NC2 classical composition theorem, including all three
positions of the positive normalization exponent, the complete last-layer
NC2 condition and the specified output differential. -/
public theorem classicalNCComposition
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1) :
    ClassicalNCCompositionStatement T he :=
  classical_nc_composition T he

/-- Finite-layer surjectivity proves the fixed-model composition proposition,
with the selected first-quotient boundary as output. -/
public theorem finiteLayerSurjectivityMahowaldLeibniz
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0) :
    FiniteLayerSurjectivityMahowaldLeibnizStatement T hf hg hh :=
  finite_layer_surj_statement T hf hg hh

end
end KIP126.ProofTools.Standard
