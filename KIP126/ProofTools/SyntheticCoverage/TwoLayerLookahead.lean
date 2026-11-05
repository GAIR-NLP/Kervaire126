module

import all KIP126.ProofTools.SyntheticCoverage.RecursivePermanence

/-! Two-layer lookahead on a finite residual. The residual’s Q₂ restriction
is compared with the common representative. Its complete image and higher
terminal term yield permanence of the next label, and joint adjacent-layer
relations exclude the leading term of a higher-filtration error. The argument
uses the Q₂ projection equality of the complete class β. The three endpoints
cover the normalized f-, g-, and h-positive cases; each takes the finite
relation and its projection test as inputs. -/

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

private def lookaheadFinalTop (Y : (AdamsObject (coefficients := background.coefficients))) (j m : ℕ) (hm : 3≤m) (s t : ℤ)
    (v : Ambient background Y (s+m-1,t+m-1)) :
    BiHom (t-s) (t-j) (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (j+m)) :=
  homotopyRegrade (show (t+m-1)-(s+m-1)=t-s by omega) rfl
    (finiteTopLabelAtWeight Y (j+m-1) (by omega) (j+m) (by omega)
      (s+m-1) (t+m-1) (t-j) (by omega) v)

private theorem lookahead_final_top_high (Y : (AdamsObject (coefficients := background.coefficients))) (j m : ℕ) (hm : 3≤m) (s t : ℤ)
    (v : Ambient background Y (s+m-1,t+m-1)) :
    FiltrationAtLeast background.syntheticTower (s+2) (lookaheadFinalTop Y j m hm s t v) := by
  have hd := finite_top_label_at_weight_detects Y (j+m-1) (by omega) (j+m) (by omega)
    (s+m-1) (t+m-1) (t-j) (by omega) v
  have hfil := detects_filtration (.quotient (j+m) (.nu Y)) (s+m-1,t+m-1,t-j) _ _ hd
  apply background.syntheticTower.filtrationSubmodule_antitone _ _ (show s+2≤s+m-1 by omega)
  exact (regrade_filtration_iff _ _ _ _).mpr hfil

/-- Representatives with the same first label differ in Q₂
by a single top class. -/
private theorem lookahead_q2_difference
    (X : (AdamsObject (coefficients := background.coefficients))) (m : ℕ) (hm : 3≤m) (s t : ℤ)
    (e : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) m))
    (k : Ambient background X (s,t))
    (he : e≫(background.quotients.tower _).rho 1 m (by omega)=nativeFirstLabel X s t k)
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 2))
    (hc : c≫(background.quotients.tower _).rho 1 2 (by decide)=nativeFirstLabel X s t k) :
    ∃ u : Ambient background X (s+1,t+1),
      e≫(background.quotients.tower _).rho 2 m (by omega)=c+recursiveMiddleTopLabel X s t u := by
  let e₂ := e≫(background.quotients.tower _).rho 2 m (by omega)
  have he₂ : e₂≫(background.quotients.tower _).rho 1 2 (by decide)=nativeFirstLabel X s t k := by
    dsimp only [e₂]
    rw [Category.assoc,(background.quotients.tower _).rho_comp]
    exact he
  have hd := detects_sub_filtration (background.convergence (.quotient 2 (.nu X))) (s,t,t)
    (first_label_detects_unshifted X 2 (by decide) s t k e₂ he₂)
    (first_label_detects_unshifted X 2 (by decide) s t k c hc)
  let a := homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
    (show t=(t+1)-(1:ℕ) by omega) (e₂-c)
  have ha : FiltrationAtLeast background.syntheticTower (s+1) a := (regrade_filtration_iff _ _ _ _).mpr hd
  obtain ⟨u,hu⟩ := finiteTopLabel_exists X 1 (by decide) (s+1) (t+1) a ha
  have h := congrArg (homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
    (show (t+1)-(1:ℕ)=t by omega)) hu
  have hdiff : e₂-c=recursiveMiddleTopLabel X s t u := by
    simpa only [a,recursiveMiddleTopLabel,homotopy_regrade_inverse] using h
  exact ⟨u,by change e₂=_; rw [←hdiff]; abel⟩

private theorem lookahead_middle_top_add (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (x y : Ambient background X (s+1,t+1)) :
    recursiveMiddleTopLabel X s t (x+y)=recursiveMiddleTopLabel X s t x+recursiveMiddleTopLabel X s t y := by
  simp only [recursiveMiddleTopLabel,finite_top_label_add,regrade_add]

private theorem lookahead_middle_top_natural (X Y : (AdamsObject (coefficients := background.coefficients)))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (s t : ℤ)
    (x : Ambient background X (s+1,t+1)) :
    recursiveMiddleTopLabel X s t x≫XModLambdaN.map (background.nu.functor.map f) 2=
      recursiveMiddleTopLabel Y s t ((background.classical.map f).pageMap 2 (s+1,t+1) x) := by
  simp only [recursiveMiddleTopLabel,←regrade_comp,finite_top_label_ordinary_natural]

/-- Comparing the genuine Q₂ restriction with the common representative
produces the actual z+F₂u top, on the same image of the original e_m. -/
private theorem lookahead_ordinary_image_top
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (m : ℕ) (hm : 3≤m) (s t : ℤ)
    (e : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) m))
    (k : Ambient background X (s,t))
    (he : e≫(background.quotients.tower _).rho 1 m (by omega)=nativeFirstLabel X s t k)
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 2))
    (hc : c≫(background.quotients.tower _).rho 1 2 (by decide)=nativeFirstLabel X s t k)
    (z : Ambient background Y (s+1,t+1))
    (hcz : c≫XModLambdaN.map (background.nu.functor.map f) 2=recursiveMiddleTopLabel Y s t z) :
    ∃ u : Ambient background X (s+1,t+1),
      (e≫XModLambdaN.map (background.nu.functor.map f) m)≫(background.quotients.tower _).rho 2 m (by omega)=
        recursiveMiddleTopLabel Y s t (z+(background.classical.map f).pageMap 2 (s+1,t+1) u) := by
  obtain ⟨u,hu⟩ := lookahead_q2_difference X m hm s t e k he c hc
  refine ⟨u,?_⟩
  rw [Category.assoc,←(background.quotients.natural (background.nu.functor.map f)).rho_naturality (by omega),
    ←Category.assoc,hu,Preadditive.add_comp,hcz,lookahead_middle_top_natural,lookahead_middle_top_add]

private theorem lookahead_coefficient_insert_detects
    (Y : (AdamsObject (coefficients := background.coefficients))) (j m d : ℕ) (hd : d<m) (s t : ℤ)
    (z : Ambient background Y (s,t))
    (e : BiHom (t-s) (t-d) (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) m))
    (he : Detects (background.convergence (.quotient m (.nu Y))) (s,t,t-d)
      (finiteTargetLabel background Y m s t d z) e) :
    Detects (background.convergence (.quotient (j+m) (.nu Y))) (s,t,t-(j+d))
      (finiteTargetLabel background Y (j+m) s t (j+d) z)
      (homotopyRegrade rfl (show (t-d)-j=t-(j+d) by omega)
        (finiteCoefficientInsert _ j m (by omega) (t-s) (t-d) e)) := by
  have ha : Detects (background.convergence (.quotient (j+m-j) (.nu Y))) (s,t,t-d)
      (finiteTargetLabel background Y (j+m-j) s t d z)
      (by simpa only [Nat.add_sub_cancel_left,SyntheticObject.obj] using e) := by
    have transport (n : ℕ) (hn : n=m)
        (ht : BiHom (t-s) (t-d) (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) m)=
          BiHom (t-s) (t-d) (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) n)) :
        Detects (background.convergence (.quotient n (.nu Y))) (s,t,t-d)
          (finiteTargetLabel background Y n s t d z) (ht.mp e) := by
      subst n
      exact he
    exact transport _ (by omega) _
  exact finite_coefficient_shift_layer_detects Y (j+m) j d (by omega) (by omega) s t z _ ha

/-- The complete image makes the specified two-layer label permanent.
The bound `m ≥ 3` places the terminal term above this grade, yielding
the joint-relation condition. -/
private theorem lookahead_full_image_label_permanent
    (Y : (AdamsObject (coefficients := background.coefficients))) (j m : ℕ) (hm : 3≤m) (s t : ℤ)
    (e : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) m))
    (z : Ambient background Y (s+1,t+1))
    (he : e≫(background.quotients.tower _).rho 2 m (by omega)=recursiveMiddleTopLabel Y s t z)
    (β : BiHom (t-s) (t-j) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (v : Ambient background Y (s+m-1,t+m-1))
    (hβ : β≫XModLambdaN.incl _ (j+m)=
      finiteCoefficientInsert _ j m (by omega) (t-s) t e+lookaheadFinalTop Y j m hm s t v) :
    z ∈ permanentCycles background Y (s+1,t+1) := by
  let e' := homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
    (show t=(t+1)-(1:ℕ) by omega) e
  have he' : e'≫(background.quotients.tower _).rho 2 m (by omega)=
      finiteTopLabel Y 1 (by decide) (s+1) (t+1) z := by
    dsimp only [e']
    rw [←regrade_comp,he]
    simp only [recursiveMiddleTopLabel,homotopy_regrade_inverse]
  have hdet := finite_target_rho_detects Y 2 m 1 (by decide) (by omega) (s+1) (t+1) z
    _ (finiteTopLabel_detects Y 1 (by decide) (s+1) (t+1) z) e' he'
  have hi := lookahead_coefficient_insert_detects Y j m 1 (by omega)
    (s+1) (t+1) z e' hdet
  let b := finiteCoefficientInsert _ j m (by omega) (t-s) t e
  let β' := homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
    (show t-j=(t+1)-((j:ℤ)+(1:ℕ)) by omega) β
  have hib : Detects (background.convergence (.quotient (j+m) (.nu Y)))
      (s+1,t+1,(t+1)-((j:ℤ)+(1:ℕ))) (finiteTargetLabel background Y (j+m) (s+1) (t+1) (j+1) z)
      (homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
        (show t-j=(t+1)-((j:ℤ)+(1:ℕ)) by omega) b) := by
    convert hi using 1
    simp only [b,e',finite_coefficient_insert_regrade,last_layer_regrade_trans]
    rfl
  have hhigh : FiltrationAtLeast background.syntheticTower ((s+1)+1)
      (β'≫XModLambdaN.incl _ (j+m)-homotopyRegrade
        (show t-s=(t+1)-(s+1) by omega) (show t-j=(t+1)-((j:ℤ)+(1:ℕ)) by omega) b) := by
    dsimp only [β']
    rw [←regrade_comp,←homotopy_regrade_sub,hβ]
    have hcancel : finiteCoefficientInsert _ j m (by omega) (t-s) t e+
        lookaheadFinalTop Y j m hm s t v-b=lookaheadFinalTop Y j m hm s t v := by dsimp only [b]; abel
    rw [hcancel]
    exact (regrade_filtration_iff _ _ _ _).mpr (by
      convert lookahead_final_top_high Y j m hm s t v using 1
      omega)
  have hfull := detects_of_high_difference (.quotient (j+m) (.nu Y))
    (s+1,t+1,(t+1)-((j:ℤ)+(1:ℕ))) _ _ _ hib hhigh
  rw [←middle_finite_label_as_weight] at hfull
  exact KIP126.ProofTools.finite_target_from_full_lift_is_permanent Y (j+m) (by omega)
    (s+1) (t+1) ((t+1)-((j:ℤ)+(1:ℕ))) (by omega) z β' hfull

/-- Once the actual first label vanishes, triangle exactness divides the
same residual itself by one layer. -/
private theorem lookahead_divide_original_residual
    (X : (AdamsObject (coefficients := background.coefficients))) (m : ℕ) (hm : 3≤m) (s t : ℤ)
    (e : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) m))
    (he : e≫(background.quotients.tower _).rho 1 m (by omega)=0) :
    ∃ e' : BiHom (t-s) (t+1)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (m-1)),
      homotopyRegrade rfl (show (t+1)-(1:ℕ)=t by omega)
        (finiteCoefficientShiftClass _ m 1 (by omega) (t-s) (t+1) e')=e := by
  let a := homotopyRegrade rfl (show t=(t+1)-(1:ℕ) by omega) e
  have ha : a≫(background.quotients.tower _).rho 1 m (by omega)=0 := by
    dsimp only [a]
    rw [←regrade_comp,he,last_layer_regrade_zero]
  obtain ⟨e',he'⟩ := native_coefficient_preimage_of_zero_restriction _ m 1 (by decide)
    (by omega) (t-s) (t+1) a ha
  refine ⟨e',?_⟩
  rw [he']
  simp only [a,homotopy_regrade_inverse]

/-- The concluding step keeps the specified residual, including the next
coefficient preimage obtained from its own vanishing restriction. -/
private theorem lookahead_zero_head_divides
    (X : (AdamsObject (coefficients := background.coefficients))) (m : ℕ) (hm : 3≤m) (s t : ℤ)
    (e : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) m))
    (k : Ambient background X (s,t))
    (he : e≫(background.quotients.tower _).rho 1 m (by omega)=nativeFirstLabel X s t k)
    (hk : k=0) :
    k=0 ∧ ∃ e' : BiHom (t-s) (t+1)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (m-1)),
      homotopyRegrade rfl (show (t+1)-(1:ℕ)=t by omega)
        (finiteCoefficientShiftClass _ m 1 (by omega) (t-s) (t+1) e')=e := by
  refine ⟨hk,lookahead_divide_original_residual X m hm s t e ?_⟩
  rw [he,hk]
  simp only [nativeFirstLabel_eq_regrade,map_zero,last_layer_regrade_zero,zero_comp]

private def LookaheadPositiveHRelation
    (T : TriangleData background.auxiliary) (hh : normalizedExponent background.classicalTower T.h=1)
    (s t : ℤ) (U : Ambient background T.Z (s,t))
    (k : Ambient background T.X (s+1,t)) (z : Ambient background T.Y (s+1+1,t+1)) : Prop :=
  (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t U)
      (by simpa only [add_sub_cancel_right] using k) ∧
    HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
      (s,t) (s+1+1,t+1) U ((background.classical.map T.g).pageMap 2 (s+1+1,t+1) z)

/-- The complete two-layer relation, its surjectivity, and the full joint
projection test eliminate the actual high residual head (h-positive branch).
The next-layer condition is produced from the genuine full image equality. -/
private theorem two_layer_lookahead_positive_h
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (j m : ℕ) (hm : 3≤m) (s t : ℤ)
    (K₀ : Submodule ℤ (Ambient background T.X (s+1,t)))
    (_hK₀ : ∀ k∈K₀, (background.classical.map T.f).pageMap 2 (s+1,t) k=0 ∧
      k∈cycles background T.X m (s+1,t))
    (hsurj : ∀ k∈K₀, ∃ (U : Ambient background T.Z (s,t))
      (z : Ambient background T.Y (s+1+1,t+1)), LookaheadPositiveHRelation T hh s t U k z)
    (Pnext : Submodule ℤ (Ambient background T.Y (s+1+1,t+1)))
    (hP : permanentCycles background T.Y (s+1+1,t+1)≤Pnext)
    (hjoint : ∀ (U : Ambient background T.Z (s,t)) (k : Ambient background T.X (s+1,t))
      (z : Ambient background T.Y (s+1+1,t+1)) (u : Ambient background T.X (s+1+1,t+1)),
      k∈K₀ → LookaheadPositiveHRelation T hh s t U k z →
      z+(background.classical.map T.f).pageMap 2 (s+1+1,t+1) u∈Pnext → k=0)
    (e : BiHom (t-(s+1)) t
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) m))
    (k : Ambient background T.X (s+1,t)) (hk : k∈K₀)
    (hek : e≫(background.quotients.tower _).rho 1 m (by omega)=nativeFirstLabel T.X (s+1) t k)
    (β : BiHom (t-(s+1)) (t-j) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (v : Ambient background T.Y ((s+1)+m-1,t+m-1))
    (hβ : β≫XModLambdaN.incl _ (j+m)=
      finiteCoefficientInsert _ j m (by omega) (t-(s+1)) t
        (e≫XModLambdaN.map (background.nu.functor.map T.f) m)+
      lookaheadFinalTop T.Y j m hm (s+1) t v) :
    k=0 ∧ ∃ e' : BiHom (t-(s+1)) (t+1)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (m-1)),
      homotopyRegrade rfl (show (t+1)-(1:ℕ)=t by omega)
        (finiteCoefficientShiftClass _ m 1 (by omega) (t-(s+1)) (t+1) e')=e := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨U,z,hU,hd,c,hc,hcz⟩ := recursive_common_lift_positive_h T he hT hf hg hh
    s t K₀ hsurj k hk
  obtain ⟨u,hu⟩ := lookahead_ordinary_image_top T.X T.Y T.f m hm (s+1) t e k hek c hc z hcz
  have hp := lookahead_full_image_label_permanent T.Y j m hm (s+1) t
    (e≫XModLambdaN.map (background.nu.functor.map T.f) m)
    (z+(background.classical.map T.f).pageMap 2 (s+1+1,t+1) u) hu β v hβ
  have hk0 := hjoint U k z u hk ⟨hU,hd⟩ (hP hp)
  exact lookahead_zero_head_divides T.X m hm (s+1) t e k hek hk0

private def LookaheadPositiveGRelation
    (T : TriangleData background.auxiliary) (hg : normalizedExponent background.classicalTower T.g=1)
    (s t : ℤ) (U : Ambient background T.Z (s+1,t+1))
    (k : Ambient background T.X (s+1,t)) (z : Ambient background T.Y (s+1+1,t+1)) : Prop :=
  (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((background.classical.map T.h).pageMap 2 (s+1,t+1) U)
      (by simpa only [add_sub_cancel_right] using k) ∧
    HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
      (s+1,t+1) ((s+1+1)+1,(t+1)+1) U
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) (s+1+1) (t+1) z)

/-- The complete two-layer relation, its surjectivity, and the full joint
projection test eliminate the actual high residual head (g-positive branch).
The next-layer condition is produced from the genuine full image equality. -/
private theorem two_layer_lookahead_positive_g
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (j m : ℕ) (hm : 3≤m) (s t : ℤ)
    (K₀ : Submodule ℤ (Ambient background T.X (s+1,t)))
    (_hK₀ : ∀ k∈K₀, (background.classical.map T.f).pageMap 2 (s+1,t) k=0 ∧
      k∈cycles background T.X m (s+1,t))
    (hsurj : ∀ k∈K₀, ∃ (U : Ambient background T.Z (s+1,t+1))
      (z : Ambient background T.Y (s+1+1,t+1)), LookaheadPositiveGRelation T hg s t U k z)
    (Pnext : Submodule ℤ (Ambient background T.Y (s+1+1,t+1)))
    (hP : permanentCycles background T.Y (s+1+1,t+1)≤Pnext)
    (hjoint : ∀ (U : Ambient background T.Z (s+1,t+1)) (k : Ambient background T.X (s+1,t))
      (z : Ambient background T.Y (s+1+1,t+1)) (u : Ambient background T.X (s+1+1,t+1)),
      k∈K₀ → LookaheadPositiveGRelation T hg s t U k z →
      z+(background.classical.map T.f).pageMap 2 (s+1+1,t+1) u∈Pnext → k=0)
    (e : BiHom (t-(s+1)) t
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) m))
    (k : Ambient background T.X (s+1,t)) (hk : k∈K₀)
    (hek : e≫(background.quotients.tower _).rho 1 m (by omega)=nativeFirstLabel T.X (s+1) t k)
    (β : BiHom (t-(s+1)) (t-j) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (v : Ambient background T.Y ((s+1)+m-1,t+m-1))
    (hβ : β≫XModLambdaN.incl _ (j+m)=
      finiteCoefficientInsert _ j m (by omega) (t-(s+1)) t
        (e≫XModLambdaN.map (background.nu.functor.map T.f) m)+
      lookaheadFinalTop T.Y j m hm (s+1) t v) :
    k=0 ∧ ∃ e' : BiHom (t-(s+1)) (t+1)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (m-1)),
      homotopyRegrade rfl (show (t+1)-(1:ℕ)=t by omega)
        (finiteCoefficientShiftClass _ m 1 (by omega) (t-(s+1)) (t+1) e')=e := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨U,z,hU,hd,c,hc,hcz⟩ := recursive_common_lift_positive_g T he hT hf hg hh
    s t K₀ hsurj k hk
  obtain ⟨u,hu⟩ := lookahead_ordinary_image_top T.X T.Y T.f m hm (s+1) t e k hek c hc z hcz
  have hp := lookahead_full_image_label_permanent T.Y j m hm (s+1) t
    (e≫XModLambdaN.map (background.nu.functor.map T.f) m)
    (z+(background.classical.map T.f).pageMap 2 (s+1+1,t+1) u) hu β v hβ
  have hk0 := hjoint U k z u hk ⟨hU,hd⟩ (hP hp)
  exact lookahead_zero_head_divides T.X m hm (s+1) t e k hek hk0

private def lookaheadPositiveImage
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (N : ℕ) (s t : ℤ)
    (e : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)) :
    BiHom ((t+1)-(s+1)) (t+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N) :=
  homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
    (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s) t e)

private theorem lookahead_positive_image_add
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (N : ℕ) (s t : ℤ)
    (a b : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)) :
    lookaheadPositiveImage T hf N s t (a+b)=
      lookaheadPositiveImage T hf N s t a+lookaheadPositiveImage T hf N s t b := by
  simp only [lookaheadPositiveImage,positiveFiniteImage,shiftHomotopyClass,Functor.map_add,
    Preadditive.comp_add,regrade_precomp,Preadditive.add_comp]

private theorem lookahead_positive_image_top
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (s t : ℤ) (u : Ambient background T.X (s+1,t+1)) :
    lookaheadPositiveImage T hf 2 s t (recursiveMiddleTopLabel T.X s t u)=
      recursiveMiddleTopLabel T.Y (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+1) (t+1) u) := by
  have h := selective_positive_top_image T hf 1 (by decide) (s+1) (t+1)
    (levelQuotientShiftIso T.X 1 2) (level_quotient_shift_incl T.X 1 2) u
  have h' := congrArg (homotopyRegrade
    (rfl : ((t+1)+1)-((s+1)+1)=((t+1)+1)-((s+1)+1))
    (show ((t+1)+1)-(1:ℕ)=t+1 by omega)) h
  simp only [lookaheadPositiveImage,recursiveMiddleTopLabel,←positiveFiniteImage_regrade,
    normalized_homotopy_regrade_trans]
  simp only [normalized_homotopy_regrade_trans] at h'
  simpa only [normalized_homotopy_regrade_trans] using congrArg (homotopyRegrade
    (show ((t+1)+1)-((s+1)+1)=(t+1)-(s+1) by omega) rfl) h'

private theorem lookahead_positive_image_restriction
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (m : ℕ) (hm : 3≤m) (s t : ℤ)
    (e : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) m)) :
    lookaheadPositiveImage T hf m s t e≫(background.quotients.tower _).rho 2 m (by omega)=
      lookaheadPositiveImage T hf 2 s t (e≫(background.quotients.tower _).rho 2 m (by omega)) := by
  dsimp only [lookaheadPositiveImage]
  rw [←regrade_comp,selective_positive_image_restriction T hf 2 m (by decide) (by omega)
    _ _ (level_quotient_shift_incl T.X 1 2) (level_quotient_shift_incl T.X 1 m)]

private theorem lookahead_positive_image_same_q2
    (T : TriangleData background.auxiliary) (hf : normalizedExponent background.classicalTower T.f=1)
    (m : ℕ) (hm : 3≤m) (s t : ℤ)
    (e : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) m))
    (k : Ambient background T.X (s,t))
    (he : e≫(background.quotients.tower _).rho 1 m (by omega)=nativeFirstLabel T.X s t k)
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2))
    (hc : c≫(background.quotients.tower _).rho 1 2 (by decide)=nativeFirstLabel T.X s t k)
    (z : Ambient background T.Y (s+1+1,t+1+1))
    (hcz : lookaheadPositiveImage T hf 2 s t c=recursiveMiddleTopLabel T.Y (s+1) (t+1) z) :
    ∃ u : Ambient background T.X (s+1,t+1),
      lookaheadPositiveImage T hf m s t e≫(background.quotients.tower _).rho 2 m (by omega)=
        recursiveMiddleTopLabel T.Y (s+1) (t+1)
          (z+KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+1) (t+1) u) := by
  obtain ⟨u,hu⟩ := lookahead_q2_difference T.X m hm s t e k he c hc
  refine ⟨u,?_⟩
  rw [lookahead_positive_image_restriction T hf m hm,hu,lookahead_positive_image_add,hcz,
    lookahead_positive_image_top,lookahead_middle_top_add]

private def LookaheadPositiveFRelation
    (T : TriangleData background.auxiliary) (s t : ℤ)
    (U : Ambient background T.Z (s,t+1)) (k : Ambient background T.X (s,t))
    (z : Ambient background T.Y (s+1+1,t+1+1)) : Prop :=
  (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) U) (by simpa using k) ∧
    HasDifferential (background.classical.obj (T.Z.obj background.auxiliary)) 2
      (s,t+1) (s+1+1,t+1+1) U ((background.classical.map T.g).pageMap 2 (s+1+1,t+1+1) z)

/-- The positive-first-map branch uses the same native residual and the
canonical actual quotient comparison. The joint relation is imposed on all
vectors and all choices, including the top difference of this actual residual. -/
private theorem two_layer_lookahead_positive_f
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (j m : ℕ) (hm : 3≤m) (s t : ℤ)
    (K₀ : Submodule ℤ (Ambient background T.X (s,t)))
    (_hK₀ : ∀ k∈K₀, KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t k=0 ∧
      k∈cycles background T.X m (s,t))
    (hsurj : ∀ k∈K₀, ∃ (U : Ambient background T.Z (s,t+1))
      (z : Ambient background T.Y (s+1+1,t+1+1)), LookaheadPositiveFRelation T s t U k z)
    (Pnext : Submodule ℤ (Ambient background T.Y (s+1+1,t+1+1)))
    (hP : permanentCycles background T.Y (s+1+1,t+1+1)≤Pnext)
    (hjoint : ∀ (U : Ambient background T.Z (s,t+1)) (k : Ambient background T.X (s,t))
      (z : Ambient background T.Y (s+1+1,t+1+1)) (u : Ambient background T.X (s+1,t+1)),
      k∈K₀ → LookaheadPositiveFRelation T s t U k z →
      z+KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+1) (t+1) u∈Pnext → k=0)
    (e : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) m))
    (k : Ambient background T.X (s,t)) (hk : k∈K₀)
    (hek : e≫(background.quotients.tower _).rho 1 m (by omega)=nativeFirstLabel T.X s t k)
    (β : BiHom ((t+1)-(s+1)) ((t+1)-j) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (v : Ambient background T.Y ((s+1)+m-1,(t+1)+m-1))
    (hβ : β≫XModLambdaN.incl _ (j+m)=
      finiteCoefficientInsert _ j m (by omega) ((t+1)-(s+1)) (t+1)
        (lookaheadPositiveImage T hf m s t e)+lookaheadFinalTop T.Y j m hm (s+1) (t+1) v) :
    k=0 ∧ ∃ e' : BiHom (t-s) (t+1)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (m-1)),
      homotopyRegrade rfl (show (t+1)-(1:ℕ)=t by omega)
        (finiteCoefficientShiftClass _ m 1 (by omega) (t-s) (t+1) e')=e := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨U,z,hU,hd⟩ := hsurj k hk
  obtain ⟨c,hc,hcz⟩ := recursive_common_lift_positive_f T he hT hf hg hh s t U k z hU hd
  have hcz' : lookaheadPositiveImage T hf 2 s t c=
      recursiveMiddleTopLabel T.Y (s+1) (t+1) z := by
    dsimp only [lookaheadPositiveImage,recursiveMiddleTopLabel]
    rw [hcz,last_layer_regrade_trans]
  obtain ⟨u,hu⟩ := lookahead_positive_image_same_q2 T hf m hm s t e k hek c hc z hcz'
  have hp := lookahead_full_image_label_permanent T.Y j m hm (s+1) (t+1)
    (lookaheadPositiveImage T hf m s t e)
    (z+KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+1) (t+1) u) hu β v hβ
  have hk0 := hjoint U k z u hk ⟨hU,hd⟩ (hP hp)
  exact lookahead_zero_head_divides T.X m hm s t e k hek hk0

end
end KIP126.ProofTools.Internal.SyntheticCoverage
