module

import all KIP126.ProofTools.MahowaldLeibniz.Corollaries
import all KIP126.ProofTools.MahowaldLeibniz.LastLayerNative
import all KIP126.ProofTools.MahowaldLeibniz.TopTarget
import all KIP126.ProofTools.GeneralizedMahowald.SphereAutomorphismDetection

/-! Last-layer image labels for the synthetic coverage arguments. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

/-- The normalized map sends the specified top class to
the top class of its first-quotient operation. -/
private theorem normalized_first_map_top_eq
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (d : ℕ) (hd : 0 < d) (s t : ℤ)
    (a : BiHom (t-s) (t+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) 1)) :
    homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
      (finiteTopOfFirst _ d hd (t-s) (t+1) a ≫
        XModLambdaN.map (lastLayerNormalizedMap T hf) (d+1)) =
      finiteTopLabel T.Y d hd (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t
          ((background.firstQuotient T.X 1 s t) a)) := by
  have hfirst := normalizedFirstMap_boundary T hf s t
    ((background.firstQuotient T.X 1 s t) a)
  rw [LinearEquiv.symm_apply_apply] at hfirst
  rw [finiteTopOfFirst_natural]
  have h := congrArg (finiteTopOfFirst _ d hd ((t+1)-(s+1)) (t+1)) hfirst
  rw [←finiteTopOfFirst_regrade] at h
  exact h

/-- The last source filtration has an actual image represented by F₂e for
some E₂ vector e. The quotient comparison is the selected one and preserves
its inclusion; the output is equality of finite homotopy classes. -/
private theorem last_layer_positive_image_eq_top
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (d : ℕ) (hd : 0 < d) (s t : ℤ)
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (d+1) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (hεq : XModLambdaN.incl _ (d+1) ≫ εq.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (d+1)))
    (a : BiHom (t-s) (t-d)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    ∃ e : Ambient background T.X (s,t),
      homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
        (show (t-d)+1=t+1-d by omega)
        (positiveFiniteImage T hf (d+1) εq (t-s) (t-d) a) =
      finiteTopLabel T.Y d hd (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e) := by
  obtain ⟨x,rfl⟩ := finiteTopLabel_exists T.X d hd s t a ha
  let A := background.nu.functor.obj (T.X.obj background.auxiliary)
  letI := background.exactness.shiftCommShift (0,1)
  letI := background.exactness.shiftExact (0,1)
  obtain ⟨εn,hεn,_⟩ := quotient_shift_exists background.quotients.coherence (0,1) ((d+1)-d) A
  let b := oneQuotientCast A ((d+1)-d) (by omega) (t-s) t (nativeFirstLabel T.X s t x)
  have htop : finiteTopLabel T.X d hd s t x =
      finiteLambdaClass T.X (d+1) d hd (Nat.lt_succ_self d) s t b :=
    finiteTopOfFirst_eq_raw A d hd (t-s) t _
  have hshift := shifted_finite_lambda_class_general T.X (0,1) (d+1) d hd
    (Nat.lt_succ_self d) s t εn εq hεn hεq b
  rw [←htop] at hshift
  let b₁ := oneQuotientUncast _ ((d+1)-d) (by omega) (t-s+0) (t+1)
    (shiftHomotopyClass (0,1) (t-s,t) b ≫ εn.inv)
  have hshift' :
      homotopyRegrade (m':=t-s+0) (w':=t+1-d) (by simp) (by dsimp; omega)
          (shiftHomotopyClass (0,1) (t-s,t-d) (finiteTopLabel T.X d hd s t x)) ≫ εq.inv =
        finiteTopOfFirst _ d hd (t-s+0) (t+1) b₁ := by
    exact hshift.trans (raw_eq_finiteTopOfFirst ((SyntheticCategory.biShift (0,1)).obj A)
      d hd (t-s+0) (t+1) (shiftHomotopyClass (0,1) (t-s,t) b ≫ εn.inv))
  let b₀ := homotopyRegrade (show t-s+0=t-s by omega) rfl b₁
  refine ⟨(background.firstQuotient T.X 1 s t) b₀,?_⟩
  have hi := congrArg (fun u => u ≫ XModLambdaN.map (lastLayerNormalizedMap T hf) (d+1)) hshift'
  have hi' := congrArg (homotopyRegrade (show t-s+0=(t+1)-(s+1) by omega)
    (rfl : t+1-d=t+1-d)) hi
  have hb := normalized_first_map_top_eq T hf d hd s t b₀
  rw [regrade_comp,←finiteTopOfFirst_regrade] at hb
  simp only [regrade_comp,last_layer_regrade_trans] at hi' hb
  simpa only [positiveFiniteImage,b₀,regrade_comp,last_layer_regrade_trans,Category.assoc] using
    hi'.trans hb

/-- A sphere-coordinate automorphism fixes the actual top label. This uses
label preservation and the one remaining filtration, not equality on a full
finite-quotient homotopy group. -/
private theorem finite_top_label_sphere_automorphism
    (X : (AdamsObject (coefficients := background.coefficients))) (d : ℕ) (hd : 0<d) (s t : ℤ)
    (x : Ambient background X (s,t))
    (u : Smn (Syn:=SyntheticSpectrum) (t-s) (t-d) ≅ Smn (t-s) (t-d)) :
    u.hom ≫ finiteTopLabel X d hd s t x = finiteTopLabel X d hd s t x := by
  have hx := finiteTopLabel_detects X d hd s t x
  exact finite_top_detection_unique X (d+1) (by omega) s t (t-d) (by omega)
    _ _ _ (sphere_automorphism_finite_detects X (d+1) d (by omega) s t x u _ hx) hx

private theorem regrade_add {A : SyntheticSpectrum} {m m' w w' : ℤ}
    (hm : m=m') (hw : w=w') (a b : BiHom m w A) :
    homotopyRegrade hm hw (a+b) = homotopyRegrade hm hw a + homotopyRegrade hm hw b := by
  subst m'
  subst w'
  rfl

private theorem native_first_label_add (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (x y : Ambient background X (s,t)) :
    nativeFirstLabel X s t (x+y) = nativeFirstLabel X s t x + nativeFirstLabel X s t y := by
  simp only [nativeFirstLabel,first_label_inline,map_add,regrade_add,Preadditive.add_comp]

private theorem finite_top_label_add (X : (AdamsObject (coefficients := background.coefficients))) (d : ℕ) (hd : 0<d)
    (s t : ℤ) (x y : Ambient background X (s,t)) :
    finiteTopLabel X d hd s t (x+y) =
      finiteTopLabel X d hd s t x + finiteTopLabel X d hd s t y := by
  simp only [finiteTopLabel,finiteTopOfFirst,native_first_label_add,shiftHomotopyClass,
    Functor.map_add,Preadditive.comp_add,regrade_add,Preadditive.add_comp]

private theorem finite_top_label_at_weight_add (X : (AdamsObject (coefficients := background.coefficients)))
    (d : ℕ) (hd : 0<d) (N : ℕ) (hN : d+1=N)
    (s t w : ℤ) (hw : t-d=w) (x y : Ambient background X (s,t)) :
    finiteTopLabelAtWeight X d hd N hN s t w hw (x+y) =
      finiteTopLabelAtWeight X d hd N hN s t w hw x +
        finiteTopLabelAtWeight X d hd N hN s t w hw y := by
  subst N
  simp only [finiteTopLabelAtWeight,finite_top_label_add,regrade_add]

private theorem finite_may_top_label_add (X : (AdamsObject (coefficients := background.coefficients)))
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x y : Ambient background X (s+q+1,t+q)) :
    finiteMayTopLabel X c q hq s t (x+y) =
      finiteMayTopLabel X c q hq s t x + finiteMayTopLabel X c q hq s t y := by
  simp only [finiteMayTopLabel,finite_top_label_at_weight_add,regrade_add]

private theorem ordinary_suspended_representative_add
    (A : SyntheticSpectrum) (m w : ℤ) (a b : BiHom (m-1) w A) :
    ordinarySuspendedRepresentative A m w (a+b) =
      ordinarySuspendedRepresentative A m w a + ordinarySuspendedRepresentative A m w b := by
  simp only [ordinarySuspendedRepresentative,shiftHomotopyClass,Functor.map_add,
    Preadditive.comp_add,regrade_add,Preadditive.add_comp]

/-- The last-layer image corrects the May image of the common
representative, with the correction retained in the target label. -/
private theorem finite_top_image_with_last_error
    (X : (AdamsObject (coefficients := background.coefficients))) (d : ℕ) (hd : 0<d) (s t : ℤ)
    (A : SyntheticSpectrum)
    (f : A ⟶ (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1))⟦(1:ℤ)⟧)
    (a common residual : BiHom (t-s+1) (t-d) A)
    (v error : Ambient background X (s,t))
    (hcommon : common ≫ f = ordinarySuspendedRepresentative _ (t-s+1) (t-d)
      (homotopyRegrade (by omega) rfl (finiteTopLabel X d hd s t v)))
    (hresidual : residual ≫ f = (a-common) ≫ f)
    (herror : residual ≫ f = ordinarySuspendedRepresentative _ (t-s+1) (t-d)
      (homotopyRegrade (by omega) rfl (finiteTopLabel X d hd s t error))) :
    a ≫ f = ordinarySuspendedRepresentative _ (t-s+1) (t-d)
      (homotopyRegrade (by omega) rfl (finiteTopLabel X d hd s t (v+error))) := by
  have hdiff : a ≫ f - common ≫ f = residual ≫ f := by
    simpa only [Preadditive.sub_comp] using hresidual.symm
  have ha : a ≫ f = common ≫ f + residual ≫ f := by
    rw [←hdiff]
    abel
  rw [ha,hcommon,herror,finite_top_label_add,regrade_add,ordinary_suspended_representative_add]

/-- The same addition rule in the finite May coordinates used by the
classical terminal decoder. -/
private theorem finite_may_top_image_with_last_error
    (X : (AdamsObject (coefficients := background.coefficients))) (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (A : SyntheticSpectrum)
    (f : A ⟶ (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (c+(q+1)))⟦(1:ℤ)⟧)
    (a common residual : BiHom (t-s) (t-c) A)
    (v error : Ambient background X (s+q+1,t+q))
    (hcommon : common ≫ f = ordinarySuspendedRepresentative _ (t-s) (t-c)
      (finiteMayTopLabel X c q hq s t v))
    (hresidual : residual ≫ f = (a-common) ≫ f)
    (herror : residual ≫ f = ordinarySuspendedRepresentative _ (t-s) (t-c)
      (finiteMayTopLabel X c q hq s t error)) :
    a ≫ f = ordinarySuspendedRepresentative _ (t-s) (t-c)
      (finiteMayTopLabel X c q hq s t (v+error)) := by
  have hdiff : a ≫ f - common ≫ f = residual ≫ f := by
    simpa only [Preadditive.sub_comp] using hresidual.symm
  have ha : a ≫ f = common ≫ f + residual ≫ f := by
    rw [←hdiff]
    abel
  rw [ha,hcommon,herror,finite_may_top_label_add,ordinary_suspended_representative_add]

private theorem top_sphere_fixed_regrade {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (a : BiHom m w A)
    (ha : ∀ u : Smn m w ≅ Smn m w, u.hom ≫ a = a) :
    ∀ u : Smn m' w' ≅ Smn m' w',
      u.hom ≫ homotopyRegrade hm hw a = homotopyRegrade hm hw a := by
  subst m'
  subst w'
  exact ha

private theorem finite_may_top_label_sphere_automorphism
    (X : (AdamsObject (coefficients := background.coefficients))) (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (v : Ambient background X (s+q+1,t+q))
    (u : Smn (Syn:=SyntheticSpectrum) ((t-s)-1) (t-c) ≅ Smn ((t-s)-1) (t-c)) :
    u.hom ≫ finiteMayTopLabel X c q hq s t v = finiteMayTopLabel X c q hq s t v := by
  have fixed (N : ℕ) (hN : c+q+1=N) :
      ∀ u : Smn (Syn:=SyntheticSpectrum) ((t+q)-(s+q+1)) (t-c) ≅
        Smn ((t+q)-(s+q+1)) (t-c),
      u.hom ≫ finiteTopLabelAtWeight X (c+q) (by omega) N hN
          (s+q+1) (t+q) (t-c) (by omega) v =
        finiteTopLabelAtWeight X (c+q) (by omega) N hN
          (s+q+1) (t+q) (t-c) (by omega) v := by
    subst N
    exact top_sphere_fixed_regrade rfl (by omega) _
      (finite_top_label_sphere_automorphism X (c+q) (by omega) (s+q+1) (t+q) v)
  exact top_sphere_fixed_regrade (by omega) rfl _ (fixed _ (by omega)) u


set_option maxHeartbeats 300000

private theorem last_layer_positive_image_eq_top_at_weight
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (d N : ℕ) (hd : 0<d) (hN : d+1=N) (s t w : ℤ) (hw : t-d=w)
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ N))
    (a : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    ∃ e : Ambient background T.X (s,t),
      homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
        (positiveFiniteImage T hf N ε (t-s) w a) =
      finiteTopLabelAtWeight T.Y d hd N hN (s+1) (t+1) (w+1) (by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e) := by
  subst N
  subst w
  obtain ⟨e,he⟩ := last_layer_positive_image_eq_top T hf d hd s t ε hε a ha
  refine ⟨e,?_⟩
  have h := congrArg (homotopyRegrade (rfl : (t+1)-(s+1)=(t+1)-(s+1))
    (show t+1-d=(t-d)+1 by omega)) he
  simpa only [finiteTopLabelAtWeight,last_layer_regrade_trans] using h

private def topClassicalRegrade {X : (AdamsObject (coefficients := background.coefficients))} {p q : ℤ×ℤ}
    (h : p=q) (x : Ambient background X p) : Ambient background X q := h ▸ x

private theorem top_classical_regrade_heq {X : (AdamsObject (coefficients := background.coefficients))} {p q : ℤ×ℤ}
    (h : p=q) (x : Ambient background X p) : HEq (topClassicalRegrade h x) x := by
  cases h
  rfl

private theorem top_label_at_weight_regrade
    (X : (AdamsObject (coefficients := background.coefficients))) (d N : ℕ) (hd : 0<d) (hN : d+1=N)
    (s t s' t' w : ℤ) (hs : s=s') (ht : t=t') (hw : t-d=w)
    (x : Ambient background X (s,t)) :
    homotopyRegrade (show t-s=t'-s' by omega) rfl
      (finiteTopLabelAtWeight X d hd N hN s t w hw x) =
      finiteTopLabelAtWeight X d hd N hN s' t' w (by omega)
        (topClassicalRegrade (X:=X) (Prod.ext hs ht) x) := by
  subst s'
  subst t'
  rfl

private theorem top_label_at_weight_output_regrade
    (X : (AdamsObject (coefficients := background.coefficients))) (d N : ℕ) (hd : 0<d) (hN : d+1=N)
    (s t w w' m' : ℤ) (hw : t-d=w) (hw' : w=w') (hm : t-s=m')
    (x : Ambient background X (s,t)) :
    homotopyRegrade hm hw' (finiteTopLabelAtWeight X d hd N hN s t w hw x) =
      homotopyRegrade hm rfl
        (finiteTopLabelAtWeight X d hd N hN s t w' (hw.trans hw') x) := by
  subst w'
  rfl

/-- Last-layer image decoding in precisely the finite May coordinates.
The error is the actual normalized F₂ image of one E₂ class. -/
private theorem last_layer_positive_image_eq_finite_may_top
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (c q : ℕ) (hq : 0<q) (S V : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (hε : XModLambdaN.incl _ (c+(q+1)) ≫ ε.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (c+(q+1))))
    (a : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (ha : FiltrationAtLeast background.syntheticTower (S+q) a) :
    ∃ e : Ambient background T.X (S+q,V+q),
    ∃ error : Ambient background T.Y (S+q+1,(V+1)+q),
      HEq error (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
        T hf (S+q) (V+q) e) ∧
      homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
        (show (V-c)+1=(V+1)-c by omega)
        (positiveFiniteImage T hf (c+(q+1)) ε (V-S) (V-c) a) =
      finiteMayTopLabel T.Y c q hq S (V+1) error := by
  let a' := homotopyRegrade (show V-S=(V+q)-(S+q) by omega) rfl a
  have ha' : FiltrationAtLeast background.syntheticTower (S+q) a' := by
    exact (regrade_filtration_iff _ _ _ _).mpr ha
  obtain ⟨e,he⟩ := last_layer_positive_image_eq_top_at_weight T hf (c+q) (c+(q+1))
    (by omega) (by omega) (S+q) (V+q) (V-c) (by push_cast; omega) ε hε a' ha'
  let b := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+q) (V+q) e
  let error : Ambient background T.Y (S+q+1,(V+1)+q) :=
    topClassicalRegrade (X:=T.Y) (show (S+q+1,V+q+1)=(S+q+1,(V+1)+q) by congr 1; omega) b
  refine ⟨e,error,?_,?_⟩
  · exact top_classical_regrade_heq _ _
  · have hb := top_label_at_weight_regrade T.Y (c+q) (c+(q+1)) (by omega) (by omega)
      (S+q+1) (V+q+1) (S+q+1) ((V+1)+q) ((V-c)+1) rfl (by omega)
      (by push_cast; omega) b
    have he' := congrArg (homotopyRegrade
      (show (V+q+1)-(S+q+1)=((V+1)+q)-(S+q+1) by omega)
      (rfl : (V-c)+1=(V-c)+1)) he
    have hh := congrArg (homotopyRegrade
      (show ((V+1)+q)-(S+q+1)=((V+1)-S)-1 by omega)
      (show (V-c)+1=(V+1)-c by omega)) (he'.trans hb)
    simp only [a',←positiveFiniteImage_regrade,last_layer_regrade_trans] at hh
    rw [top_label_at_weight_output_regrade] at hh
    simpa only [finiteMayTopLabel] using hh

end
end KIP126.ProofTools.Internal.SyntheticCoverage
