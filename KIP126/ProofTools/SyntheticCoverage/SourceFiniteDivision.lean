module

import all KIP126.ProofTools.SyntheticCoverage.EarlySourceCorrection
import all KIP126.ProofTools.SyntheticCoverage.OrdinarySourceFinite

/-! The divided source with the same actual absolute boundary.
The coefficient comparison is normalized on the source sphere before the
first label is chosen. Thus the source and its full boundary remain paired,
while the first-label discrepancy is a genuine earlier boundary.
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

/-- Normalize the same coefficient preimage at its source sphere. Its
first label is unchanged and its normalized insertion is the original one. -/
private theorem coefficient_preimage_with_normalized_boundary
    (X : (AdamsObject (coefficients := background.coefficients))) (d N : ℕ) (hd : 0 < d) (hdN : d < N) (m t : ℤ)
    (b₀ : BiHom m t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-d))) :
    ∃ b : BiHom m t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-d)),
      boundaryNormalizedInsertion X d N hd hdN m t b =
        verticalShiftEquiv _ d m (t-d) (homotopyRegrade rfl (by omega) b₀) ≫
          ((background.quotients.tower _).triangle hd hdN).lambdaMap ∧
      b ≫ (background.quotients.tower _).rho 1 (N-d) (by omega) =
        b₀ ≫ (background.quotients.tower _).rho 1 (N-d) (by omega) := by
  let u := boundaryDivisionSourceIso d N hdN.le m t
  let v := boundaryLiftSourceIso m t (N-d:ℕ) u.symm
  let b := v.inv ≫ b₀
  refine ⟨b,?_,?_⟩
  · dsimp only [boundaryNormalizedInsertion,b,u,v]
    rw [←Category.assoc,Iso.hom_inv_id,Category.id_comp]
  · dsimp only [b]
    rw [Category.assoc]
    exact sphere_automorphism_first_finite X m t v.symm _

/-- A top restriction gives a divided source whose absolute boundary
equals the specified original boundary. -/
private theorem source_finite_division_same_boundary
    (X : (AdamsObject (coefficients := background.coefficients))) (d N : ℕ) (hd : 0 < d) (hdN : d < N)
    (s t : ℤ) (x : Ambient background X (s,t))
    (a : BiHom (t-s) (t-d)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (htop : a ≫ (background.quotients.tower _).rho (d+1) N (by omega) =
      finiteTopLabel X d hd s t x) :
    ∃ b : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-d)),
    ∃ w : Ambient background X (s,t),
      boundaryNormalizedInsertion X d N hd hdN (t-s) t b = a ∧
      b ≫ (background.quotients.tower _).rho 1 (N-d) (by omega) = nativeFirstLabel X s t w ∧
      homotopyRegrade rfl (show (t-d)+N=t+(N-d:ℕ) by omega)
          (biSuspensionHomEquiv (t-s) (t-d) N (background.nu.functor.obj (X.obj background.auxiliary))
            (a ≫ XModLambdaN.proj _ N)) =
        biSuspensionHomEquiv (t-s) t (N-d:ℕ) (background.nu.functor.obj (X.obj background.auxiliary))
          (b ≫ XModLambdaN.proj _ (N-d)) ∧
      w-x ∈ boundaries background X (d+1) (s,t) := by
  have hzero := congrArg (fun b => b ≫ (background.quotients.tower
    (background.nu.functor.obj (X.obj background.auxiliary))).rho d (d+1) (by omega)) htop
  rw [Category.assoc,(background.quotients.tower _).rho_comp (by omega) (by omega),
    finite_top_restriction_zero] at hzero
  obtain ⟨b₀,hb₀,_⟩ := native_finite_source_division_of_zero_restriction X d N hd hdN (t-s) t a hzero
  obtain ⟨b,hb,hfirst⟩ := coefficient_preimage_with_normalized_boundary X d N hd hdN (t-s) t b₀
  obtain ⟨w,hw⟩ := quotient_first_label_exists X (N-d) (by omega) s t b₀
  have hfull := (finite_rho_lift_label_and_cycles X (d+1) N d
    (by omega) (by omega) s t x _ (finiteTopLabel_detects X d hd s t x) a htop).1
  have hlabel : nuWeightLabel background X s t (t-d) (by omega) x = targetNuLabel background X s t d x := by
    have hd' : (t-(t-d)).toNat=d := by omega
    have transport (a b : ℕ) (hab : a=b) (h : (s,t,t-a)=(s,t,t-b)) :
        regradeE2 h (targetNuLabel background X s t a x) = targetNuLabel background X s t b x := by
      subst b; rfl
    exact transport _ d hd' _
  have hdet : Detects (background.convergence (.quotient N (.nu X))) (s,t,t-d)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) N).pageMap
        2 (s,t,t-d) (nuWeightLabel background X s t (t-d) (by omega) x)) a := by
    rw [hlabel]
    exact hfull
  have hcong := finite_lambda_division_first_label_congruent X N d hd hdN s t x w b₀ hw a hdet hb₀
  have hinsert := hb.trans hb₀
  refine ⟨b,w,hinsert,hfirst.trans hw,?_,?_⟩
  · rw [←hinsert]
    exact boundary_normalized_insertion_boundary X d N hd hdN (t-s) t b
  · simpa only [neg_sub] using (boundaries background X (d+1) (s,t)).neg_mem hcong

/-- The earlier source error and a separately surviving correction preserve
the independently supplied later survival of the requested source. -/
private theorem source_finite_divided_label_survives
    (X : (AdamsObject (coefficients := background.coefficients))) (D b : ℤ) (p : ℤ × ℤ)
    (w y error : Ambient background X p)
    (hw : w-y-error ∈ boundaries background X b p)
    (hy : y ∈ cycles background X D p) (he : error ∈ cycles background X D p) :
    w ∈ cycles background X D p := by
  have hb := boundaries_le_cycles background X p b D hw
  have h := (cycles background X D p).add_mem ((cycles background X D p).add_mem hb hy) he
  convert h using 1; abel

private theorem source_finite_divided_label_difference_cycle
    (X : (AdamsObject (coefficients := background.coefficients))) (D b : ℤ) (p : ℤ × ℤ)
    (w y error : Ambient background X p)
    (hw : w-y-error ∈ boundaries background X b p)
    (he : error ∈ cycles background X D p) : w-y ∈ cycles background X D p := by
  have hb := boundaries_le_cycles background X p b D hw
  have h := (cycles background X D p).add_mem hb he
  simpa only [sub_add_cancel] using h

/-- The same construction with independent displayed quotient length and
weight. This preserves the exact full-boundary equality through regrading. -/
private theorem source_finite_division_same_boundary_at_weight
    (X : (AdamsObject (coefficients := background.coefficients))) (d N M : ℕ) (hd : 0 < d) (hdN : d < N) (hM : d+1=M)
    (s t w : ℤ) (hw : t-d=w) (x : Ambient background X (s,t))
    (a : BiHom (t-s) w
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (htop : a ≫ (background.quotients.tower _).rho M N (by omega) =
      finiteTopLabelAtWeight X d hd M hM s t w hw x) :
    ∃ b : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-d)),
    ∃ wy : Ambient background X (s,t),
      boundaryNormalizedInsertion X d N hd hdN (t-s) t b = homotopyRegrade rfl hw.symm a ∧
      b ≫ (background.quotients.tower _).rho 1 (N-d) (by omega) = nativeFirstLabel X s t wy ∧
      homotopyRegrade rfl (show w+N=t+(N-d:ℕ) by omega)
          (biSuspensionHomEquiv (t-s) w N (background.nu.functor.obj (X.obj background.auxiliary))
            (a ≫ XModLambdaN.proj _ N)) =
        biSuspensionHomEquiv (t-s) t (N-d:ℕ) (background.nu.functor.obj (X.obj background.auxiliary))
          (b ≫ XModLambdaN.proj _ (N-d)) ∧
      wy-x ∈ boundaries background X (d+1) (s,t) := by
  subst M; subst w
  exact source_finite_division_same_boundary X d N hd hdN s t x a htop

/-- The divided source survives to the independently known later page;
its exact full boundary is retained together with the actual source. -/
private theorem source_finite_division_with_surviving_label
    (X : (AdamsObject (coefficients := background.coefficients))) (d N M : ℕ) (hd : 0 < d) (hdN : d < N) (hM : d+1=M)
    (s t w D : ℤ) (hw : t-d=w) (y error : Ambient background X (s,t))
    (hy : y ∈ cycles background X D (s,t)) (he : error ∈ cycles background X D (s,t))
    (a : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (htop : a ≫ (background.quotients.tower _).rho M N (by omega) =
      finiteTopLabelAtWeight X d hd M hM s t w hw (y+error)) :
    ∃ b : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-d)),
    ∃ wy : Ambient background X (s,t),
      boundaryNormalizedInsertion X d N hd hdN (t-s) t b = homotopyRegrade rfl hw.symm a ∧
      b ≫ (background.quotients.tower _).rho 1 (N-d) (by omega) = nativeFirstLabel X s t wy ∧
      homotopyRegrade rfl (show w+N=t+(N-d:ℕ) by omega)
          (biSuspensionHomEquiv (t-s) w N (background.nu.functor.obj (X.obj background.auxiliary))
            (a ≫ XModLambdaN.proj _ N)) =
        biSuspensionHomEquiv (t-s) t (N-d:ℕ) (background.nu.functor.obj (X.obj background.auxiliary))
          (b ≫ XModLambdaN.proj _ (N-d)) ∧
      wy-y-error ∈ boundaries background X (d+1) (s,t) ∧
      wy ∈ cycles background X D (s,t) := by
  obtain ⟨b,wy,hb,hfirst,hboundary,hcong⟩ := source_finite_division_same_boundary_at_weight
    X d N M hd hdN hM s t w hw (y+error) a htop
  have hc : wy-y-error ∈ boundaries background X (d+1) (s,t) := by
    simpa only [sub_add_eq_sub_sub] using hcong
  exact ⟨b,wy,hb,hfirst,hboundary,hc,
    source_finite_divided_label_survives X D (d+1) (s,t) wy y error hc hy he⟩

/-- Original positive-first-arrow top data produce the divided source and its exact full boundary, with independent later survival. -/
private theorem positive_source_finite_division_producer
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q N : ℕ) (hq : 0 < q) (hqN : q+1 ≤ N) (s t D : ℤ)
    (x : Ambient background T.X (s,t)) (z : Ambient background T.Z (s,t+1))
    (y : Ambient background T.Y (s+q+1,(t+1)+q))
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
    (ζ : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hζ : ζ ≫ (background.quotients.tower _).rho 1 N (by omega) = nativeFirstLabel T.X s t x)
    (hy : y ∈ cycles background T.Y D (s+q+1,(t+1)+q))
    (himage : ∀ e : Ambient background T.X (s+q,t+q),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+q) (t+q) e ∈
        cycles background T.Y D (s+q+1,(t+q)+1)) :
    let S := s+q+1
    let V := (t+1)+q
    let d : ℕ := 0+q
    let η := positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s) t ζ
    ∃ e : Ambient background T.X (s+q,t+q),
    ∃ error : Ambient background T.Y (S,V),
      HEq error (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+q) (t+q) e) ∧
    ∃ b : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (N-d)),
    ∃ wy : Ambient background T.Y (S,V),
      boundaryNormalizedInsertion T.Y d N (by dsimp [d]; omega) (by dsimp [d]; omega) (V-S) V b =
        homotopyRegrade (show t-s=V-S by dsimp [S,V]; omega)
          (show t+1=V-d by dsimp [V,d]; omega) η ∧
      b ≫ (background.quotients.tower _).rho 1 (N-d) (by dsimp [d]; omega) = nativeFirstLabel T.Y S V wy ∧
      (verticalTranslate _ 1 ((t+N)-(s+N+1)) (t+N)
          (positiveAdjustedBoundary T.X N s t ζ) ≫ lastLayerNormalizedMap T hf) =
        homotopyRegrade
          (show (V-S)-1=(t+N)-(s+N+1) by dsimp [S,V]; omega)
          (show V+(N-d:ℕ)=(t+N)+1 by dsimp [V,d]; omega)
          (biSuspensionHomEquiv (V-S) V (N-d:ℕ) (background.nu.functor.obj (T.Y.obj background.auxiliary))
            (b ≫ XModLambdaN.proj _ (N-d))) ∧
      wy-y-error ∈ boundaries background T.Y (d+1) (S,V) ∧
      wy ∈ cycles background T.Y D (S,V) := by
  dsimp only
  obtain ⟨e,error,herror,htop⟩ := positive_source_finite_top_restriction
    T he hT hf hg hh q N hq hqN s t x z y hxz hdz hmid ζ hζ
  let S := s+q+1
  let V := (t+1)+q
  let d : ℕ := 0+q
  let η := positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s) t ζ
  let a : BiHom (V-S) (t+1) (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N) :=
    homotopyRegrade (show t-s=V-S by dsimp [S,V]; omega) rfl η
  have ha : a ≫ (background.quotients.tower _).rho (0+(q+1)) N (by omega) =
      finiteTopLabelAtWeight T.Y d (by dsimp [d]; omega) (0+(q+1)) (by dsimp [d]; omega)
        S V (t+1) (by dsimp [V,d]; omega) (y+error) := by
    dsimp only [a]
    rw [←regrade_comp]
    exact htop
  have hecycle : error ∈ cycles background T.Y D (S,V) := by
    have transport (p p' : ℤ × ℤ) (hp : p=p') (a : Ambient background T.Y p) (a' : Ambient background T.Y p')
        (ha : HEq a a') (h : a' ∈ cycles background T.Y D p') : a ∈ cycles background T.Y D p := by
      subst p'; cases eq_of_heq ha; exact h
    exact transport _ _ (by congr 1; omega)
      error _ herror (himage e)
  obtain ⟨b,wy,hb,hfirst,hboundary,hcong,hcycle⟩ := source_finite_division_with_surviving_label
    T.Y d N (0+(q+1)) (by dsimp [d]; omega) (by dsimp [d]; omega)
    (by dsimp [d]; omega) S V (t+1) D (by dsimp [V,d]; omega) y error hy hecycle a ha
  refine ⟨e,error,herror,b,wy,?_,hfirst,?_,hcong,hcycle⟩
  · simpa only [a,last_layer_regrade_trans] using hb
  · have hsmall := congrArg (homotopyRegrade
      (show (V-S)-1=(t+N)-(s+N+1) by dsimp [S,V]; omega)
      (show V+(N-d:ℕ)=(t+N)+1 by dsimp [V,d]; omega)) hboundary
    have horiginal := positive_finite_image_absolute_boundary T hf N s t ζ
    apply horiginal.symm.trans
    simpa only [a,η,source_boundary_regrade,last_layer_regrade_trans] using hsmall

/-- Original ordinary-first-arrow top data produce a divided source with the same literal full boundary and independent later survival. -/
private theorem ordinary_source_finite_division_producer_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q N : ℕ) (hq : 0 < q) (hqN : q+1 ≤ N) (B W D : ℤ)
    (x : Ambient background T.X (B+1,W)) (z : Ambient background T.Z (B+1,W+1))
    (y : Ambient background T.Y (B+q+1,W+q))
    (hxz : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      ((background.classical.map T.h).pageMap 2 (B+1,W+1) z) (by simpa using x))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (B+1,W+1) ((B+q+1)+1,(W+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (B+q+1) (W+q) y))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X (B+1+j,W+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (B+1+j,W+j) →
        ∃ z' : Ambient background T.Z (B+1+j,W+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (B+1+j,W+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (B+1+j) (W+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (B+1+j,W+j))
    (ζ : BiHom (W-(B+1)) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hζ : ζ ≫ (background.quotients.tower _).rho 1 N (by omega) = nativeFirstLabel T.X (B+1) W x)
    (hy : y ∈ cycles background T.Y D (B+q+1,W+q))
    (himage : ∀ e : Ambient background T.X (B+q+1,W+q),
      (background.classical.map T.f).pageMap 2 (B+q+1,W+q) e ∈ cycles background T.Y D (B+q+1,W+q)) :
    let S := B+q+1
    let V := W+q
    let d : ℕ := 0+q
    let η := ζ ≫ XModLambdaN.map (background.nu.functor.map T.f) N
    ∃ e : Ambient background T.X (S,V),
    ∃ b : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (N-d)),
    ∃ wy : Ambient background T.Y (S,V),
      boundaryNormalizedInsertion T.Y d N (by dsimp [d]; omega) (by dsimp [d]; omega) (V-S) V b =
        homotopyRegrade (show W-(B+1)=V-S by dsimp [S,V]; omega)
          (show W=V-d by dsimp [V,d]; omega) η ∧
      b ≫ (background.quotients.tower _).rho 1 (N-d) (by dsimp [d]; omega) = nativeFirstLabel T.Y S V wy ∧
      (boundaryRepresentative T.X N (B+1) W ζ ≫ background.nu.functor.map T.f) =
        homotopyRegrade
          (show (V-S)-1=(W+N)-((B+1)+N+1) by dsimp [S,V]; omega)
          (show V+(N-d:ℕ)=W+N by dsimp [V,d]; omega)
          (biSuspensionHomEquiv (V-S) V (N-d:ℕ) (background.nu.functor.obj (T.Y.obj background.auxiliary))
            (b ≫ XModLambdaN.proj _ (N-d))) ∧
      wy-y-(background.classical.map T.f).pageMap 2 (S,V) e ∈ boundaries background T.Y (d+1) (S,V) ∧
      wy ∈ cycles background T.Y D (S,V) ∧ wy-y ∈ cycles background T.Y D (S,V) := by
  dsimp only
  have hdet := ordinary_source_restriction_detects T.X q N hqN B W x ζ hζ
  obtain ⟨e,hi⟩ := ordinary_finite_image_of_same_source_second T he hT hf hg hh
    0 q hq B W x z y hxz hdz hmid _ hdet
  have htop := ordinary_source_image_restriction_top T.X T.Y T.f q N hq hqN B W ζ
    (y+(background.classical.map T.f).pageMap 2 (B+q+1,W+q) e) hi
  let S := B+q+1
  let V := W+q
  let d : ℕ := 0+q
  let η := ζ ≫ XModLambdaN.map (background.nu.functor.map T.f) N
  let a : BiHom (V-S) W (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N) :=
    homotopyRegrade (show W-(B+1)=V-S by dsimp [S,V]; omega) rfl η
  have ha : a ≫ (background.quotients.tower _).rho (0+(q+1)) N (by omega) =
      finiteTopLabelAtWeight T.Y d (by dsimp [d]; omega) (0+(q+1)) (by dsimp [d]; omega)
        S V W (by dsimp [V,d]; omega) (y+(background.classical.map T.f).pageMap 2 (S,V) e) := by
    dsimp only [a]
    rw [←regrade_comp]
    exact htop
  obtain ⟨b,wy,hb,hfirst,hboundary,hcong,hcycle⟩ := source_finite_division_with_surviving_label
    T.Y d N (0+(q+1)) (by dsimp [d]; omega) (by dsimp [d]; omega)
    (by dsimp [d]; omega) S V W D (by dsimp [V,d]; omega) y _ hy (himage e) a ha
  refine ⟨e,b,wy,?_,hfirst,?_,hcong,hcycle,?_⟩
  · simpa only [a,last_layer_regrade_trans] using hb
  · have hsmall := congrArg (homotopyRegrade
      (show (V-S)-1=(W+N)-((B+1)+N+1) by dsimp [S,V]; omega)
      (show V+(N-d:ℕ)=W+N by dsimp [V,d]; omega)) hboundary
    have horiginal := boundary_representative_natural T.X T.Y (background.nu.functor.map T.f) N (B+1) W ζ
    apply horiginal.symm.trans
    simpa only [boundaryRepresentative,a,η,source_boundary_regrade,last_layer_regrade_trans] using hsmall
  · exact source_finite_divided_label_difference_cycle T.Y D (d+1) (S,V) wy y _ hcong (himage e)

/-- Original ordinary-first-arrow top data produce a divided source with the same literal full boundary and independent later survival. -/
private theorem ordinary_source_finite_division_producer_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
    (q N : ℕ) (hq : 0 < q) (hqN : q+1 ≤ N) (B W D : ℤ)
    (x : Ambient background T.X (B+1,W)) (z : Ambient background T.Z (B,W))
    (y : Ambient background T.Y (B+q+1,W+q))
    (hxz : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) B W z)
      (by simpa using x))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (B,W) (B+q+1,W+q) z
      ((background.classical.map T.g).pageMap 2 (B+q+1,W+q) y))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X ((B+1)+j-1+1,W+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) ((B+1)+j-1+1,W+j) →
        ∃ z' : Ambient background T.Z ((B+1)+j-1,W+j),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) ((B+1)+j-1,W+j) ∧
        ∃ u' : Ambient background T.X ((B+1)+j-1+1,W+j),
          (background.classicalSuspension T.X).DesuspendsClass ((B+1)+j-1+1) (W+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              ((B+1)+j-1) (W+j) z') (by simpa only [add_sub_cancel_right] using u') ∧
          a-u' ∈ boundaries background T.X ((j:ℤ)+1) ((B+1)+j-1+1,W+j))
    (ζ : BiHom (W-(B+1)) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hζ : ζ ≫ (background.quotients.tower _).rho 1 N (by omega) = nativeFirstLabel T.X (B+1) W x)
    (hy : y ∈ cycles background T.Y D (B+q+1,W+q))
    (himage : ∀ e : Ambient background T.X (B+q+1,W+q),
      (background.classical.map T.f).pageMap 2 (B+q+1,W+q) e ∈ cycles background T.Y D (B+q+1,W+q)) :
    let S := B+q+1
    let V := W+q
    let d : ℕ := 0+q
    let η := ζ ≫ XModLambdaN.map (background.nu.functor.map T.f) N
    ∃ e : Ambient background T.X (S,V),
    ∃ b : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (N-d)),
    ∃ wy : Ambient background T.Y (S,V),
      boundaryNormalizedInsertion T.Y d N (by dsimp [d]; omega) (by dsimp [d]; omega) (V-S) V b =
        homotopyRegrade (show W-(B+1)=V-S by dsimp [S,V]; omega)
          (show W=V-d by dsimp [V,d]; omega) η ∧
      b ≫ (background.quotients.tower _).rho 1 (N-d) (by dsimp [d]; omega) = nativeFirstLabel T.Y S V wy ∧
      (boundaryRepresentative T.X N (B+1) W ζ ≫ background.nu.functor.map T.f) =
        homotopyRegrade
          (show (V-S)-1=(W+N)-((B+1)+N+1) by dsimp [S,V]; omega)
          (show V+(N-d:ℕ)=W+N by dsimp [V,d]; omega)
          (biSuspensionHomEquiv (V-S) V (N-d:ℕ) (background.nu.functor.obj (T.Y.obj background.auxiliary))
            (b ≫ XModLambdaN.proj _ (N-d))) ∧
      wy-y-(background.classical.map T.f).pageMap 2 (S,V) e ∈ boundaries background T.Y (d+1) (S,V) ∧
      wy ∈ cycles background T.Y D (S,V) ∧ wy-y ∈ cycles background T.Y D (S,V) := by
  dsimp only
  have hdet := ordinary_source_restriction_detects T.X q N hqN B W x ζ hζ
  obtain ⟨e,hi⟩ := ordinary_finite_image_of_same_source_third T he hT hf hg hh
    0 q hq B W x z y hxz hdz hmid _ hdet
  have htop := ordinary_source_image_restriction_top T.X T.Y T.f q N hq hqN B W ζ
    (y+(background.classical.map T.f).pageMap 2 (B+q+1,W+q) e) hi
  let S := B+q+1
  let V := W+q
  let d : ℕ := 0+q
  let η := ζ ≫ XModLambdaN.map (background.nu.functor.map T.f) N
  let a : BiHom (V-S) W (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N) :=
    homotopyRegrade (show W-(B+1)=V-S by dsimp [S,V]; omega) rfl η
  have ha : a ≫ (background.quotients.tower _).rho (0+(q+1)) N (by omega) =
      finiteTopLabelAtWeight T.Y d (by dsimp [d]; omega) (0+(q+1)) (by dsimp [d]; omega)
        S V W (by dsimp [V,d]; omega) (y+(background.classical.map T.f).pageMap 2 (S,V) e) := by
    dsimp only [a]
    rw [←regrade_comp]
    exact htop
  obtain ⟨b,wy,hb,hfirst,hboundary,hcong,hcycle⟩ := source_finite_division_with_surviving_label
    T.Y d N (0+(q+1)) (by dsimp [d]; omega) (by dsimp [d]; omega)
    (by dsimp [d]; omega) S V W D (by dsimp [V,d]; omega) y _ hy (himage e) a ha
  refine ⟨e,b,wy,?_,hfirst,?_,hcong,hcycle,?_⟩
  · simpa only [a,last_layer_regrade_trans] using hb
  · have hsmall := congrArg (homotopyRegrade
      (show (V-S)-1=(W+N)-((B+1)+N+1) by dsimp [S,V]; omega)
      (show V+(N-d:ℕ)=W+N by dsimp [V,d]; omega)) hboundary
    have horiginal := boundary_representative_natural T.X T.Y (background.nu.functor.map T.f) N (B+1) W ζ
    apply horiginal.symm.trans
    simpa only [boundaryRepresentative,a,η,source_boundary_regrade,last_layer_regrade_trans] using hsmall
  · exact source_finite_divided_label_difference_cycle T.Y D (d+1) (S,V) wy y _ hcong (himage e)

end
end KIP126.ProofTools.Internal.SyntheticCoverage
