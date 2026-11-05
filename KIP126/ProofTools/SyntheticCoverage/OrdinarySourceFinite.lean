module

public import KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch

public import KIP126.ProofTools.MahowaldLeibniz.PositiveBranches

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.SourceFiniteDifferential
import all KIP126.ProofTools.SyntheticCoverage.OrdinaryTerminal
import all KIP126.ProofTools.SyntheticCoverage.BottomFiniteLift

/-! Source-finite constructions for an ordinary first arrow.
Both remaining exponent branches retain the specified finite source through
the actual normalized square, coefficient division, and boundary comparison.
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

/-- Recover a raw ordinary May source from the specified native source. -/
private theorem ordinary_source_desuspend_surjective
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (N c : ℕ) (B W : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (a : BiHom (W-(B+1)) (W-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)) :
    ∃ raw : BiHom (W-B) (W-c)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N),
      positiveHSourceDesuspend T he hf N c B W ε raw = a := by
  let Q := background.quotients.functoriality.functor N
  let e := Q.mapIso (normalizedSuspensionZeroIso T he hf)
  let b := shiftHomotopyClass (1,0) (W-(B+1),W-c) a ≫ ε.inv
  let raw := homotopyRegrade (show W-(B+1)+1=W-B by omega)
    (show (W-c)+0=W-c by omega) (b ≫ e.inv)
  refine ⟨raw,?_⟩
  have hraw : raw ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom N =
      homotopyRegrade (show W-(B+1)+1=W-B by omega)
        (show (W-c)+0=W-c by omega) b := by
    dsimp only [raw]
    rw [←regrade_comp]
    change homotopyRegrade _ _ ((b ≫ e.inv) ≫ e.hom) = _
    rw [Category.assoc,e.inv_hom_id]
    exact congrArg (homotopyRegrade (show W-(B+1)+1=W-B by omega)
      (show (W-c)+0=W-c by omega)) (Category.comp_id b)
  dsimp only [positiveHSourceDesuspend]
  rw [hraw,last_layer_regrade_trans]
  exact quotient_unshift_shift T.X (1,0) (W-(B+1),W-c) N ε a

/-- The actual common source and last residual determine the ordinary
image of the specified native source, with its literal F₂ correction. -/
private theorem ordinary_native_image_from_common_residual
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (c q : ℕ) (hq : 0 < q) (B W : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (hε : XModLambdaN.incl _ (c+(q+1)) ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (c+(q+1))))
    (eY : XModLambdaN ((background.nu.functor.obj (T.Y.obj background.auxiliary))⟦(1:ℤ)⟧)
        (c+(q+1)) ≅
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (c+(q+1)))⟦(1:ℤ)⟧)
    (heY : XModLambdaN.incl _ (c+(q+1)) ≫ eY.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (c+(q+1))))
    (d a e : BiHom (W-B) (W-c)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+(q+1))))
    (v : Ambient background T.Y (B+q+1,W+q))
    (hcommon : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) (c+(q+1)) ≫ eY.hom =
      ordinarySuspendedRepresentative _ (W-B) (W-c)
        (finiteMayTopLabel T.Y c q hq B W v))
    (hefil : FiltrationAtLeast background.syntheticTower (B+q+1)
      (positiveHSourceDesuspend T he hf (c+(q+1)) c B W ε e))
    (heimage : e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) (c+(q+1)) =
      (d-a) ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+(q+1))) :
    ∃ e₂ : Ambient background T.X (B+q+1,W+q),
      homotopyRegrade (show W-(B+1)=(W-B)-1 by omega) rfl
        (positiveHSourceDesuspend T he hf (c+(q+1)) c B W ε d ≫
          XModLambdaN.map (background.nu.functor.map T.f) (c+(q+1))) =
        finiteMayTopLabel T.Y c q hq B W
          (v+(background.classical.map T.f).pageMap 2 (B+q+1,W+q) e₂) := by
  obtain ⟨e₂,herror⟩ := last_layer_ordinary_image_eq_finite_may_top
    T.X T.Y T.f c q hq B W (positiveHSourceDesuspend T he hf (c+(q+1)) c B W ε e) hefil
  have herrorRaw := native_ordinary_image_eq_raw_image T he hf (c+(q+1)) c
    (by omega) B W ε hε eY heY e
  rw [herror] at herrorRaw
  have hresidual := congrArg (fun b => b ≫ eY.hom) heimage
  have himage := finite_may_top_image_with_last_error T.Y c q hq B W _
    (XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) (c+(q+1)) ≫ eY.hom)
    d a e v ((background.classical.map T.f).pageMap 2 (B+q+1,W+q) e₂)
    (by simpa only [Category.assoc] using hcommon)
    (by simpa only [Category.assoc] using hresidual)
    (by simpa only [Category.assoc] using herrorRaw)
  have hd := native_ordinary_image_eq_raw_image T he hf (c+(q+1)) c
    (by omega) B W ε hε eY heY d
  refine ⟨e₂,?_⟩
  apply ordinary_suspended_representative_injective _ (W-B) (W-c)
  exact hd.symm.trans (by simpa only [Category.assoc] using himage)

/-- The positive-second-arrow upper zigzag controls the actual ordinary
image of the same specified finite source. -/
private theorem ordinary_finite_image_of_same_source_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (c q : ℕ) (hq : 0 < q) (B W : ℤ)
    (u : Ambient background T.X (B+1,W)) (z : Ambient background T.Z (B+1,W+1))
    (v : Ambient background T.Y (B+q+1,W+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      ((background.classical.map T.h).pageMap 2 (B+1,W+1) z) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (B+1,W+1) ((B+q+1)+1,(W+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (B+q+1) (W+q) v))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X (B+1+j,W+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (B+1+j,W+j) →
        ∃ z' : Ambient background T.Z (B+1+j,W+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (B+1+j,W+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (B+1+j) (W+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (B+1+j,W+j))
    (a₀ : BiHom (W-(B+1)) (W-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (ha₀ : Detects (background.convergence (.quotient (c+(q+1)) (.nu T.X)))
      (B+1,W,W-c) (finiteTargetLabel background T.X (c+(q+1)) (B+1) W c u) a₀) :
    ∃ e₂ : Ambient background T.X (B+q+1,W+q),
      homotopyRegrade (show W-(B+1)=(W-B)-1 by omega) rfl
        (a₀ ≫ XModLambdaN.map (background.nu.functor.map T.f) (c+(q+1))) =
        finiteMayTopLabel T.Y c q hq B W
          (v+(background.classical.map T.f).pageMap 2 (B+q+1,W+q) e₂) := by
  let N := c+(q+1)
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) N
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) (q+1)
  obtain ⟨eY,heY⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) N
  obtain ⟨d,hd⟩ := ordinary_source_desuspend_surjective T he hf N c B W ε a₀
  have hddet : Detects (background.convergence (.quotient N (.nu T.X)))
      (B+1,W,W-c) (finiteTargetLabel background T.X N (B+1) W c u)
      (positiveHSourceDesuspend T he hf N c B W ε d) := by rw [hd]; exact ha₀
  obtain ⟨_,a,ha,hi,_⟩ := positive_second_finite_core T he hT hf hg hh
    c q hq B W z u v hu hdz ey hey ε hε
  have hdiff := detects_sub_filtration (background.convergence (.quotient N (.nu T.X)))
    (B+1,W,W-c) hddet ha
  change FiltrationAtLeast background.syntheticTower ((B+1)+1)
    (positiveHSourceDesuspend T he hf N c B W ε d-
      positiveHSourceDesuspend T he hf N c B W ε a) at hdiff
  rw [←positive_h_source_desuspend_sub] at hdiff
  obtain ⟨e,hefil,heimage⟩ := positive_second_last_residual
    T he hf hg hh hT c q hq B W hmid ε (d-a) hdiff
  have hcommon := congrArg (fun k => k ≫ eY.hom) hi
  have htop := finite_may_signed_target_eq_top_at_level T.Y c q hq B W v ey eY hey heY
  have hcommon' : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N ≫ eY.hom =
      ordinarySuspendedRepresentative _ (W-B) (W-c) (finiteMayTopLabel T.Y c q hq B W v) := by
    simpa only [Category.assoc] using hcommon.trans htop
  obtain ⟨e₂,he₂⟩ := ordinary_native_image_from_common_residual T he hf c q hq B W
    ε hε eY heY d a e v hcommon' hefil heimage
  rw [hd] at he₂
  exact ⟨e₂,he₂⟩

/-- The positive-third-arrow upper zigzag controls the actual ordinary
image of the same specified finite source. -/
private theorem ordinary_finite_image_of_same_source_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
    (c q : ℕ) (hq : 0 < q) (B W : ℤ)
    (u : Ambient background T.X (B+1,W)) (z : Ambient background T.Z (B,W))
    (v : Ambient background T.Y (B+q+1,W+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) B W z)
      (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (B,W) (B+q+1,W+q) z
      ((background.classical.map T.g).pageMap 2 (B+q+1,W+q) v))
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
    (a₀ : BiHom (W-(B+1)) (W-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (ha₀ : Detects (background.convergence (.quotient (c+(q+1)) (.nu T.X)))
      (B+1,W,W-c) (finiteTargetLabel background T.X (c+(q+1)) (B+1) W c u) a₀) :
    ∃ e₂ : Ambient background T.X (B+q+1,W+q),
      homotopyRegrade (show W-(B+1)=(W-B)-1 by omega) rfl
        (a₀ ≫ XModLambdaN.map (background.nu.functor.map T.f) (c+(q+1))) =
        finiteMayTopLabel T.Y c q hq B W
          (v+(background.classical.map T.f).pageMap 2 (B+q+1,W+q) e₂) := by
  let N := c+(q+1)
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) N
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) (q+1)
  obtain ⟨eY,heY⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) N
  obtain ⟨d,hd⟩ := ordinary_source_desuspend_surjective T he hf N c B W ε a₀
  have hddet : Detects (background.convergence (.quotient N (.nu T.X)))
      (B+1,W,W-c) (finiteTargetLabel background T.X N (B+1) W c u)
      (positiveHSourceDesuspend T he hf N c B W ε d) := by rw [hd]; exact ha₀
  obtain ⟨a,ha,hi,_,_⟩ := positive_third_finite_core T he hT hf hg hh
    c q hq B W z u v hu hdz ey hey ε hε
  have hdiff := detects_sub_filtration (background.convergence (.quotient N (.nu T.X)))
    (B+1,W,W-c) hddet ha
  change FiltrationAtLeast background.syntheticTower ((B+1)+1)
    (positiveHSourceDesuspend T he hf N c B W ε d-
      positiveHSourceDesuspend T he hf N c B W ε a) at hdiff
  rw [←positive_h_source_desuspend_sub] at hdiff
  have hres := middle_positive_h_residual_same_image T he hf hg hh hT
    c (q+1) (by omega) (B+1) W (fun j hj hjq b hb => by
      obtain ⟨z',hz',u',hu',hbu⟩ := hmid j hj hjq b hb
      exact ⟨z',hz',u',hu',boundaries_monotone background T.X _ (by omega) hbu⟩) ε
  rw [show B+1-1=B by omega] at hres
  obtain ⟨e,hefil',heimage⟩ := hres (d-a) hdiff
  have hefil : FiltrationAtLeast background.syntheticTower (B+q+1)
      (positiveHSourceDesuspend T he hf N c B W ε e) := by
    simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hefil'
  have hcommon := congrArg (fun k => k ≫ eY.hom) hi
  have htop := finite_may_signed_target_eq_top_at_level T.Y c q hq B W v ey eY hey heY
  have hcommon' : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N ≫ eY.hom =
      ordinarySuspendedRepresentative _ (W-B) (W-c) (finiteMayTopLabel T.Y c q hq B W v) := by
    simpa only [Category.assoc] using hcommon.trans htop
  obtain ⟨e₂,he₂⟩ := ordinary_native_image_from_common_residual T he hf c q hq B W
    ε hε eY heY d a e v hcommon' hefil heimage
  rw [hd] at he₂
  exact ⟨e₂,he₂⟩

/-- Restriction of an ordinary image of the specified long source. -/
private theorem ordinary_source_restriction_detects
    (X : (AdamsObject (coefficients := background.coefficients))) (q N : ℕ) (hqN : q+1 ≤ N) (B W : ℤ)
    (x : Ambient background X (B+1,W))
    (ζ : BiHom (W-(B+1)) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (hζ : ζ ≫ (background.quotients.tower _).rho 1 N (by omega) = nativeFirstLabel X (B+1) W x) :
    Detects (background.convergence (.quotient (0+(q+1)) (.nu X)))
      (B+1,W,W-(0:ℕ)) (finiteTargetLabel background X (0+(q+1)) (B+1) W 0 x)
      (homotopyRegrade rfl (show W=W-(0:ℕ) by omega)
        (ζ ≫ (background.quotients.tower _).rho (0+(q+1)) N (by omega))) := by
  have hfirst : (ζ ≫ (background.quotients.tower _).rho (0+(q+1)) N (by omega)) ≫
      (background.quotients.tower _).rho 1 (0+(q+1)) (by omega) = nativeFirstLabel X (B+1) W x := by
    rw [Category.assoc,(background.quotients.tower _).rho_comp (by omega) (by omega),hζ]
  have hd := first_label_detects_unshifted X (0+(q+1)) (by omega) (B+1) W x _ hfirst
  rw [←zero_weight_label] at hd
  have h := finite_weight_detection_regrade X (0+(q+1)) (B+1) W W (W-(0:ℕ))
    (by omega) (by omega) (by omega) x _ hd
  rwa [finite_coefficient_weight_label] at h

private theorem ordinary_source_image_restriction_top
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q N : ℕ) (hq : 0 < q) (hqN : q+1 ≤ N) (B W : ℤ)
    (ζ : BiHom (W-(B+1)) W (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (v : Ambient background Y (B+q+1,W+q))
    (hi : homotopyRegrade (show W-(B+1)=(W-B)-1 by omega) rfl
      ((homotopyRegrade rfl (show W=W-(0:ℕ) by omega)
        (ζ ≫ (background.quotients.tower _).rho (0+(q+1)) N (by omega))) ≫
        XModLambdaN.map (background.nu.functor.map f) (0+(q+1))) =
      finiteMayTopLabel Y 0 q hq B W v) :
    homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
        ((ζ ≫ XModLambdaN.map (background.nu.functor.map f) N) ≫
          (background.quotients.tower _).rho (0+(q+1)) N (by omega)) =
      finiteTopLabelAtWeight Y (0+q) (by omega) (0+(q+1)) (by omega)
        (B+q+1) (W+q) W (by omega) v := by
  have ht := congrArg (homotopyRegrade
    (show (W-B)-1=(W+q)-(B+q+1) by omega) (show W-(0:ℕ)=W by omega)) hi
  simp only [←regrade_comp,finiteMayTopLabel,last_layer_regrade_trans] at ht
  rw [top_label_at_weight_output_regrade] at ht
  rw [Category.assoc,←(background.quotients.natural (background.nu.functor.map f)).rho_naturality
    (show 0+(q+1)≤N by omega),←Category.assoc]
  simpa only [top_target_regrade_self] using ht

/-- Source division with an ordinary F₂ correction and the actual boundary
of the same long target lift. True source boundaries need no page inclusion. -/
private theorem ordinary_source_finite_of_top_and_boundary
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q N : ℕ) (hq : 0 < q) (hqN : q+1 ≤ N) (B W : ℤ)
    (y : Ambient background Y (B+q+1,W+q)) (e : Ambient background X (B+q+1,W+q))
    (wv v : Ambient background Y ((B+1)+N+1,W+N))
    (η : BiHom (W-(B+1)) W (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (htop : homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
        (η ≫ (background.quotients.tower _).rho (0+(q+1)) N (by omega)) =
      finiteTopLabelAtWeight Y (0+q) (by omega) (0+(q+1)) (by omega)
        (B+q+1) (W+q) W (by omega) (y+(background.classical.map f).pageMap 2 (B+q+1,W+q) e))
    (hboundary : homotopyRegrade (show (W-(B+1))-1=(W+N)-((B+1)+N+1) by omega) rfl
        (biSuspensionHomEquiv (W-(B+1)) W N (background.nu.functor.obj (Y.obj background.auxiliary))
          (η ≫ XModLambdaN.proj _ N)) ≫ XModLambdaN.incl _ 1 = nativeFirstLabel Y ((B+1)+N+1) (W+N) wv)
    (himage : (background.classical.map f).pageMap 2 (B+q+1,W+q) e ∈
      cycles background Y ((N-q:ℕ)+1) (B+q+1,W+q))
    (htarget : wv-v ∈ boundaries background Y (N-q:ℕ) ((B+1)+N+1,W+N)) :
    IsCycle background Y (N-q:ℕ) (B+q+1,W+q) y ∧
      IsCycle background Y (N-q:ℕ) ((B+1)+N+1,W+N) v ∧
      DifferentialAt background Y ((N-q:ℕ)+1) (B+q+1,W+q) ((B+1)+N+1,W+N) y v := by
  let S := B+q+1
  let V := W+q
  let d : ℕ := 0+q
  let w' : Ambient background Y (S+(N-d:ℕ)+1,V+(N-d:ℕ)) :=
    topClassicalRegrade (show ((B+1)+N+1,W+N)=(S+(N-d:ℕ)+1,V+(N-d:ℕ)) by
      ext <;> dsimp [S,V,d] <;> omega) wv
  have hw' : HEq w' wv := top_classical_regrade_heq _ _
  let a : BiHom (V-S) W (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N) :=
    homotopyRegrade (show W-(B+1)=V-S by dsimp [S,V]; omega) rfl η
  have ha : a ≫ (background.quotients.tower _).rho (0+(q+1)) N (by omega) =
      finiteTopLabelAtWeight Y d (by dsimp [d]; omega) (0+(q+1)) (by dsimp [d]; omega)
        S V W (by dsimp [V,d]; omega) (y+(background.classical.map f).pageMap 2 (S,V) e) := by
    dsimp only [a]
    rw [←regrade_comp]
    exact htop
  have hb := congrArg (homotopyRegrade
    (show (W+N)-((B+1)+N+1)=(V+(N-d:ℕ))-(S+(N-d:ℕ)+1) by dsimp [S,V,d]; omega)
    (show W+N=V+(N-d:ℕ) by dsimp [V,d]; omega)) hboundary
  rw [source_native_label_transport Y ((B+1)+N+1) (W+N)
    (S+(N-d:ℕ)+1) (V+(N-d:ℕ)) (by dsimp [S,d]; omega) (by dsimp [V,d]; omega) wv w' hw'] at hb
  have hba : homotopyRegrade (by omega) (by omega)
      (biSuspensionHomEquiv (V-S) W N (background.nu.functor.obj (Y.obj background.auxiliary))
        (a ≫ XModLambdaN.proj _ N)) ≫ XModLambdaN.incl _ 1 =
      nativeFirstLabel Y (S+(N-d:ℕ)+1) (V+(N-d:ℕ)) w' := by
    simpa only [a,source_boundary_regrade,regrade_comp,last_layer_regrade_trans] using hb
  have hd := finite_source_differential_of_top_at_weight Y d N (0+(q+1))
    (by dsimp [d]; omega) (by dsimp [d]; omega) (by dsimp [d]; omega)
    S V W (by dsimp [V,d]; omega) (y+(background.classical.map f).pageMap 2 (S,V) e) w' a ha hba
  have hdactual := classical_differential_heq Y ((N-d:ℕ)+1) rfl
    (show (S+(N-d:ℕ)+1,V+(N-d:ℕ))=((B+1)+N+1,W+N) by
      ext <;> dsimp [S,V,d] <;> omega) _ _ w' wv HEq.rfl hw' hd
  have hfinal := differential_of_source_correction Y ((N-d:ℕ)+1) (q+1)
    (S,V) ((B+1)+N+1,W+N) (y+(background.classical.map f).pageMap 2 (S,V) e) y
    ((background.classical.map f).pageMap 2 (S,V) e) wv v hdactual
    (by have hz : (y+(background.classical.map f).pageMap 2 (S,V) e)-y-
          (background.classical.map f).pageMap 2 (S,V) e=0 := by abel
        rw [hz]; exact (boundaries background Y (q+1) (S,V)).zero_mem)
    (by simpa only [d,Nat.zero_add] using himage)
    (by simpa only [d,Nat.zero_add,add_sub_cancel_right] using htarget)
  simpa only [d,Nat.zero_add,add_sub_cancel_right] using hfinal

private theorem ordinary_finite_image_boundary_label
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N : ℕ) (s t : ℤ) (u : Ambient background X (s+N+1,t+N))
    (ζ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (hζ : adjacentBoundaryLabel X N s t ζ = nativeFirstLabel X (s+N+1) (t+N) u) :
    homotopyRegrade (show (t-s)-1=(t+N)-(s+N+1) by omega) rfl
        (biSuspensionHomEquiv (t-s) t N (background.nu.functor.obj (Y.obj background.auxiliary))
          ((ζ ≫ XModLambdaN.map (background.nu.functor.map f) N) ≫ XModLambdaN.proj _ N)) ≫
        XModLambdaN.incl _ 1 =
      nativeFirstLabel Y (s+N+1) (t+N) ((background.classical.map f).pageMap 2 (s+N+1,t+N) u) := by
  change adjacentBoundaryLabel Y N s t (ζ ≫ XModLambdaN.map (background.nu.functor.map f) N) = _
  dsimp only [adjacentBoundaryLabel]
  rw [boundary_representative_natural,Category.assoc,XModLambdaN.incl_naturality,
    ←Category.assoc]
  change adjacentBoundaryLabel X N s t ζ ≫ XModLambdaN.map (background.nu.functor.map f) 1 = _
  rw [hζ,native_first_label_natural]

/-- The finite-source differential criterion with an ordinary first arrow and
K₂=1, in the second exponent branch. -/
public theorem source_finite_differential_ordinary_second_bottom_one
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q N : ℕ) (hq : 0 < q) (hqN : q+1 ≤ N) (B W : ℤ)
    (x : Ambient background T.X (B+1,W)) (z : Ambient background T.Z (B+1,W+1))
    (y : Ambient background T.Y (B+q+1,W+q))
    (hxz : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      ((background.classical.map T.h).pageMap 2 (B+1,W+1) z) (by simpa using x))
    (u : Ambient background T.X ((B+1)+N+1,W+N))
    (_hFx : (background.classical.map T.f).pageMap 2 (B+1,W) x = 0)
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (B+1,W) ((B+1)+N+1,W+N) x u)
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
    (himage : ∀ e : Ambient background T.X (B+q+1,W+q),
      (background.classical.map T.f).pageMap 2 (B+q+1,W+q) e ∈
        cycles background T.Y ((N-q:ℕ)+1) (B+q+1,W+q)) :
    let v := (background.classical.map T.f).pageMap 2 ((B+1)+N+1,W+N) u
    IsCycle background T.Y (N-q:ℕ) (B+q+1,W+q) y ∧
      IsCycle background T.Y (N-q:ℕ) ((B+1)+N+1,W+N) v ∧
      DifferentialAt background T.Y ((N-q:ℕ)+1) (B+q+1,W+q) ((B+1)+N+1,W+N) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T he
  dsimp only
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X N (by omega)
    (B+1) W x u).mp hdx
  have hdet := ordinary_source_restriction_detects T.X q N hqN B W x ζ hζ
  obtain ⟨e,hi⟩ := ordinary_finite_image_of_same_source_second T he hT hf hg hh
    0 q hq B W x z y hxz hdz hmid _ hdet
  have htop := ordinary_source_image_restriction_top T.X T.Y T.f q N hq hqN B W ζ
    (y+(background.classical.map T.f).pageMap 2 (B+q+1,W+q) e) hi
  have hboundary := ordinary_finite_image_boundary_label T.X T.Y T.f N (B+1) W u ζ hU
  exact ordinary_source_finite_of_top_and_boundary T.X T.Y T.f q N hq hqN B W
    y e _ _ (ζ ≫ XModLambdaN.map (background.nu.functor.map T.f) N) htop hboundary (himage e)
    (by rw [sub_self]; exact (boundaries background T.Y (N-q:ℕ) _).zero_mem)

/-- The finite-source differential criterion with an ordinary first arrow and
K₂=1, in the third exponent branch. -/
public theorem source_finite_differential_ordinary_third_bottom_one
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
    (q N : ℕ) (hq : 0 < q) (hqN : q+1 ≤ N) (B W : ℤ)
    (x : Ambient background T.X (B+1,W)) (z : Ambient background T.Z (B,W))
    (y : Ambient background T.Y (B+q+1,W+q))
    (hxz : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) B W z)
      (by simpa using x))
    (u : Ambient background T.X ((B+1)+N+1,W+N))
    (_hFx : (background.classical.map T.f).pageMap 2 (B+1,W) x = 0)
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (B+1,W) ((B+1)+N+1,W+N) x u)
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
    (himage : ∀ e : Ambient background T.X (B+q+1,W+q),
      (background.classical.map T.f).pageMap 2 (B+q+1,W+q) e ∈
        cycles background T.Y ((N-q:ℕ)+1) (B+q+1,W+q)) :
    let v := (background.classical.map T.f).pageMap 2 ((B+1)+N+1,W+N) u
    IsCycle background T.Y (N-q:ℕ) (B+q+1,W+q) y ∧
      IsCycle background T.Y (N-q:ℕ) ((B+1)+N+1,W+N) v ∧
      DifferentialAt background T.Y ((N-q:ℕ)+1) (B+q+1,W+q) ((B+1)+N+1,W+N) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T he
  dsimp only
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X N (by omega)
    (B+1) W x u).mp hdx
  have hdet := ordinary_source_restriction_detects T.X q N hqN B W x ζ hζ
  obtain ⟨e,hi⟩ := ordinary_finite_image_of_same_source_third T he hT hf hg hh
    0 q hq B W x z y hxz hdz hmid _ hdet
  have htop := ordinary_source_image_restriction_top T.X T.Y T.f q N hq hqN B W ζ
    (y+(background.classical.map T.f).pageMap 2 (B+q+1,W+q) e) hi
  have hboundary := ordinary_finite_image_boundary_label T.X T.Y T.f N (B+1) W u ζ hU
  exact ordinary_source_finite_of_top_and_boundary T.X T.Y T.f q N hq hqN B W
    y e _ _ (ζ ≫ XModLambdaN.map (background.nu.functor.map T.f) N) htop hboundary (himage e)
    (by rw [sub_self]; exact (boundaries background T.Y (N-q:ℕ) _).zero_mem)

/-- A last residual compares the actual full ordinary image with the
specified top label, retaining its literal ordinary F₂ correction. -/
private theorem ordinary_full_source_top_of_residual
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (hq : 0 < q) (B W : ℤ)
    (U : BiHom (W-(B+1)) W (background.nu.functor.obj (X.obj background.auxiliary)))
    (a e : BiHom (W-(B+1)) W
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q+1)))
    (v : Ambient background Y (B+q+1,W+q))
    (hcommon : a ≫ XModLambdaN.map (background.nu.functor.map f) (q+1) =
      homotopyRegrade (show (W+q)-(B+q+1)=W-(B+1) by omega)
        (show (W+q)-q=W by omega) (finiteTopLabel Y q hq (B+q+1) (W+q) v))
    (hefil : FiltrationAtLeast background.syntheticTower (B+q+1) e)
    (heimage : e ≫ XModLambdaN.map (background.nu.functor.map f) (q+1) =
      (U ≫ XModLambdaN.incl _ (q+1)-a) ≫ XModLambdaN.map (background.nu.functor.map f) (q+1)) :
    ∃ e₂ : Ambient background X (B+q+1,W+q),
      homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
        ((U ≫ background.nu.functor.map f) ≫ XModLambdaN.incl _ (q+1)) =
      finiteTopLabelAtWeight Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega)
        (v+(background.classical.map f).pageMap 2 (B+q+1,W+q) e₂) := by
  let e' := homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl e
  have hefil' : FiltrationAtLeast background.syntheticTower (B+q+1) e' :=
    (regrade_filtration_iff _ _ _ _).mpr hefil
  obtain ⟨e₂,he₂⟩ := last_layer_ordinary_image_eq_top_at_weight X Y f q (q+1) hq rfl
    (B+q+1) (W+q) W (by omega) e' hefil'
  have hc := congrArg (homotopyRegrade
    (show W-(B+1)=(W+q)-(B+q+1) by omega) (rfl : W=W)) hcommon
  have hsum : (U ≫ background.nu.functor.map f) ≫ XModLambdaN.incl _ (q+1) =
      a ≫ XModLambdaN.map (background.nu.functor.map f) (q+1)+
        e ≫ XModLambdaN.map (background.nu.functor.map f) (q+1) := by
    rw [heimage,Preadditive.sub_comp]
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
    abel
  refine ⟨e₂,?_⟩
  rw [hsum,regrade_add]
  have hc' : homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
      (a ≫ XModLambdaN.map (background.nu.functor.map f) (q+1)) =
      finiteTopLabelAtWeight Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega) v := by
    simpa only [finiteTopLabelAtWeight,last_layer_regrade_trans,top_target_regrade_self] using hc
  rw [hc']
  have he' : homotopyRegrade (show W-(B+1)=(W+q)-(B+q+1) by omega) rfl
      (e ≫ XModLambdaN.map (background.nu.functor.map f) (q+1)) =
      finiteTopLabelAtWeight Y q hq (q+1) rfl (B+q+1) (W+q) W (by omega)
        ((background.classical.map f).pageMap 2 (B+q+1,W+q) e₂) := by
    simpa only [e',←regrade_comp] using he₂
  rw [he',finite_top_label_at_weight_add]

/-- The specified full source image under the original restricted middle condition. -/
private theorem ordinary_full_image_of_selective_middle_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q : ℕ) (hq : 0 < q) (B W : ℤ)
    (u : Ambient background T.X (B+1,W)) (z : Ambient background T.Z (B+1,W+1))
    (v : Ambient background T.Y (B+q+1,W+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      ((background.classical.map T.h).pageMap 2 (B+1,W+1) z) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (B+1,W+1) ((B+q+1)+1,(W+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (B+q+1) (W+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((B+1)+j-1+1,W+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → permanentCycles background T.Y ((B+1)+j-1+1,W+j) ≤ Pm j)
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
    (hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X (B+1) W u) :
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
  have H := selective_positive_g_native_residual_same_image T he hf hg hh hT
    0 (q+1) (by omega) (B+1) W Pm hPm hmid
  have transport (N : ℕ) (w : ℤ) (hN : 0+(q+1)=N) (hw : W-(0:ℕ)=w) :
      ∀ r : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+1) r →
      ∀ β : BiHom (W-(B+1)) w (background.nu.functor.obj (T.Y.obj background.auxiliary)),
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
  obtain ⟨e,hefil,heimage⟩ := H' (a₀-a) hres (U ≫ background.nu.functor.map T.f)
    (a ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1))
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hvfil)
    (by dsimp only [a₀]; rw [Preadditive.sub_comp,Category.assoc,
          ←XModLambdaN.incl_naturality,←Category.assoc])
  exact ordinary_full_source_top_of_residual T.X T.Y T.f q hq B W U a e v hi
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hefil) heimage

/-- The specified full source image under the original restricted middle condition. -/
private theorem ordinary_full_image_of_selective_middle_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
    (q : ℕ) (hq : 0 < q) (B W : ℤ)
    (u : Ambient background T.X (B+1,W)) (z : Ambient background T.Z (B,W))
    (v : Ambient background T.Y (B+q+1,W+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) B W z)
      (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (B,W) (B+q+1,W+q) z
      ((background.classical.map T.g).pageMap 2 (B+q+1,W+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((B+1)+j-1+1,W+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → permanentCycles background T.Y ((B+1)+j-1+1,W+j) ≤ Pm j)
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
    (hU : U ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.X (B+1) W u) :
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
  have H := selective_positive_h_native_residual_same_image T he hf hg hh hT
    0 (q+1) (by omega) (B+1) W Pm hPm hmid
  have transport (N : ℕ) (w : ℤ) (hN : 0+(q+1)=N) (hw : W-(0:ℕ)=w) :
      ∀ r : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+1) r →
      ∀ β : BiHom (W-(B+1)) w (background.nu.functor.obj (T.Y.obj background.auxiliary)),
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
  obtain ⟨e,hefil,heimage⟩ := H' (a₀-a) hres (U ≫ background.nu.functor.map T.f)
    (a ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1))
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hvfil)
    (by dsimp only [a₀]; rw [Preadditive.sub_comp,Category.assoc,
          ←XModLambdaN.incl_naturality,←Category.assoc])
  exact ordinary_full_source_top_of_residual T.X T.Y T.f q hq B W U a e v hi
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hefil) heimage

/-- A top formula for the image of the actual boundary extends the image
of the same finite source. Its new absolute boundary supplies the target. -/
private theorem ordinary_bottom_extension_from_boundary_top
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (L q : ℕ) (hL : 0 < L) (hq : 0 < q) (s t : ℤ)
    (ζ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) L))
    (v : Ambient background Y (s+L+q+1,t+L+q))
    (htop : homotopyRegrade
        (show (t+L)-(s+L+1)=(t+L+q)-(s+L+q+1) by omega) rfl
        ((boundaryRepresentative X L s t ζ ≫ background.nu.functor.map f) ≫
          XModLambdaN.incl _ (q+1)) =
      finiteTopLabelAtWeight Y q hq (q+1) rfl (s+L+q+1) (t+L+q) (t+L) (by omega) v) :
    ∃ η : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (L+q)),
    ∃ wv : Ambient background Y (s+L+q+1,t+L+q),
      η ≫ (background.quotients.tower _).rho L (L+q) (by omega) =
        ζ ≫ XModLambdaN.map (background.nu.functor.map f) L ∧
      homotopyRegrade (show (t-s)-1=(t+L+q)-(s+L+q+1) by omega)
          (show t+(L+q:ℕ)=t+L+q by omega)
          (biSuspensionHomEquiv (t-s) t (L+q:ℕ) (background.nu.functor.obj (Y.obj background.auxiliary))
            (η ≫ XModLambdaN.proj _ (L+q))) ≫ XModLambdaN.incl _ 1 =
        nativeFirstLabel Y (s+L+q+1) (t+L+q) wv ∧
      wv ∈ permanentCycles background Y (s+L+q+1,t+L+q) ∧
      wv-v ∈ boundaries background Y (q+1) (s+L+q+1,t+L+q) := by
  apply finite_extension_of_boundary_top_at_weight Y L q (q+1) hL hq rfl
    (t-s) t (s+L+q+1) (t+L+q) (t+L) (by omega) (by omega) rfl
    (ζ ≫ XModLambdaN.map (background.nu.functor.map f) L) v
  have hb := boundary_representative_natural X Y (background.nu.functor.map f) L s t ζ
  have hb' := congrArg (fun a => homotopyRegrade
    (show (t+L)-(s+L+1)=(t+L+q)-(s+L+q+1) by omega) (rfl : t+L=t+L)
    (a ≫ XModLambdaN.incl _ (q+1))) hb
  have h := hb'.trans htop
  simpa only [boundaryRepresentative,regrade_comp,last_layer_regrade_trans] using h

/-- The finite-source differential criterion with full upper and selective
lower conditions. -/
public theorem source_finite_differential_ordinary_second_selective_bottom
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
    (hPm : ∀ j : ℕ, 1≤j → j<(b+1)-1 → permanentCycles background T.Y ((((B+1)+L)+1)+j-1+1,(W+L)+j) ≤ Pm j)
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
    KIP126.Literature.Standard.normalized_triangle_distinguished T he
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X L (by omega)
    (B+1) W x u).mp hdx
  have hdet := ordinary_source_restriction_detects T.X a L haL B W x ζ hζ
  obtain ⟨et,hit⟩ := ordinary_finite_image_of_same_source_second T he hT hf hg hh
    0 a ha B W x z₁ y hxz hdz₁ htop _ hdet
  have htopζ := ordinary_source_image_restriction_top T.X T.Y T.f a L ha haL B W ζ
    (y+(background.classical.map T.f).pageMap 2 (B+a+1,W+a) et) hit
  let U := boundaryRepresentative T.X L (B+1) W ζ
  obtain ⟨eb,hib⟩ := ordinary_full_image_of_selective_middle_second T he hT hf hg hh
    b hb ((B+1)+L) (W+L) u z₂ v huz hdz₂ Pm hPm hbottom U hU
  let error := (background.classical.map T.f).pageMap 2 ((((B+1)+L)+b+1),((W+L)+b)) eb
  obtain ⟨η,wv,hη,hboundary,hperm,herr⟩ := ordinary_bottom_extension_from_boundary_top
    T.X T.Y T.f L b (by omega) hb (B+1) W ζ (v+error) hib
  have herrorP : error ∈ P := by
    have hB := hP (boundary_mem_permanent_cycles T.Y (b+1) _ (wv-(v+error)) herr)
    have h := P.sub_mem (P.sub_mem (hP hperm) hv) hB
    convert h using 1; abel
  have herrorB : error ∈ boundaries background T.Y (L+b-a:ℕ) ((((B+1)+L)+b+1),((W+L)+b)) :=
    hker error herrorP (positive_second_triangle_composite_zero T hf hg hh hT (((B+1)+L)+b+1) ((W+L)+b) eb)
  have htarget : wv-v ∈ boundaries background T.Y (L+b-a:ℕ) ((((B+1)+L)+b+1),((W+L)+b)) := by
    have h := (boundaries background T.Y (L+b-a:ℕ) _).add_mem
      (boundaries_monotone background T.Y _ (by omega) herr) herrorB
    convert h using 1; abel
  let N := L+b
  let w₀ : Ambient background T.Y ((B+1)+N+1,W+N) :=
    topClassicalRegrade (show ((((B+1)+L)+b+1),((W+L)+b))=((B+1)+N+1,W+N) by
      ext <;> dsimp [N] <;> omega) wv
  let v₀ : Ambient background T.Y ((B+1)+N+1,W+N) :=
    topClassicalRegrade (show ((((B+1)+L)+b+1),((W+L)+b))=((B+1)+N+1,W+N) by
      ext <;> dsimp [N] <;> omega) v
  have hw₀ : HEq w₀ wv := top_classical_regrade_heq _ _
  have hv₀ : HEq v₀ v := top_classical_regrade_heq _ _
  have hsub : HEq (w₀-v₀) (wv-v) := by
    have transport (p p' : ℤ × ℤ) (hp : p=p')
        (a b : Ambient background T.Y p) (a' b' : Ambient background T.Y p')
        (ha : HEq a' a) (hb : HEq b' b) : HEq (a'-b') (a-b) := by
      subst p'; cases eq_of_heq ha; cases eq_of_heq hb; rfl
    exact transport _ _ (by ext <;> dsimp [N] <;> omega) wv v w₀ v₀ hw₀ hv₀
  have htarget₀ : w₀-v₀ ∈ boundaries background T.Y (N-a:ℕ) ((B+1)+N+1,W+N) :=
    classical_boundary_heq T.Y (N-a:ℕ)
      (show ((((B+1)+L)+b+1),((W+L)+b))=((B+1)+N+1,W+N) by ext <;> dsimp [N] <;> omega)
      (wv-v) (w₀-v₀) hsub.symm htarget
  have hb₀ := congrArg (homotopyRegrade
    (show ((W+L)+b)-(((B+1)+L)+b+1)=(W+N)-((B+1)+N+1) by dsimp [N]; omega)
    (show ((W+L)+b)=W+N by dsimp [N]; omega)) hboundary
  rw [source_native_label_transport T.Y (((B+1)+L)+b+1) ((W+L)+b) ((B+1)+N+1) (W+N)
    (by dsimp [N]; omega) (by dsimp [N]; omega) wv w₀ hw₀] at hb₀
  have htopη : homotopyRegrade (show W-(B+1)=(W+a)-(B+a+1) by omega) rfl
      (η ≫ (background.quotients.tower _).rho (0+(a+1)) N (by dsimp [N]; omega)) =
      finiteTopLabelAtWeight T.Y (0+a) (by omega) (0+(a+1)) (by omega)
        (B+a+1) (W+a) W (by omega)
        (y+(background.classical.map T.f).pageMap 2 (B+a+1,W+a) et) := by
    rw [←(background.quotients.tower _).rho_comp (show 0+(a+1)≤L by omega)
      (show L≤N by dsimp [N]; omega),←Category.assoc,hη]
    exact htopζ
  have hresult := ordinary_source_finite_of_top_and_boundary T.X T.Y T.f a N ha
    (by dsimp [N]; omega) B W y et w₀ v₀ η htopη
    (by simpa only [regrade_comp,last_layer_regrade_trans] using hb₀)
    (himage et) htarget₀
  have hvcycle := classical_cycle_heq T.Y (N-a:ℕ)
    (show ((B+1)+N+1,W+N)=((((B+1)+L)+b+1),((W+L)+b)) by ext <;> dsimp [N] <;> omega)
    v₀ v hv₀ hresult.2.1
  have hdiff := classical_differential_heq T.Y ((N-a:ℕ)+1) rfl
    (show ((B+1)+N+1,W+N)=((((B+1)+L)+b+1),((W+L)+b)) by ext <;> dsimp [N] <;> omega)
    y y v₀ v HEq.rfl hv₀ hresult.2.2
  exact ⟨hresult.1,hvcycle,hdiff⟩

/-- The finite-source differential criterion with full upper and selective
lower conditions. -/
public theorem source_finite_differential_ordinary_third_selective_bottom
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
    (hPm : ∀ j : ℕ, 1≤j → j<(b+1)-1 → permanentCycles background T.Y ((((B+1)+L)+1)+j-1+1,(W+L)+j) ≤ Pm j)
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
    (P : Submodule ℤ (Ambient background T.Y ((((B+1)+L)+b+1),((W+L)+b))))
    (hP : permanentCycles background T.Y ((((B+1)+L)+b+1),((W+L)+b)) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ z ∈ P, (background.classical.map T.g).pageMap 2 ((((B+1)+L)+b+1),((W+L)+b)) z = 0 →
      z ∈ boundaries background T.Y (L+b-a:ℕ) ((((B+1)+L)+b+1),((W+L)+b))) :
    IsCycle background T.Y (L+b-a:ℕ) (B+a+1,W+a) y ∧
      IsCycle background T.Y (L+b-a:ℕ) ((((B+1)+L)+b+1),((W+L)+b)) v ∧
      DifferentialAt background T.Y ((L+b-a:ℕ)+1) (B+a+1,W+a) ((((B+1)+L)+b+1),((W+L)+b)) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T he
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X L (by omega)
    (B+1) W x u).mp hdx
  have hdet := ordinary_source_restriction_detects T.X a L haL B W x ζ hζ
  obtain ⟨et,hit⟩ := ordinary_finite_image_of_same_source_third T he hT hf hg hh
    0 a ha B W x z₁ y hxz hdz₁ htop _ hdet
  have htopζ := ordinary_source_image_restriction_top T.X T.Y T.f a L ha haL B W ζ
    (y+(background.classical.map T.f).pageMap 2 (B+a+1,W+a) et) hit
  let U := boundaryRepresentative T.X L (B+1) W ζ
  obtain ⟨eb,hib⟩ := ordinary_full_image_of_selective_middle_third T he hT hf hg hh
    b hb ((B+1)+L) (W+L) u z₂ v huz hdz₂ Pm hPm hbottom U hU
  let error := (background.classical.map T.f).pageMap 2 ((((B+1)+L)+b+1),((W+L)+b)) eb
  obtain ⟨η,wv,hη,hboundary,hperm,herr⟩ := ordinary_bottom_extension_from_boundary_top
    T.X T.Y T.f L b (by omega) hb (B+1) W ζ (v+error) hib
  have herrorP : error ∈ P := by
    have hB := hP (boundary_mem_permanent_cycles T.Y (b+1) _ (wv-(v+error)) herr)
    have h := P.sub_mem (P.sub_mem (hP hperm) hv) hB
    convert h using 1; abel
  have herrorB : error ∈ boundaries background T.Y (L+b-a:ℕ) ((((B+1)+L)+b+1),((W+L)+b)) :=
    hker error herrorP (ordinary_triangle_composite_zero T (((B+1)+L)+b+1) ((W+L)+b) eb)
  have htarget : wv-v ∈ boundaries background T.Y (L+b-a:ℕ) ((((B+1)+L)+b+1),((W+L)+b)) := by
    have h := (boundaries background T.Y (L+b-a:ℕ) _).add_mem
      (boundaries_monotone background T.Y _ (by omega) herr) herrorB
    convert h using 1; abel
  let N := L+b
  let w₀ : Ambient background T.Y ((B+1)+N+1,W+N) :=
    topClassicalRegrade (show ((((B+1)+L)+b+1),((W+L)+b))=((B+1)+N+1,W+N) by
      ext <;> dsimp [N] <;> omega) wv
  let v₀ : Ambient background T.Y ((B+1)+N+1,W+N) :=
    topClassicalRegrade (show ((((B+1)+L)+b+1),((W+L)+b))=((B+1)+N+1,W+N) by
      ext <;> dsimp [N] <;> omega) v
  have hw₀ : HEq w₀ wv := top_classical_regrade_heq _ _
  have hv₀ : HEq v₀ v := top_classical_regrade_heq _ _
  have hsub : HEq (w₀-v₀) (wv-v) := by
    have transport (p p' : ℤ × ℤ) (hp : p=p')
        (a b : Ambient background T.Y p) (a' b' : Ambient background T.Y p')
        (ha : HEq a' a) (hb : HEq b' b) : HEq (a'-b') (a-b) := by
      subst p'; cases eq_of_heq ha; cases eq_of_heq hb; rfl
    exact transport _ _ (by ext <;> dsimp [N] <;> omega) wv v w₀ v₀ hw₀ hv₀
  have htarget₀ : w₀-v₀ ∈ boundaries background T.Y (N-a:ℕ) ((B+1)+N+1,W+N) :=
    classical_boundary_heq T.Y (N-a:ℕ)
      (show ((((B+1)+L)+b+1),((W+L)+b))=((B+1)+N+1,W+N) by ext <;> dsimp [N] <;> omega)
      (wv-v) (w₀-v₀) hsub.symm htarget
  have hb₀ := congrArg (homotopyRegrade
    (show ((W+L)+b)-(((B+1)+L)+b+1)=(W+N)-((B+1)+N+1) by dsimp [N]; omega)
    (show ((W+L)+b)=W+N by dsimp [N]; omega)) hboundary
  rw [source_native_label_transport T.Y (((B+1)+L)+b+1) ((W+L)+b) ((B+1)+N+1) (W+N)
    (by dsimp [N]; omega) (by dsimp [N]; omega) wv w₀ hw₀] at hb₀
  have htopη : homotopyRegrade (show W-(B+1)=(W+a)-(B+a+1) by omega) rfl
      (η ≫ (background.quotients.tower _).rho (0+(a+1)) N (by dsimp [N]; omega)) =
      finiteTopLabelAtWeight T.Y (0+a) (by omega) (0+(a+1)) (by omega)
        (B+a+1) (W+a) W (by omega)
        (y+(background.classical.map T.f).pageMap 2 (B+a+1,W+a) et) := by
    rw [←(background.quotients.tower _).rho_comp (show 0+(a+1)≤L by omega)
      (show L≤N by dsimp [N]; omega),←Category.assoc,hη]
    exact htopζ
  have hresult := ordinary_source_finite_of_top_and_boundary T.X T.Y T.f a N ha
    (by dsimp [N]; omega) B W y et w₀ v₀ η htopη
    (by simpa only [regrade_comp,last_layer_regrade_trans] using hb₀)
    (himage et) htarget₀
  have hvcycle := classical_cycle_heq T.Y (N-a:ℕ)
    (show ((B+1)+N+1,W+N)=((((B+1)+L)+b+1),((W+L)+b)) by ext <;> dsimp [N] <;> omega)
    v₀ v hv₀ hresult.2.1
  have hdiff := classical_differential_heq T.Y ((N-a:ℕ)+1) rfl
    (show ((B+1)+N+1,W+N)=((((B+1)+L)+b+1),((W+L)+b)) by ext <;> dsimp [N] <;> omega)
    y y v₀ v HEq.rfl hv₀ hresult.2.2
  exact ⟨hresult.1,hvcycle,hdiff⟩

end
end KIP126.ProofTools.Internal.SyntheticCoverage
