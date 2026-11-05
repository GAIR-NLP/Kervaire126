module

import all KIP126.ProofTools.SyntheticCoverage.OrdinarySourceFinite
import all KIP126.ProofTools.SyntheticCoverage.SelectiveBoundaryDifferential

/-! Finite-torsion refinements of the ordinary two-sided finite-source
criterion. The upper finite representative is unchanged; only its same
actual absolute boundary supplies the smaller lower candidate spaces. -/

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


/-- The same full source, with its actual finite torsion bound, gives the literal lower top. -/
private theorem torsion_ordinary_full_image_of_selective_middle_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q l : ℕ) (hq : 0 < q) (hl : 0<l) (B W : ℤ)
    (u : Ambient background T.X (B+1,W)) (z : Ambient background T.Z (B+1,W+1))
    (v : Ambient background T.Y (B+q+1,W+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      ((background.classical.map T.h).pageMap 2 (B+1,W+1) z) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (B+1,W+1) ((B+q+1)+1,(W+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (B+q+1) (W+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((B+1)+j-1+1,W+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → boundaries background T.Y ((l:ℤ)+j+1) ((B+1)+j-1+1,W+j) ≤ Pm j)
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
    (hUt : lambdaMultiply l U=0) :
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
  have H := torsion_selective_positive_g_native_residual_same_image T he hf hg hh hT
    0 (q+1) l (by omega) hl (B+1) W Pm
    (fun j hj hjq => by simpa only [Nat.cast_zero,zero_add,add_comm,add_left_comm,add_assoc] using hPm j hj hjq) hmid
  have transport (N : ℕ) (w : ℤ) (hN : 0+(q+1)=N) (hw : W-(0:ℕ)=w) :
      ∀ r : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+1) r →
      ∀ β : BiHom (W-(B+1)) w (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      ∀ v : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+(q+1:ℕ)-1) v →
      r ≫ XModLambdaN.map (background.nu.functor.map T.f) N = β ≫ XModLambdaN.incl _ N-v →
      lambdaMultiply l β=0 →
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
    (lambda_torsion_postcomp l U (background.nu.functor.map T.f) hUt)
  exact ordinary_full_source_top_of_residual T.X T.Y T.f q hq B W U a e v hi
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hefil) heimage


/-- The same full source, with its actual finite torsion bound, gives the literal lower top. -/
private theorem torsion_ordinary_full_image_of_selective_middle_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
    (q l : ℕ) (hq : 0 < q) (hl : 0<l) (B W : ℤ)
    (u : Ambient background T.X (B+1,W)) (z : Ambient background T.Z (B,W))
    (v : Ambient background T.Y (B+q+1,W+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (B+1) (W+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) B W z)
      (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (B,W) (B+q+1,W+q) z
      ((background.classical.map T.g).pageMap 2 (B+q+1,W+q) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((B+1)+j-1+1,W+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(q+1)-1 → boundaries background T.Y ((l:ℤ)+j+1) ((B+1)+j-1+1,W+j) ≤ Pm j)
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
    (hUt : lambdaMultiply l U=0) :
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
  have H := torsion_selective_positive_h_native_residual_same_image T he hf hg hh hT
    0 (q+1) l (by omega) hl (B+1) W Pm
    (fun j hj hjq => by simpa only [Nat.cast_zero,zero_add,add_comm,add_left_comm,add_assoc] using hPm j hj hjq) hmid
  have transport (N : ℕ) (w : ℤ) (hN : 0+(q+1)=N) (hw : W-(0:ℕ)=w) :
      ∀ r : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+1) r →
      ∀ β : BiHom (W-(B+1)) w (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      ∀ v : BiHom (W-(B+1)) w
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N),
      FiltrationAtLeast background.syntheticTower ((B+1)+(q+1:ℕ)-1) v →
      r ≫ XModLambdaN.map (background.nu.functor.map T.f) N = β ≫ XModLambdaN.incl _ N-v →
      lambdaMultiply l β=0 →
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
    (lambda_torsion_postcomp l U (background.nu.functor.map T.f) hUt)
  exact ordinary_full_source_top_of_residual T.X T.Y T.f q hq B W U a e v hi
    (by simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hefil) heimage


/-- The ordinary finite-source differential criterion, retaining all upper
conditions and refining only the lower candidates by true finite torsion. -/
private theorem source_finite_differential_ordinary_second_torsion_bottom
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
    (hPm : ∀ j : ℕ, 1≤j → j<(b+1)-1 → boundaries background T.Y ((L:ℤ)+j+1) ((((B+1)+L)+1)+j-1+1,(W+L)+j) ≤ Pm j)
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
  obtain ⟨eb,hib⟩ := torsion_ordinary_full_image_of_selective_middle_second T he hT hf hg hh
    b L hb (by omega) ((B+1)+L) (W+L) u z₂ v huz hdz₂ Pm hPm hbottom U hU
    (by dsimp only [U,boundaryRepresentative]; rw [lambda_regrade,absolute_boundary_lambda_zero,regrade_zero])
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


/-- The ordinary finite-source differential criterion, retaining all upper
conditions and refining only the lower candidates by true finite torsion. -/
private theorem source_finite_differential_ordinary_third_torsion_bottom
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
    (hPm : ∀ j : ℕ, 1≤j → j<(b+1)-1 → boundaries background T.Y ((L:ℤ)+j+1) ((((B+1)+L)+1)+j-1+1,(W+L)+j) ≤ Pm j)
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
  obtain ⟨eb,hib⟩ := torsion_ordinary_full_image_of_selective_middle_third T he hT hf hg hh
    b L hb (by omega) ((B+1)+L) (W+L) u z₂ v huz hdz₂ Pm hPm hbottom U hU
    (by dsimp only [U,boundaryRepresentative]; rw [lambda_regrade,absolute_boundary_lambda_zero,regrade_zero])
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
