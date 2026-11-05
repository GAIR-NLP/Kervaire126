module

import all KIP126.ProofTools.GeneralizedMahowald.FiniteMayAtTriangle
import all KIP126.ProofTools.MahowaldLeibniz.Corollaries
import all KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch
import all KIP126.ProofTools.MahowaldLeibniz.PositiveGSource
import all KIP126.ProofTools.SyntheticCoverage.RawImageComparison
import all KIP126.ProofTools.MahowaldLeibniz.TopTarget

/-! A common lift from a finite-quotient diagram chase.
The input and both outputs use the same normalized triangle and selected
quotient maps.  The finite diagram chase constructs the common lift from the specified
adjacent connecting equation.  The two ordinary-first-arrow branches then
start from the original classical E₂ fold and construct a native Q₂ class
with both the exact first restriction and the exact top-layer image.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/-- Negation fixes the actual shifted first-quotient label. -/
private theorem suspended_first_label_neg_eq
    (X : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (s t : ℤ)
    (v : Ambient background X (s+q+1,t+q)) :
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel X (s+q+1) (t+q) v))
    (-b = b) := by
  dsimp only
  have h := native_first_label_neg_eq X (s+q+1) (t+q) v
  have h' := congrArg (homotopyRegrade
    (show (t+q)-(s+q+1)=(t-s)-1 by omega) (rfl : t+q=t+q)) h
  rw [output_regrade_neg] at h'
  simpa only [map_neg] using congrArg
    (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1)).symm h'

private theorem top_inclusion_eq_adjacent
    (A : SyntheticSpectrum) (q : ℕ) (hq : 0 < q) :
    finiteTopInclusion A q hq =
      (show (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A 1) ⟶
          XModLambdaN A (q+1) from by
        simpa only [show q.succ-q=1 by omega] using
          ((background.quotients.tower A).triangle hq (Nat.lt_succ_self q)).lambdaMap) := by
  have transport (n : ℕ) (hn : n=1)
      (l : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n) ⟶
        XModLambdaN A (q+1)) :
      oneInclusionCast A _ q n hn l =
        (show (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A 1) ⟶
            XModLambdaN A (q+1) from by simpa only [hn] using l) := by
    subst n
    rfl
  exact transport _ (by omega) _

/-- An adjacent finite zigzag gives one representative with
the prescribed first restriction and highest-layer image. The suspension
comparison is constructed from the rows; mod-two first-layer detection
removes the sign. Here `q+1` is the quotient length and bottom-differential
page, with `q=1` giving the two-layer lift. The finite-quotient core
supplies the E₂ source labels and differential-to-connecting comparison. -/
private theorem finite_common_lift_first_and_top
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (v : Ambient background T.Y (s+q+1,t+q)) :
    let V := normalizedTriangle background T he
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel T.Y (s+q+1) (t+q) v))
    let delta : XModLambdaN V.obj₃ q ⟶ (F.obj (XModLambdaN V.obj₃ 1))⟦(1:ℤ)⟧ := by
      simpa only [show q.succ-q=1 by omega] using
        ((background.quotients.tower V.obj₃).triangle hq (Nat.lt_succ_self q)).delta
    ∀ (a : BiHom (t-s) t (XModLambdaN V.obj₃ q)),
      a ≫ delta = b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (F.map (XModLambdaN.map V.mor₂ 1)) →
      ∃ ey : XModLambdaN (V.obj₂⟦(1:ℤ)⟧) (q+1) ≅
          (XModLambdaN V.obj₂ (q+1))⟦(1:ℤ)⟧,
        XModLambdaN.incl _ (q+1) ≫ ey.hom =
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl V.obj₂ (q+1)) ∧
        ∃ c : BiHom (t-s) t (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (q+1)),
          c ≫ (background.quotients.tower _).rho 1 (q+1) (by omega) =
            a ≫ (background.quotients.tower _).rho 1 q hq ≫ XModLambdaN.map V.mor₃ 1 ∧
          c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁)
              (q+1) ≫ ey.hom =
            b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
              (finiteTopInclusion (background.nu.functor.obj (T.Y.obj background.auxiliary)) q hq) := by
  dsimp only
  intro a ha
  let V := normalizedTriangle background T he
  obtain ⟨ey,hey,_⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he (q+1) (by omega)
  obtain ⟨c,hc,himage⟩ := finite_may_at_normalized_triangle_explicit_lengths
    T he hT q 1 hq (by omega) (t-s) t ey hey a _ ha
  refine ⟨ey,hey,c,?_,?_⟩
  · rw [←(background.quotients.tower _).rho_comp hq (Nat.le_succ q),
      ←Category.assoc,hc,Category.assoc,
      ←(background.quotients.natural V.mor₃).rho_naturality hq]
  · have hb := suspended_first_label_neg_eq T.Y q s t v
    have hsign := congrArg (fun b => b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (finiteTopInclusion (background.nu.functor.obj (T.Y.obj background.auxiliary)) q hq)) hb
    exact himage.trans (by
      simpa only [normalizedTriangle, Triangle.mk, Preadditive.neg_comp, top_inclusion_eq_adjacent] using hsign)

private theorem ordinary_may_desuspend_zero
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (N : ℕ) (s t : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (a : BiHom (t-s) t (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N)) :
    homotopyRegrade rfl (show t-(0:ℕ)=t by simp)
      (positiveHSourceDesuspend T he hf N 0 s t ε
        (homotopyRegrade rfl (show t=t-(0:ℕ) by simp) a)) =
      homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (show t-(1,0).2=t by simp)
        (quotientShiftDesuspend T.X (1,0) N ε (t-s) t
          (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom N)) := by
  erw [quotient_shift_desuspend_as_native_unshift T.X (1,0) (t-(s+1),t)
    N (t-s) t (by dsimp; omega) (by simp)]
  unfold positiveHSourceDesuspend
  rw [quotient_unshift_regrade_pair T.X (1,0) (t-(s+1),t-(0:ℕ)) (t-(s+1),t)
    (Prod.ext rfl (by simp)) N ε]
  simp only [←regrade_comp,output_regrade_trans]

private theorem coefficient_insert_zero_regrade (A : SyntheticSpectrum)
    (m w : ℤ) (a : BiHom m w (XModLambdaN A 2)) :
    homotopyRegrade rfl (show w-(0:ℕ)=w by simp)
      (finiteCoefficientInsert A 0 2 (by decide) m w a) = a := by
  change homotopyRegrade rfl (show w-(0:ℕ)=w by omega)
    (homotopyRegrade rfl (show w=w-(0:ℕ) by omega) a)=a
  exact homotopy_regrade_inverse rfl (show w=w-(0:ℕ) by omega) a

private theorem ordinary_susp_regrade_weight (A : SyntheticSpectrum) (m w w' : ℤ)
    (hw : w=w') (a : BiHom (m-1) w A) :
    homotopyRegrade rfl hw (ordinarySuspendedRepresentative A m w a) =
      ordinarySuspendedRepresentative A m w' (homotopyRegrade rfl hw a) := by
  subst w'
  rfl


/-- The classical d₂ fold and specified H₂ source label give
the common Q₂ representative in the positive-h branch. -/
private theorem two_layer_raw_lift_positive_h
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (s t : ℤ)
    (z : Ambient background T.Z (s,t)) (x : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+1+1,t+1))
    (hx : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      2 (s,t) (s+1+1,t+1) z ((background.classical.map T.g).pageMap 2 (s+1+1,t+1) v)) :
    ∃ (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) 2 ≅
        (SyntheticCategory.biShift (1,0)).obj
          (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2))
      (ey : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) 2 ≅
        (XModLambdaN (normalizedTriangle background T he).obj₂ 2)⟦(1:ℤ)⟧),
      XModLambdaN.incl _ 2 ≫ ε.hom =
        (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ 2) ∧
      XModLambdaN.incl _ 2 ≫ ey.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ 2) ∧
      ∃ a : BiHom (t-s) t (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) 2),
        (homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (show t-(1,0).2=t by simp)
          (quotientShiftDesuspend T.X (1,0) 2 ε (t-s) t
            (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom 2))) ≫
            (background.quotients.tower _).rho 1 2 (by decide) = nativeFirstLabel T.X (s+1) t x ∧
        a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
            (normalizedTriangle background T he).mor₁) 2 ≫ ey.hom =
          ordinarySuspendedRepresentative _ (t-s) t
            (homotopyRegrade rfl (show t-(0:ℕ)=t by simp)
              (finiteMayTopLabel T.Y 0 1 (by decide) s t v)) := by
  obtain ⟨ey,hey,_⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he 2 (by decide)
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) 2
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  obtain ⟨a,c,ha,_,hc,hi⟩ := classical_second_differential_may
    T he hT hg 1 (by decide) s t z v hd ey hey
  have hsource := positive_h_may_source_first_label T he hf hg hh 1 2 (by decide)
    (by decide) s t z x hx ε hε a c ha hc
  refine ⟨ε,ey,hε,hey,c,?_,?_⟩
  · simpa only [sub_zero] using hsource.1
  · have htop := finite_may_signed_target_eq_top_at_level T.Y 0 1 (by decide)
      s t v ey ey hey hey
    have htop' := congrArg (homotopyRegrade (rfl : t-s=t-s)
      (show t-(0:ℕ)=t by simp)) htop
    rw [regrade_comp,coefficient_insert_zero_regrade,
      ordinary_susp_regrade_weight] at htop'
    exact hi.trans (by
      simpa only [normalizedTriangle,Triangle.mk,Category.assoc,Iso.inv_hom_id,
        Category.comp_id,Preadditive.neg_comp] using htop')


/-- The same classical d₂ construction in the positive-g normalization. -/
private theorem two_layer_raw_lift_positive_g
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t : ℤ)
    (z : Ambient background T.Z (s+1,t+1)) (x : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+1+1,t+1))
    (hx : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((background.classical.map T.h).pageMap 2 (s+1,t+1) z)
      (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      2 (s+1,t+1) ((s+1+1)+1,(t+1)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (s+1+1) (t+1) v)) :
    ∃ (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) 2 ≅
        (SyntheticCategory.biShift (1,0)).obj
          (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2))
      (ey : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) 2 ≅
        (XModLambdaN (normalizedTriangle background T he).obj₂ 2)⟦(1:ℤ)⟧),
      XModLambdaN.incl _ 2 ≫ ε.hom =
        (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ 2) ∧
      XModLambdaN.incl _ 2 ≫ ey.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ 2) ∧
      ∃ a : BiHom (t-s) t (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) 2),
        (homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (show t-(1,0).2=t by simp)
          (quotientShiftDesuspend T.X (1,0) 2 ε (t-s) t
            (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom 2))) ≫
            (background.quotients.tower _).rho 1 2 (by decide) = nativeFirstLabel T.X (s+1) t x ∧
        a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
            (normalizedTriangle background T he).mor₁) 2 ≫ ey.hom =
          ordinarySuspendedRepresentative _ (t-s) t
            (homotopyRegrade rfl (show t-(0:ℕ)=t by simp)
              (finiteMayTopLabel T.Y 0 1 (by decide) s t v)) := by
  obtain ⟨ey,hey,_⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he 2 (by decide)
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) 2
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  let V := normalizedTriangle background T he
  let v' : Ambient background T.Y ((s+1)+(1:ℕ),(t+1)+(1:ℕ)-1) :=
    positiveClassicalRegrade (Prod.ext (by omega) (by omega)) v
  have hd' : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((1:ℕ)+1) (s+1,t+1) ((s+1)+(1:ℕ)+1,(t+1)+(1:ℕ)) z
      (positiveClassicalRegrade (X:=T.Z) (Prod.ext (by omega) (by omega))
        (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
          ((s+1)+(1:ℕ)) ((t+1)+(1:ℕ)-1) v')) := by
    dsimp only [v']
    rw [positive_first_quotient_operation_regrade T.Y T.Z (normalizedSecondPositiveMap T hg)
      (s+(1:ℕ)+1) (t+(1:ℕ)) ((s+1)+(1:ℕ)) ((t+1)+(1:ℕ)-1) (by omega) (by omega),
      positive_classical_regrade_trans]
    exact positive_has_differential_target_regrade T.Z _ _ _ _ _ z _ hd
  obtain ⟨a₀,d₀,ha₀,_,hd₀,hf₀⟩ := positive_second_differential_may
    T he hT hg (1:ℕ) (by decide) (s+1) (t+1) z v' hd' ey hey
  let a := homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
    (show (t+1)-1=t by omega) a₀
  let d := homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
    (show (t+1)-1=t by omega) d₀
  have ha : a ≫ (background.quotients.tower _).rho 1 (1:ℕ) (by decide) =
      homotopyRegrade (by dsimp;omega) (by dsimp;omega)
        (shiftHomotopyClass (0,-1) ((t+1)-(s+1),t+1)
          (nativeFirstLabel T.Z (s+1) (t+1) z)) ≫
        (levelQuotientShiftIso T.Z (-1) 1).inv ≫
          XModLambdaN.map (normalizedThirdNegativeIso T he hg).inv 1 := by
    have h := congrArg (homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
      (show (t+1)-1=t by omega)) ha₀
    simpa only [a,regrade_comp,regrade_transitive] using h
  have hdR : d ≫ (background.quotients.tower _).rho (1:ℕ) ((1:ℕ)+1) (by omega) =
      a ≫ XModLambdaN.map V.mor₃ (1:ℕ) := by
    have h := congrArg (homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
      (show (t+1)-1=t by omega)) hd₀
    simpa only [a,d,regrade_comp] using h
  have hs := positive_g_may_source_first_label T he hf hg hh 1 2 (by decide)
    (by decide) s t z x hx ε hε a d ha hdR
  refine ⟨ε,ey,hε,hey,d,?_,?_⟩
  · simpa only [sub_zero] using hs.1
  · let b := (biSuspensionHomEquiv (t-s) t ((1:ℕ):ℤ)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+(1:ℕ))-(s+(1:ℕ)+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel T.Y (s+(1:ℕ)+1) (t+(1:ℕ)) v))
    let ly : (SyntheticCategory.biShift (0,-((1:ℕ):ℤ))).obj
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1) ⟶
        XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 2 := by
      simpa only [show (1:ℕ).succ-1=1 by decide] using
        ((background.quotients.tower (background.nu.functor.obj (T.Y.obj background.auxiliary))).triangle
          (show 0<(1:ℕ) by decide) (Nat.lt_succ_self 1)).lambdaMap
    have h := congrArg (homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
      (show (t+1)-1=t by omega)) hf₀
    have hv : nativeFirstLabel T.Y ((s+1)+(1:ℕ)) ((t+1)+(1:ℕ)-1) v' =
        homotopyRegrade (by omega) (by omega)
          (nativeFirstLabel T.Y (s+(1:ℕ)+1) (t+(1:ℕ)) v) :=
      native_first_label_transport T.Y (show s+(1:ℕ)+1=(s+1)+(1:ℕ) by omega)
        (show t+(1:ℕ)=(t+1)+(1:ℕ)-1 by omega) v
    rw [hv] at h

    have hi : d ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) 2 ≫ ey.hom =
        -(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly) := by
      simpa only [b,ly,d,regrade_comp,output_regrade_neg,bi_susp_symm_regrade,
        regrade_transitive,normalizedTriangle,Triangle.mk] using h
    have htop := finite_may_signed_target_eq_top_at_level T.Y 0 1 (by decide)
      s t v ey ey hey hey
    have htop' := congrArg (homotopyRegrade (rfl : t-s=t-s)
      (show t-(0:ℕ)=t by simp)) htop
    rw [regrade_comp,coefficient_insert_zero_regrade,
      ordinary_susp_regrade_weight] at htop'
    exact hi.trans (by
      simpa only [b,ly,normalizedTriangle,Triangle.mk,Category.assoc,Iso.inv_hom_id,
        Category.comp_id,Preadditive.neg_comp] using htop')

/-- The same raw representative descends to a native Q₂ class with both
prescribed equations.  This is only a coordinate comparison; the two
classical constructions below discharge its raw inputs. -/
private theorem ordinary_two_layer_native_of_raw
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (s t : ℤ) (x : Ambient background T.X (s+1,t)) (v : Ambient background T.Y (s+1+1,t+1))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) 2 ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2))
    (hε : XModLambdaN.incl _ 2 ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ 2))
    (ey : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) 2 ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ 2)⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ 2 ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ 2))
    (a : BiHom (t-s) t (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) 2))
    (ha : (homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (show t-(1,0).2=t by simp)
        (quotientShiftDesuspend T.X (1,0) 2 ε (t-s) t
          (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom 2))) ≫
          (background.quotients.tower _).rho 1 2 (by decide) = nativeFirstLabel T.X (s+1) t x)
    (hi : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) 2 ≫ ey.hom =
      ordinarySuspendedRepresentative _ (t-s) t
        (homotopyRegrade rfl (show t-(0:ℕ)=t by simp)
          (finiteMayTopLabel T.Y 0 1 (by decide) s t v))) :
    ∃ c : BiHom (t-(s+1)) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2),
      c ≫ (background.quotients.tower _).rho 1 2 (by decide) = nativeFirstLabel T.X (s+1) t x ∧
      c ≫ XModLambdaN.map (background.nu.functor.map T.f) 2 =
        homotopyRegrade (show (t+1)-(s+1+1)=t-(s+1) by omega)
          (show (t+1)-(1:ℕ)=t by omega)
          (finiteTopLabel T.Y 1 (by decide) (s+1+1) (t+1) v) := by
  let c := homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (show t-(1,0).2=t by simp)
    (quotientShiftDesuspend T.X (1,0) 2 ε (t-s) t
      (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom 2))
  let a' := homotopyRegrade (rfl : t-s=t-s) (show t=t-(0:ℕ) by simp) a
  have hraw := native_ordinary_image_eq_raw_image T he hf 2 0 (by decide) s t ε hε ey hey a'
  have hraw' := congrArg (homotopyRegrade (rfl : t-s=t-s)
    (show t-(0:ℕ)=t by simp)) hraw
  rw [ordinary_susp_regrade_weight] at hraw'
  have hdesc := ordinary_may_desuspend_zero T he hf 2 s t ε a
  have hsquare : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) 2 ≫ ey.hom =
      ordinarySuspendedRepresentative _ (t-s) t
        (homotopyRegrade (show t-(s+1)=(t-s)-1 by omega) rfl
          (c ≫ XModLambdaN.map (background.nu.functor.map T.f) 2)) := by
    have hc := congrArg (fun z => homotopyRegrade
      (show t-(s+1)=(t-s)-1 by omega) rfl
        (z ≫ XModLambdaN.map (background.nu.functor.map T.f) 2)) hdesc
    simp only [regrade_comp,output_regrade_trans] at hc
    simp only [a',regrade_comp,output_regrade_trans] at hraw'
    rw [hc] at hraw'
    simpa only [c,regrade_comp,output_regrade_trans,top_target_regrade_self] using hraw'
  have heq := ordinary_suspended_representative_injective _ (t-s) t (hsquare.symm.trans hi)
  have hn := congrArg (homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (rfl : t=t)) heq
  refine ⟨c,ha,?_⟩
  simp only [finiteMayTopLabel,finiteTopLabelAtWeight,output_regrade_trans,
    top_target_regrade_self] at hn
  convert hn using 1
  rfl

/-- Classical E₂ fold to one native Q₂ representative with both exact equations. -/
private theorem two_layer_common_lift_positive_h
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (s t : ℤ)
    (z : Ambient background T.Z (s,t)) (x : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+1+1,t+1))
    (hx : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      2 (s,t) (s+1+1,t+1) z ((background.classical.map T.g).pageMap 2 (s+1+1,t+1) v)) :
    ∃ c : BiHom (t-(s+1)) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2),
      c ≫ (background.quotients.tower _).rho 1 2 (by decide) = nativeFirstLabel T.X (s+1) t x ∧
      c ≫ XModLambdaN.map (background.nu.functor.map T.f) 2 =
        homotopyRegrade (show (t+1)-(s+1+1)=t-(s+1) by omega)
          (show (t+1)-(1:ℕ)=t by omega)
          (finiteTopLabel T.Y 1 (by decide) (s+1+1) (t+1) v) := by
  obtain ⟨ε,ey,hε,hey,a,ha,hi⟩ := two_layer_raw_lift_positive_h
    T he hT hf hg hh s t z x v hx hd
  exact ordinary_two_layer_native_of_raw T he hf s t x v ε hε ey hey a ha hi

/-- Classical E₂ fold to one native Q₂ representative with both exact equations. -/
private theorem two_layer_common_lift_positive_g
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t : ℤ)
    (z : Ambient background T.Z (s+1,t+1)) (x : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+1+1,t+1))
    (hx : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((background.classical.map T.h).pageMap 2 (s+1,t+1) z)
      (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      2 (s+1,t+1) ((s+1+1)+1,(t+1)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (s+1+1) (t+1) v)) :
    ∃ c : BiHom (t-(s+1)) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2),
      c ≫ (background.quotients.tower _).rho 1 2 (by decide) = nativeFirstLabel T.X (s+1) t x ∧
      c ≫ XModLambdaN.map (background.nu.functor.map T.f) 2 =
        homotopyRegrade (show (t+1)-(s+1+1)=t-(s+1) by omega)
          (show (t+1)-(1:ℕ)=t by omega)
          (finiteTopLabel T.Y 1 (by decide) (s+1+1) (t+1) v) := by
  obtain ⟨ε,ey,hε,hey,a,ha,hi⟩ := two_layer_raw_lift_positive_g
    T he hT hf hg hh s t z x v hx hd
  exact ordinary_two_layer_native_of_raw T he hf s t x v ε hε ey hey a ha hi

private theorem coefficient_insert_zero_regrade_general (A : SyntheticSpectrum)
    (K : ℕ) (hK : 0<K) (m w : ℤ) (a : BiHom m w (XModLambdaN A K)) :
    homotopyRegrade rfl (show w-(0:ℕ)=w by simp)
      (finiteCoefficientInsert A 0 K hK m w a) =
      (by simpa only [Nat.zero_add] using a) := by
  let a' : BiHom m w (XModLambdaN A (0+K)) := by simpa only [Nat.zero_add] using a
  change homotopyRegrade rfl (show w-(0:ℕ)=w by omega)
    (homotopyRegrade rfl (show w=w-(0:ℕ) by omega) a') = a'
  exact homotopy_regrade_inverse rfl (show w=w-(0:ℕ) by omega) a'

/-- The unextended signed May target is the ordinary suspension of one
specified top label, at any finite quotient length. -/
private theorem ordinary_may_signed_top_target
    (X : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (v : Ambient background X (s+q+1,t+q)) :
    let A := background.nu.functor.obj (X.obj background.auxiliary)
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN A 1)).symm
      (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
        (nativeFirstLabel X (s+q+1) (t+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A 1) ⟶
        XModLambdaN A (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((background.quotients.tower A).triangle hq (Nat.lt_succ_self q)).lambdaMap
    (-(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly) =
      ordinarySuspendedRepresentative _ (t-s) t
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega)
          (show (t+q)-q=t by omega) (finiteTopLabel X q hq (s+q+1) (t+q) v))) := by
  dsimp only
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let α : BiHom ((t-s)-1) (t+q) (XModLambdaN A 1) :=
    homotopyRegrade (by omega) rfl (nativeFirstLabel X (s+q+1) (t+q) v)
  let α' : BiHom ((t-s)-1) (t+q) (XModLambdaN A (q+1-q)) :=
    by simpa only [Nat.add_sub_cancel_left] using α
  let b₀ := finiteMayNativeTargetClass A (q+1) q (by omega) (t-s) t α'
  have hα := first_label_detects_unshifted X 1 (by omega) (s+q+1) (t+q) v
    (nativeFirstLabel X (s+q+1) (t+q) v) (by
      rw [(background.quotients.tower _).rho_id,Category.comp_id]
      rfl)
  have hα' : Detects (background.convergence (.quotient (q+1-q) (.nu X)))
      (s+q+1,t+q,t+q)
      (regradeE2 (by simp) (finiteTargetLabel background X (q+1-q) (s+q+1) (t+q) 0 v))
      (homotopyRegrade (by dsimp; omega) rfl α') := by
    have transport (n : ℕ) (hn : n=1)
        (hA : BiHom ((t-s)-1) (t+q) (XModLambdaN A 1) =
          BiHom ((t-s)-1) (t+q) (XModLambdaN A n)) :
        Detects (background.convergence (.quotient n (.nu X))) (s+q+1,t+q,t+q)
          (regradeE2 (by simp) (finiteTargetLabel background X n (s+q+1) (t+q) 0 v))
          (homotopyRegrade (by dsimp; omega) rfl (hA.mp α)) := by
      subst n
      convert hα using 1
      change homotopyRegrade (show ((t-s)-1)=(t+q)-(s+q+1) by omega) rfl
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
        (nativeFirstLabel X (s+q+1) (t+q) v)) = _
      rw [output_regrade_trans]
      rfl
    exact transport (q+1-q) (by omega) _
  have hd := finite_may_native_target_detects X (q+1) q (by omega) (t-s) t
    (s+q+1) (t+q) (by omega) rfl v α' hα'
  rw [←finite_coefficient_weight_label] at hd
  have hd' := finite_weight_detection_regrade X (q+1) (s+q+1) (t+q)
    ((t+q)-q) t (by omega) (by omega) (by omega) v _ hd
  have hbase : Detects (background.convergence (.quotient (q+1) (.nu X)))
      (s+q+1,t+q,t)
      ((background.family.quotientProjection A (q+1)).pageMap 2 (s+q+1,t+q,t)
        (nuWeightLabel background X (s+q+1) (t+q) t (by omega) v))
      (homotopyRegrade (by dsimp; omega) rfl b₀) := by
    simpa only [b₀,A,SyntheticObject.obj,output_regrade_trans] using hd'
  have hrawbase := finite_may_signed_target_ordinary A (q+1) q hq (by omega) (t-s) t α'
  have hbase' :
      (-((biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN A 1)).symm α) ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (by simpa only [show q.succ-q=1 by omega] using
            ((background.quotients.tower A).triangle hq (Nat.lt_succ_self q)).lambdaMap)) =
      ordinarySuspendedRepresentative _ (t-s) t b₀ := by
    have transport (n : ℕ) (hn : n=1)
        (hA : BiHom ((t-s)-1) (t+q) (XModLambdaN A 1) =
          BiHom ((t-s)-1) (t+q) (XModLambdaN A n))
        (ln : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n) ⟶
          XModLambdaN A (q+1))
        (hL : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n) ⟶
          XModLambdaN A (q+1)) =
          ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A 1) ⟶
          XModLambdaN A (q+1))) :
        (-(biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN A n)).symm (hA.mp α) ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map ln) =
        (-(biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN A 1)).symm α ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map (hL.mp ln)) := by
      subst n
      rfl
    have hraw :
        (-(biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN A (q+1-q))).symm α' ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map
            ((background.quotients.tower A).triangle hq (Nat.lt_succ_self q)).lambdaMap) =
        (-(biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN A 1)).symm α ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map
            (by simpa only [show q.succ-q=1 by omega] using
              ((background.quotients.tower A).triangle hq (Nat.lt_succ_self q)).lambdaMap)) :=
      transport (q+1-q) (by omega) _ _ _
    exact hraw.symm.trans hrawbase
  have htop := finite_top_label_at_weight_detects X q hq (q+1) rfl
    (s+q+1) (t+q) t (by omega) v
  have heq := finite_top_detection_unique X (q+1) (by omega)
    (s+q+1) (t+q) t (by omega) _ _ _ hbase htop
  have hn := congrArg (homotopyRegrade
    (show (t+q)-(s+q+1)=(t-s)-1 by omega) (rfl : t=t)) heq
  simp only [finiteTopLabelAtWeight,output_regrade_trans,top_target_regrade_self] at hn
  rw [hn] at hbase'
  simpa only [α,Preadditive.neg_comp] using hbase'

private theorem finite_raw_lift_positive_h
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient background T.Z (s,t)) (x : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hx : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) v)) :
    ∃ (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (q+1) ≅
        (SyntheticCategory.biShift (1,0)).obj
          (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)))
      (ey : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
        (XModLambdaN (normalizedTriangle background T he).obj₂ (q+1))⟦(1:ℤ)⟧),
      XModLambdaN.incl _ (q+1) ≫ ε.hom =
        (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (q+1)) ∧
      XModLambdaN.incl _ (q+1) ≫ ey.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)) ∧
      ∃ a : BiHom (t-s) t (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (q+1)),
        (homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (show t-(1,0).2=t by simp)
          (quotientShiftDesuspend T.X (1,0) (q+1) ε (t-s) t
            (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom (q+1)))) ≫
            (background.quotients.tower _).rho 1 (q+1) (by omega) = nativeFirstLabel T.X (s+1) t x ∧
        a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
            (normalizedTriangle background T he).mor₁) (q+1) ≫ ey.hom =
          ordinarySuspendedRepresentative _ (t-s) t
            (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega)
              (show (t+q)-q=t by omega) (finiteTopLabel T.Y q hq (s+q+1) (t+q) v)) := by
  obtain ⟨ey,hey,_⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he (q+1) (by omega)
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) (q+1)
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  obtain ⟨a,c,ha,_,hc,hi⟩ := classical_second_differential_may
    T he hT hg q hq s t z v hd ey hey
  have hsource := positive_h_may_source_first_label T he hf hg hh q (q+1) (by omega)
    (by omega) s t z x hx ε hε a c ha hc
  refine ⟨ε,ey,hε,hey,c,?_,?_⟩
  · simpa only [sub_zero] using hsource.1
  · exact hi.trans (by
      simpa only [normalizedTriangle,Triangle.mk,Preadditive.neg_comp] using
        ordinary_may_signed_top_target T.Y q hq s t v)

private theorem ordinary_finite_native_of_raw
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (q : ℕ) (hq : 0<q) (s t : ℤ) (x : Ambient background T.X (s+1,t)) (v : Ambient background T.Y (s+q+1,t+q))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (q+1) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)))
    (hε : XModLambdaN.incl _ (q+1) ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (q+1)))
    (ey : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ (q+1))⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)))
    (a : BiHom (t-s) t (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (q+1)))
    (ha : (homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (show t-(1,0).2=t by simp)
        (quotientShiftDesuspend T.X (1,0) (q+1) ε (t-s) t
          (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom (q+1)))) ≫
          (background.quotients.tower _).rho 1 (q+1) (by omega) = nativeFirstLabel T.X (s+1) t x)
    (hi : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (q+1) ≫ ey.hom =
      ordinarySuspendedRepresentative _ (t-s) t
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega)
          (show (t+q)-q=t by omega) (finiteTopLabel T.Y q hq (s+q+1) (t+q) v))) :
    ∃ c : BiHom (t-(s+1)) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)),
      c ≫ (background.quotients.tower _).rho 1 (q+1) (by omega) = nativeFirstLabel T.X (s+1) t x ∧
      c ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1) =
        homotopyRegrade (show (t+q)-(s+q+1)=t-(s+1) by omega)
          (show (t+q)-q=t by omega)
          (finiteTopLabel T.Y q hq (s+q+1) (t+q) v) := by
  let c := homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (show t-(1,0).2=t by simp)
    (quotientShiftDesuspend T.X (1,0) (q+1) ε (t-s) t
      (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom (q+1)))
  let a' := homotopyRegrade (rfl : t-s=t-s) (show t=t-(0:ℕ) by simp) a
  have hraw := native_ordinary_image_eq_raw_image T he hf (q+1) 0 (by omega) s t ε hε ey hey a'
  have hraw' := congrArg (homotopyRegrade (rfl : t-s=t-s)
    (show t-(0:ℕ)=t by simp)) hraw
  rw [ordinary_susp_regrade_weight] at hraw'
  have hdesc := ordinary_may_desuspend_zero T he hf (q+1) s t ε a
  have hsquare : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (q+1) ≫ ey.hom =
      ordinarySuspendedRepresentative _ (t-s) t
        (homotopyRegrade (show t-(s+1)=(t-s)-1 by omega) rfl
          (c ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1))) := by
    have hc := congrArg (fun z => homotopyRegrade
      (show t-(s+1)=(t-s)-1 by omega) rfl
        (z ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1))) hdesc
    simp only [regrade_comp,output_regrade_trans] at hc
    simp only [a',regrade_comp,output_regrade_trans] at hraw'
    rw [hc] at hraw'
    simpa only [c,regrade_comp,output_regrade_trans,top_target_regrade_self] using hraw'
  have heq := ordinary_suspended_representative_injective _ (t-s) t (hsquare.symm.trans hi)
  have hn := congrArg (homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (rfl : t=t)) heq
  refine ⟨c,ha,?_⟩
  simpa only [output_regrade_trans,top_target_regrade_self] using hn

private theorem finite_raw_lift_positive_g
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient background T.Z (s+1,t+1)) (x : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hx : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((background.classical.map T.h).pageMap 2 (s+1,t+1) z)
      (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+1,t+1) ((s+q+1)+1,(t+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (s+q+1) (t+q) v)) :
    ∃ (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (q+1) ≅
        (SyntheticCategory.biShift (1,0)).obj
          (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)))
      (ey : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
        (XModLambdaN (normalizedTriangle background T he).obj₂ (q+1))⟦(1:ℤ)⟧),
      XModLambdaN.incl _ (q+1) ≫ ε.hom =
        (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (q+1)) ∧
      XModLambdaN.incl _ (q+1) ≫ ey.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)) ∧
      ∃ a : BiHom (t-s) t (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (q+1)),
        (homotopyRegrade (show (t-s)-1=t-(s+1) by omega) (show t-(1,0).2=t by simp)
          (quotientShiftDesuspend T.X (1,0) (q+1) ε (t-s) t
            (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom (q+1)))) ≫
            (background.quotients.tower _).rho 1 (q+1) (by omega) = nativeFirstLabel T.X (s+1) t x ∧
        a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
            (normalizedTriangle background T he).mor₁) (q+1) ≫ ey.hom =
          ordinarySuspendedRepresentative _ (t-s) t
            (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega)
              (show (t+q)-q=t by omega) (finiteTopLabel T.Y q hq (s+q+1) (t+q) v)) := by
  obtain ⟨ey,hey,_⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he (q+1) (by omega)
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) (q+1)
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  let V := normalizedTriangle background T he
  let v' : Ambient background T.Y ((s+1)+q,(t+1)+q-1) :=
    positiveClassicalRegrade (Prod.ext (by omega) (by omega)) v
  have hd' : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+1,t+1) ((s+1)+q+1,(t+1)+q) z
      (positiveClassicalRegrade (X:=T.Z) (Prod.ext (by omega) (by omega))
        (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
          ((s+1)+q) ((t+1)+q-1) v')) := by
    dsimp only [v']
    rw [positive_first_quotient_operation_regrade T.Y T.Z (normalizedSecondPositiveMap T hg)
      (s+q+1) (t+q) ((s+1)+q) ((t+1)+q-1) (by omega) (by omega),
      positive_classical_regrade_trans]
    exact positive_has_differential_target_regrade T.Z _ _ _ _ _ z _ hd
  obtain ⟨a₀,d₀,ha₀,_,hd₀,hf₀⟩ := positive_second_differential_may
    T he hT hg q hq (s+1) (t+1) z v' hd' ey hey
  let a := homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
    (show (t+1)-1=t by omega) a₀
  let d := homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
    (show (t+1)-1=t by omega) d₀
  have ha : a ≫ (background.quotients.tower _).rho 1 q hq =
      homotopyRegrade (by dsimp;omega) (by dsimp;omega)
        (shiftHomotopyClass (0,-1) ((t+1)-(s+1),t+1)
          (nativeFirstLabel T.Z (s+1) (t+1) z)) ≫
        (levelQuotientShiftIso T.Z (-1) 1).inv ≫
          XModLambdaN.map (normalizedThirdNegativeIso T he hg).inv 1 := by
    have h := congrArg (homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
      (show (t+1)-1=t by omega)) ha₀
    simpa only [a,regrade_comp,regrade_transitive] using h
  have hdR : d ≫ (background.quotients.tower _).rho q (q+1) (by omega) =
      a ≫ XModLambdaN.map V.mor₃ q := by
    have h := congrArg (homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
      (show (t+1)-1=t by omega)) hd₀
    simpa only [a,d,regrade_comp] using h
  have hs := positive_g_may_source_first_label T he hf hg hh q (q+1) hq
    (by omega) s t z x hx ε hε a d ha hdR
  refine ⟨ε,ey,hε,hey,d,?_,?_⟩
  · simpa only [sub_zero] using hs.1
  · let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel T.Y (s+q+1) (t+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1) ⟶
        XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((background.quotients.tower (background.nu.functor.obj (T.Y.obj background.auxiliary))).triangle
          hq (Nat.lt_succ_self q)).lambdaMap
    have h := congrArg (homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
      (show (t+1)-1=t by omega)) hf₀
    have hv : nativeFirstLabel T.Y ((s+1)+q) ((t+1)+q-1) v' =
        homotopyRegrade (by omega) (by omega)
          (nativeFirstLabel T.Y (s+q+1) (t+q) v) :=
      native_first_label_transport T.Y (show s+q+1=(s+1)+q by omega)
        (show t+q=(t+1)+q-1 by omega) v
    rw [hv] at h
    have hi : d ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (q+1) ≫ ey.hom =
        -(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly) := by
      simpa only [b,ly,d,regrade_comp,output_regrade_neg,bi_susp_symm_regrade,
        regrade_transitive,normalizedTriangle,Triangle.mk] using h
    exact hi.trans (ordinary_may_signed_top_target T.Y q hq s t v)

/-- The original classical fold supplies one native representative at every finite level. -/
private theorem finite_common_lift_positive_h
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient background T.Z (s,t)) (x : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hx : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) v)) :
    ∃ c : BiHom (t-(s+1)) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)),
      c ≫ (background.quotients.tower _).rho 1 (q+1) (by omega) = nativeFirstLabel T.X (s+1) t x ∧
      c ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1) =
        homotopyRegrade (show (t+q)-(s+q+1)=t-(s+1) by omega)
          (show (t+q)-q=t by omega)
          (finiteTopLabel T.Y q hq (s+q+1) (t+q) v) := by
  obtain ⟨ε,ey,hε,hey,a,ha,hi⟩ := finite_raw_lift_positive_h
    T he hT hf hg hh q hq s t z x v hx hd
  exact ordinary_finite_native_of_raw T he hf q hq s t x v ε hε ey hey a ha hi

/-- The original classical fold supplies one native representative at every finite level. -/
private theorem finite_common_lift_positive_g
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient background T.Z (s+1,t+1)) (x : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hx : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((background.classical.map T.h).pageMap 2 (s+1,t+1) z)
      (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+1,t+1) ((s+q+1)+1,(t+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (s+q+1) (t+q) v)) :
    ∃ c : BiHom (t-(s+1)) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)),
      c ≫ (background.quotients.tower _).rho 1 (q+1) (by omega) = nativeFirstLabel T.X (s+1) t x ∧
      c ≫ XModLambdaN.map (background.nu.functor.map T.f) (q+1) =
        homotopyRegrade (show (t+q)-(s+q+1)=t-(s+1) by omega)
          (show (t+q)-q=t by omega)
          (finiteTopLabel T.Y q hq (s+q+1) (t+q) v) := by
  obtain ⟨ε,ey,hε,hey,a,ha,hi⟩ := finite_raw_lift_positive_g
    T he hT hf hg hh q hq s t z x v hx hd
  exact ordinary_finite_native_of_raw T he hf q hq s t x v ε hε ey hey a ha hi

end
end KIP126.ProofTools.Internal.SyntheticCoverage
