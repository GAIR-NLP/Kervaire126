module

import all KIP126.ProofTools.SyntheticCoverage.BoundaryPermanence
import all KIP126.ProofTools.SyntheticCoverage.MiddleElimination
import all KIP126.ProofTools.SyntheticCoverage.SourceFiniteDifferential
import all KIP126.ProofTools.SyntheticCoverage.EarlyPositiveNaturality
import all KIP126.ProofTools.SyntheticCoverage.EarlyRotatedLabel
import all KIP126.ProofTools.GeneralizedMahowald.FiniteMayAtTriangle

/-! Actual coefficient constructions for early-boundary differential criteria.
The finite representative and the torsion correction are constructed by the
selected coefficient triangles. -/

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
set_option maxHeartbeats 2000000

/-- A zero restriction constructs one coefficient preimage in the actual
selected tower, also for a normalized object with a nonzero weight shift. -/
private theorem early_source_coefficient_preimage
    (A : SyntheticSpectrum) (i N : ℕ) (hi : 0 < i) (hiN : i < N) (m w : ℤ)
    (a : BiHom m w (XModLambdaN A N))
    (ha : a ≫ (background.quotients.tower A).rho i N hiN.le=0) :
    ∃ c : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A (N-i))),
      c ≫ ((background.quotients.tower A).triangle hi hiN).lambdaMap = a := by
  let C := (background.quotients.tower A).triangle hi hiN
  have hz : a ≫ C.rho=0 := by
    simpa only [C,(background.quotients.tower A).triangle_rho] using ha
  obtain ⟨c,hc⟩ := (Triangle.mk C.lambdaMap C.rho C.delta).coyoneda_exact₂
    C.distinguished a hz
  exact ⟨c,hc.symm⟩

/-- The actual coefficient kernel is a projected absolute boundary. Its
preimage is produced by exactness; the full correction is killed by the
specified power of λ. This applies to early d₂ and to higher early d_a. -/
private theorem early_coefficient_kernel_torsion_boundary
    (Y : (AdamsObject (coefficients := background.coefficients))) (i N : ℕ) (hi : 0 < i) (hiN : i < N) (m w : ℤ)
    (e : BiHom m w (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (N-i)))⟦(1:ℤ)⟧))
    (he : e ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      ((background.quotients.tower (background.nu.functor.obj (Y.obj background.auxiliary))).triangle hi hiN).lambdaMap=0) :
    ∃ a : BiHom m w (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) i),
      lambdaMultiply i (biSuspensionHomEquiv m w i
        (background.nu.functor.obj (Y.obj background.auxiliary)) (a ≫ XModLambdaN.proj _ i))=0 ∧
      e = a ≫ XModLambdaN.proj _ i ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map
          (XModLambdaN.incl (background.nu.functor.obj (Y.obj background.auxiliary)) (N-i))) := by
  let A := background.nu.functor.obj (Y.obj background.auxiliary)
  let C := (background.quotients.tower A).triangle hi hiN
  let row := Triangle.mk C.lambdaMap C.rho C.delta
  have hz : e ≫ row.rotate.mor₃=0 := by
    change e ≫ (-(shiftFunctor SyntheticSpectrum (1:ℤ)).map C.lambdaMap)=0
    have he' : e ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map C.lambdaMap=0 := he
    rw [Preadditive.comp_neg,he',neg_zero]
  obtain ⟨a,ha⟩ := row.rotate.coyoneda_exact₃
    (rot_of_distTriang row C.distinguished) e hz
  change e=a ≫ C.delta at ha
  refine ⟨a,absolute_boundary_lambda_zero A m w i a,?_⟩
  exact ha.trans (selected_delta_evaluation_eq_cofiber Y i N C m w a)

/-- Dividing the source and the prescribed image through the same
coefficient inclusion places their actual image difference in its kernel. -/
private theorem early_divided_image_coefficient_kernel
    (A B : SyntheticSpectrum) (f : A ⟶ B)
    (i N : ℕ) (hi : 0 < i) (hiN : i < N) (m w : ℤ)
    (a : BiHom m w (XModLambdaN A N))
    (c : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A (N-i))))
    (v : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN B (N-i))))
    (hc : c ≫ ((background.quotients.tower A).triangle hi hiN).lambdaMap=a)
    (ha : a ≫ XModLambdaN.map f N =
      v ≫ ((background.quotients.tower B).triangle hi hiN).lambdaMap) :
    (c ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.map f (N-i))-v) ≫
      ((background.quotients.tower B).triangle hi hiN).lambdaMap=0 := by
  rw [Preadditive.sub_comp,Category.assoc,
    (background.quotients.natural f).lambda_naturality hi hiN,←Category.assoc,hc,ha,sub_self]

/-- The original whole H₂-image condition is transported through the fixed
classical suspension, at the same degree and the same B₂ denominator. -/
private theorem early_whole_h_image_suspended_boundary
    (T : TriangleData background.auxiliary) (S V : ℤ)
    (hH : ∀ z : Ambient background T.Z (S,V+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T S V z ∈
        boundaries background T.X 2 (S,V)) :
    ∀ z : Ambient background T.Z (S,V+1),
      (background.classical.map T.h).pageMap 2 (S,V+1) z ∈
        boundaries background (.shift 1 T.X) 2 (S,V+1) := by
  intro z
  have hz := KIP126.ProofTools.Standard.classicalTriangleHMapHom_spec T S V z
  apply (desuspendsClass_boundary_iff T.X 2 S (V+1) _ _ hz).mpr
  have hc := hH z
  have transport (v v' : ℤ) (hv : v=v') (x : Ambient background T.X (S,v))
      (e : (Ambient background T.X (S,v') : Type)=(Ambient background T.X (S,v) : Type))
      (hx : x ∈ boundaries background T.X 2 (S,v)) :
      e.mpr x ∈ boundaries background T.X 2 (S,v') := by
    subst v'
    cases e
    exact hx
  exact transport V (V+1-1) (by omega) _ _ hc

/-- Two Q₂ lifts of the same source label have equal H-images under
the early-boundary H condition. -/
private theorem early_same_first_label_same_h_image
    (T : TriangleData background.auxiliary) (S V : ℤ)
    (hH : ∀ z : Ambient background T.Z (S,V+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T S V z ∈
        boundaries background T.X 2 (S,V))
    (z : Ambient background T.Z (S-1,V))
    (a b : BiHom (V-(S-1)) V
      (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) 2))
    (ha : a ≫ (background.quotients.tower _).rho 1 2 (by decide)=nativeFirstLabel T.Z (S-1) V z)
    (hb : b ≫ (background.quotients.tower _).rho 1 2 (by decide)=nativeFirstLabel T.Z (S-1) V z) :
    a ≫ XModLambdaN.map (background.nu.functor.map T.h) 2 =
      b ≫ XModLambdaN.map (background.nu.functor.map T.h) 2 := by
  have had := first_label_detects_unshifted T.Z 2 (by decide) (S-1) V z a ha
  have hbd := first_label_detects_unshifted T.Z 2 (by decide) (S-1) V z b hb
  have hdiff := detects_sub_filtration
    (background.convergence (.quotient 2 (.nu T.Z))) (S-1,V,V) had hbd
  have hfil : FiltrationAtLeast background.syntheticTower S (a-b) := by
    simpa only [sub_add_cancel] using hdiff
  let e := homotopyRegrade (show V-(S-1)=(V+1)-S by omega) rfl (a-b)
  have hef : FiltrationAtLeast background.syntheticTower S e :=
    (regrade_filtration_iff _ _ _ _).mpr hfil
  have he := ordinary_map_top_filtration_zero T.Z (.shift 1 T.X) T.h
    2 (by decide) S (V+1) V (by norm_num)
    (early_whole_h_image_suspended_boundary T S V hH) e hef
  have hz : (a-b) ≫ XModLambdaN.map (background.nu.functor.map T.h) 2=0 := by
    apply (ordinary_regrade_zero_iff (show V-(S-1)=(V+1)-S by omega) (rfl : V=V) _).mp
    simpa only [e,regrade_comp] using he
  exact sub_eq_zero.mp (by simpa only [Preadditive.sub_comp] using hz)

/-- The same Q₂ comparison in the actual normalized triangle. Both the
source and the H-image use its fixed quotient maps. -/
private theorem early_normalized_same_first_label_same_h_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (S V : ℤ)
    (hH : ∀ z : Ambient background T.Z (S,V+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T S V z ∈
        boundaries background T.X 2 (S,V))
    (z : Ambient background T.Z (S-1,V))
    (a b : BiHom (V-(S-1)) V (XModLambdaN (normalizedTriangle background T he).obj₃ 2))
    (ha : a ≫ (background.quotients.tower _).rho 1 2 (by decide) =
      nativeFirstLabel T.Z (S-1) V z ≫ XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1)
    (hb : b ≫ (background.quotients.tower _).rho 1 2 (by decide) =
      nativeFirstLabel T.Z (S-1) V z ≫ XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1) :
    a ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ 2 =
      b ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ 2 := by
  let EZ := normalizedThirdZeroIso T he hg
  let EX := normalizedSuspensionNativeIso T he hf
  have first (r : BiHom (V-(S-1)) V (XModLambdaN (normalizedTriangle background T he).obj₃ 2))
      (hr : r ≫ (background.quotients.tower _).rho 1 2 (by decide) =
        nativeFirstLabel T.Z (S-1) V z ≫ XModLambdaN.map EZ.inv 1) :
      (r ≫ XModLambdaN.map EZ.hom 2) ≫ (background.quotients.tower _).rho 1 2 (by decide) =
        nativeFirstLabel T.Z (S-1) V z := by
    rw [Category.assoc,←(background.quotients.natural EZ.hom).rho_naturality (by decide),
      ←Category.assoc,hr,Category.assoc,←background.quotients.functoriality.map_comp,
      Iso.inv_hom_id,background.quotients.functoriality.map_id,Category.comp_id]
  have hnative := early_same_first_label_same_h_image T S V hH z
    (a ≫ XModLambdaN.map EZ.hom 2) (b ≫ XModLambdaN.map EZ.hom 2)
    (first a ha) (first b hb)
  apply (cancel_mono ((background.quotients.functoriality.functor 2).mapIso EX).hom).mp
  have hs := normalized_third_arrow_zero T he hf hg hh
  have hq := congrArg (fun f => XModLambdaN.map f 2) hs
  rw [background.quotients.functoriality.map_comp,background.quotients.functoriality.map_comp] at hq
  have hq' : XModLambdaN.map (normalizedTriangle background T he).mor₃ 2 ≫
      XModLambdaN.map EX.hom 2 = XModLambdaN.map EZ.hom 2 ≫
        XModLambdaN.map (background.nu.functor.map T.h) 2 := hq
  change (a ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ 2) ≫
      XModLambdaN.map EX.hom 2 = (b ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ 2) ≫
      XModLambdaN.map EX.hom 2
  simpa only [Category.assoc,hq'] using hnative

/-- The same kernel preimage gives an equality after the fixed bi-suspension
comparison. In particular the correction on the finite quotient is the
projection of the produced full torsion class. -/
private theorem early_coefficient_kernel_full_projection
    (Y : (AdamsObject (coefficients := background.coefficients))) (i N : ℕ) (hi : 0 < i) (hiN : i < N) (m w : ℤ)
    (e : BiHom m w (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (N-i)))⟦(1:ℤ)⟧))
    (he : e ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      ((background.quotients.tower (background.nu.functor.obj (Y.obj background.auxiliary))).triangle hi hiN).lambdaMap=0) :
    ∃ a : BiHom m w (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) i),
      lambdaMultiply i (biSuspensionHomEquiv m w i
        (background.nu.functor.obj (Y.obj background.auxiliary)) (a ≫ XModLambdaN.proj _ i))=0 ∧
      biSuspensionHomEquiv m w i
          (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (N-i)) e =
        biSuspensionHomEquiv m w i (background.nu.functor.obj (Y.obj background.auxiliary))
          (a ≫ XModLambdaN.proj _ i) ≫ XModLambdaN.incl _ (N-i) := by
  obtain ⟨a,ha,heq⟩ := early_coefficient_kernel_torsion_boundary Y i N hi hiN m w e he
  refine ⟨a,ha,?_⟩
  have hd := selected_delta_evaluation_eq_cofiber Y i N
    ((background.quotients.tower (background.nu.functor.obj (Y.obj background.auxiliary))).triangle hi hiN) m w a
  rw [←hd] at heq
  rw [heq]
  exact cofiber_boundary_projection Y i N hi hiN m w a

/-- Coefficient exactness constructs a divided source and torsion
correction for the specified representative and image. -/
private theorem early_divided_image_torsion_correction
    (A : SyntheticSpectrum) (Y : (AdamsObject (coefficients := background.coefficients)))
    (f : A ⟶ background.nu.functor.obj (Y.obj background.auxiliary))
    (i N : ℕ) (hi : 0 < i) (hiN : i < N) (m w : ℤ)
    (a : BiHom m w (XModLambdaN A N))
    (ha0 : a ≫ (background.quotients.tower A).rho i N hiN.le=0)
    (v : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (N-i))))
    (ha : a ≫ XModLambdaN.map f N =
      v ≫ ((background.quotients.tower (background.nu.functor.obj (Y.obj background.auxiliary))).triangle hi hiN).lambdaMap) :
    ∃ c : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A (N-i))),
    ∃ b : BiHom (m+1) w (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) i),
      c ≫ ((background.quotients.tower A).triangle hi hiN).lambdaMap=a ∧
      lambdaMultiply i (biSuspensionHomEquiv (m+1) w i
        (background.nu.functor.obj (Y.obj background.auxiliary)) (b ≫ XModLambdaN.proj _ i))=0 ∧
      biSuspensionHomEquiv (m+1) w i
        (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (N-i))
        (ordinarySuspendedRepresentative _ (m+1) w
          (homotopyRegrade (show m=m+1-1 by omega) rfl
            (c ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.map f (N-i))-v))) =
        biSuspensionHomEquiv (m+1) w i (background.nu.functor.obj (Y.obj background.auxiliary))
          (b ≫ XModLambdaN.proj _ i) ≫ XModLambdaN.incl _ (N-i) := by
  obtain ⟨c,hc⟩ := early_source_coefficient_preimage A i N hi hiN m w a ha0
  have hz := early_divided_image_coefficient_kernel A _ f i N hi hiN m w a c v hc ha
  let e := ordinarySuspendedRepresentative _ (m+1) w
    (homotopyRegrade (show m=m+1-1 by omega) rfl
      (c ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.map f (N-i))-v))
  have he : e ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      ((background.quotients.tower (background.nu.functor.obj (Y.obj background.auxiliary))).triangle hi hiN).lambdaMap=0 := by
    dsimp only [e]
    rw [←ordinarySuspendedRepresentative_natural,←regrade_comp,hz]
    simp only [ordinarySuspendedRepresentative,shiftHomotopyClass,Functor.map_zero,
      regrade_precomp,comp_zero,zero_comp]
  obtain ⟨b,hb,hbe⟩ := early_coefficient_kernel_full_projection Y i N hi hiN (m+1) w e he
  exact ⟨c,b,hc,hb,hbe⟩

/-- Detection determines the entire top layer for the specified coefficient
inclusion, including the zero label. -/
private theorem early_top_detects_unique
    (X : (AdamsObject (coefficients := background.coefficients))) (d : ℕ) (hd : 0<d) (s t : ℤ)
    (x : Ambient background X (s,t))
    (a : BiHom (t-s) (t-d)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)))
    (ha : Detects (background.convergence (.quotient (d+1) (.nu X))) (s,t,t-d)
      (finiteTargetLabel background X (d+1) s t d x) a) :
    a=finiteTopLabel X d hd s t x := by
  have h := detects_sub_filtration (background.convergence (.quotient (d+1) (.nu X)))
    (s,t,t-d) ha (finiteTopLabel_detects X d hd s t x)
  exact sub_eq_zero.mp (finite_high_filtration_zero X (d+1) (by omega)
    (t-s) (t-d) (s+1) (by omega) _ h)

/-- An actual top class stays the prescribed top class after insertion of
any number of coefficients. This supplies the nested top used when an early
boundary of order i+1 is divided from a longer finite May representative. -/
private theorem early_insert_top
    (X : (AdamsObject (coefficients := background.coefficients))) (i d : ℕ) (hd : 0<d) (s t : ℤ)
    (x : Ambient background X (s,t)) :
    homotopyRegrade rfl (show (t-d)-i=t-(i+d) by omega)
      (finiteCoefficientInsert _ i (d+1) (by omega) (t-s) (t-d)
        (finiteTopLabel X d hd s t x)) =
      finiteTopLabel X (i+d) (by omega) s t x := by
  apply early_top_detects_unique
  have ha : Detects (background.convergence (.quotient (i+(d+1)-i) (.nu X))) (s,t,t-d)
      (finiteTargetLabel background X (i+(d+1)-i) s t d x)
      (by simpa only [Nat.add_sub_cancel_left,SyntheticObject.obj] using finiteTopLabel X d hd s t x) := by
    have transport (n : ℕ) (hn : n=d+1)
        (ht : BiHom (t-s) (t-d) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)) =
          BiHom (t-s) (t-d) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) n)) :
        Detects (background.convergence (.quotient n (.nu X))) (s,t,t-d)
          (finiteTargetLabel background X n s t d x) (ht.mp (finiteTopLabel X d hd s t x)) := by
      subst n
      exact finiteTopLabel_detects X d hd s t x
    exact transport _ (by omega) _
  have h := finite_coefficient_shift_layer_detects X (i+(d+1)) i d (by omega) (by omega)
    s t x _ ha
  exact h

/-- The finite May representative attached to a root in the actual G₂
image has zero first restriction. The same long representative is retained. -/
private theorem early_root_may_zero_restriction
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (q N : ℕ) (hq : 0<q) (hqN : q≤N) (s t : ℤ)
    (c : Ambient background T.Y (s,t))
    (a : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ q))
    (b : BiHom (t-s) t (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N))
    (ha : a ≫ (background.quotients.tower _).rho 1 q hq =
      nativeFirstLabel T.Z s t ((background.classical.map T.g).pageMap 2 (s,t) c) ≫
        XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1)
    (hb : b ≫ (background.quotients.tower _).rho q N hqN =
      a ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ q) :
    b ≫ (background.quotients.tower _).rho 1 N (by omega)=0 := by
  let V := normalizedTriangle background T he
  let E := normalizedThirdZeroIso T he hg
  have hfirst : b ≫ (background.quotients.tower _).rho 1 N (by omega) =
      (nativeFirstLabel T.Z s t ((background.classical.map T.g).pageMap 2 (s,t) c) ≫
        XModLambdaN.map E.inv 1) ≫ XModLambdaN.map V.mor₃ 1 := by
    rw [←(background.quotients.tower _).rho_comp (show 1≤q by omega) hqN,
      ←Category.assoc,hb,Category.assoc,←(background.quotients.natural V.mor₃).rho_naturality hq,
      ←Category.assoc,ha]
  have hgmap : background.nu.functor.map T.g ≫ E.inv=V.mor₂ := by
    apply (cancel_mono E.hom).mp
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      (normalized_second_arrow_zero T he hg).symm
  obtain ⟨ey,_,hrow⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he 1 (by decide)
  have hz := comp_distTriang_mor_zero₁₂ _ hrow
  change XModLambdaN.map V.mor₂ 1 ≫ XModLambdaN.map V.mor₃ 1=0 at hz
  have hgq : XModLambdaN.map (background.nu.functor.map T.g) 1 ≫ XModLambdaN.map E.inv 1 =
      XModLambdaN.map V.mor₂ 1 := by
    rw [←background.quotients.functoriality.map_comp,hgmap]
  rw [hfirst,←native_first_label_natural T.Y T.Z T.g s t c,
    Category.assoc (nativeFirstLabel T.Y s t c) (XModLambdaN.map (background.nu.functor.map T.g) 1),
    hgq,Category.assoc,hz,comp_zero]

/-- The Q₂ restriction of the same long May representative is fixed by the
rotated early root. The whole H₂-image condition removes precisely the
ambiguity between these two specified root lifts. -/
private theorem early_root_may_two_layer_comparison
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q N : ℕ) (hq : 2≤q) (hqN : q≤N) (S V : ℤ)
    (hH : ∀ z : Ambient background T.Z (S,V+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T S V z ∈
        boundaries background T.X 2 (S,V))
    (z : Ambient background T.Z (S-1,V))
    (a : BiHom (V-(S-1)) V (XModLambdaN (normalizedTriangle background T he).obj₃ q))
    (R : BiHom (V-(S-1)) V (XModLambdaN (normalizedTriangle background T he).obj₃ 2))
    (b : BiHom (V-(S-1)) V
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N))
    (ha : a ≫ (background.quotients.tower _).rho 1 q (by omega) =
      nativeFirstLabel T.Z (S-1) V z ≫ XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1)
    (hR : R ≫ (background.quotients.tower _).rho 1 2 (by decide) =
      nativeFirstLabel T.Z (S-1) V z ≫ XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1)
    (hb : b ≫ (background.quotients.tower _).rho q N hqN =
      a ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ q) :
    b ≫ (background.quotients.tower _).rho 2 N (by omega) =
      R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ 2 := by
  have ha₂ : (a ≫ (background.quotients.tower _).rho 2 q hq) ≫
      (background.quotients.tower _).rho 1 2 (by decide) =
        nativeFirstLabel T.Z (S-1) V z ≫ XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1 := by
    rw [Category.assoc,(background.quotients.tower _).rho_comp]
    exact ha
  have heq := early_normalized_same_first_label_same_h_image T he hf hg hh S V hH z
    (a ≫ (background.quotients.tower _).rho 2 q hq) R ha₂ hR
  rw [←(background.quotients.tower _).rho_comp hq hqN,←Category.assoc,hb,Category.assoc,
    ←(background.quotients.natural (normalizedTriangle background T he).mor₃).rho_naturality hq,
    ←Category.assoc,heq]

/-- Restriction commutes with the actual positive-first native source
comparison on the same representative, for inclusion-compatible quotient
choices at the two finite lengths. -/
private theorem early_raw_source_desuspend_restriction
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (i N c : ℕ) (hi : 0 < i) (hiN : i ≤ N) (S V : ℤ)
    (εi : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) i ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) i))
    (εN : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hεi : XModLambdaN.incl _ i ≫ εi.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ i))
    (hεN : XModLambdaN.incl _ N ≫ εN.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ N))
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N)) :
    rawMaySourceDesuspend T he hf N c S V εN a ≫ (background.quotients.tower _).rho i N hiN =
      rawMaySourceDesuspend T he hf i c S V εi
        (a ≫ (background.quotients.tower _).rho i N hiN) := by
  dsimp only [rawMaySourceDesuspend]
  rw [quotient_unshift_restriction T.X (1,1) (V-S,V-c) i N hi hiN εi εN hεi hεN]
  congr 1
  simp only [regrade_comp,Category.assoc]
  rw [←(background.quotients.natural (background.nu.suspensionIso (T.X.obj background.auxiliary)).hom).rho_naturality hiN,
    ←Category.assoc (XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N)]
  erw [←(background.quotients.natural (normalizedSuspensionNativeIso T he hf).hom).rho_naturality hiN]
  simp only [Category.assoc]

/-- The coefficient-insertion kernel on native homotopy classes consists
of projections of absolute boundaries. The constructed full class is
annihilated by `λ^i`. -/
private theorem early_native_coefficient_kernel_torsion
    (Y : (AdamsObject (coefficients := background.coefficients))) (i N : ℕ) (hi : 0 < i) (hiN : i < N) (m w : ℤ)
    (e : BiHom (m-1) (w+i)
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (N-i)))
    (he : finiteCoefficientShiftClass _ N i hiN (m-1) (w+i) e=0) :
    ∃ a : BiHom m w (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) i),
      lambdaMultiply i (biSuspensionHomEquiv m w i
        (background.nu.functor.obj (Y.obj background.auxiliary)) (a ≫ XModLambdaN.proj _ i))=0 ∧
      e=biSuspensionHomEquiv m w i (background.nu.functor.obj (Y.obj background.auxiliary))
        (a ≫ XModLambdaN.proj _ i) ≫ XModLambdaN.incl _ (N-i) := by
  let A := background.nu.functor.obj (Y.obj background.auxiliary)
  let eS := (biSuspensionHomEquiv m w i (XModLambdaN A (N-i))).symm e
  have hz : eS ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      ((background.quotients.tower A).triangle hi hiN).lambdaMap=0 := by
    apply (cancel_mono ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)).mp
    rw [zero_comp]
    have h := finite_coefficient_shift_suspended_target A N i hi hiN m w e
    rw [he] at h
    simpa only [eS,shiftHomotopyClass,Functor.map_zero,regrade_precomp,comp_zero,Category.assoc] using h
  obtain ⟨a,ha,hp⟩ := early_coefficient_kernel_full_projection Y i N hi hiN m w eS hz
  exact ⟨a,ha,(by simpa only [eS,A,AddEquiv.apply_symm_apply] using hp)⟩

/-- The early top restriction constructs a divided finite source
whose first label has boundary indeterminacy `B_(d+1)`. -/
private theorem early_native_top_division
    (X : (AdamsObject (coefficients := background.coefficients))) (N d : ℕ) (hd : 0 < d) (hdN : d < N)
    (s t : ℤ) (u : Ambient background X (s,t))
    (a : BiHom (t-s) (t-d)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (ha : a ≫ (background.quotients.tower _).rho (d+1) N (by omega) =
      finiteTopLabel X d hd s t u) :
    ∃ b : BiHom (t-s) t
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-d)),
    ∃ u' : Ambient background X (s,t),
      finiteCoefficientShiftClass _ N d hdN (t-s) t b=a ∧
      b ≫ (background.quotients.tower _).rho 1 (N-d) (by omega)=nativeFirstLabel X s t u' ∧
      u'-u ∈ boundaries background X (d+1) (s,t) := by
  have hdet := (finite_rho_lift_label_and_cycles X (d+1) N d (by omega) (by omega)
    s t u _ (finiteTopLabel_detects X d hd s t u) a ha).1
  have haf := detects_filtration (.quotient N (.nu X)) (s,t,t-d) _ a hdet
  have hrf := map_preserves_filtration (background.convergentMap
    (.quotient N (.nu X)) (.quotient d (.nu X)) ((background.quotients.tower _).rho d N hdN.le))
    (t-s,t-d) s a haf
  have hz : a ≫ (background.quotients.tower _).rho d N hdN.le=0 :=
    finite_high_filtration_zero X d hd (t-s) (t-d) s (by omega) _ hrf
  obtain ⟨b,hb⟩ := native_coefficient_preimage_of_zero_restriction _ N d hd hdN (t-s) t a hz
  obtain ⟨u',hu'⟩ := quotient_first_label_exists X (N-d) (by omega) s t b
  have hcoeff : finiteLambdaClass X N d hd hdN s t b=a := by
    simpa only [finiteCoefficientShiftClass,show d≠0 by omega,↓reduceDIte,finiteLambdaClass] using hb
  have hdet' : Detects (background.convergence (.quotient N (.nu X))) (s,t,t-d)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) N).pageMap
        2 (s,t,t-d) (nuWeightLabel background X s t (t-d) (by omega) u)) a := by
    rw [finite_coefficient_weight_label]
    exact hdet
  have hcong := finite_lambda_first_label_congruent X N d hd hdN s t u u' b hu' a hdet' hcoeff
  refine ⟨b,u',hb,hu',?_⟩
  simpa only [neg_sub] using (boundaries background X (d+1) (s,t)).neg_mem hcong

private theorem early_coefficient_shift_sub
    (A : SyntheticSpectrum) (N i : ℕ) (hiN : i < N) (m w : ℤ)
    (a b : BiHom m w (XModLambdaN A (N-i))) :
    finiteCoefficientShiftClass A N i hiN m w (a-b)=
      finiteCoefficientShiftClass A N i hiN m w a-
        finiteCoefficientShiftClass A N i hiN m w b := by
  by_cases hi : i=0
  · subst i
    simp only [finiteCoefficientShiftClass,↓reduceDIte,homotopy_regrade_sub]
  · simp only [finiteCoefficientShiftClass,hi,↓reduceDIte,shiftHomotopyClass,
      Functor.map_sub,Preadditive.comp_sub,homotopy_regrade_sub,Preadditive.sub_comp]

/-- Native coordinates for the absolute boundary from the coefficient
kernel, together with its defining preimage for source correction. -/
private theorem early_native_coefficient_kernel_at_weight
    (Y : (AdamsObject (coefficients := background.coefficients))) (i N : ℕ) (hi : 0 < i) (hiN : i < N) (m t : ℤ)
    (e : BiHom m t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (N-i)))
    (he : finiteCoefficientShiftClass _ N i hiN m t e=0) :
    ∃ a : BiHom (m+1) (t-i)
        (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) i),
    ∃ W : BiHom m t (background.nu.functor.obj (Y.obj background.auxiliary)),
      W=homotopyRegrade (show (m+1)-1=m by omega) (show (t-i)+i=t by omega)
        (biSuspensionHomEquiv (m+1) (t-i) i
          (background.nu.functor.obj (Y.obj background.auxiliary)) (a ≫ XModLambdaN.proj _ i)) ∧
      lambdaMultiply i W=0 ∧ e=W ≫ XModLambdaN.incl _ (N-i) := by
  let e' := homotopyRegrade (show m=(m+1)-1 by omega) (show t=(t-i)+i by omega) e
  have he' : finiteCoefficientShiftClass _ N i hiN ((m+1)-1) ((t-i)+i) e'=0 := by
    dsimp only [e']
    rw [coefficient_shift_regrade,he]
    simp only [regrade_precomp,comp_zero]
  obtain ⟨a,ha,hea⟩ := early_native_coefficient_kernel_torsion Y i N hi hiN (m+1) (t-i) e' he'
  let W := homotopyRegrade (show (m+1)-1=m by omega) (show (t-i)+i=t by omega)
    (biSuspensionHomEquiv (m+1) (t-i) i
      (background.nu.functor.obj (Y.obj background.auxiliary)) (a ≫ XModLambdaN.proj _ i))
  refine ⟨a,W,rfl,?_,?_⟩
  · dsimp only [W]
    rw [lambda_regrade,ha]
    simp only [regrade_precomp,comp_zero]
  · have h := congrArg (homotopyRegrade (show (m+1)-1=m by omega)
        (show (t-i)+i=t by omega)) hea
    simpa only [e',W,last_layer_regrade_trans,regrade_comp,top_target_regrade_self] using h

/-- A specified long source and a specified coefficient image produce one
short source and one actual early absolute boundary. This is the common
construction used before either the target- or source-side early correction. -/
private theorem early_positive_native_division_and_torsion
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N i : ℕ) (hi : 0 < i) (hiN : i < N) (m w : ℤ)
    (a : BiHom m (w-i)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (ha0 : a ≫ (background.quotients.tower _).rho i N hiN.le=0)
    (v : BiHom m (w+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (N-i)))
    (ha : positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m (w-i) a =
      homotopyRegrade rfl (show (w+1)-i=(w-i)+1 by omega)
        (finiteCoefficientShiftClass _ N i hiN m (w+1) v)) :
    ∃ b : BiHom m w
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (N-i)),
    ∃ c : BiHom (m+1) ((w+1)-i)
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) i),
    ∃ W : BiHom m (w+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      finiteCoefficientShiftClass _ N i hiN m w b=a ∧
      W=homotopyRegrade (show (m+1)-1=m by omega) (show ((w+1)-i)+i=w+1 by omega)
        (biSuspensionHomEquiv (m+1) ((w+1)-i) i
          (background.nu.functor.obj (T.Y.obj background.auxiliary)) (c ≫ XModLambdaN.proj _ i)) ∧
      lambdaMultiply i W=0 ∧
      positiveFiniteImage T hf (N-i) (levelQuotientShiftIso T.X 1 (N-i)) m w b =
        W ≫ XModLambdaN.incl _ (N-i)+v := by
  obtain ⟨b,hb⟩ := native_coefficient_preimage_of_zero_restriction _ N i hi hiN m w a ha0
  have hn := positive_finite_image_coefficient_shift_level T hf N i hiN m w b
  rw [hb,ha] at hn
  have heq := homotopy_regrade_injective rfl
    (show (w+1)-i=(w-i)+1 by omega) hn
  let e := positiveFiniteImage T hf (N-i) (levelQuotientShiftIso T.X 1 (N-i)) m w b-v
  have he : finiteCoefficientShiftClass _ N i hiN m (w+1) e=0 := by
    dsimp only [e]
    rw [early_coefficient_shift_sub,←heq,sub_self]
  obtain ⟨c,W,hW,hW0,heW⟩ := early_native_coefficient_kernel_at_weight T.Y i N hi hiN m (w+1) e he
  exact ⟨b,c,W,hb,hW,hW0,sub_eq_iff_eq_add.mp heW⟩

/-- Any specified coefficient preimage has the required original source
label modulo the exact early-boundary subgroup. Thus imposing its image
relation never requires replacing the chosen divided source. -/
private theorem early_same_divided_source_label
    (X : (AdamsObject (coefficients := background.coefficients))) (N d : ℕ) (hd : 0 < d) (hdN : d < N)
    (s t : ℤ) (u : Ambient background X (s,t))
    (a : BiHom (t-s) (t-d)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (ha : a ≫ (background.quotients.tower _).rho (d+1) N (by omega) =
      finiteTopLabel X d hd s t u)
    (b : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-d)))
    (hb : finiteCoefficientShiftClass _ N d hdN (t-s) t b=a) :
    ∃ u' : Ambient background X (s,t),
      b ≫ (background.quotients.tower _).rho 1 (N-d) (by omega)=nativeFirstLabel X s t u' ∧
      u'-u ∈ boundaries background X (d+1) (s,t) := by
  have hdet := (finite_rho_lift_label_and_cycles X (d+1) N d (by omega) (by omega)
    s t u _ (finiteTopLabel_detects X d hd s t u) a ha).1
  obtain ⟨u',hu'⟩ := quotient_first_label_exists X (N-d) (by omega) s t b
  have hcoeff : finiteLambdaClass X N d hd hdN s t b=a := by
    simpa only [finiteCoefficientShiftClass,show d≠0 by omega,↓reduceDIte,finiteLambdaClass] using hb
  have hdet' : Detects (background.convergence (.quotient N (.nu X))) (s,t,t-d)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) N).pageMap
        2 (s,t,t-d) (nuWeightLabel background X s t (t-d) (by omega) u)) a := by
    rw [finite_coefficient_weight_label]
    exact hdet
  have hcong := finite_lambda_first_label_congruent X N d hd hdN s t u u' b hu' a hdet' hcoeff
  exact ⟨u',hu',by simpa only [neg_sub] using (boundaries background X (d+1) (s,t)).neg_mem hcong⟩

/-- The actual source label and the actual torsion correction are produced
for one and the same divided representative. This is the coefficient step
for early d₂ and for every higher early boundary. -/
private theorem early_positive_top_division_and_torsion
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N i : ℕ) (hi : 0 < i) (hiN : i < N) (S V : ℤ)
    (u : Ambient background T.X (S,V))
    (a : BiHom (V-S) (V-i)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hsource : a ≫ (background.quotients.tower _).rho (i+1) N (by omega) =
      finiteTopLabel T.X i hi S V u)
    (v : BiHom (V-S) (V+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (N-i)))
    (himage : positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (V-S) (V-i) a =
      homotopyRegrade rfl (show (V+1)-i=(V-i)+1 by omega)
        (finiteCoefficientShiftClass _ N i hiN (V-S) (V+1) v)) :
    ∃ b : BiHom (V-S) V
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (N-i)),
    ∃ u' : Ambient background T.X (S,V),
    ∃ c : BiHom ((V-S)+1) ((V+1)-i)
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) i),
    ∃ W : BiHom (V-S) (V+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      finiteCoefficientShiftClass _ N i hiN (V-S) V b=a ∧
      b ≫ (background.quotients.tower _).rho 1 (N-i) (by omega)=nativeFirstLabel T.X S V u' ∧
      u'-u ∈ boundaries background T.X (i+1) (S,V) ∧
      W=homotopyRegrade (show ((V-S)+1)-1=V-S by omega) (show ((V+1)-i)+i=V+1 by omega)
        (biSuspensionHomEquiv ((V-S)+1) ((V+1)-i) i
          (background.nu.functor.obj (T.Y.obj background.auxiliary)) (c ≫ XModLambdaN.proj _ i)) ∧
      lambdaMultiply i W=0 ∧
      positiveFiniteImage T hf (N-i) (levelQuotientShiftIso T.X 1 (N-i)) (V-S) V b =
        W ≫ XModLambdaN.incl _ (N-i)+v := by
  have hdet := (finite_rho_lift_label_and_cycles T.X (i+1) N i (by omega) (by omega)
    S V u _ (finiteTopLabel_detects T.X i hi S V u) a hsource).1
  have haf := detects_filtration (.quotient N (.nu T.X)) (S,V,V-i) _ a hdet
  have hrf := map_preserves_filtration (background.convergentMap
    (.quotient N (.nu T.X)) (.quotient i (.nu T.X)) ((background.quotients.tower _).rho i N hiN.le))
    (V-S,V-i) S a haf
  have hz : a ≫ (background.quotients.tower _).rho i N hiN.le=0 :=
    finite_high_filtration_zero T.X i hi (V-S) (V-i) S (by omega) _ hrf
  obtain ⟨b,c,W,hb,hW,hW0,himage'⟩ := early_positive_native_division_and_torsion
    T hf N i hi hiN (V-S) V a hz v himage
  obtain ⟨u',hu',hu'cong⟩ := early_same_divided_source_label T.X N i hi hiN S V u a hsource b hb
  exact ⟨b,u',c,W,hb,hu',hu'cong,hW,hW0,himage'⟩

/-- Exact top output under the raw/native positive image comparison. The
sphere-coordinate ambiguity is removed only on this actual top label. -/
private theorem early_raw_positive_image_top
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (q c : ℕ) (hq : 0<q) (S V s t : ℤ)
    (hm : t-s=V-S) (hw : t-q=(V-c)+1)
    (v : Ambient background T.Y (s,t))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (q+1) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)))
    (hε : XModLambdaN.incl _ (q+1) ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (q+1)))
    (ey : XModLambdaN ((background.nu.functor.obj (T.Y.obj background.auxiliary))⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (q+1))⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)))
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (q+1)))
    (ha : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (q+1) ≫ ey.hom =
      ordinarySuspendedRepresentative _ (V-S+1) (V-c+1)
        (homotopyRegrade (show t-s=(V-S+1)-1 by omega) hw
          (finiteTopLabel T.Y q hq s t v))) :
    positiveFiniteImage T hf (q+1) (levelQuotientShiftIso T.X 1 (q+1)) (V-S) (V-c)
        (rawMaySourceDesuspend T he hf (q+1) c S V ε a) =
      homotopyRegrade hm hw (finiteTopLabel T.Y q hq s t v) := by
  obtain ⟨u,hu⟩ := native_positive_image_up_to_sphere T he hf (q+1) c (by omega) S V ε
    (levelQuotientShiftIso T.X 1 (q+1)) hε (level_quotient_shift_incl T.X 1 (q+1)) ey hey a
  let top := homotopyRegrade (show t-s=(V-S+1)-1 by omega) hw (finiteTopLabel T.Y q hq s t v)
  have hfixed := ordinary_suspension_sphere_fixed _ (V-S+1) (V-c+1) top
    (sphere_fixed_regrade _ _ _ (finite_top_label_sphere_automorphism T.Y q hq s t v)) u.symm
  have hh := congrArg (fun b => u.inv ≫ b) (hu.symm.trans ha)
  simp only [←Category.assoc,u.inv_hom_id,Category.id_comp] at hh
  have hn := ordinary_suspended_representative_injective _ (V-S+1) (V-c+1) (hh.trans hfixed)
  have hh' := congrArg (homotopyRegrade (show (V-S+1)-1=V-S by omega) (rfl : V-c+1=V-c+1)) hn
  simpa only [top,last_layer_regrade_trans,top_target_regrade_self] using hh'

/-- The specified bottom differential and the actual early two-layer root
produce one long native source with both the prescribed early top and the
prescribed final top image. The root and its target are not replaced. -/
private theorem early_bottom_with_fixed_two_layer_root
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q : ℕ) (hq : 2≤q) (s t : ℤ)
    (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q)
      ((background.classical.map T.g).pageMap 2 (s,t) c)
      ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
    (hH : ∀ z : Ambient background T.Z (s+1,t+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+1) t z ∈
        boundaries background T.X 2 (s+1,t))
    (ε₂ : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) 2 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2))
    (hε₂ : XModLambdaN.incl _ 2 ≫ ε₂.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 2))
    (R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ 2))
    (hR : R ≫ (background.quotients.tower _).rho 1 2 (by decide) =
      nativeFirstLabel T.Z s t ((background.classical.map T.g).pageMap 2 (s,t) c) ≫
        XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1)
    (hRtop : rawMaySourceDesuspend T he hf 2 1 (s+1) t ε₂
        (homotopyRegrade (show t-s=t-(s+1)+1 by omega) (show t=t-1+1 by omega)
          (R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ 2)) =
      finiteTopLabel T.X 1 (by decide) (s+1) t u) :
    ∃ a : BiHom (t-(s+1)) (t-1)
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)),
      a ≫ (background.quotients.tower _).rho 2 (q+1) (by omega)=
        finiteTopLabel T.X 1 (by decide) (s+1) t u ∧
      positiveFiniteImage T hf (q+1) (levelQuotientShiftIso T.X 1 (q+1)) (t-(s+1)) (t-1) a =
        homotopyRegrade (show (t+q)-(s+q+1)=t-(s+1) by omega)
          (show (t+q)-q=(t-1)+1 by omega) (finiteTopLabel T.Y q (by omega) (s+q+1) (t+q) v) := by
  obtain ⟨ey,hey,_⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he (q+1) (by omega)
  obtain ⟨a,b,ha,_,hb,hbi⟩ := classical_second_differential_may T he hT hg q (by omega)
    s t ((background.classical.map T.g).pageMap 2 (s,t) c) v hd ey hey
  have comparison (S s₀ : ℤ) (hs : S-1=s₀)
      (hH : ∀ z : Ambient background T.Z (S,t+1),
        KIP126.ProofTools.Standard.classicalTriangleHMapHom T S t z ∈ boundaries background T.X 2 (S,t))
      (z : Ambient background T.Z (s₀,t))
      (a : BiHom (t-s₀) t (XModLambdaN (normalizedTriangle background T he).obj₃ q))
      (R : BiHom (t-s₀) t (XModLambdaN (normalizedTriangle background T he).obj₃ 2))
      (b : BiHom (t-s₀) t (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (q+1)))
      (ha : a ≫ (background.quotients.tower _).rho 1 q (by omega) =
        nativeFirstLabel T.Z s₀ t z ≫ XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1)
      (hR : R ≫ (background.quotients.tower _).rho 1 2 (by omega) =
        nativeFirstLabel T.Z s₀ t z ≫ XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1)
      (hb : b ≫ (background.quotients.tower _).rho q (q+1) (by omega) =
        a ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ q) :
      b ≫ (background.quotients.tower _).rho 2 (q+1) (by omega) =
        R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ 2 := by
    subst s₀
    exact early_root_may_two_layer_comparison T he hf hg hh q (q+1) hq (by omega)
      S t hH z a R b ha hR hb
  have hb₂ := comparison (s+1) s (by omega) hH
    ((background.classical.map T.g).pageMap 2 (s,t) c) a R b ha hR hb
  letI := background.exactness.shiftCommShift (1,1)
  letI := background.exactness.shiftExact (1,1)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,1) (q+1)
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  let b' := homotopyRegrade (show t-s=t-(s+1)+1 by omega) (show t=t-1+1 by omega) b
  let an := rawMaySourceDesuspend T he hf (q+1) 1 (s+1) t ε b'
  refine ⟨an,?_,?_⟩
  · dsimp only [an]
    rw [early_raw_source_desuspend_restriction T he hf 2 (q+1) 1 (by decide)
      (by omega) (s+1) t ε₂ ε hε₂ hε]
    simpa only [b',←regrade_comp,hb₂] using hRtop
  · apply early_raw_positive_image_top T he hf q 1 (by omega) (s+1) t
      (s+q+1) (t+q) (by omega) (by omega) v ε hε ey hey b'
    dsimp only [b']
    rw [←regrade_comp]
    erw [hbi,ordinary_may_signed_top_target]
    simp only [ordinary_suspended_representative_regrade,last_layer_regrade_trans]
    rfl

/-- One coefficient insertion of the specified penultimate top is the
specified final top. Both quotient length and weight are explicit. -/
private theorem early_coefficient_top_successor
    (X : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (hq : 2≤q) (s t w : ℤ)
    (hw : t-q=w-1) (x : Ambient background X (s,t)) :
    finiteCoefficientShiftClass _ (q+1) 1 (by omega) (t-s) w
      (finiteTopLabelAtWeight X (q-1) (by omega) ((q+1)-1) (by omega)
        s t w (by omega) x) =
      finiteTopLabelAtWeight X q (by omega) (q+1) rfl s t (w-1) hw x := by
  have hs := finite_top_label_at_weight_detects X (q-1) (by omega) ((q+1)-1) (by omega)
    s t w (by omega) x
  have hi := finite_coefficient_shift_detects X (q+1) 1 (by omega) s t w
    (by omega) x _ hs
  have ht := finite_top_label_at_weight_detects X q (by omega) (q+1) rfl s t (w-1) hw x
  exact finite_top_detection_unique X (q+1) (by omega) s t (w-1) (by omega) _ _ _ hi ht

/-- Both the divided source and the torsion correction are constructed from the same early root and the prescribed bottom differential. -/
private theorem early_compatible_positive_finite_lift_of_two_layer_root
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q : ℕ) (hq : 2≤q) (s t : ℤ)
    (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q)
      ((background.classical.map T.g).pageMap 2 (s,t) c)
      ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
    (hH : ∀ z : Ambient background T.Z (s+1,t+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+1) t z ∈
        boundaries background T.X 2 (s+1,t))
    (ε₂ : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) 2 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) 2))
    (hε₂ : XModLambdaN.incl _ 2 ≫ ε₂.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 2))
    (R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ 2))
    (hR : R ≫ (background.quotients.tower _).rho 1 2 (by decide) =
      nativeFirstLabel T.Z s t ((background.classical.map T.g).pageMap 2 (s,t) c) ≫
        XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1)
    (hRtop : rawMaySourceDesuspend T he hf 2 1 (s+1) t ε₂
        (homotopyRegrade (show t-s=t-(s+1)+1 by omega) (show t=t-1+1 by omega)
          (R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ 2)) =
      finiteTopLabel T.X 1 (by decide) (s+1) t u) :
    ∃ b : BiHom (t-(s+1)) t
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) ((q+1)-1)),
    ∃ u' : Ambient background T.X (s+1,t),
    ∃ aHat : BiHom ((t-(s+1))+1) ((t+1)-1)
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1),
    ∃ W : BiHom (t-(s+1)) (t+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      b ≫ (background.quotients.tower _).rho 1 ((q+1)-1) (by omega)=nativeFirstLabel T.X (s+1) t u' ∧
      u'-u ∈ boundaries background T.X 2 (s+1,t) ∧
      W=homotopyRegrade (show ((t-(s+1))+1)-1=t-(s+1) by omega)
        (show ((t+1)-1)+1=t+1 by omega)
        (biSuspensionHomEquiv ((t-(s+1))+1) ((t+1)-1) 1
          (background.nu.functor.obj (T.Y.obj background.auxiliary)) (aHat ≫ XModLambdaN.proj _ 1)) ∧
      lambdaMultiply 1 W=0 ∧
      positiveFiniteImage T hf ((q+1)-1) (levelQuotientShiftIso T.X 1 ((q+1)-1)) (t-(s+1)) t b =
        W ≫ XModLambdaN.incl _ ((q+1)-1)+
          homotopyRegrade (show (t+q)-(s+q+1)=t-(s+1) by omega) rfl
            (finiteTopLabelAtWeight T.Y (q-1) (by omega) ((q+1)-1) (by omega)
              (s+q+1) (t+q) (t+1) (by omega) v) := by
  obtain ⟨a,has,hai⟩ := early_bottom_with_fixed_two_layer_root
    T he hT hf hg hh q hq s t c u v hd hH ε₂ hε₂ R hR hRtop
  let vShort := homotopyRegrade (show (t+q)-(s+q+1)=t-(s+1) by omega) rfl
    (finiteTopLabelAtWeight T.Y (q-1) (by omega) ((q+1)-1) (by omega)
      (s+q+1) (t+q) (t+1) (by omega) v)
  have hv₀ := early_coefficient_top_successor T.Y q hq (s+q+1) (t+q) (t+1) (by omega) v
  have hv₁ := congrArg (homotopyRegrade (show (t+q)-(s+q+1)=t-(s+1) by omega)
    (show (t+1)-1=(t-1)+1 by omega)) hv₀
  have hv : homotopyRegrade rfl (show (t+1)-1=(t-1)+1 by omega)
      (finiteCoefficientShiftClass _ (q+1) 1 (by omega) (t-(s+1)) (t+1) vShort) =
      homotopyRegrade (show (t+q)-(s+q+1)=t-(s+1) by omega)
        (show (t+q)-q=(t-1)+1 by omega) (finiteTopLabel T.Y q (by omega) (s+q+1) (t+q) v) := by
    simpa only [vShort,coefficient_shift_regrade,finiteTopLabelAtWeight,last_layer_regrade_trans] using hv₁
  obtain ⟨b,u',aHat,W,_,hb,hu,hW,hW0,hbi⟩ := early_positive_top_division_and_torsion
    T hf (q+1) 1 (by omega) (by omega) (s+1) t u a has vShort (hai.trans hv.symm)
  exact ⟨b,u',aHat,W,hb,hu,hW,hW0,hbi⟩

/-- From the literal early d₂ boundary, the prescribed d_(q+1) root differential, and the whole H₂-image boundary condition, construct one compatible finite source and one actual λ-torsion absolute boundary. This is the common finite construction used by the early target and early source criteria. -/
private theorem early_positive_compatible_finite_lift
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (q : ℕ) (hq : 2≤q) (s t : ℤ)
    (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q)
      ((background.classical.map T.g).pageMap 2 (s,t) c)
      ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
    (hH : ∀ z : Ambient background T.Z (s+1,t+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+1) t z ∈
        boundaries background T.X 2 (s+1,t))
    (hd₂ : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      2 (s,t) (s+1+1,t+1) c
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+1) t u)) :
    ∃ b : BiHom (t-(s+1)) t
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) ((q+1)-1)),
    ∃ u' : Ambient background T.X (s+1,t),
    ∃ aHat : BiHom ((t-(s+1))+1) ((t+1)-1)
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1),
    ∃ W : BiHom (t-(s+1)) (t+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      b ≫ (background.quotients.tower _).rho 1 ((q+1)-1) (by omega)=nativeFirstLabel T.X (s+1) t u' ∧
      u'-u ∈ boundaries background T.X 2 (s+1,t) ∧
      W=homotopyRegrade (show ((t-(s+1))+1)-1=t-(s+1) by omega)
        (show ((t+1)-1)+1=t+1 by omega)
        (biSuspensionHomEquiv ((t-(s+1))+1) ((t+1)-1) 1
          (background.nu.functor.obj (T.Y.obj background.auxiliary)) (aHat ≫ XModLambdaN.proj _ 1)) ∧
      lambdaMultiply 1 W=0 ∧
      positiveFiniteImage T hf ((q+1)-1) (levelQuotientShiftIso T.X 1 ((q+1)-1)) (t-(s+1)) t b =
        W ≫ XModLambdaN.incl _ ((q+1)-1)+
          homotopyRegrade (show (t+q)-(s+q+1)=t-(s+1) by omega) rfl
            (finiteTopLabelAtWeight T.Y (q-1) (by omega) ((q+1)-1) (by omega)
              (s+q+1) (t+q) (t+1) (by omega) v) := by
  letI := background.exactness.shiftCommShift (1,1)
  letI := background.exactness.shiftExact (1,1)
  obtain ⟨ε₂,hε₂,_⟩ := quotient_shift_exists background.quotients.coherence (1,1) 2
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  obtain ⟨R,hR,hRtop⟩ := early_positive_rotated_first_and_top T he hT hf hg ε₂ hε₂ s t c u hd₂
  exact early_compatible_positive_finite_lift_of_two_layer_root
    T he hT hf hg hh q hq s t c u v hd hH ε₂ hε₂ R hR hRtop

end
end KIP126.ProofTools.Internal.SyntheticCoverage
