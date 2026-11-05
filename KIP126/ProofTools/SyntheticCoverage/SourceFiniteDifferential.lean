module

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.GeneralizedLeibniz.WeightedReverse
import all KIP126.ProofTools.MahowaldLeibniz.Bockstein
import all KIP126.ProofTools.MahowaldLeibniz.LastLayer
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelLabels
import all KIP126.ProofTools.SyntheticCoverage.Differentials
import all KIP126.ProofTools.SyntheticCoverage.PositiveBoundaryComparison

/-! Finite-source division for differential criteria. The coefficient
triangle divides a representative with zero restriction, preserving
its absolute boundary through the shift comparison. Canonical
desuspension identifies the first-quotient boundary labels.
True source-boundary errors may occur at any cutoff. The final theorem
gives the positive-first-arrow case `K₂=1` from its E₂ hypotheses. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.Core.SpectralSequence.FinitePageCalculus
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000

/-- An actual zero restriction supplies a coefficient preimage, preserving
the specified absolute boundary with its actual shift comparison. -/
private theorem finite_source_division_of_zero_restriction
    (X : (AdamsObject (coefficients := background.coefficients))) (d N : ℕ) (hd : 0 < d) (hdN : d < N)
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (ha : a ≫ (background.quotients.tower _).rho d N hdN.le = 0) :
    ∃ b : BiHom m w ((SyntheticCategory.biShift (0,-(d:ℤ))).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-d))),
      b ≫ ((background.quotients.tower _).triangle hd hdN).lambdaMap = a ∧
      b ≫ (SyntheticCategory.biShift (0,-(d:ℤ))).map
          (absoluteBoundary (background.nu.functor.obj (X.obj background.auxiliary)) (N-d)) ≫
        (boundaryDivisionIso X d N hdN.le).hom =
          a ≫ absoluteBoundary (background.nu.functor.obj (X.obj background.auxiliary)) N := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let C := (background.quotients.tower A).triangle hd hdN
  have hz : a ≫ C.rho = 0 := by
    simpa only [C,(background.quotients.tower A).triangle_rho] using ha
  obtain ⟨b,hb⟩ := (Triangle.mk C.lambdaMap C.rho C.delta).coyoneda_exact₂
    C.distinguished a hz
  change a = b ≫ C.lambdaMap at hb
  refine ⟨b,hb.symm,?_⟩
  rw [←absolute_boundary_division_evaluation X d N hd hdN m w b]
  change b ≫ C.lambdaMap ≫ absoluteBoundary A N = a ≫ absoluteBoundary A N
  rw [←Category.assoc,←hb]

/-- Source division in native bidegrees, preserving
the first label of the boundary. -/
private theorem native_finite_source_division_of_zero_restriction
    (X : (AdamsObject (coefficients := background.coefficients))) (d N : ℕ) (hd : 0 < d) (hdN : d < N)
    (m t : ℤ)
    (a : BiHom m (t-d)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (ha : a ≫ (background.quotients.tower _).rho d N hdN.le = 0) :
    ∃ b : BiHom m t
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-d)),
      verticalShiftEquiv _ d m (t-d) (homotopyRegrade rfl (by omega) b) ≫
          ((background.quotients.tower _).triangle hd hdN).lambdaMap = a ∧
      homotopyRegrade rfl (by omega)
          (biSuspensionHomEquiv m (t-d) N
            (background.nu.functor.obj (X.obj background.auxiliary)) (a ≫ XModLambdaN.proj _ N)) ≫
        XModLambdaN.incl _ 1 =
      biSuspensionHomEquiv m t (N-d:ℕ)
          (background.nu.functor.obj (X.obj background.auxiliary)) (b ≫ XModLambdaN.proj _ (N-d)) ≫
        XModLambdaN.incl _ 1 := by
  obtain ⟨bS,hbS,_⟩ := finite_source_division_of_zero_restriction X d N hd hdN m (t-d) a ha
  let e := verticalShiftEquiv
    (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N-d)) d m (t-d)
  let b := homotopyRegrade rfl (by omega : t-d+d=t) (e.symm bS)
  have hback : homotopyRegrade rfl (by omega : t=t-d+d) b = e.symm bS := by
    have cancel (A : SyntheticSpectrum) (m w w' : ℤ) (h : w=w') (h' : w'=w)
        (c : BiHom m w A) : homotopyRegrade rfl h' (homotopyRegrade rfl h c)=c := by
      subst w'; rfl
    exact cancel _ _ _ _ _ _ (e.symm bS)
  have hb : verticalShiftEquiv _ d m (t-d) (homotopyRegrade rfl (by omega) b) ≫
      ((background.quotients.tower _).triangle hd hdN).lambdaMap = a := by
    rw [hback]
    exact (congrArg (fun z => z ≫ ((background.quotients.tower _).triangle hd hdN).lambdaMap)
      (e.apply_symm_apply bS)).trans hbS
  refine ⟨b,hb,?_⟩
  have h := divided_boundary_first_quotient X d N hd hdN m t b
  dsimp only at h
  rwa [hb] at h

/-- A source correction surviving one page beyond the desired differential
has zero differential, so subtracting it preserves the specified target. -/
private theorem differential_of_source_later_cycle
    (X : (AdamsObject (coefficients := background.coefficients))) (r : ℤ) (p q : ℤ × ℤ)
    (x x₀ : Ambient background X p) (v : Ambient background X q)
    (hd : DifferentialAt background X r p q x₀ v)
    (hx : x-x₀ ∈ cycles background X r p) :
    DifferentialAt background X r p q x v := by
  let E := background.classical.obj (X.obj background.auxiliary)
  obtain ⟨hr,hdeg,xr,vr,hxr,hvr,hdr⟩ := hd
  have hnext : ReachesPage E (r+1) p (x-x₀) :=
    (isCycle_iff_reaches background X (r+1) (by omega) p (x-x₀)).mp
      ⟨by omega,by simpa only [add_sub_cancel_right] using hx⟩
  obtain ⟨zr,hzr⟩ := reaches_earlier hr (by omega : r≤r+1) hnext
  have hdz : E.d r p zr = 0 := represents_d_zero_of_later
    (by change (background.classical.obj (X.obj background.auxiliary)).r₀ ≤ r
        rw [background.classical.firstPage]; exact hr)
    (by omega : r<r+1) hzr hnext
  refine ⟨hr,hdeg,xr+zr,vr,?_,hvr,?_⟩
  · have hh := middle_add hxr hzr
    have he : x₀+(x-x₀)=x := by abel
    simpa only [he] using hh
  · rw [map_add,hdr]
    change vr + (eqToHom (congrArg (E.Page r) hdeg)) (E.d r p zr) = vr
    rw [hdz,map_zero,add_zero]

/-- Terminal source-error removal for the finite-source differential criterion.
The true source boundary cutoff is unrestricted, including cutoffs larger than `D-1`. -/
private theorem differential_of_source_correction
    (X : (AdamsObject (coefficients := background.coefficients))) (D b : ℤ) (p q : ℤ × ℤ)
    (w y e : Ambient background X p) (wᵥ v : Ambient background X q)
    (hd : DifferentialAt background X D p q w wᵥ)
    (hsource : w-y-e ∈ boundaries background X b p)
    (himage : e ∈ cycles background X D p)
    (htarget : wᵥ-v ∈ boundaries background X (D-1) q) :
    IsCycle background X (D-1) p y ∧ IsCycle background X (D-1) q v ∧
      DifferentialAt background X D p q y v := by
  have hwy : w-y ∈ cycles background X D p := by
    have h := (cycles background X D p).add_mem
      (boundaries_le_cycles background X p b D hsource) himage
    simpa only [sub_add_cancel] using h
  have hdy := differential_of_source_later_cycle X D p q y w wᵥ hd
    (by simpa only [neg_sub] using (cycles background X D p).neg_mem hwy)
  have hdv := differentialAt_of_congruent background X hdy
    ⟨by have := hd.1; omega,
      by simpa only [neg_sub] using (boundaries background X (D-1) q).neg_mem htarget⟩
  obtain ⟨hD,hdeg,yr,vr,hyr,hvr,hyv⟩ := hdv
  exact ⟨(isCycle_iff_reaches background X D hD p y).mpr ⟨yr,hyr⟩,
    (isCycle_iff_reaches background X D hD q v).mpr ⟨vr,hvr⟩,
    hD,hdeg,yr,vr,hyr,hvr,hyv⟩

/-- The finite-source differential is obtained from the actual top
restriction and the actual absolute boundary. The smaller-quotient source
is constructed internally by exactness; its first label can differ from
the specified source only by a true boundary. -/
private theorem finite_source_differential_of_top_restriction
    (X : (AdamsObject (coefficients := background.coefficients))) (d N : ℕ) (hd : 0 < d) (hdN : d < N)
    (s t : ℤ) (x : Ambient background X (s,t))
    (v : Ambient background X (s+(N-d:ℕ)+1,t+(N-d:ℕ)))
    (a : BiHom (t-s) (t-d)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (hsource : a ≫ (background.quotients.tower _).rho (d+1) N (by omega) =
      finiteTopLabel X d hd s t x)
    (hboundary :
      homotopyRegrade (by omega) (by omega)
          (biSuspensionHomEquiv (t-s) (t-d) N
            (background.nu.functor.obj (X.obj background.auxiliary)) (a ≫ XModLambdaN.proj _ N)) ≫
        XModLambdaN.incl _ 1 = nativeFirstLabel X (s+(N-d:ℕ)+1) (t+(N-d:ℕ)) v) :
    DifferentialAt background X ((N-d:ℕ)+1) (s,t) (s+(N-d:ℕ)+1,t+(N-d:ℕ)) x v := by
  have htop := finiteTopLabel_detects X d hd s t x
  have hfull := (finite_rho_lift_label_and_cycles X (d+1) N d
    (by omega) (by omega) s t x _ htop a hsource).1
  have hlabel : nuWeightLabel background X s t (t-d) (by omega) x =
      targetNuLabel background X s t d x := by
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
  have hfil := detects_filtration (.quotient N (.nu X)) (s,t,t-d) _ _ hdet
  have hrhofil := map_preserves_filtration (background.convergentMap
    (.quotient N (.nu X)) (.quotient d (.nu X))
    ((background.quotients.tower _).rho d N hdN.le)) (t-s,t-d) s a hfil
  have hzero : a ≫ (background.quotients.tower _).rho d N hdN.le = 0 :=
    finite_high_filtration_zero X d hd (t-s) (t-d) s (by omega) _ hrhofil
  obtain ⟨b,hb,hboundary'⟩ := native_finite_source_division_of_zero_restriction
    X d N hd hdN (t-s) t a hzero
  obtain ⟨x₀,hx₀⟩ := quotient_first_label_exists X (N-d) (by omega) s t b
  have hcong := finite_lambda_division_first_label_congruent
    X N d hd hdN s t x x₀ b hx₀ a hdet hb
  have hsmall : adjacentBoundaryLabel X (N-d) s t b =
      nativeFirstLabel X (s+(N-d:ℕ)+1) (t+(N-d:ℕ)) v := by
    have hh := congrArg (homotopyRegrade
      (show (t-s)-1=(t+(N-d:ℕ))-(s+(N-d:ℕ)+1) by omega) rfl) hboundary'
    have heq : homotopyRegrade (by omega) (by omega)
        (biSuspensionHomEquiv (t-s) (t-d) N
          (background.nu.functor.obj (X.obj background.auxiliary)) (a ≫ XModLambdaN.proj _ N)) ≫
        XModLambdaN.incl _ 1 = adjacentBoundaryLabel X (N-d) s t b := by
      simpa only [adjacentBoundaryLabel,boundaryRepresentative,regrade_precomp,
        ←Category.assoc,eqToHom_trans] using hh
    exact heq.symm.trans hboundary
  have hdiff := (differential_iff_specified_adjacent_lift X (N-d) (by omega)
    s t x₀ v).mpr ⟨b,hx₀,hsmall⟩
  exact ⟨by omega,differential_of_source_boundary_congruent X ((N-d:ℕ)+1) (d+1)
    (s,t) (s+(N-d:ℕ)+1,t+(N-d:ℕ)) x x₀ v hdiff hcong⟩

private theorem finite_source_differential_of_top_at_weight
    (X : (AdamsObject (coefficients := background.coefficients))) (d N M : ℕ) (hd : 0 < d) (hdN : d < N)
    (hM : d+1=M) (s t w : ℤ) (hw : t-d=w)
    (x : Ambient background X (s,t)) (v : Ambient background X (s+(N-d:ℕ)+1,t+(N-d:ℕ)))
    (a : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (hsource : a ≫ (background.quotients.tower _).rho M N (by omega) =
      finiteTopLabelAtWeight X d hd M hM s t w hw x)
    (hboundary : homotopyRegrade (by omega) (by omega)
        (biSuspensionHomEquiv (t-s) w N (background.nu.functor.obj (X.obj background.auxiliary))
          (a ≫ XModLambdaN.proj _ N)) ≫ XModLambdaN.incl _ 1 =
      nativeFirstLabel X (s+(N-d:ℕ)+1) (t+(N-d:ℕ)) v) :
    DifferentialAt background X ((N-d:ℕ)+1) (s,t) (s+(N-d:ℕ)+1,t+(N-d:ℕ)) x v := by
  subst M; subst w
  apply finite_source_differential_of_top_restriction X d N hd hdN s t x v a
    _ hboundary
  simpa only [finiteTopLabelAtWeight,top_target_regrade_self] using hsource

/-- Recover a raw May source while preserving the specified native finite source
and differential lift. -/
private theorem raw_may_source_desuspend_surjective
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
    (a : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)) :
    ∃ raw : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N),
      rawMaySourceDesuspend T he hf N c S V ε raw = a := by
  let Q := background.quotients.functoriality.functor N
  let e := Q.mapIso (normalizedSuspensionNativeIso T he hf) ≪≫
    Q.mapIso (background.nu.suspensionIso (T.X.obj background.auxiliary))
  let raw := (shiftHomotopyClass (1,1) (V-S,V-c) a ≫ ε.inv) ≫ e.inv
  refine ⟨raw,?_⟩
  have hraw : raw ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N ≫
      XModLambdaN.map (background.nu.suspensionIso (T.X.obj background.auxiliary)).hom N =
      shiftHomotopyClass (1,1) (V-S,V-c) a ≫ ε.inv := by
    change raw ≫ e.hom = _
    dsimp only [raw]
    rw [Category.assoc,e.inv_hom_id]
    exact Category.comp_id _
  dsimp only [rawMaySourceDesuspend]
  rw [hraw]
  exact quotient_unshift_shift T.X (1,1) (V-S,V-c) N ε a

/-- The converse nonzero comparison only removes a source automorphism
on the specified top label, preserving the fixed normalized first map. -/
private theorem finite_may_top_of_raw_positive_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (c q : ℕ) (hq : 0<q) (S V : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (εp : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (hε : XModLambdaN.incl _ (c+(q+1)) ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (c+(q+1))))
    (hεp : XModLambdaN.incl _ (c+(q+1)) ≫ εp.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (c+(q+1))))
    (ey : XModLambdaN ((background.nu.functor.obj (T.Y.obj background.auxiliary))⟦(1:ℤ)⟧) (c+(q+1)) ≅
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (c+(q+1)))⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ (c+(q+1)) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (c+(q+1))))
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+(q+1))))
    (v : Ambient background T.Y (S+q+1,(V+1)+q))
    (himage : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+(q+1)) ≫ ey.hom =
      ordinarySuspendedRepresentative _ (V-S+1) (V-c+1)
        (homotopyRegrade (show ((V+1)-S)-1=(V-S+1)-1 by omega)
          (show (V+1)-c=V-c+1 by omega) (finiteMayTopLabel T.Y c q hq S (V+1) v))) :
    homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
      (show (V-c)+1=(V+1)-c by omega)
      (positiveFiniteImage T hf (c+(q+1)) εp (V-S) (V-c)
        (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε a)) =
      finiteMayTopLabel T.Y c q hq S (V+1) v := by
  obtain ⟨u,hu⟩ := native_positive_image_up_to_sphere T he hf (c+(q+1)) c
    (by omega) S V ε εp hε hεp ey hey a
  let top := homotopyRegrade (show ((V+1)-S)-1=(V-S+1)-1 by omega)
    (show (V+1)-c=V-c+1 by omega) (finiteMayTopLabel T.Y c q hq S (V+1) v)
  have hfixed := ordinary_suspension_sphere_fixed _ (V-S+1) (V-c+1) top
    (sphere_fixed_regrade _ _ _
      (finite_may_top_label_sphere_automorphism T.Y c q hq S (V+1) v)) u.symm
  have hh := congrArg (fun b => u.inv ≫ b) (hu.symm.trans himage)
  simp only [←Category.assoc,u.inv_hom_id,Category.id_comp] at hh
  have hnative := ordinary_suspended_representative_injective _ (V-S+1) (V-c+1)
    (hh.trans hfixed)
  have hregrade := congrArg (homotopyRegrade
    (show (V-S+1)-1=((V+1)-S)-1 by omega)
    (show V-c+1=(V+1)-c by omega)) hnative
  simpa only [top,last_layer_regrade_trans,top_target_regrade_self] using hregrade

/-- The upper broken line and middle image conditions determine
the normalized image of the specified finite source `a₀` up to an F₂ error. -/
private theorem positive_finite_image_of_same_source
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (c q : ℕ) (hq : 0<q) (S V : ℤ)
    (u : Ambient background T.X (S,V)) (z : Ambient background T.Z (S,V+1))
    (v : Ambient background T.Y (S+q+1,(V+1)+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass S (V+1)
      ((background.classical.map T.h).pageMap 2 (S,V+1) z) (by simpa using u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (S,V+1) (S+q+1,(V+1)+q) z
      ((background.classical.map T.g).pageMap 2 (S+q+1,(V+1)+q) v))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X (S+j,V+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (S+j,V+j) →
        ∃ z' : Ambient background T.Z (S+j,V+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (S+j,V+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (S+j,V+j))
    (εp : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (hεp : XModLambdaN.incl _ (c+(q+1)) ≫ εp.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (c+(q+1))))
    (a₀ : BiHom (V-S) (V-c)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (ha₀ : Detects (background.convergence (.quotient (c+(q+1)) (.nu T.X)))
      (S,V,V-c) (finiteTargetLabel background T.X (c+(q+1)) S V c u) a₀) :
    ∃ e : Ambient background T.X (S+q,V+q),
    ∃ error : Ambient background T.Y (S+q+1,(V+1)+q),
      HEq error (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
        T hf (S+q) (V+q) e) ∧
      homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
        (show (V-c)+1=(V+1)-c by omega)
        (positiveFiniteImage T hf (c+(q+1)) εp (V-S) (V-c) a₀) =
      finiteMayTopLabel T.Y c q hq S (V+1) (v+error) := by
  let N := c+(q+1)
  letI := background.exactness.shiftCommShift (1,1)
  letI := background.exactness.shiftExact (1,1)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,1) N
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) (q+1)
  obtain ⟨eY,heY⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) N
  obtain ⟨d,hd⟩ := raw_may_source_desuspend_surjective T he hf N c S V ε a₀
  have hddet : Detects (background.convergence (.quotient N (.nu T.X)))
      (S,V,V-c) (finiteTargetLabel background T.X N S V c u)
      (rawMaySourceDesuspend T he hf N c S V ε d) := by rw [hd]; exact ha₀
  obtain ⟨a,e,hefil,haimage,heimage⟩ := positive_first_common_last_residual
    T he hT hf hg hh c q hq S V u z v hu hdz hmid ε hε ey hey eY heY d hddet
  obtain ⟨e₂,error,herror,herrorTop⟩ := last_layer_positive_image_eq_finite_may_top
    T hf c q hq S V εp hεp (rawMaySourceDesuspend T he hf N c S V ε e) hefil
  have herrorRaw := native_positive_image_eq_finite_may_top
    T he hf c q hq S V ε εp hε hεp eY heY e error herrorTop
  rw [←ordinary_suspended_representative_regrade _ ((V+1)-S) (V-S+1)
    ((V+1)-c) (V-c+1) (by omega) (by omega)
    (finiteMayTopLabel T.Y c q hq S (V+1) error)] at herrorRaw
  let f := XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
    (normalizedTriangle background T he).mor₁) N ≫ eY.hom
  have hresidual : e ≫ f = (d-a) ≫ f := by
    simpa only [f,Category.assoc] using congrArg (fun b => b ≫ eY.hom) heimage
  have himage : d ≫ f =
      homotopyRegrade (show (V+1)-S=V-S+1 by omega)
        (show (V+1)-c=V-c+1 by omega)
        (ordinarySuspendedRepresentative _ ((V+1)-S) ((V+1)-c)
          (finiteMayTopLabel T.Y c q hq S (V+1) (v+error))) := by
    have hsum : d ≫ f = a ≫ f + e ≫ f := by
      rw [hresidual,Preadditive.sub_comp]; abel
    rw [hsum]
    change a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N ≫ eY.hom +
      e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N ≫ eY.hom = _
    rw [haimage,herrorRaw,finite_may_top_label_add,
      ordinary_suspended_representative_add,regrade_add]
  have hi := finite_may_top_of_raw_positive_image T he hf c q hq S V
    ε εp hε hεp eY heY d (v+error) (by
      rw [←ordinary_suspended_representative_regrade]
      exact himage)
  rw [hd] at hi
  exact ⟨e₂,error,herror,hi⟩

/-- Restriction of the selected positive normalized image is the image of
the same restricted source. Inclusion-compatible quotient choices suffice. -/
private theorem positive_finite_image_restriction
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (i N : ℕ) (hi : 0 < i) (hiN : i ≤ N) (m w : ℤ)
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N)) :
    positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) m w a ≫
        (background.quotients.tower _).rho i N hiN =
      positiveFiniteImage T hf i (levelQuotientShiftIso T.X 1 i) m w
        (a ≫ (background.quotients.tower _).rho i N hiN) := by
  let a' := homotopyRegrade (m':=m) (w':=w+1) (by dsimp; omega) rfl
    (shiftHomotopyClass (0,1) (m,w) a) ≫ (levelQuotientShiftIso T.X 1 N).inv
  have hshift : a' ≫ (background.quotients.tower _).rho i N hiN =
      homotopyRegrade (m':=m) (w':=w+1) (by dsimp; omega) rfl
        (shiftHomotopyClass (0,1) (m,w) (a ≫ (background.quotients.tower _).rho i N hiN)) ≫
          (levelQuotientShiftIso T.X 1 i).inv := by
    apply (cancel_mono (levelQuotientShiftIso T.X 1 i).hom).mp
    have h := quotient_shift_restriction_on_spheres T.X (0,1) i N hi hiN
      (levelQuotientShiftIso T.X 1 i) (levelQuotientShiftIso T.X 1 N)
      (level_quotient_shift_incl T.X 1 i) (level_quotient_shift_incl T.X 1 N) m (w+1) a'
    simpa only [a',Category.assoc,Iso.inv_hom_id,Iso.inv_hom_id_assoc,Category.comp_id,
      shift_hom_comp,regrade_comp] using h
  change (a' ≫ XModLambdaN.map (lastLayerNormalizedMap T hf) N) ≫
    (background.quotients.tower _).rho i N hiN = _
  rw [Category.assoc,←(background.quotients.natural (lastLayerNormalizedMap T hf)).rho_naturality hiN,
    ←Category.assoc,hshift]
  rfl

/-- From the original upper E₂ broken line, the full middle conditions
give the required top restriction of the image of the same arbitrary
long source lift. This produces the top restriction for the finite-source
differential criterion. -/
private theorem positive_source_finite_top_restriction
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q N : ℕ) (hq : 0 < q) (hqN : q+1 ≤ N) (s t : ℤ)
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
    (hζ : ζ ≫ (background.quotients.tower _).rho 1 N (by omega) = nativeFirstLabel T.X s t x) :
    ∃ e : Ambient background T.X (s+q,t+q),
    ∃ error : Ambient background T.Y (s+q+1,(t+1)+q),
      HEq error (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+q) (t+q) e) ∧
      homotopyRegrade (show t-s=((t+1)+q)-(s+q+1) by omega)
        rfl
        (positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s) t ζ ≫
          (background.quotients.tower _).rho (0+(q+1)) N (by omega)) =
        finiteTopLabelAtWeight T.Y (0+q) (by omega) (0+(q+1)) (by omega)
          (s+q+1) ((t+1)+q) (t+1) (by omega) (y+error) := by
  let a := ζ ≫ (background.quotients.tower _).rho (0+(q+1)) N (by omega)
  have hfirst : a ≫ (background.quotients.tower _).rho 1 (0+(q+1)) (by omega) =
      nativeFirstLabel T.X s t x := by
    dsimp only [a]
    rw [Category.assoc,(background.quotients.tower _).rho_comp (by omega) (by omega),hζ]
  have ha := first_label_detects_unshifted T.X (0+(q+1)) (by omega) s t x a hfirst
  rw [←zero_weight_label] at ha
  have ha₀ := finite_weight_detection_regrade T.X (0+(q+1)) s t t (t-(0:ℕ))
    (by omega) (by omega) (by omega) x a ha
  rw [finite_coefficient_weight_label] at ha₀
  have H := positive_finite_image_of_same_source T he hT hf hg hh 0 q hq s t
    x z y hxz hdz hmid
  let a₀ : BiHom (t-s) (t-(0:ℕ))
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (0+(q+1))) := by
    exact homotopyRegrade rfl (by omega) a
  obtain ⟨e,error,herror,hi⟩ := H (levelQuotientShiftIso T.X 1 (0+(q+1)))
    (level_quotient_shift_incl T.X 1 (0+(q+1))) a₀ ha₀
  refine ⟨e,error,herror,?_⟩
  rw [positive_finite_image_restriction T hf (0+(q+1)) N (by omega) (by omega)]
  have ht := congrArg (homotopyRegrade
    (show ((t+1)-s)-1=((t+1)+q)-(s+q+1) by omega)
    (show (t+1)-(0:ℕ)=t+1 by omega)) hi
  simp only [a,a₀,←positiveFiniteImage_regrade,finiteMayTopLabel,
    last_layer_regrade_trans] at ht
  rw [top_label_at_weight_output_regrade] at ht
  simpa only [top_target_regrade_self] using ht

private theorem source_boundary_regrade (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ)
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w')
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)) :
    biSuspensionHomEquiv m' w' N (background.nu.functor.obj (X.obj background.auxiliary))
      (homotopyRegrade hm hw a ≫ XModLambdaN.proj _ N) =
      homotopyRegrade (show m-1=m'-1 by omega) (show w+N=w'+N by omega)
        (biSuspensionHomEquiv m w N (background.nu.functor.obj (X.obj background.auxiliary))
          (a ≫ XModLambdaN.proj _ N)) := by
  subst m'; subst w'; rfl

private theorem source_native_label_transport (X : (AdamsObject (coefficients := background.coefficients)))
    (s t s' t' : ℤ) (hs : s=s') (ht : t=t')
    (x : Ambient background X (s,t)) (x' : Ambient background X (s',t')) (hx : HEq x' x) :
    homotopyRegrade (show t-s=t'-s' by omega) ht (nativeFirstLabel X s t x) =
      nativeFirstLabel X s' t' x' := by
  subst s'; subst t'; cases eq_of_heq hx; rfl

/-- The finite-source differential criterion for positive first exponent and
`K₂=1`, with `r=N+1`, `K₁=q+1`, and output page `D=N-q+1`.
The original upper differential, all middle H-image conditions, and the
entire final F₂ image condition are the inputs. The long source and its
absolute boundary are chosen together from the original differential and
retained throughout the construction. -/
public theorem source_finite_differential_positive_first_bottom_one
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (q N : ℕ) (hq : 0 < q) (hqN : q+1 ≤ N) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (u : Ambient background T.X (s+N+1,t+N))
    (z : Ambient background T.Z (s,t+1))
    (y : Ambient background T.Y (s+q+1,(t+1)+q))
    (_hFx : KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x = 0)
    (hxz : (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) z) (by simpa using x))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (s,t) (s+N+1,t+N) x u)
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
    (himage : ∀ e : Ambient background T.X (s+q,t+q),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+q) (t+q) e ∈
        cycles background T.Y ((N-q:ℕ)+1) (s+q+1,(t+q)+1)) :
    let v := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+N+1) (t+N) u
    IsCycle background T.Y (N-q:ℕ) (s+q+1,(t+1)+q) y ∧
      IsCycle background T.Y (N-q:ℕ) ((s+N+1)+1,(t+N)+1) v ∧
      DifferentialAt background T.Y ((N-q:ℕ)+1) (s+q+1,(t+1)+q)
        ((s+N+1)+1,(t+N)+1) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  dsimp only
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X N (by omega)
    s t x u).mp hdx
  obtain ⟨e,error,herror,htop⟩ := positive_source_finite_top_restriction
    T he hT hf hg hh q N hq hqN s t x z y hxz hdz hmid ζ hζ
  let S := s+q+1
  let V := (t+1)+q
  let d : ℕ := 0+q
  let v := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+N+1) (t+N) u
  let v' : Ambient background T.Y (S+(N-d:ℕ)+1,V+(N-d:ℕ)) :=
    topClassicalRegrade (show ((s+N+1)+1,(t+N)+1)=(S+(N-d:ℕ)+1,V+(N-d:ℕ)) by
      ext <;> dsimp [S,V,d] <;> omega) v
  have hv' : HEq v' v := top_classical_regrade_heq _ _
  let η := positiveFiniteImage T hf N (levelQuotientShiftIso T.X 1 N) (t-s) t ζ
  let a : BiHom (V-S) (t+1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N) :=
    homotopyRegrade (show t-s=V-S by dsimp [S,V]; omega)
      rfl η
  have ha : a ≫ (background.quotients.tower _).rho (0+(q+1)) N (by omega) =
      finiteTopLabelAtWeight T.Y d (by dsimp [d]; omega) (0+(q+1)) (by dsimp [d]; omega)
        S V (t+1) (by dsimp [V,d]; omega) (y+error) := by
    dsimp only [a]
    rw [←regrade_comp]
    exact htop
  have hb := positive_finite_image_boundary_label T hf N (by omega) s t u ζ hU
  have hb' := congrArg (homotopyRegrade
    (show ((t+N)+1)-((s+N+1)+1)=(V+(N-d:ℕ))-(S+(N-d:ℕ)+1) by dsimp [S,V,d]; omega)
    (show (t+N)+1=V+(N-d:ℕ) by dsimp [V,d]; omega)) hb
  rw [source_native_label_transport T.Y ((s+N+1)+1) ((t+N)+1)
    (S+(N-d:ℕ)+1) (V+(N-d:ℕ)) (by dsimp [S,d]; omega) (by dsimp [V,d]; omega) v v' hv'] at hb'
  have hba : homotopyRegrade (by omega) (by omega)
      (biSuspensionHomEquiv (V-S) (t+1) N (background.nu.functor.obj (T.Y.obj background.auxiliary))
        (a ≫ XModLambdaN.proj _ N)) ≫ XModLambdaN.incl _ 1 =
      nativeFirstLabel T.Y (S+(N-d:ℕ)+1) (V+(N-d:ℕ)) v' := by
    simpa only [a,η,source_boundary_regrade,regrade_comp,last_layer_regrade_trans] using hb'
  have hd := finite_source_differential_of_top_at_weight T.Y d N (0+(q+1))
    (by dsimp [d]; omega) (by dsimp [d]; omega) (by dsimp [d]; omega)
    S V (t+1) (by dsimp [V,d]; omega) (y+error) v' a ha hba
  have hecycle : error ∈ cycles background T.Y ((N-d:ℕ)+1) (S,V) := by
    have h := classical_cycle_heq T.Y ((N-d:ℕ)+1)
      (show (s+q+1,(t+q)+1)=(S,V) by dsimp [S,V]; congr 1; omega)
      _ error herror.symm ⟨by omega,by simpa only [d,Nat.zero_add] using himage e⟩
    exact h.2
  have hdy := differential_of_source_later_cycle T.Y ((N-d:ℕ)+1)
    (S,V) (S+(N-d:ℕ)+1,V+(N-d:ℕ)) y (y+error) v' hd (by
      simpa only [sub_add_cancel_left,zero_sub] using
        (cycles background T.Y ((N-d:ℕ)+1) (S,V)).neg_mem hecycle)
  have hfinal := classical_differential_heq T.Y ((N-d:ℕ)+1) rfl
    (show (S+(N-d:ℕ)+1,V+(N-d:ℕ))=((s+N+1)+1,(t+N)+1) by
      ext <;> dsimp [S,V,d] <;> omega) y y v' v HEq.rfl hv' hdy
  have hcycles := cycles_of_differential T.Y ((N-d:ℕ)+1) _ _ y v hfinal
  exact ⟨by simpa only [d,Nat.zero_add,add_sub_cancel_right] using hcycles.1,
    by simpa only [d,Nat.zero_add,add_sub_cancel_right] using hcycles.2,
    by simpa only [d,Nat.zero_add] using hfinal⟩

end
end KIP126.ProofTools.Internal.SyntheticCoverage
