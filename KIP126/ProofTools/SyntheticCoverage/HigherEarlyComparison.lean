module

import all KIP126.ProofTools.SyntheticCoverage.AffinePermanence
import all KIP126.ProofTools.SyntheticCoverage.EarlyBoundaryDifferential
import all KIP126.ProofTools.SyntheticCoverage.HigherEarlyInput

/-! Compatible changes of a higher early-boundary root. A correction
one quotient level higher preserves the adjacent boundary after restriction. -/

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
set_option maxHeartbeats 500000

/-- An actual finite cycle supplies a representative in its prescribed
weight and filtration. This uses the exact finite-window quotient. -/
private theorem higher_finite_cycle_representative
    (X : (AdamsObject (coefficients := background.coefficients))) (q j : ℕ) (hjq : j<q) (p t : ℤ)
    (x : Ambient background X (p,t)) (hx : x ∈ cycles background X (q-j:ℕ) (p,t)) :
    ∃ b : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q),
      Detects (background.convergence (.quotient q (.nu X))) (p,t,t-j)
        (finiteTargetLabel background X q p t j x) b := by
  have hx' : x ∈ cycles background X ((q:ℤ)-t+(t-j)) (p,t) := by
    convert hx using 1
    congr 1
    omega
  let e := (KIP126.Literature.Standard.infinityFiniteWindow X q (by omega)
    (p,t) (t-j) (by omega)).symm
      (subquotientClass (cycles background X ((q:ℤ)-t+(t-j)) (p,t))
        (boundaries background X (1+t-(t-j)) (p,t)) ⟨x,hx'⟩)
  have he : HasInfinityRepresentative _ 2 (p,t,t-j)
      (finiteTargetLabel background X q p t j x) e := by
    rw [←middle_finite_label_as_weight]
    apply (KIP126.Literature.Standard.eInfinity_finite_labels X q (by omega)
      p t (t-j) (by omega) x e).mpr
    exact ⟨hx',AddEquiv.apply_symm_apply _ _⟩
  let A : SyntheticObject := .quotient q (.nu X)
  let F := background.syntheticTower.filtration (A.obj background.nu background.auxiliary)
  haveI : Epi (F.toAssociatedGraded p (t-p,t-j)) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨b,hb⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded p (t-p,t-j))).mp
    inferInstance (((background.convergence A).identification (p,t,t-j)).hom e)
  exact ⟨(F.F p (t-p,t-j)).arrow b,e,he,b,rfl,hb.symm⟩

/-- Restriction preserves the actual finite label at the same weight. -/
private theorem higher_finite_restriction_detects
    (X : (AdamsObject (coefficients := background.coefficients))) (i q j : ℕ) (hiq : i≤q) (p t : ℤ)
    (x : Ambient background X (p,t))
    (b : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (hb : Detects (background.convergence (.quotient q (.nu X))) (p,t,t-j)
      (finiteTargetLabel background X q p t j x) b) :
    Detects (background.convergence (.quotient i (.nu X))) (p,t,t-j)
      (finiteTargetLabel background X i p t j x)
      (b ≫ (background.quotients.tower _).rho i q hiq) := by
  have h := KIP126.ProofTools.Internal.detects_map (.quotient q (.nu X)) (.quotient i (.nu X))
    ((background.quotients.tower _).rho i q hiq) (p,t,t-j) _ b hb
  have he : familyPageMap background.family ((background.quotients.tower
      (background.nu.functor.obj (X.obj background.auxiliary))).rho i q hiq) 2 (p,t,t-j)
      (finiteTargetLabel background X q p t j x)=finiteTargetLabel background X i p t j x := by
    rw [←middle_finite_label_as_weight,←middle_finite_label_as_weight]
    change background.family.pageMap _ 2 (p,t,t-j)
      (background.family.pageMap (XModLambdaN.incl _ q) 2 (p,t,t-j) _) =
        background.family.pageMap (XModLambdaN.incl _ i) 2 (p,t,t-j) _
    rw [←ModuleCat.comp_apply,←familyPageMap_comp,(background.quotients.tower _).rho_quotient]
  exact he ▸ h

/-- The additional Z-cycle summand in R_j produces a correction from Q_(N+1).
After restricting to Q_N it keeps the first quotient zero and its actual
adjacent boundary is zero. This supplies the longer lift for the higher early-boundary comparison. -/
private theorem higher_root_correction
    (X : (AdamsObject (coefficients := background.coefficients))) (N j : ℕ) (hj : 0<j) (hjN : j<N) (p t : ℤ)
    (k : Ambient background X (p,t)) (hk : k ∈ cycles background X (N+1-j:ℕ) (p,t)) :
    ∃ b : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (N+1)),
      Detects (background.convergence (.quotient (N+1) (.nu X))) (p,t,t-j)
        (finiteTargetLabel background X (N+1) p t j k) b ∧
      (b ≫ (background.quotients.tower _).rho N (N+1) (by omega)) ≫
        (background.quotients.tower _).rho 1 N (by omega)=0 ∧
      (b ≫ (background.quotients.tower _).rho N (N+1) (by omega)) ≫
        ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta=0 := by
  obtain ⟨b,hb⟩ := higher_finite_cycle_representative X (N+1) j (by omega) p t k hk
  refine ⟨b,hb,?_,?_⟩
  · rw [Category.assoc,(background.quotients.tower _).rho_comp]
    exact finite_filtered_first_quotient_zero X (N+1) j (by omega) hj p t b
      (KIP126.ProofTools.Internal.Leibniz.detects_filtration (.quotient (N+1) (.nu X))
        (p,t,t-j) (finiteTargetLabel background X (N+1) p t j k) b hb)
  · let C := (background.quotients.tower
      (background.nu.functor.obj (X.obj background.auxiliary))).triangle (show 0<N by omega) (Nat.lt_succ_self N)
    have hz : C.rho ≫ C.delta=0 := comp_distTriang_mor_zero₂₃ _ C.distinguished
    rw [(background.quotients.tower _).triangle_rho] at hz
    rw [Category.assoc,hz,comp_zero]

/-- One original R_j step. The short representative changes by a genuine
G image, while the specified root changes by the restriction of a longer
lift. Both its first quotient and its exact adjacent boundary are retained. -/
private theorem higher_ordinary_root_correction_step
    (Y Z : (AdamsObject (coefficients := background.coefficients))) (g : Y.obj background.auxiliary ⟶ Z.obj background.auxiliary)
    (D : SyntheticSpectrum) (h : background.nu.functor.obj (Z.obj background.auxiliary) ⟶ D)
    (hgh : background.nu.functor.map g ≫ h=0)
    (a N j : ℕ) (hja : j<a) (haN : a≤N) (hj : 0<j) (p t : ℤ)
    (hR : ∀ z : Ambient background Z (p,t), z ∈ cycles background Z (a-j:ℕ) (p,t) →
      ∃ u : Ambient background Y (p,t), u ∈ cycles background Y (a-j:ℕ) (p,t) ∧
      ∃ k : Ambient background Z (p,t), k ∈ cycles background Z (N+1-j:ℕ) (p,t) ∧
        z-(background.classical.map g).pageMap 2 (p,t) u-k ∈ boundaries background Z (j+1) (p,t))
    (R : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) a))
    (root : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) N))
    (herror : FiltrationAtLeast background.syntheticTower p
      (R-root ≫ (background.quotients.tower _).rho a N haN)) :
    ∃ (R' : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) a))
      (root' : BiHom (t-p) (t-j) (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) N)),
      R' ≫ (background.quotients.tower _).rho 1 a (by omega)=R ≫ (background.quotients.tower _).rho 1 a (by omega) ∧
      R' ≫ XModLambdaN.map h a=R ≫ XModLambdaN.map h a ∧
      root' ≫ (background.quotients.tower _).rho 1 N (by omega)=root ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      root' ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta=
        root ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta ∧
      FiltrationAtLeast background.syntheticTower (p+1)
        (R'-root' ≫ (background.quotients.tower _).rho a N haN) := by
  obtain ⟨z,hzc,hzd⟩ := middle_finite_filtration_label Z a j hja p t
    (R-root ≫ (background.quotients.tower _).rho a N haN) herror
  obtain ⟨u,hu,k,hk,hcong⟩ := hR z hzc
  obtain ⟨b,hb⟩ := higher_finite_cycle_representative Y a j hja p t u hu
  obtain ⟨c,hc,hcf,hcd⟩ := higher_root_correction Z N j hj (by omega) p t k hk
  have hbimage := KIP126.ProofTools.Internal.detects_map (.quotient a (.nu Y)) (.quotient a (.nu Z))
    (XModLambdaN.map (background.nu.functor.map g) a) (p,t,t-j) _ b hb
  erw [←middle_finite_label_as_weight,finite_weight_label_natural Y Z g a p t (t-j) (by omega) u,
    middle_finite_label_as_weight] at hbimage
  have hcshort := higher_finite_restriction_detects Z a (N+1) j (by omega) p t k c hc
  have hsub := KIP126.ProofTools.Internal.Mahowald.detects_sub
    (.quotient a (.nu Z)) (p,t,t-j) hzd hbimage
  rw [←finiteTargetLabel_sub] at hsub
  have hnext := middle_finite_congruent_difference Z a j hja p t
    (z-(background.classical.map g).pageMap 2 (p,t) u) k hcong
    ((R-root ≫ (background.quotients.tower _).rho a N haN)-b ≫ XModLambdaN.map (background.nu.functor.map g) a)
    (c ≫ (background.quotients.tower _).rho a (N+1) (by omega)) hsub hcshort
  have hbfirst : b ≫ (background.quotients.tower _).rho 1 a (by omega)=0 :=
    finite_filtered_first_quotient_zero Y a j (by omega) hj p t b
      (KIP126.ProofTools.Internal.Leibniz.detects_filtration (.quotient a (.nu Y))
        (p,t,t-j) (finiteTargetLabel background Y a p t j u) b hb)
  refine ⟨R-b ≫ XModLambdaN.map (background.nu.functor.map g) a,
    root+c ≫ (background.quotients.tower _).rho N (N+1) (by omega),?_,?_,?_,?_,?_⟩
  · rw [Preadditive.sub_comp,Category.assoc,
      ←(background.quotients.natural (background.nu.functor.map g)).rho_naturality (show 1≤a by omega),
      ←Category.assoc,hbfirst,zero_comp,sub_zero]
  · rw [Preadditive.sub_comp,Category.assoc,
      quotient_map_comp_zero (background.nu.functor.map g) h hgh,comp_zero,sub_zero]
  · rw [Preadditive.add_comp,hcf,add_zero]
  · rw [Preadditive.add_comp,hcd,add_zero]
  · rw [Preadditive.add_comp,Category.assoc,(background.quotients.tower _).rho_comp]
    convert hnext using 1
    abel

private theorem higher_ordinary_root_correction_step_at
    (Y Z : (AdamsObject (coefficients := background.coefficients))) (g : Y.obj background.auxiliary ⟶ Z.obj background.auxiliary)
    (D : SyntheticSpectrum) (h : background.nu.functor.obj (Z.obj background.auxiliary) ⟶ D)
    (hgh : background.nu.functor.map g ≫ h=0)
    (a N j : ℕ) (hja : j<a) (haN : a≤N) (hj : 0<j) (p t m w : ℤ) (hm : m=t-p) (hw : w=t-j)
    (hR : ∀ z : Ambient background Z (p,t), z ∈ cycles background Z (a-j:ℕ) (p,t) →
      ∃ u : Ambient background Y (p,t), u ∈ cycles background Y (a-j:ℕ) (p,t) ∧
      ∃ k : Ambient background Z (p,t), k ∈ cycles background Z (N+1-j:ℕ) (p,t) ∧
        z-(background.classical.map g).pageMap 2 (p,t) u-k ∈ boundaries background Z (j+1) (p,t))
    (R : BiHom m w (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) a))
    (root : BiHom m w (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) N))
    (herror : FiltrationAtLeast background.syntheticTower p
      (R-root ≫ (background.quotients.tower _).rho a N haN)) :
    ∃ (R' : BiHom m w (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) a))
      (root' : BiHom m w (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) N)),
      R' ≫ (background.quotients.tower _).rho 1 a (by omega)=R ≫ (background.quotients.tower _).rho 1 a (by omega) ∧
      R' ≫ XModLambdaN.map h a=R ≫ XModLambdaN.map h a ∧
      root' ≫ (background.quotients.tower _).rho 1 N (by omega)=root ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      root' ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta=
        root ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta ∧
      FiltrationAtLeast background.syntheticTower (p+1)
        (R'-root' ≫ (background.quotients.tower _).rho a N haN) := by
  subst m
  subst w
  exact higher_ordinary_root_correction_step Y Z g D h hgh a N j hja haN hj p t hR R root herror

/-- Finite R_j iteration for the same specified root. The extra longer-cycle
summand is used at every step, and all exact first and boundary data survive. -/
private theorem higher_ordinary_root_correction_to_last
    (Y Z : (AdamsObject (coefficients := background.coefficients))) (g : Y.obj background.auxiliary ⟶ Z.obj background.auxiliary)
    (D : SyntheticSpectrum) (h : background.nu.functor.obj (Z.obj background.auxiliary) ⟶ D)
    (hgh : background.nu.functor.map g ≫ h=0)
    (a N : ℕ) (ha : 0<a) (haN : a≤N) (m w u v : ℤ)
    (huv : u≤v) (hwindow : 0<m+u-w) (hv : v≤(a:ℤ)+w-m)
    (hR : ∀ p : ℤ, u≤p → p<v →
      ∀ z : Ambient background Z (p,m+p), z ∈ cycles background Z (a-(m+p-w).toNat:ℕ) (p,m+p) →
      ∃ y : Ambient background Y (p,m+p), y ∈ cycles background Y (a-(m+p-w).toNat:ℕ) (p,m+p) ∧
      ∃ k : Ambient background Z (p,m+p), k ∈ cycles background Z (N+1-(m+p-w).toNat:ℕ) (p,m+p) ∧
        z-(background.classical.map g).pageMap 2 (p,m+p) y-k ∈
          boundaries background Z ((m+p-w).toNat+1) (p,m+p))
    (R : BiHom m w (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) a))
    (root : BiHom m w (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) N))
    (herror : FiltrationAtLeast background.syntheticTower u
      (R-root ≫ (background.quotients.tower _).rho a N haN)) :
    ∃ (R' : BiHom m w (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) a))
      (root' : BiHom m w (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) N)),
      R' ≫ (background.quotients.tower _).rho 1 a ha=R ≫ (background.quotients.tower _).rho 1 a ha ∧
      R' ≫ XModLambdaN.map h a=R ≫ XModLambdaN.map h a ∧
      root' ≫ (background.quotients.tower _).rho 1 N (by omega)=root ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      root' ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta=
        root ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta ∧
      FiltrationAtLeast background.syntheticTower v
        (R'-root' ≫ (background.quotients.tower _).rho a N haN) := by
  induction hd : (v-u).toNat using Nat.strong_induction_on generalizing u R root with
  | h n ih =>
    by_cases heq : v≤u
    · have huv' : u=v := le_antisymm huv heq
      exact ⟨R,root,rfl,rfl,rfl,rfl,huv' ▸ herror⟩
    · let j := (m+u-w).toNat
      have hj : (j:ℤ)=m+u-w := by dsimp [j]; omega
      have hjpos : 0<j := by omega
      have hja : j<a := by omega
      obtain ⟨R₁,root₁,hRfirst,hRimage,hrootfirst,hrootboundary,hnext⟩ :=
        higher_ordinary_root_correction_step_at Y Z g D h hgh a N j hja haN hjpos
          u (m+u) m w (by omega) (by omega) (hR u le_rfl (by omega)) R root herror
      have hd' : (v-(u+1)).toNat<n := by omega
      obtain ⟨R₂,root₂,hRfirst₂,hRimage₂,hrootfirst₂,hrootboundary₂,hfinal⟩ :=
        ih (v-(u+1)).toNat hd' (u+1) (by omega) (by omega)
          (fun p hp hpv => hR p (by omega) hpv) R₁ root₁ hnext rfl
      exact ⟨R₂,root₂,hRfirst₂.trans hRfirst,hRimage₂.trans hRimage,
        hrootfirst₂.trans hrootfirst,hrootboundary₂.trans hrootboundary,hfinal⟩

/-- The full higher early comparison when the two last arrows are ordinary.
The original R_j conditions, including the longer-cycle term, construct a
root with the same first label and exact adjacent boundary whose H-image
agrees with the specified rotated representative. R_last applies to the
entire final E₂ group. -/
private theorem higher_ordinary_root_compatible
    (Y Z W : (AdamsObject (coefficients := background.coefficients)))
    (g : Y.obj background.auxiliary ⟶ Z.obj background.auxiliary)
    (h : Z.obj background.auxiliary ⟶ W.obj background.auxiliary) (hgh : g ≫ h=0)
    (a N : ℕ) (ha : 2≤a) (haN : a≤N) (s t : ℤ)
    (hR : ∀ p : ℤ, s+1≤p → p<s+a-1 →
      ∀ z : Ambient background Z (p,t-s+p), z ∈ cycles background Z (a-(p-s).toNat:ℕ) (p,t-s+p) →
      ∃ y : Ambient background Y (p,t-s+p), y ∈ cycles background Y (a-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background Z (p,t-s+p), k ∈ cycles background Z (N+1-(p-s).toNat:ℕ) (p,t-s+p) ∧
        z-(background.classical.map g).pageMap 2 (p,t-s+p) y-k ∈
          boundaries background Z ((p-s).toNat+1) (p,t-s+p))
    (hH : ∀ z : Ambient background Z (s+a-1,t+a-1),
      (background.classical.map h).pageMap 2 (s+a-1,t+a-1) z ∈ boundaries background W a (s+a-1,t+a-1))
    (R : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) a))
    (root : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) N))
    (hfirst : R ≫ (background.quotients.tower _).rho 1 a (by omega)=
      root ≫ (background.quotients.tower _).rho 1 N (by omega)) :
    ∃ root' : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) N),
      root' ≫ (background.quotients.tower _).rho 1 N (by omega)=root ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      root' ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta=
        root ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta ∧
      (root' ≫ (background.quotients.tower _).rho a N haN) ≫ XModLambdaN.map (background.nu.functor.map h) a=
        R ≫ XModLambdaN.map (background.nu.functor.map h) a := by
  letI := background.nu.additive
  have hn : background.nu.functor.map g ≫ background.nu.functor.map h=0 := by
    rw [←Functor.map_comp,hgh,Functor.map_zero]
  have herror : FiltrationAtLeast background.syntheticTower (s+1)
      (R-root ≫ (background.quotients.tower _).rho a N haN) := by
    apply finite_first_kernel_filtration Z a ha s t
    rw [Preadditive.sub_comp,Category.assoc,(background.quotients.tower _).rho_comp,hfirst,sub_self]
  obtain ⟨R',root',_,hRimage,hrootfirst,hrootboundary,hfinal⟩ :=
    higher_ordinary_root_correction_to_last Y Z g _ (background.nu.functor.map h) hn
      a N (by omega) haN (t-s) t (s+1) (s+a-1) (by omega) (by omega) (by omega)
      (by
        intro p hp hpv
        have hi : (t-s+p-t).toNat=(p-s).toNat := by congr 1; omega
        simpa only [hi] using hR p hp hpv) R root herror
  let e := R'-root' ≫ (background.quotients.tower _).rho a N haN
  let e' := homotopyRegrade (show t-s=(t+a-1)-(s+a-1) by omega) rfl e
  have hef : FiltrationAtLeast background.syntheticTower (s+a-1) e' :=
    (KIP126.ProofTools.Internal.Leibniz.regrade_filtration_iff _ _ _ _).mpr hfinal
  have he' := ordinary_map_top_filtration_zero Z W h a ha (s+a-1) (t+a-1) t
    (by omega) hH e' hef
  have he : e ≫ XModLambdaN.map (background.nu.functor.map h) a=0 := by
    apply (ordinary_regrade_zero_iff (show t-s=(t+a-1)-(s+a-1) by omega) rfl _).mp
    simpa only [e',regrade_comp] using he'
  have heq : R' ≫ XModLambdaN.map (background.nu.functor.map h) a=
      (root' ≫ (background.quotients.tower _).rho a N haN) ≫ XModLambdaN.map (background.nu.functor.map h) a := by
    exact sub_eq_zero.mp (by simpa only [e,Preadditive.sub_comp] using he)
  exact ⟨root',hrootfirst,hrootboundary,heq.symm.trans hRimage⟩

/-- Same-root comparison in the positive-first-arrow normalized triangle,
with the specified representative and adjacent boundary. -/
private theorem higher_normalized_root_compatible
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (a N : ℕ) (ha : 2≤a) (haN : a≤N) (s t : ℤ)
    (hR : ∀ p : ℤ, s+1≤p → p<s+a-1 →
      ∀ z : Ambient background T.Z (p,t-s+p), z ∈ cycles background T.Z (a-(p-s).toNat:ℕ) (p,t-s+p) →
      ∃ y : Ambient background T.Y (p,t-s+p), y ∈ cycles background T.Y (a-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background T.Z (p,t-s+p), k ∈ cycles background T.Z (N+1-(p-s).toNat:ℕ) (p,t-s+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,t-s+p) y-k ∈
          boundaries background T.Z ((p-s).toNat+1) (p,t-s+p))
    (hH : ∀ z : Ambient background T.Z (s+a-1,t+a-1),
      (background.classical.map T.h).pageMap 2 (s+a-1,t+a-1) z ∈
        boundaries background (.shift 1 T.X) a (s+a-1,t+a-1))
    (R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ a))
    (root : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ N))
    (hfirst : R ≫ (background.quotients.tower _).rho 1 a (by omega)=
      root ≫ (background.quotients.tower _).rho 1 N (by omega)) :
    ∃ root' : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ N),
      root' ≫ (background.quotients.tower _).rho 1 N (by omega)=root ≫ (background.quotients.tower _).rho 1 N (by omega) ∧
      root' ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta=
        root ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta ∧
      (root' ≫ (background.quotients.tower _).rho a N haN) ≫
          XModLambdaN.map (normalizedTriangle background T he).mor₃ a=
        R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ a := by
  let EZ := normalizedThirdZeroIso T he hg
  let EX := normalizedSuspensionNativeIso T he hf
  let Rn := R ≫ XModLambdaN.map EZ.hom a
  let rootn := root ≫ XModLambdaN.map EZ.hom N
  have restrict {i n : ℕ} (hin : i≤n)
      (b : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ n)) :
      (b ≫ XModLambdaN.map EZ.hom n) ≫ (background.quotients.tower _).rho i n hin=
        (b ≫ (background.quotients.tower _).rho i n hin) ≫ XModLambdaN.map EZ.hom i := by
    rw [Category.assoc,←(background.quotients.natural EZ.hom).rho_naturality hin,←Category.assoc]
  have hfirstn : Rn ≫ (background.quotients.tower _).rho 1 a (by omega)=
      rootn ≫ (background.quotients.tower _).rho 1 N (by omega) := by
    dsimp only [Rn,rootn]
    rw [restrict,restrict,hfirst]
  obtain ⟨b,hbf,hbd,hbh⟩ := higher_ordinary_root_compatible T.Y T.Z (.shift 1 T.X) T.g T.h
    (comp_distTriang_mor_zero₂₃ _ T.distinguished) a N ha haN s t hR hH Rn rootn hfirstn
  let braw := b ≫ XModLambdaN.map EZ.inv N
  have hbraw : braw ≫ XModLambdaN.map EZ.hom N=b := by
    dsimp only [braw]
    rw [Category.assoc,←background.quotients.functoriality.map_comp,Iso.inv_hom_id,
      background.quotients.functoriality.map_id,Category.comp_id]
  refine ⟨braw,?_,?_,?_⟩
  · apply (cancel_mono ((background.quotients.functoriality.functor 1).mapIso EZ).hom).mp
    change (braw ≫ (background.quotients.tower _).rho 1 N (by omega)) ≫ XModLambdaN.map EZ.hom 1=
      (root ≫ (background.quotients.tower _).rho 1 N (by omega)) ≫ XModLambdaN.map EZ.hom 1
    rw [←restrict,←restrict,hbraw]
    exact hbf
  · let I := (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      ((SyntheticCategory.biShift (0,-(N:ℤ))).mapIso
        ((background.quotients.functoriality.functor ((N+1)-N)).mapIso EZ))
    apply (cancel_mono I.hom).mp
    change (braw ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta) ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(N:ℤ))).map (XModLambdaN.map EZ.hom ((N+1)-N)))=
      (root ≫ ((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta) ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(N:ℤ))).map (XModLambdaN.map EZ.hom ((N+1)-N)))
    simp only [Category.assoc,←(background.quotients.natural EZ.hom).delta_naturality
      (show 0<N by omega) (Nat.lt_succ_self N)]
    rw [←Category.assoc,hbraw]
    simpa only [rootn,Category.assoc] using hbd
  · have hs := normalized_third_arrow_zero T he hf hg hh
    have hq := congrArg (fun f => XModLambdaN.map f a) hs
    rw [background.quotients.functoriality.map_comp,background.quotients.functoriality.map_comp] at hq
    have hq' : XModLambdaN.map (normalizedTriangle background T he).mor₃ a ≫
        XModLambdaN.map EX.hom a=XModLambdaN.map EZ.hom a ≫
          XModLambdaN.map (background.nu.functor.map T.h) a := hq
    apply (cancel_mono ((background.quotients.functoriality.functor a).mapIso EX).hom).mp
    change ((braw ≫ (background.quotients.tower _).rho a N haN) ≫
        XModLambdaN.map (normalizedTriangle background T he).mor₃ a) ≫ XModLambdaN.map EX.hom a=
      (R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ a) ≫ XModLambdaN.map EX.hom a
    simp only [Category.assoc,hq']
    have ht := congrArg (fun z => z ≫ XModLambdaN.map (background.nu.functor.map T.h) a) (restrict haN braw)
    rw [hbraw] at ht
    simpa only [Rn,Category.assoc] using ht.symm.trans hbh

private theorem higher_adjacent_delta_equality
    (A : SyntheticSpectrum) (q : ℕ) (hq : 0<q) (m w : ℤ)
    (a b : BiHom m w (XModLambdaN A q))
    (hab : a ≫ ((background.quotients.tower A).triangle hq (Nat.lt_succ_self q)).delta=
      b ≫ ((background.quotients.tower A).triangle hq (Nat.lt_succ_self q)).delta) :
    a ≫ adjacentDelta A q hq=b ≫ adjacentDelta A q hq := by
  have transport (n : ℕ) (hn : n=1)
      (d : XModLambdaN A q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧)
      (hd : a ≫ d=b ≫ d) :
      a ≫ Eq.mp (congrArg (fun l => XModLambdaN A q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A l))⟦(1:ℤ)⟧) hn) d=
      b ≫ Eq.mp (congrArg (fun l => XModLambdaN A q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A l))⟦(1:ℤ)⟧) hn) d := by
    subst n
    exact hd
  exact transport (q.succ-q) (by omega) _ hab

/-- The root differential and `R_j/R_last` construct a long source
with the prescribed early top and image at the final compatible root. -/
private theorem higher_bottom_with_fixed_rotated_root
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (i q : ℕ) (hi : 0 < i) (hiq : i < q) (s t : ℤ)
    (z : Ambient background T.Z (s,t)) (u : Ambient background T.X (s+i,t+i-1))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
    (hR : ∀ p : ℤ, s+1≤p → p<s+(i+1)-1 →
      ∀ z : Ambient background T.Z (p,t-s+p), z ∈ cycles background T.Z ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) →
      ∃ y : Ambient background T.Y (p,t-s+p), y ∈ cycles background T.Y ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background T.Z (p,t-s+p), k ∈ cycles background T.Z (q+1-(p-s).toNat:ℕ) (p,t-s+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,t-s+p) y-k ∈
          boundaries background T.Z ((p-s).toNat+1) (p,t-s+p))
    (hH : ∀ z : Ambient background T.Z (s+(i+1)-1,t+(i+1)-1),
      (background.classical.map T.h).pageMap 2 (s+(i+1)-1,t+(i+1)-1) z ∈
        boundaries background (.shift 1 T.X) (i+1) (s+(i+1)-1,t+(i+1)-1))
    (εa : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (i+1) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (i+1)))
    (hεa : XModLambdaN.incl _ (i+1) ≫ εa.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (i+1)))
    (R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ (i+1)))
    (hRfirst : R ≫ (background.quotients.tower _).rho 1 (i+1) (by omega)=
      nativeFirstLabel T.Z s t z ≫ XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1)
    (hRtop : rawMaySourceDesuspend T he hf (i+1) i (s+i) (t+i-1) εa
        (homotopyRegrade (show t-s=(t+i-1)-(s+i)+1 by omega)
          (show t=(t+i-1)-i+1 by omega)
          (R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ (i+1)))=
      finiteTopLabel T.X i hi (s+i) (t+i-1) u) :
    ∃ a : BiHom ((t+i-1)-(s+i)) ((t+i-1)-i)
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)),
      a ≫ (background.quotients.tower _).rho (i+1) (q+1) (by omega)=
        finiteTopLabel T.X i hi (s+i) (t+i-1) u ∧
      positiveFiniteImage T hf (q+1) (levelQuotientShiftIso T.X 1 (q+1))
        ((t+i-1)-(s+i)) ((t+i-1)-i) a=
        homotopyRegrade (show (t+q)-(s+q+1)=(t+i-1)-(s+i) by omega)
          (show (t+q)-q=((t+i-1)-i)+1 by omega)
          (finiteTopLabel T.Y q (by omega) (s+q+1) (t+q) v) := by
  obtain ⟨ey,hey,_⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he (q+1) (by omega)
  obtain ⟨root,_,hroot,hdelta,_,_⟩ := classical_second_differential_may T he hT hg q (by omega)
    s t z v hd ey hey
  obtain ⟨root',_,hdelta',hcompatible⟩ := higher_normalized_root_compatible T he hf hg hh
    (i+1) q (by omega) (by omega) s t hR hH R root (hRfirst.trans hroot.symm)
  have hsame := higher_adjacent_delta_equality (normalizedTriangle background T he).obj₃ q
    (by omega) (t-s) t root' root hdelta'
  let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
    (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1)).symm
      (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
        (nativeFirstLabel T.Y (s+q+1) (t+q) v))
  obtain ⟨a,ha,himage⟩ := finite_may_at_normalized_triangle_explicit_lengths T he hT q 1
    (by omega) (by decide) (t-s) t ey hey root' b (hsame.trans hdelta)
  have haearly : a ≫ (background.quotients.tower _).rho (i+1) (q+1) (by omega)=
      R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ (i+1) := by
    rw [←(background.quotients.tower _).rho_comp (show i+1≤q by omega) (show q≤q+1 by omega),
      ←Category.assoc,ha,Category.assoc,
      ←(background.quotients.natural (normalizedTriangle background T he).mor₃).rho_naturality (show i+1≤q by omega),
      ←Category.assoc,hcompatible]
  letI := background.exactness.shiftCommShift (1,1)
  letI := background.exactness.shiftExact (1,1)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,1) (q+1)
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  let a' := homotopyRegrade (show t-s=(t+i-1)-(s+i)+1 by omega)
    (show t=(t+i-1)-i+1 by omega) a
  let an := rawMaySourceDesuspend T he hf (q+1) i (s+i) (t+i-1) ε a'
  refine ⟨an,?_,?_⟩
  · dsimp only [an]
    rw [early_raw_source_desuspend_restriction T he hf (i+1) (q+1) i (by omega)
      (by omega) (s+i) (t+i-1) εa ε hεa hε]
    simpa only [a',←regrade_comp,haearly] using hRtop
  · apply early_raw_positive_image_top T he hf q i (by omega) (s+i) (t+i-1)
      (s+q+1) (t+q) (by omega) (by omega) v ε hε ey hey a'
    dsimp only [a']
    rw [←regrade_comp]
    erw [himage,ordinary_may_signed_top_target]
    simp only [ordinary_suspended_representative_regrade,last_layer_regrade_trans]

/-- The prescribed top factors through the selected i-th coefficient map.
The equality is on the actual highest filtered layer. -/
private theorem higher_coefficient_top
    (X : (AdamsObject (coefficients := background.coefficients))) (q i : ℕ) (hiq : i < q) (s t w : ℤ)
    (hw : t-(q-i:ℕ)=w) (x : Ambient background X (s,t)) :
    finiteCoefficientShiftClass _ (q+1) i (by omega) (t-s) w
      (finiteTopLabelAtWeight X (q-i) (by omega) ((q+1)-i) (by omega) s t w hw x)=
      finiteTopLabelAtWeight X q (by omega) (q+1) rfl s t (w-i) (by omega) x := by
  have hs := finite_top_label_at_weight_detects X (q-i) (by omega) ((q+1)-i) (by omega) s t w hw x
  have hi := finite_coefficient_shift_detects X (q+1) i (by omega) s t w (by omega) x _ hs
  have ht := finite_top_label_at_weight_detects X q (by omega) (q+1) rfl s t (w-i) (by omega) x
  exact finite_top_detection_unique X (q+1) (by omega) s t (w-i) (by omega) _ _ _ hi ht

private theorem higher_compatible_positive_finite_lift_of_rotated_root
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (i q : ℕ) (hi : 0 < i) (hiq : i < q) (s t : ℤ)
    (z : Ambient background T.Z (s,t)) (u : Ambient background T.X (s+i,t+i-1))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
    (hR : ∀ p : ℤ, s+1≤p → p<s+(i+1)-1 →
      ∀ z : Ambient background T.Z (p,t-s+p), z ∈ cycles background T.Z ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) →
      ∃ y : Ambient background T.Y (p,t-s+p), y ∈ cycles background T.Y ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background T.Z (p,t-s+p), k ∈ cycles background T.Z (q+1-(p-s).toNat:ℕ) (p,t-s+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,t-s+p) y-k ∈
          boundaries background T.Z ((p-s).toNat+1) (p,t-s+p))
    (hH : ∀ z : Ambient background T.Z (s+(i+1)-1,t+(i+1)-1),
      (background.classical.map T.h).pageMap 2 (s+(i+1)-1,t+(i+1)-1) z ∈
        boundaries background (.shift 1 T.X) (i+1) (s+(i+1)-1,t+(i+1)-1))
    (εa : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (i+1) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (i+1)))
    (hεa : XModLambdaN.incl _ (i+1) ≫ εa.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (i+1)))
    (R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ (i+1)))
    (hRfirst : R ≫ (background.quotients.tower _).rho 1 (i+1) (by omega)=
      nativeFirstLabel T.Z s t z ≫ XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1)
    (hRtop : rawMaySourceDesuspend T he hf (i+1) i (s+i) (t+i-1) εa
        (homotopyRegrade (show t-s=(t+i-1)-(s+i)+1 by omega)
          (show t=(t+i-1)-i+1 by omega)
          (R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ (i+1)))=
      finiteTopLabel T.X i hi (s+i) (t+i-1) u) :
    let S : ℤ := s+i
    let V : ℤ := t+i-1
    let K : ℕ := (q+1)-i
    ∃ b : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) K),
    ∃ u' : Ambient background T.X (S,V),
    ∃ aHat : BiHom ((V-S)+1) ((V+1)-i)
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) i),
    ∃ W : BiHom (V-S) (V+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      b ≫ (background.quotients.tower _).rho 1 K (by dsimp [K]; omega)=nativeFirstLabel T.X S V u' ∧
      u'-u ∈ boundaries background T.X (i+1) (S,V) ∧
      W=homotopyRegrade (show ((V-S)+1)-1=V-S by omega)
        (show ((V+1)-i)+i=V+1 by omega)
        (biSuspensionHomEquiv ((V-S)+1) ((V+1)-i) i
          (background.nu.functor.obj (T.Y.obj background.auxiliary)) (aHat ≫ XModLambdaN.proj _ i)) ∧
      lambdaMultiply i W=0 ∧
      positiveFiniteImage T hf K (levelQuotientShiftIso T.X 1 K) (V-S) V b=
        W ≫ XModLambdaN.incl _ K+
          homotopyRegrade (show (t+q)-(s+q+1)=V-S by dsimp [S,V]; omega) rfl
            (finiteTopLabelAtWeight T.Y (q-i) (by omega) K (by dsimp [K]; omega)
              (s+q+1) (t+q) (V+1) (by dsimp [V]; omega) v) := by
  dsimp only
  obtain ⟨a,has,hai⟩ := higher_bottom_with_fixed_rotated_root
    T he hT hf hg hh i q hi hiq s t z u v hd hR hH εa hεa R hRfirst hRtop
  let vShort := homotopyRegrade
    (show (t+q)-(s+q+1)=(t+i-1)-(s+i) by omega) rfl
    (finiteTopLabelAtWeight T.Y (q-i) (by omega) ((q+1)-i) (by omega)
      (s+q+1) (t+q) ((t+i-1)+1) (by omega) v)
  have hv₀ := higher_coefficient_top T.Y q i hiq (s+q+1) (t+q) ((t+i-1)+1) (by omega) v
  have hv₁ := congrArg (homotopyRegrade
    (show (t+q)-(s+q+1)=(t+i-1)-(s+i) by omega)
    (show ((t+i-1)+1)-i=((t+i-1)-i)+1 by omega)) hv₀
  have hv : homotopyRegrade rfl (show ((t+i-1)+1)-i=((t+i-1)-i)+1 by omega)
      (finiteCoefficientShiftClass _ (q+1) i (by omega) ((t+i-1)-(s+i)) ((t+i-1)+1) vShort)=
      homotopyRegrade (show (t+q)-(s+q+1)=(t+i-1)-(s+i) by omega)
        (show (t+q)-q=((t+i-1)-i)+1 by omega) (finiteTopLabel T.Y q (by omega) (s+q+1) (t+q) v) := by
    simpa only [vShort,coefficient_shift_regrade,finiteTopLabelAtWeight,last_layer_regrade_trans] using hv₁
  obtain ⟨b,u',aHat,W,_,hb,hu,hW,hW0,hbi⟩ := early_positive_top_division_and_torsion
    T hf (q+1) i hi (by omega) (s+i) (t+i-1) u a has vShort (hai.trans hv.symm)
  exact ⟨b,u',aHat,W,hb,hu,hW,hW0,hbi⟩

private theorem higher_whole_h_image_suspended_boundary
    (T : TriangleData background.auxiliary) (a : ℕ) (S V : ℤ)
    (hH : ∀ z : Ambient background T.Z (S,V+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T S V z ∈
        boundaries background T.X a (S,V)) :
    ∀ z : Ambient background T.Z (S,V+1),
      (background.classical.map T.h).pageMap 2 (S,V+1) z ∈
        boundaries background (.shift 1 T.X) a (S,V+1) := by
  intro z
  have hz := KIP126.ProofTools.Standard.classicalTriangleHMapHom_spec T S V z
  apply (desuspendsClass_boundary_iff T.X a S (V+1) _ _ hz).mpr
  have hc := hH z
  have transport (v v' : ℤ) (hv : v=v') (x : Ambient background T.X (S,v))
      (e : (Ambient background T.X (S,v') : Type)=(Ambient background T.X (S,v) : Type))
      (hx : x ∈ boundaries background T.X a (S,v)) :
      e.mpr x ∈ boundaries background T.X a (S,v') := by
    subst v'
    cases e
    exact hx
  exact transport V (V+1-1) (by omega) _ _ hc


/-- Higher early-boundary comparison in the positive-first-arrow branch.
The early differential, root differential, and full R_j/R_last spaces
construct the same finite source and an actual absolute-boundary torsion
correction. -/
private theorem higher_positive_compatible_finite_lift
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (i q : ℕ) (hi : 0 < i) (hiq : i < q) (s t : ℤ)
    (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (s+i,t+i-1))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) ((background.classical.map T.g).pageMap 2 (s,t) c) ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) (s,t) (s+i+1,t+i) c
      (boundaryLabelRegrade rfl (show (t+i-1)+1=t+i by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+i) (t+i-1) u)))
    (hR : ∀ p : ℤ, s+1≤p → p<s+(i+1)-1 →
      ∀ z : Ambient background T.Z (p,t-s+p), z ∈ cycles background T.Z ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) →
      ∃ y : Ambient background T.Y (p,t-s+p), y ∈ cycles background T.Y ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background T.Z (p,t-s+p), k ∈ cycles background T.Z (q+1-(p-s).toNat:ℕ) (p,t-s+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,t-s+p) y-k ∈
          boundaries background T.Z ((p-s).toNat+1) (p,t-s+p))
    (hH : ∀ z : Ambient background T.Z (s+i,(t+i-1)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+i) (t+i-1) z ∈
        boundaries background T.X (i+1) (s+i,t+i-1)) :
    let S : ℤ := s+i
    let V : ℤ := t+i-1
    let K : ℕ := (q+1)-i
    ∃ b : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) K),
    ∃ u' : Ambient background T.X (S,V),
    ∃ aHat : BiHom ((V-S)+1) ((V+1)-i)
        (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) i),
    ∃ W : BiHom (V-S) (V+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      b ≫ (background.quotients.tower _).rho 1 K (by dsimp [K]; omega)=nativeFirstLabel T.X S V u' ∧
      u'-u ∈ boundaries background T.X (i+1) (S,V) ∧
      W=homotopyRegrade (show ((V-S)+1)-1=V-S by omega)
        (show ((V+1)-i)+i=V+1 by omega)
        (biSuspensionHomEquiv ((V-S)+1) ((V+1)-i) i
          (background.nu.functor.obj (T.Y.obj background.auxiliary)) (aHat ≫ XModLambdaN.proj _ i)) ∧
      lambdaMultiply i W=0 ∧
      positiveFiniteImage T hf K (levelQuotientShiftIso T.X 1 K) (V-S) V b=
        W ≫ XModLambdaN.incl _ K+
          homotopyRegrade (show (t+q)-(s+q+1)=V-S by dsimp [S,V]; omega) rfl
            (finiteTopLabelAtWeight T.Y (q-i) (by omega) K (by dsimp [K]; omega)
              (s+q+1) (t+q) (V+1) (by dsimp [V]; omega) v) := by
  have hH' : ∀ z : Ambient background T.Z (s+(i+1)-1,t+(i+1)-1),
      (background.classical.map T.h).pageMap 2 (s+(i+1)-1,t+(i+1)-1) z ∈
        boundaries background (.shift 1 T.X) (i+1) (s+(i+1)-1,t+(i+1)-1) := by
    have hp : s+(i+1)-1=s+i := by omega
    have ht : t+(i+1)-1=(t+i-1)+1 := by omega
    rw [hp,ht]
    exact higher_whole_h_image_suspended_boundary T (i+1) (s+i) (t+i-1) hH
  letI := background.exactness.shiftCommShift (1,1)
  letI := background.exactness.shiftExact (1,1)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,1) (i+1)
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  obtain ⟨R,hRfirst,hRtop⟩ := higher_positive_rotated_first_and_top
    T he hT hf hg i hi ε hε s t c u hearly
  exact higher_compatible_positive_finite_lift_of_rotated_root T he hT hf hg hh i q hi hiq s t
    ((background.classical.map T.g).pageMap 2 (s,t) c) u v hd hR hH' ε hε R hRfirst hRtop

end
end KIP126.ProofTools.Internal.SyntheticCoverage
