module

public import KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch

public import KIP126.ProofTools.MahowaldLeibniz.PositiveBranches

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.MiddleElimination
import all KIP126.ProofTools.SyntheticCoverage.TerminalComparison
import all KIP126.ProofTools.SyntheticCoverage.RawImageComparison
import all KIP126.ProofTools.SyntheticCoverage.OrdinaryTerminal
import all KIP126.ProofTools.GeneralizedMahowald.PageCalculus
import all KIP126.ProofTools.MahowaldLeibniz.ClassicalComposition
import KIP126.Literature.E2Exactness

/-! Actual-page steps for the synthetic differential criteria.

The differential criteria use actual common finite representatives, retain
the H-image terms, and compare prescribed targets through the restricted
kernel. Separate specializations treat all three exponent positions when
middle errors are boundaries. In the source
document Z_<q and B_<q use the level q-1 below.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

/-- Changing either E₂ representative by a true earlier boundary preserves
both actual page classes, hence the specified differential. -/
private theorem differential_of_earlier_boundaries
    (X : (AdamsObject (coefficients := background.coefficients))) (r a b : ℤ) (p q : ℤ × ℤ)
    (x x' : Ambient background X p) (y y' : Ambient background X q)
    (hd : DifferentialAt background X r p q x y)
    (ha : a ≤ r-1) (hb : b ≤ r-1)
    (hx : x'-x ∈ boundaries background X a p)
    (hy : y'-y ∈ boundaries background X b q) :
    DifferentialAt background X r p q x' y' := by
  obtain ⟨hr,hdeg,xr,yr,hxr,hyr,hxy⟩ := hd
  refine ⟨hr,hdeg,xr,yr,?_,?_,hxy⟩
  · exact representsOnPage_of_congruent background X hr hxr
      ⟨by omega,boundaries_monotone background X p ha hx⟩
  · exact representsOnPage_of_congruent background X hr hyr
      ⟨by omega,boundaries_monotone background X q hb hy⟩

/-- The output includes the cycle qualifications for both literal labels;
zero classes and boundary labels remain allowed. -/
private theorem cycles_of_differential
    (X : (AdamsObject (coefficients := background.coefficients))) (r : ℤ) (p q : ℤ × ℤ)
    (x : Ambient background X p) (y : Ambient background X q)
    (hd : DifferentialAt background X r p q x y) :
    IsCycle background X (r-1) p x ∧ IsCycle background X (r-1) q y := by
  obtain ⟨hr,hdeg,xr,yr,hxr,hyr,hxy⟩ := hd
  exact ⟨(isCycle_iff_reaches background X r hr p x).mpr ⟨xr,hxr⟩,
    (isCycle_iff_reaches background X r hr q y).mpr ⟨yr,hyr⟩⟩

/-- Vanishing of E₃ gives inclusion of the entire intermediate cycle
space in the boundary space required by the differential criteria. -/
private theorem middle_boundaries_of_third_page_vanishes
    (X : (AdamsObject (coefficients := background.coefficients))) (p : ℤ × ℤ) (K j : ℕ)
    (hj : 1 ≤ j) (hjK : j ≤ K-2)
    [Subsingleton ((background.classical.obj (X.obj background.auxiliary)).Page 3 p)] :
    cycles background X ((K:ℤ)-j) p ≤ boundaries background X ((j:ℤ)+1) p := by
  intro a ha
  have ha2 : IsCycle background X 2 p a :=
    ⟨by omega,cycles_antitone background X p (by omega) ha⟩
  obtain ⟨ar,har⟩ := (isCycle_iff_reaches background X 3 (by omega) p a).mp ha2
  have har0 : RepresentsOnPage (background.classical.obj (X.obj background.auxiliary)) 3 p a 0 := by
    simpa only [Subsingleton.elim ar 0] using har
  exact boundaries_monotone background X p (by omega)
    (represents_zero_mem_boundary background X 3 p a har0)

/-- The final restricted-kernel comparison for the differential criteria,
using the constructed differential with target w and the final error e. -/
private theorem differential_target_of_restricted_kernel
    (Y Z : (AdamsObject (coefficients := background.coefficients))) (g : Y.obj background.auxiliary ⟶ Z.obj background.auxiliary)
    (r : ℤ) (p q : ℤ × ℤ)
    (x : Ambient background Y p) (w v e : Ambient background Y q)
    (P : Submodule ℤ (Ambient background Y q))
    (hd : DifferentialAt background Y r p q x w)
    (hw : w ∈ P) (hv : v ∈ P)
    (hBP : boundaries background Y (r-1) q ≤ P)
    (herror : w-v-e ∈ boundaries background Y (r-1) q)
    (he : (background.classical.map g).pageMap 2 q e = 0)
    (hker : ∀ a ∈ P, (background.classical.map g).pageMap 2 q a = 0 →
      a ∈ boundaries background Y (r-1) q) :
    DifferentialAt background Y r p q x v := by
  have heP : e ∈ P := by
    have hh := P.sub_mem (P.sub_mem hw hv) (hBP herror)
    convert hh using 1; abel
  have hev := (boundaries background Y (r-1) q).add_mem herror (hker e heP he)
  have hdiff : w-v ∈ boundaries background Y (r-1) q := by
    simpa only [sub_add_cancel] using hev
  exact differentialAt_of_congruent background Y hd ⟨by have := hd.1; omega,by
    simpa only [neg_sub] using (boundaries background Y (r-1) q).neg_mem hdiff⟩

/-- Positive-first-arrow differential criterion: all middle errors and
the final g₂ kernel lie in the specified early-boundary subspaces of Adams E₂. -/
private theorem differential_of_middle_boundaries_and_full_kernel
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (R K : ℕ) (hR : 2 ≤ R) (hK : 2 ≤ K) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (u : Ambient background T.X (s+R,t+R-1))
    (z : Ambient background T.Z (s+R,t+R))
    (v : Ambient background T.Y (s+R+K,t+R+K-1))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+R) (t+R)
      ((background.classical.map T.h).pageMap 2 (s+R,t+R) z) u)
    (hdx : DifferentialAt background T.X R (s,t) (s+R,t+R-1) x u)
    (hdz : DifferentialAt background T.Z K (s+R,t+R) (s+R+K,t+R+K-1) z
      ((background.classical.map T.g).pageMap 2 (s+R+K,t+R+K-1) v))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < K-1 →
      cycles background T.X ((K:ℤ)-j) (s+R+j,t+R+j-1) ≤
        boundaries background T.X ((j:ℤ)+1) (s+R+j,t+R+j-1))
    (hker : ∀ a : Ambient background T.Y (s+R+K,t+R+K-1),
      (background.classical.map T.g).pageMap 2 (s+R+K,t+R+K-1) a = 0 →
      a ∈ boundaries background T.Y ((R:ℤ)+K-2) (s+R+K,t+R+K-1)) :
    let y := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x
    IsCycle background T.Y ((R:ℤ)+K-2) (s+1,t+1) y ∧
      IsCycle background T.Y ((R:ℤ)+K-2) (s+R+K,t+R+K-1) v ∧
      DifferentialAt background T.Y ((R:ℤ)+K-1) (s+1,t+1)
        (s+R+K,t+R+K-1) y v := by
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  have hresult := KIP126.ProofTools.Internal.MahowaldLeibniz.pdf_conditions_classical_corollary_RK
    T (by simp [hf,hg,hh]) hT hf hg hh R K hR hK s t x u z v hu hdx hdz
    (fun j hj hjK => (hmid j hj hjK).trans
      (boundaries_monotone background T.X _ (by omega)))
  have hlast : ∀ a : Ambient background T.X (s+R+K-1,t+R+K-2),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf
        (s+R+K-1) (t+R+K-2) a ∈
      boundaries background T.Y ((R:ℤ)+K-2)
        ((s+R+K-1)+1,(t+R+K-2)+1) := by
    intro a
    have hz := (KIP126.Literature.Standard.E2Exactness.e2ExactAtY
      T hf hg hh (s+R+K-1) (t+R+K-2)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf
        (s+R+K-1) (t+R+K-2) a)).mpr ⟨a,rfl⟩
    have hker' (p : ℤ × ℤ) (hp : p = (s+R+K,t+R+K-1)) :
        ∀ a : Ambient background T.Y p,
          (background.classical.map T.g).pageMap 2 p a = 0 →
          a ∈ boundaries background T.Y ((R:ℤ)+K-2) p := by
      subst p
      exact hker
    exact hker' _ (by ext <;> dsimp <;> omega) _ hz
  obtain ⟨hy,hd⟩ := hresult hlast
  refine ⟨hy,?_,hd⟩
  simpa only [show (R:ℤ)+K-1-1=(R:ℤ)+K-2 by omega] using
    (cycles_of_differential T.Y _ _ _ _ _ hd).2

/-- Page-class differential criterion with H-image and output source
congruent to the specified target and F₂x modulo `B_<R`. -/
private theorem differential_of_page_classes_and_full_kernel
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (R K : ℕ) (hR : 2 ≤ R) (hK : 2 ≤ K) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u u' : Ambient background T.X (s+R,t+R-1))
    (y : Ambient background T.Y (s+1,t+1))
    (z : Ambient background T.Z (s+R,t+R))
    (v : Ambient background T.Y (s+R+K,t+R+K-1))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+R) (t+R)
      ((background.classical.map T.h).pageMap 2 (s+R,t+R) z) u')
    (huu : u'-u ∈ boundaries background T.X ((R:ℤ)-1) (s+R,t+R-1))
    (hyy : y-KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈
      boundaries background T.Y ((R:ℤ)-1) (s+1,t+1))
    (hdx : DifferentialAt background T.X R (s,t) (s+R,t+R-1) x u)
    (hdz : DifferentialAt background T.Z K (s+R,t+R) (s+R+K,t+R+K-1) z
      ((background.classical.map T.g).pageMap 2 (s+R+K,t+R+K-1) v))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < K-1 →
      cycles background T.X ((K:ℤ)-j) (s+R+j,t+R+j-1) ≤
        boundaries background T.X ((j:ℤ)+1) (s+R+j,t+R+j-1))
    (hker : ∀ a : Ambient background T.Y (s+R+K,t+R+K-1),
      (background.classical.map T.g).pageMap 2 (s+R+K,t+R+K-1) a = 0 →
      a ∈ boundaries background T.Y ((R:ℤ)+K-2) (s+R+K,t+R+K-1)) :
    IsCycle background T.Y ((R:ℤ)+K-2) (s+1,t+1) y ∧
      IsCycle background T.Y ((R:ℤ)+K-2) (s+R+K,t+R+K-1) v ∧
      DifferentialAt background T.Y ((R:ℤ)+K-1) (s+1,t+1)
        (s+R+K,t+R+K-1) y v := by
  have hdx' : DifferentialAt background T.X R (s,t) (s+R,t+R-1) x u' :=
    differentialAt_of_congruent background T.X hdx ⟨by omega,huu⟩
  obtain ⟨_,_,hd⟩ := differential_of_middle_boundaries_and_full_kernel
    T hf hg hh R K hR hK s t x u' z v hu hdx' hdz hmid hker
  have hd' := differential_of_earlier_boundaries T.Y ((R:ℤ)+K-1)
    ((R:ℤ)-1) ((R:ℤ)-1) (s+1,t+1) (s+R+K,t+R+K-1)
    _ y v v hd (by omega) (by omega) hyy
    (by simpa only [sub_self] using (boundaries background T.Y ((R:ℤ)-1)
      (s+R+K,t+R+K-1)).zero_mem)
  have hc := cycles_of_differential T.Y _ _ _ _ _ hd'
  refine ⟨?_,?_,hd'⟩
  · simpa only [show (R:ℤ)+K-1-1=(R:ℤ)+K-2 by omega] using hc.1
  · simpa only [show (R:ℤ)+K-1-1=(R:ℤ)+K-2 by omega] using hc.2

/-- Ordinary E₂ maps of consecutive arrows have zero composite by the
first-quotient comparison. -/
private theorem ordinary_triangle_composite_zero
    (T : TriangleData background.auxiliary) (s t : ℤ)
    (a : Ambient background T.X (s,t)) :
    (background.classical.map T.g).pageMap 2 (s,t)
      ((background.classical.map T.f).pageMap 2 (s,t) a) = 0 := by
  letI := background.nu.additive
  have hfg : T.f ≫ T.g = 0 :=
    CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂ _ T.distinguished
  apply KIP126.ProofTools.Internal.MahowaldLeibniz.native_first_label_injective T.Z s t
  rw [←KIP126.ProofTools.Internal.MahowaldLeibniz.native_first_label_natural,
    ←KIP126.ProofTools.Internal.MahowaldLeibniz.native_first_label_natural,
    Category.assoc,quotient_map_comp_zero (background.nu.functor.map T.f)
      (background.nu.functor.map T.g) (by
        rw [←Functor.map_comp,hfg,Functor.map_zero]) 1,CategoryTheory.Limits.comp_zero]
  rw [KIP126.ProofTools.Internal.MahowaldLeibniz.nativeFirstLabel_eq_regrade,
    map_zero,KIP126.ProofTools.Internal.MahowaldLeibniz.last_layer_regrade_zero,
    CategoryTheory.Limits.zero_comp]

/-- The same complete full-kernel criterion when the positive exponent is
on the connecting arrow. The positive H₂ relation is the one obtained from
the selected normalized map, and its suspension comparison is retained. -/
private theorem differential_of_middle_boundaries_and_full_kernel_third
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
    (R K : ℕ) (hR : 2 ≤ R) (hK : 2 ≤ K) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (u : Ambient background T.X (s+R,t+R-1))
    (z : Ambient background T.Z (s+R-1,t+R-1))
    (v : Ambient background T.Y (s+R+K-1,t+R+K-2))
    (w : Ambient background (.shift 1 T.X) (s+R,t+R))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+R) (t+R) w u)
    (hw : KIP126.ProofTools.Internal.MahowaldLeibniz.PositiveHLabelRelated
      T hh (s+R-1) (t+R-1) z w)
    (hdx : DifferentialAt background T.X R (s,t) (s+R,t+R-1) x u)
    (hdz : DifferentialAt background T.Z K (s+R-1,t+R-1)
      (s+R+K-1,t+R+K-2) z
      ((background.classical.map T.g).pageMap 2 (s+R+K-1,t+R+K-2) v))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < K-1 →
      cycles background T.X ((K:ℤ)-j) (s+R+j,t+R+j-1) ≤
        boundaries background T.X ((j:ℤ)+1) (s+R+j,t+R+j-1))
    (hker : ∀ a : Ambient background T.Y (s+R+K-1,t+R+K-2),
      (background.classical.map T.g).pageMap 2 (s+R+K-1,t+R+K-2) a = 0 →
      a ∈ boundaries background T.Y ((R:ℤ)+K-2) (s+R+K-1,t+R+K-2)) :
    let y := (background.classical.map T.f).pageMap 2 (s,t) x
    IsCycle background T.Y ((R:ℤ)+K-2) (s,t) y ∧
      IsCycle background T.Y ((R:ℤ)+K-2) (s+R+K-1,t+R+K-2) v ∧
      DifferentialAt background T.Y ((R:ℤ)+K-1) (s,t)
        (s+R+K-1,t+R+K-2) y v := by
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨hy,hd⟩ :=
    KIP126.ProofTools.Internal.MahowaldLeibniz.positive_h_pdf_classical_corollary_RK
      T (by simp [hf,hg,hh]) hT hf hg hh R K hR hK s t x u z v w hu hw hdx hdz
      (fun j hj hjK => (hmid j hj hjK).trans
        (boundaries_monotone background T.X _ (by omega)))
      (fun a => hker _ (ordinary_triangle_composite_zero T _ _ a))
  refine ⟨hy,?_,hd⟩
  simpa only [show (R:ℤ)+K-1-1=(R:ℤ)+K-2 by omega] using
    (cycles_of_differential T.Y _ _ _ _ _ hd).2

/-- Every actual boundary label is a permanent-cycle label; the represented
limiting class may of course be zero. -/
private theorem boundary_mem_permanent_cycles
    (X : (AdamsObject (coefficients := background.coefficients))) (b : ℤ) (p : ℤ × ℤ)
    (a : Ambient background X p) (ha : a ∈ boundaries background X b p) :
    a ∈ permanentCycles background X p := by
  obtain ⟨z,rfl⟩ := ha
  let E := (background.classical.obj (X.obj background.auxiliary)).ssData p
  let h : E.B (↑(b-1).toNat) ≤ E.Z ⊤ :=
    (E.B_mono le_top).trans (E.B_le_Z ⊤)
  refine ⟨(Subobject.ofLE _ _ h) z,?_⟩
  change (Subobject.ofLE _ _ h ≫ cycleLabel background X ⊤ p) z = _
  simp only [cycleLabel,boundaryLabel,E,←Category.assoc,Subobject.ofLE_comp_ofLE]

/-- The target of the constructed differential satisfies its permanence qualification. -/
private theorem differential_target_mem_permanent_cycles
    (X : (AdamsObject (coefficients := background.coefficients))) (r : ℤ) (p q : ℤ × ℤ)
    (x : Ambient background X p) (w : Ambient background X q)
    (hd : DifferentialAt background X r p q x w) :
    w ∈ permanentCycles background X q := by
  have hzero := FinitePageCalculus.differential_target_later_zero
    (by simpa only [background.classical.firstPage] using hd.1)
    (show r < r+1 by omega) hd.2
  exact boundary_mem_permanent_cycles X ((r+1)-1) q w
    (represents_zero_mem_boundary background X (r+1) q w hzero)

/-- Full terminal comparison for the original candidate-space hypothesis:
P only has to contain permanent cycles. The constructed differential target
and all true earlier boundaries lie in P, before its whole
kernel is used to remove the actual last-layer error. -/
private theorem differential_target_of_permanent_candidate_kernel
    (Y Z : (AdamsObject (coefficients := background.coefficients))) (g : Y.obj background.auxiliary ⟶ Z.obj background.auxiliary)
    (r : ℤ) (p q : ℤ × ℤ)
    (x : Ambient background Y p) (w v e : Ambient background Y q)
    (P : Submodule ℤ (Ambient background Y q))
    (hP : permanentCycles background Y q ≤ P)
    (hd : DifferentialAt background Y r p q x w)
    (hv : v ∈ P)
    (herror : w-v-e ∈ boundaries background Y (r-1) q)
    (he : (background.classical.map g).pageMap 2 q e = 0)
    (hker : ∀ a ∈ P, (background.classical.map g).pageMap 2 q a = 0 →
      a ∈ boundaries background Y (r-1) q) :
    DifferentialAt background Y r p q x v := by
  exact differential_target_of_restricted_kernel Y Z g r p q x w v e P hd
    (hP (differential_target_mem_permanent_cycles Y r p q x w hd)) hv
    (fun a ha => hP (boundary_mem_permanent_cycles Y (r-1) q a ha))
    herror he hker

/-- In the positive-second-arrow branch the positive G₂ operation kills
ordinary F₂. The proof keeps the negative-weight realization of G and then
reflects zero through its invertible shift comparisons. -/
private theorem positive_second_triangle_composite_zero
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (s t : ℤ) (a : Ambient background T.X (s,t)) :
    KIP126.ProofTools.Internal.MahowaldLeibniz.positiveFirstQuotientOperation
      T.Y T.Z (KIP126.ProofTools.Internal.MahowaldLeibniz.normalizedSecondPositiveMap T hg)
      s t ((background.classical.map T.f).pageMap 2 (s,t) a) = 0 := by
  let he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1 := by simp [hf,hg,hh]
  let N := normalizedTriangle background T he
  let G := KIP126.ProofTools.Internal.MahowaldLeibniz.normalizedSecondPositiveMap T hg
  let Xν := background.nu.functor.obj (T.X.obj background.auxiliary)
  let eX : N.obj₁ ≅ Xν :=
    eqToIso (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj Xν) hf) ≪≫
      SyntheticCategory.biShift_zero.app Xν
  have hfmap : eX.hom ≫ background.nu.functor.map T.f = N.mor₁ := by
    simpa only [eX,Iso.trans_hom,Iso.app_hom,Category.assoc,N,normalizedTriangle,
      CategoryTheory.Pretriangulated.Triangle.mk,Xν,eqToIso.hom] using
      (normalized_zero_map T.X T.Y T.f hf).symm
  have hgf : background.nu.functor.map T.f ≫ negativeLift 1 G = 0 := by
    apply (cancel_epi eX.hom).mp
    rw [←Category.assoc,hfmap]
    rw [←KIP126.ProofTools.Internal.MahowaldLeibniz.normalized_second_arrow_positive
      T he hg,←Category.assoc]
    have hz : N.mor₁ ≫ N.mor₂ = 0 :=
      CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT
    rw [hz,CategoryTheory.Limits.zero_comp,CategoryTheory.Limits.comp_zero]
  have hzero : KIP126.ProofTools.Internal.MahowaldLeibniz.nativeFirstLabel T.Y s t
      ((background.classical.map T.f).pageMap 2 (s,t) a) ≫
        XModLambdaN.map (negativeLift 1 G) 1 = 0 := by
    rw [←KIP126.ProofTools.Internal.MahowaldLeibniz.native_first_label_natural,
      Category.assoc,quotient_map_comp_zero _ _ hgf 1,CategoryTheory.Limits.comp_zero]
  have hlabel := KIP126.ProofTools.Internal.MahowaldLeibniz.positive_operation_negative_lift_label
    T.Y T.Z G s t ((background.classical.map T.f).pageMap 2 (s,t) a)
  rw [hzero] at hlabel
  apply KIP126.ProofTools.Internal.MahowaldLeibniz.native_first_label_injective T.Z (s+1) (t+1)
  apply shift_class_injective (.quotient 1 (.nu T.Z)) (0,-1) (t+1-(s+1),t+1)
  apply KIP126.ProofTools.Internal.MahowaldLeibniz.homotopy_regrade_injective (m' := t-s) (w' := t) (by dsimp; omega) (by dsimp; omega)
  apply (cancel_mono (KIP126.ProofTools.Internal.Leibniz.levelQuotientShiftIso T.Z (-1) 1).inv).mp
  refine hlabel.symm.trans ?_
  rw [KIP126.ProofTools.Internal.MahowaldLeibniz.nativeFirstLabel_eq_regrade,
    map_zero,KIP126.ProofTools.Internal.MahowaldLeibniz.last_layer_regrade_zero,
    CategoryTheory.Limits.zero_comp]
  simp only [shiftHomotopyClass,Functor.map_zero,CategoryTheory.Limits.comp_zero,
    KIP126.ProofTools.Internal.MahowaldLeibniz.last_layer_regrade_zero,
    CategoryTheory.Limits.zero_comp]

/-- The complete full-kernel criterion in the remaining positive-second-
arrow branch. The kernel is taken for the normalized degree-(1,1) G₂,
not for the unshifted ordinary page map. -/
private theorem differential_of_middle_boundaries_and_full_kernel_second
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (R K : ℕ) (hR : 2 ≤ R) (hK : 2 ≤ K) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (u : Ambient background T.X (s+R,t+R-1))
    (z : Ambient background T.Z (s+R,t+R))
    (v : Ambient background T.Y (s+R+K-1,t+R+K-2))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+R) (t+R)
      ((background.classical.map T.h).pageMap 2 (s+R,t+R) z) u)
    (hdx : DifferentialAt background T.X R (s,t) (s+R,t+R-1) x u)
    (hdz : DifferentialAt background T.Z K (s+R,t+R)
      ((s+R+K-1)+1,(t+R+K-2)+1) z
      (KIP126.ProofTools.Internal.MahowaldLeibniz.positiveFirstQuotientOperation
        T.Y T.Z (KIP126.ProofTools.Internal.MahowaldLeibniz.normalizedSecondPositiveMap T hg)
        (s+R+K-1) (t+R+K-2) v))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < K-1 →
      cycles background T.X ((K:ℤ)-j) (s+R+j,t+R+j-1) ≤
        boundaries background T.X ((j:ℤ)+1) (s+R+j,t+R+j-1))
    (hker : ∀ a : Ambient background T.Y (s+R+K-1,t+R+K-2),
      KIP126.ProofTools.Internal.MahowaldLeibniz.positiveFirstQuotientOperation
        T.Y T.Z (KIP126.ProofTools.Internal.MahowaldLeibniz.normalizedSecondPositiveMap T hg)
        (s+R+K-1) (t+R+K-2) a = 0 →
      a ∈ boundaries background T.Y ((R:ℤ)+K-2) (s+R+K-1,t+R+K-2)) :
    let y := (background.classical.map T.f).pageMap 2 (s,t) x
    IsCycle background T.Y ((R:ℤ)+K-2) (s,t) y ∧
      IsCycle background T.Y ((R:ℤ)+K-2) (s+R+K-1,t+R+K-2) v ∧
      DifferentialAt background T.Y ((R:ℤ)+K-1) (s,t)
        (s+R+K-1,t+R+K-2) y v := by
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨hy,hd⟩ :=
    KIP126.ProofTools.Internal.MahowaldLeibniz.positive_g_pdf_classical_corollary_RK
      T (by simp [hf,hg,hh]) hT hf hg hh R K hR hK s t x u z v hu hdx hdz
      (fun j hj hjK => (hmid j hj hjK).trans
        (boundaries_monotone background T.X _ (by omega)))
      (fun a => hker _ (positive_second_triangle_composite_zero T hf hg hh hT _ _ a))
  refine ⟨hy,?_,hd⟩
  simpa only [show (R:ℤ)+K-1-1=(R:ℤ)+K-2 by omega] using
    (cycles_of_differential T.Y _ _ _ _ _ hd).2

open KIP126.ProofTools.Internal.MahowaldLeibniz

/-- The complete positive-first-arrow criterion with the original H-image
terms in every middle layer and with P equal to the whole terminal E₂ group.
Here the original page parameters are R=c+2 and K=q+1. -/
private theorem differential_of_middle_images_and_full_kernel
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u : Ambient background T.X (s+(c+1)+1,t+(c+1)))
    (z : Ambient background T.Z (s+(c+1)+1,(t+(c+1))+1))
    (v : Ambient background T.Y ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+(c+1)+1) ((t+(c+1))+1)
      ((background.classical.map T.h).pageMap 2 (s+(c+1)+1,(t+(c+1))+1) z) (by simpa using u))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      ((c+1)+1) (s,t) (s+(c+1)+1,t+(c+1)) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+(c+1)+1,(t+(c+1))+1) ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) z
      ((background.classical.map T.g).pageMap 2 ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) v))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X ((s+(c+1)+1)+j,(t+(c+1))+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j)
          ((s+(c+1)+1)+j,(t+(c+1))+j) →
        ∃ z' : Ambient background T.Z ((s+(c+1)+1)+j,(t+(c+1))+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j)
            ((s+(c+1)+1)+j,(t+(c+1))+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T
            ((s+(c+1)+1)+j) ((t+(c+1))+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) ((s+(c+1)+1)+j,(t+(c+1))+j))
    (hker : ∀ a : Ambient background T.Y ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q),
      (background.classical.map T.g).pageMap 2
        ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) a = 0 →
      a ∈ boundaries background T.Y (c+(q+1))
        ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q)) :
    let y := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x
    IsCycle background T.Y (c+(q+1)) (s+1,t+1) y ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s+1,t+1)
        ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  let N := c+(q+1)
  have hN : 0<N := by dsimp [N]; omega
  let S := s+(c+1)+1
  let V := t+(c+1)
  obtain ⟨ex,hex⟩ := quotient_suspension_inclusion_exists
    ((SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (T.X.obj background.auxiliary))) N
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) (q+1)
  obtain ⟨eY,heY⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) N
  letI := background.exactness.shiftCommShift (1,1)
  letI := background.exactness.shiftExact (1,1)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,1) N
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  let d := homotopyRegrade (show t-s=V-S+1 by dsimp [S,V]; omega)
    (show (t+1)+(1:ℕ)=V-c+1 by dsimp [V]; omega)
    (actualNormalizedFirstFiniteBoundary T he hf N hN s t ex x)
  have hd := actual_first_finite_boundary_source_detects T he hf (c+1) N c
    (by omega) hN (by omega) s t x u hdx ex hex ε hε
  letI := background.exactness.shiftCommShift (0,1)
  letI := background.exactness.shiftExact (0,1)
  obtain ⟨εp,hεp,_⟩ := quotient_shift_exists background.quotients.coherence (0,1) N
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  have hlast : ∀ a : Ambient background T.X (S+(q+1:ℕ)-1,V+(q+1:ℕ)-1),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf
        (S+(q+1:ℕ)-1) (V+(q+1:ℕ)-1) a ∈
      boundaries background T.Y (c+(q+1))
        (S+(q+1:ℕ)-1+1,V+(q+1:ℕ)-1+1) := by
    intro a
    have hz := (KIP126.Literature.Standard.E2Exactness.e2ExactAtY
      T hf hg hh (S+(q+1:ℕ)-1) (V+(q+1:ℕ)-1)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf
        (S+(q+1:ℕ)-1) (V+(q+1:ℕ)-1) a)).mpr ⟨a,rfl⟩
    have hker' (p : ℤ × ℤ)
        (hp : p = ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q)) :
        ∀ a : Ambient background T.Y p,
          (background.classical.map T.g).pageMap 2 p a = 0 →
          a ∈ boundaries background T.Y (c+(q+1)) p := by
      subst p
      exact hker
    exact hker' _ (by dsimp [S,V]; ext <;> dsimp <;> omega) _ hz
  have himage := (positive_first_finite_core T he hT hf hg hh c q hq S V
    u z v hu hdz ey hey ε hε).2 (fun a ha =>
      middle_and_last_boundary_annihilation T he hf hg hh hT c (q+1)
        (by omega) S V (fun j hj hjq b hb => by
          obtain ⟨z',hz',hbz⟩ := hmid j hj hjq b hb
          exact ⟨z',hz',boundaries_monotone background T.X _ (by omega) hbz⟩)
        ε hε εp hεp hlast a ha) d hd
  obtain ⟨b,hb,hbimage⟩ := finite_may_signed_target_at_level T.Y c q hq S (V+1)
    v ey eY hey heY
  apply normalized_boundary_image_decode_general T hf N hN s t (S+q+1) ((V+1)+q)
    ((V+1)-S) ((V+1)-c) (by dsimp [S,N]; omega) (by dsimp [V,N]; omega)
    (by dsimp [S,V]; omega) (by dsimp [V]; omega) x v ex eY hex heY b hb
  apply homotopy_regrade_injective (show t-s=V-S+1 by dsimp [S,V]; omega)
    (show (t+1)+(1:ℕ)=V-c+1 by dsimp [V]; omega)
  have hi := congrArg (fun a => a ≫ eY.hom) himage
  simp only [←homotopyRegrade_comp] at hi
  dsimp only [normalizedTriangle,Triangle.mk] at hi
  rw [hbimage] at hi
  simp only [d,actualNormalizedFirstFiniteBoundary,←homotopyRegrade_comp,Category.assoc] at hi
  have hnorm := positive_normalized_source_inv_arrow T he hf
  dsimp only [normalizedTriangle,Triangle.mk] at hnorm
  rw [←Category.assoc _ (XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (background.normalizedMap T.X T.Y T.f).map) N),
    ←background.quotients.functoriality.map_comp,←Functor.map_comp,
    hnorm] at hi
  simpa only [homotopyRegrade_comp,normalized_homotopy_regrade_trans,Category.assoc] using hi
/-- The common finite May representative and the prescribed first boundary
can differ by a last-filtration residual after all original H-image terms
have been removed. The equality retains its actual map and target label. -/
private theorem positive_first_common_last_residual
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
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (hε : XModLambdaN.incl _ (c+(q+1)) ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (c+(q+1))))
    (ey : XModLambdaN ((background.nu.functor.obj (T.Y.obj background.auxiliary))⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (q+1))⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)))
    (eY : XModLambdaN ((background.nu.functor.obj (T.Y.obj background.auxiliary))⟦(1:ℤ)⟧) (c+(q+1)) ≅
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (c+(q+1)))⟦(1:ℤ)⟧)
    (heY : XModLambdaN.incl _ (c+(q+1)) ≫ eY.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (c+(q+1))))
    (d : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+(q+1))))
    (hd : Detects (background.convergence (.quotient (c+(q+1)) (.nu T.X)))
      (S,V,V-c) (finiteTargetLabel background T.X (c+(q+1)) S V c u)
      (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε d)) :
    ∃ a e : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      FiltrationAtLeast background.syntheticTower (S+q)
        (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε e) ∧
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+(q+1)) ≫ eY.hom =
        homotopyRegrade (show (V+1)-S=V-S+1 by omega)
          (show (V+1)-c=V-c+1 by omega)
          (ordinarySuspendedRepresentative _ ((V+1)-S) ((V+1)-c)
            (finiteMayTopLabel T.Y c q hq S (V+1) v)) ∧
      e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+(q+1)) =
      (d-a) ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+(q+1)) := by
  obtain ⟨a,ha,hi,_⟩ := (positive_first_finite_core
    T he hT hf hg hh c q hq S V u z v hu hdz ey hey ε hε).1
  have hdiff := detects_sub_filtration
    (background.convergence (.quotient (c+(q+1)) (.nu T.X))) (S,V,V-c) hd ha
  rw [←raw_may_source_desuspend_sub] at hdiff
  have hraw := raw_may_source_desuspend_reflects_filtration
    T he hf (c+(q+1)) c S V (S+1) ε (d-a) hdiff
  obtain ⟨e,hefil,heimage⟩ := middle_normalized_residual_same_image
    T he hf hg hh hT c (q+1) (by omega) S V
    (fun j hj hjq b hb => by
      obtain ⟨z',hz',hbz⟩ := hmid j hj hjq b hb
      exact ⟨z',hz',boundaries_monotone background T.X _ (by omega) hbz⟩) (d-a) hraw
  refine ⟨a,e,?_,?_,heimage⟩
  · have hfil := raw_may_source_desuspend_preserves_filtration
      T he hf (c+(q+1)) c S V (S+(q+1:ℕ)-1) ε e hefil
    simpa only [Nat.cast_add,Nat.cast_one,show S+((q:ℤ)+1)-1=S+q by omega] using hfil
  · have hc := congrArg (fun a => a ≫ eY.hom) hi
    rw [←homotopyRegrade_comp] at hc
    have htop := finite_may_signed_target_eq_top_at_level T.Y c q hq S (V+1)
      v ey eY hey heY
    simpa only [Category.assoc] using hc.trans (congrArg (homotopyRegrade
      (show (V+1)-S=V-S+1 by omega) (show (V+1)-c=V-c+1 by omega)) htop)

private theorem ordinary_suspended_representative_regrade
    (A : SyntheticSpectrum) (m m' w w' : ℤ) (hm : m=m') (hw : w=w')
    (a : BiHom (m-1) w A) :
    homotopyRegrade hm hw (ordinarySuspendedRepresentative A m w a) =
      ordinarySuspendedRepresentative A m' w'
        (homotopyRegrade (show m-1=m'-1 by omega) hw a) := by
  subst m'
  subst w'
  rfl


/-- The original positive-first-arrow criterion with every H-image middle
condition and an arbitrary candidate subspace containing permanent cycles.
The actual last error is constructed before the restricted kernel is used. -/
public theorem differential_of_middle_images_and_candidate_kernel
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u : Ambient background T.X (s+(c+1)+1,t+(c+1)))
    (z : Ambient background T.Z (s+(c+1)+1,(t+(c+1))+1))
    (v : Ambient background T.Y ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+(c+1)+1) ((t+(c+1))+1)
      ((background.classical.map T.h).pageMap 2 (s+(c+1)+1,(t+(c+1))+1) z) (by simpa using u))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      ((c+1)+1) (s,t) (s+(c+1)+1,t+(c+1)) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+(c+1)+1,(t+(c+1))+1) ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) z
      ((background.classical.map T.g).pageMap 2 ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) v))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X ((s+(c+1)+1)+j,(t+(c+1))+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j)
          ((s+(c+1)+1)+j,(t+(c+1))+j) →
        ∃ z' : Ambient background T.Z ((s+(c+1)+1)+j,(t+(c+1))+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j)
            ((s+(c+1)+1)+j,(t+(c+1))+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T
            ((s+(c+1)+1)+j) ((t+(c+1))+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) ((s+(c+1)+1)+j,(t+(c+1))+j))
    (P : Submodule ℤ (Ambient background T.Y
      ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q)))
    (hP : permanentCycles background T.Y
      ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ a ∈ P,
      (background.classical.map T.g).pageMap 2
        ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) a = 0 →
      a ∈ boundaries background T.Y (c+(q+1))
        ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q)) :
    let y := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x
    IsCycle background T.Y (c+(q+1)) (s+1,t+1) y ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s+1,t+1)
        ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  let N := c+(q+1)
  have hN : 0<N := by dsimp [N]; omega
  let S := s+(c+1)+1
  let V := t+(c+1)
  obtain ⟨ex,hex⟩ := quotient_suspension_inclusion_exists
    ((SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (T.X.obj background.auxiliary))) N
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) (q+1)
  obtain ⟨eY,heY⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) N
  letI := background.exactness.shiftCommShift (1,1)
  letI := background.exactness.shiftExact (1,1)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,1) N
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  let d := homotopyRegrade (show t-s=V-S+1 by dsimp [S,V]; omega)
    (show (t+1)+(1:ℕ)=V-c+1 by dsimp [V]; omega)
    (actualNormalizedFirstFiniteBoundary T he hf N hN s t ex x)
  have hd := actual_first_finite_boundary_source_detects T he hf (c+1) N c
    (by omega) hN (by omega) s t x u hdx ex hex ε hε
  letI := background.exactness.shiftCommShift (0,1)
  letI := background.exactness.shiftExact (0,1)
  obtain ⟨εp,hεp,_⟩ := quotient_shift_exists background.quotients.coherence (0,1) N
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  obtain ⟨a,e,hefil,haimage,heimage⟩ := positive_first_common_last_residual
    T he hT hf hg hh c q hq S V u z v hu hdz hmid ε hε ey hey eY heY d hd
  obtain ⟨e₂,error,herror,herrorTop⟩ := last_layer_positive_image_eq_finite_may_top
    T hf c q hq S V εp hεp (rawMaySourceDesuspend T he hf N c S V ε e) hefil
  have herrorRaw := native_positive_image_eq_finite_may_top
    T he hf c q hq S V ε εp hε hεp eY heY e error herrorTop
  rw [←ordinary_suspended_representative_regrade _ ((V+1)-S) (V-S+1)
    ((V+1)-c) (V-c+1) (by omega) (by omega)
    (finiteMayTopLabel T.Y c q hq S (V+1) error)] at herrorRaw
  let f := XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
    (normalizedTriangle background T he).mor₁) (c+(q+1)) ≫ eY.hom
  have hresidual : e ≫ f = (d-a) ≫ f := by
    simpa only [f,Category.assoc] using congrArg (fun b => b ≫ eY.hom) heimage
  have himage : d ≫ f =
      homotopyRegrade (show (V+1)-S=V-S+1 by omega)
        (show (V+1)-c=V-c+1 by omega)
        (ordinarySuspendedRepresentative _ ((V+1)-S) ((V+1)-c)
          (finiteMayTopLabel T.Y c q hq S (V+1) (v+error))) := by
    have hsum : d ≫ f = a ≫ f + e ≫ f := by
      rw [hresidual,Preadditive.sub_comp]
      abel
    rw [hsum]
    change a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) (c+(q+1)) ≫ eY.hom +
      e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) (c+(q+1)) ≫ eY.hom = _
    rw [haimage,herrorRaw,finite_may_top_label_add,
      ordinary_suspended_representative_add,regrade_add]
  have hdecoded :
      IsCycle background T.Y (c+(q+1)) (s+1,t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s+1,t+1)
        (S+q+1,(V+1)+q)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) (v+error) := by
    apply normalized_boundary_image_decode_general T hf N hN s t (S+q+1) ((V+1)+q)
      ((V+1)-S) ((V+1)-c) (by dsimp [S,N]; omega) (by dsimp [V,N]; omega)
      (by dsimp [S,V]; omega) (by dsimp [V]; omega) x (v+error) ex eY hex heY
      (finiteMayTopLabel T.Y c q hq S (V+1) (v+error))
      (finite_may_top_label_detects T.Y c q hq S (V+1) (v+error))
    apply homotopy_regrade_injective (show t-s=V-S+1 by dsimp [S,V]; omega)
      (show (t+1)+(1:ℕ)=V-c+1 by dsimp [V]; omega)
    have hi := himage
    dsimp only [f,normalizedTriangle,Triangle.mk] at hi
    simp only [d,actualNormalizedFirstFiniteBoundary,←homotopyRegrade_comp,Category.assoc] at hi
    have hnorm := positive_normalized_source_inv_arrow T he hf
    dsimp only [normalizedTriangle,Triangle.mk] at hnorm
    rw [←Category.assoc _ (XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (background.normalizedMap T.X T.Y T.f).map) N),
      ←background.quotients.functoriality.map_comp,←Functor.map_comp,hnorm] at hi
    simpa only [homotopyRegrade_comp,normalized_homotopy_regrade_trans,Category.assoc] using hi
  have heG : (background.classical.map T.g).pageMap 2 (S+q+1,(V+1)+q) error=0 := by
    have hb := (KIP126.Literature.Standard.E2Exactness.e2ExactAtY
      T hf hg hh (S+q) (V+q)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+q) (V+q) e₂)).mpr ⟨e₂,rfl⟩
    have transport (p p' : ℤ×ℤ) (hp : p=p')
        (a : Ambient background T.Y p) (b : Ambient background T.Y p') (hab : HEq a b)
        (hb : (background.classical.map T.g).pageMap 2 p' b=0) :
        (background.classical.map T.g).pageMap 2 p a=0 := by
      subst p'
      simpa only [eq_of_heq hab] using hb
    exact transport _ _ (by congr 1; omega) _ _ herror hb
  refine ⟨hdecoded.1,?_⟩
  exact differential_target_of_permanent_candidate_kernel T.Y T.Z T.g
    (c+(q+1)+1) (s+1,t+1) (S+q+1,(V+1)+q)
    _ (v+error) v error P hP hdecoded.2 hv
    (by have hz : (v+error)-v-error=0 := by abel
        rw [hz]
        exact (boundaries background T.Y (c+(q+1)+1-1) _).zero_mem)
    heG (by simpa only [add_sub_cancel_right] using hker)

/-- The complete positive-second-arrow criterion with all original H-image
terms, for the whole terminal E₂ candidate space. -/
private theorem differential_of_middle_images_and_full_kernel_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u : Ambient background T.X ((s+(c+1))+1,t+(c+1)))
    (z : Ambient background T.Z ((s+(c+1))+1,(t+(c+1))+1))
    (v : Ambient background T.Y ((s+(c+1))+q+1,(t+(c+1))+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass ((s+(c+1))+1) ((t+(c+1))+1)
      ((background.classical.map T.h).pageMap 2 ((s+(c+1))+1,(t+(c+1))+1) z) (by simpa using u))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      ((c+1)+1) (s,t) ((s+(c+1))+1,t+(c+1)) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) ((s+(c+1))+1,(t+(c+1))+1)
      (((s+(c+1))+q+1)+1,((t+(c+1))+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        ((s+(c+1))+q+1) ((t+(c+1))+q) v))
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ a : Ambient background T.X ((s+(c+1))+1+j,(t+(c+1))+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j)
          ((s+(c+1))+1+j,(t+(c+1))+j) →
        ∃ z' : Ambient background T.Z ((s+(c+1))+1+j,(t+(c+1))+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j)
            ((s+(c+1))+1+j,(t+(c+1))+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T
            ((s+(c+1))+1+j) ((t+(c+1))+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) ((s+(c+1))+1+j,(t+(c+1))+j))
    (hker : ∀ a : Ambient background T.Y ((s+(c+1))+q+1,(t+(c+1))+q),
      positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        ((s+(c+1))+q+1) ((t+(c+1))+q) a=0 →
      a ∈ boundaries background T.Y (c+(q+1))
        ((s+(c+1))+q+1,(t+(c+1))+q)) :
    let y := (background.classical.map T.f).pageMap 2 (s,t) x
    IsCycle background T.Y (c+(q+1)) (s,t) y ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s,t)
        ((s+(c+1))+q+1,(t+(c+1))+q) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  let N := c+(q+1)
  have hN : 0<N := by dsimp [N]; omega
  let B := s+(c+1)
  let W := t+(c+1)
  obtain ⟨ex,hex⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.X.obj background.auxiliary)) N
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) (q+1)
  obtain ⟨eY,heY⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) N
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) N
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  let d := homotopyRegrade (show t-s=W-B by dsimp [B,W]; omega)
    (show t+1=W-c by dsimp [W]; omega)
    (ordinaryNormalizedFirstFiniteBoundary T he hf N hN s t ex x)
  have hd := ordinary_first_finite_boundary_source_detects T he hf (c+1) N c
    (by omega) hN (by omega) s t x u hdx ex hex ε hε
  obtain ⟨_,a,ha,hi,hall⟩ := positive_second_finite_core T he hT hf hg hh
    c q hq B W z u v hu hdz ey hey ε hε
  have hlast : ∀ a : Ambient background T.X
        ((B+1)+(q+1:ℕ)-1,W+(q+1:ℕ)-1),
      (background.classical.map T.f).pageMap 2
        ((B+1)+(q+1:ℕ)-1,W+(q+1:ℕ)-1) a ∈
      boundaries background T.Y (c+(q+1))
        ((B+1)+(q+1:ℕ)-1,W+(q+1:ℕ)-1) := by
    intro a
    have hker' (S V : ℤ) (hS : S=B+q+1) (hV : V=W+q) :
        ∀ a : Ambient background T.Y (S,V),
          positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
            S V a=0 → a ∈ boundaries background T.Y (c+(q+1)) (S,V) := by
      subst S V
      exact hker
    exact hker' _ _ (by omega) (by omega) _
      (positive_second_triangle_composite_zero T hf hg hh hT _ _ a)
  have hdiff := detects_sub_filtration
    (background.convergence (.quotient N (.nu T.X))) (B+1,W,W-c) hd ha
  change FiltrationAtLeast background.syntheticTower ((B+1)+1)
    (positiveHSourceDesuspend T he hf N c B W ε d -
      positiveHSourceDesuspend T he hf N c B W ε a) at hdiff
  rw [←positive_h_source_desuspend_sub] at hdiff
  have hkill := middle_positive_g_raw_annihilation T he hf hg hh hT c (q+1)
    (by omega) (B+1) W (fun j hj hjq b hb => by
      obtain ⟨z',hz',hbz⟩ := hmid j hj hjq b hb
      exact ⟨z',hz',boundaries_monotone background T.X _ (by omega) hbz⟩) ε hε hlast
  rw [show B+1-1=B by omega] at hkill
  have hz := hkill (d-a) hdiff
  have himage := (sub_eq_zero.mp (by simpa only [Preadditive.sub_comp] using hz)).trans hi
  obtain ⟨b,hb,hbimage⟩ := finite_may_signed_target_at_level T.Y c q hq B W
    v ey eY hey heY
  apply ordinary_boundary_image_decode_coordinates T he hf N hN s t (B+q+1) (W+q)
    (W-B) (W-c) (by dsimp [B,N]; omega) (by dsimp [W,N]; omega)
    (by dsimp [B,W]; omega) (by dsimp [W]; omega) x v ex eY hex heY b hb
  apply homotopy_regrade_injective (show t-s=W-B by dsimp [B,W]; omega)
    (show t+1=W-c by dsimp [W]; omega)
  have h := congrArg (fun k => k ≫ eY.hom) himage
  erw [hbimage] at h
  simpa only [d,regrade_comp,regrade_transitive,positive_g_regrade_self,Category.assoc] using h


/-- Page-class criterion with the full middle condition, restricted
candidate space, and the source’s specified K differential. -/
public theorem differential_of_page_classes_and_candidate_kernel
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u u' : Ambient background T.X (s+(c+1)+1,t+(c+1)))
    (y : Ambient background T.Y (s+1,t+1))
    (z : Ambient background T.Z (s+(c+1)+1,(t+(c+1))+1))
    (v : Ambient background T.Y ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+(c+1)+1) ((t+(c+1))+1)
      ((background.classical.map T.h).pageMap 2 (s+(c+1)+1,(t+(c+1))+1) z) (by simpa using u'))
    (huu : u'-u ∈ boundaries background T.X (c+1)
      (s+(c+1)+1,t+(c+1)))
    (hyy : y-KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈
      boundaries background T.Y (c+1) (s+1,t+1))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      ((c+1)+1) (s,t) (s+(c+1)+1,t+(c+1)) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+(c+1)+1,(t+(c+1))+1) ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) z
      ((background.classical.map T.g).pageMap 2 ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) v))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (q+1)-1 →
      ∀ a : Ambient background T.X ((s+(c+1)+1)+j,(t+(c+1))+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j)
          ((s+(c+1)+1)+j,(t+(c+1))+j) →
        ∃ z' : Ambient background T.Z ((s+(c+1)+1)+j,(t+(c+1))+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j)
            ((s+(c+1)+1)+j,(t+(c+1))+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T
            ((s+(c+1)+1)+j) ((t+(c+1))+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) ((s+(c+1)+1)+j,(t+(c+1))+j))
    (P : Submodule ℤ (Ambient background T.Y
      ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q)))
    (hP : permanentCycles background T.Y
      ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ a ∈ P,
      (background.classical.map T.g).pageMap 2
        ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) a = 0 →
      a ∈ boundaries background T.Y (c+(q+1))
        ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q)) :
    IsCycle background T.Y (c+(q+1)) (s+1,t+1) y ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s+1,t+1)
        ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) y v := by
  have hdxA : DifferentialAt background T.X ((c+1)+1)
      (s,t) (s+(c+1)+1,t+(c+1)) x u := ⟨by omega,hdx⟩
  have hdx' : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      ((c+1)+1) (s,t) (s+(c+1)+1,t+(c+1)) x u' :=
    (differentialAt_of_congruent background T.X hdxA ⟨by omega,by
      simpa only [show ((c:ℤ)+1)+1-1=c+1 by omega] using huu⟩).2
  obtain ⟨_,hd⟩ := differential_of_middle_images_and_candidate_kernel
    T he hf hg hh c q hq s t x u' z v hu hdx' hdz hmid P hP hv hker
  have hd' := differential_of_earlier_boundaries T.Y (c+(q+1)+1)
    (c+1) (c+1) (s+1,t+1) ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q)
    _ y v v hd (by omega) (by omega) hyy
    (by simpa only [sub_self] using (boundaries background T.Y (c+1)
      ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q)).zero_mem)
  exact ⟨by simpa only [show (c:ℤ)+((q:ℤ)+1)+1-1=c+((q:ℤ)+1) by omega] using
    (cycles_of_differential T.Y _ _ _ _ _ hd').1,hd'⟩

/-- The actual positive G₂ operation can be used in the restricted terminal
kernel comparison, with permanence derived from the constructed target. -/
private theorem differential_target_of_positive_candidate_kernel
    (T : TriangleData background.auxiliary)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (r : ℤ) (p : ℤ×ℤ) (S V : ℤ)
    (x : Ambient background T.Y p) (w v e : Ambient background T.Y (S,V))
    (P : Submodule ℤ (Ambient background T.Y (S,V)))
    (hP : permanentCycles background T.Y (S,V) ≤ P)
    (hd : DifferentialAt background T.Y r p (S,V) x w)
    (hv : v ∈ P)
    (herror : w-v-e ∈ boundaries background T.Y (r-1) (S,V))
    (he : positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) S V e=0)
    (hker : ∀ a ∈ P,
      positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) S V a=0 →
      a ∈ boundaries background T.Y (r-1) (S,V)) :
    DifferentialAt background T.Y r p (S,V) x v := by
  have hwP := hP (differential_target_mem_permanent_cycles T.Y r p (S,V) x w hd)
  have heP : e ∈ P := by
    have hh := P.sub_mem (P.sub_mem hwP hv)
      (hP (boundary_mem_permanent_cycles T.Y (r-1) (S,V) _ herror))
    convert hh using 1; abel
  have hev := (boundaries background T.Y (r-1) (S,V)).add_mem herror (hker e heP he)
  have hdiff : w-v ∈ boundaries background T.Y (r-1) (S,V) := by
    simpa only [sub_add_cancel] using hev
  exact differentialAt_of_congruent background T.Y hd ⟨by have := hd.1; omega,by
    simpa only [neg_sub] using (boundaries background T.Y (r-1) (S,V)).neg_mem hdiff⟩

/-- The general H-image middle criterion in the positive-g branch retains
an actual last-filtration residual with exactly the original raw F-image. -/
private theorem positive_second_last_residual
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (c q : ℕ) (hq : 0<q) (B W : ℤ)
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ a : Ambient background T.X (B+1+j,W+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j) (B+1+j,W+j) →
        ∃ z : Ambient background T.Z (B+1+j,W+j+1),
          z ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j) (B+1+j,W+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (B+1+j) (W+j) z ∈
            boundaries background T.X ((j:ℤ)+1) (B+1+j,W+j))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (a : BiHom (W-B) (W-c)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+(q+1))))
    (ha : FiltrationAtLeast background.syntheticTower ((B+1)+1)
      (positiveHSourceDesuspend T he hf (c+(q+1)) c B W ε a)) :
    ∃ e : BiHom (W-B) (W-c)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      FiltrationAtLeast background.syntheticTower (B+q+1)
        (positiveHSourceDesuspend T he hf (c+(q+1)) c B W ε e) ∧
      e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+(q+1)) =
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+(q+1)) := by
  have hat := (middle_positive_g_native_filtration_iff T he hf (c+(q+1)) c
    B W ((B+1)+1) ε a).mp ha
  let a' := homotopyRegrade (show W-B=W-(B+1)+1 by omega) rfl a
  have haf : FiltrationAtLeast background.syntheticTower ((B+1)+1)
      (a' ≫ XModLambdaN.map (middlePositiveGTargetIso T he hf).hom (c+(q+1))) := by
    dsimp only [a']
    rw [←regrade_comp]
    exact (regrade_filtration_iff _ _ _ _).mpr hat
  obtain ⟨e,hefil,heimage⟩ := middle_positive_g_residual_same_image
    T he hf hg hh hT c (q+1) (by omega) (B+1) W
    (fun j hj hjq b hb => by
      obtain ⟨z,hz,hbz⟩ := hmid j hj hjq b hb
      exact ⟨z,hz,boundaries_monotone background T.X _ (by omega) hbz⟩) a' haf
  let e' := homotopyRegrade (show W-(B+1)+1=W-B by omega) rfl e
  have hef : FiltrationAtLeast background.syntheticTower ((B+1)+(q+1:ℕ)-1)
      (e' ≫ XModLambdaN.map (middlePositiveGTargetIso T he hf).hom (c+(q+1))) := by
    dsimp only [e']
    rw [←regrade_comp]
    exact (regrade_filtration_iff _ _ _ _).mpr hefil
  refine ⟨e',?_,?_⟩
  · have hn := (middle_positive_g_native_filtration_iff T he hf (c+(q+1)) c
      B W ((B+1)+(q+1:ℕ)-1) ε e').mpr hef
    simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hn
  · have hi := congrArg (homotopyRegrade (show W-(B+1)+1=W-B by omega)
      (rfl : W-c=W-c)) heimage
    simpa only [e',a',regrade_comp,last_layer_regrade_trans,positive_g_regrade_self] using hi

/-- The complete positive-second-arrow criterion with the original H-image
terms and arbitrary candidate P containing the true permanent cycles. -/
public theorem differential_of_middle_images_and_candidate_kernel_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u : Ambient background T.X ((s+(c+1))+1,t+(c+1)))
    (z : Ambient background T.Z ((s+(c+1))+1,(t+(c+1))+1))
    (v : Ambient background T.Y ((s+(c+1))+q+1,(t+(c+1))+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass ((s+(c+1))+1) ((t+(c+1))+1)
      ((background.classical.map T.h).pageMap 2 ((s+(c+1))+1,(t+(c+1))+1) z) (by simpa using u))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      ((c+1)+1) (s,t) ((s+(c+1))+1,t+(c+1)) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) ((s+(c+1))+1,(t+(c+1))+1)
      (((s+(c+1))+q+1)+1,((t+(c+1))+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        ((s+(c+1))+q+1) ((t+(c+1))+q) v))
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ a : Ambient background T.X ((s+(c+1))+1+j,(t+(c+1))+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j)
          ((s+(c+1))+1+j,(t+(c+1))+j) →
        ∃ z' : Ambient background T.Z ((s+(c+1))+1+j,(t+(c+1))+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j)
            ((s+(c+1))+1+j,(t+(c+1))+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T
            ((s+(c+1))+1+j) ((t+(c+1))+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) ((s+(c+1))+1+j,(t+(c+1))+j))
    (P : Submodule ℤ (Ambient background T.Y ((s+(c+1))+q+1,(t+(c+1))+q)))
    (hP : permanentCycles background T.Y ((s+(c+1))+q+1,(t+(c+1))+q) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ a ∈ P,
      positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        ((s+(c+1))+q+1) ((t+(c+1))+q) a=0 →
      a ∈ boundaries background T.Y (c+(q+1))
        ((s+(c+1))+q+1,(t+(c+1))+q)) :
    let y := (background.classical.map T.f).pageMap 2 (s,t) x
    IsCycle background T.Y (c+(q+1)) (s,t) y ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s,t)
        ((s+(c+1))+q+1,(t+(c+1))+q) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  let N := c+(q+1)
  have hN : 0<N := by dsimp [N]; omega
  let B := s+(c+1)
  let W := t+(c+1)
  obtain ⟨ex,hex⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.X.obj background.auxiliary)) N
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) (q+1)
  obtain ⟨eY,heY⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) N
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) N
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  let d := homotopyRegrade (show t-s=W-B by dsimp [B,W]; omega)
    (show t+1=W-c by dsimp [W]; omega)
    (ordinaryNormalizedFirstFiniteBoundary T he hf N hN s t ex x)
  have hd := ordinary_first_finite_boundary_source_detects T he hf (c+1) N c
    (by omega) hN (by omega) s t x u hdx ex hex ε hε
  obtain ⟨_,a,ha,hi,hall⟩ := positive_second_finite_core T he hT hf hg hh
    c q hq B W z u v hu hdz ey hey ε hε
  have hdiff := detects_sub_filtration
    (background.convergence (.quotient N (.nu T.X))) (B+1,W,W-c) hd ha
  change FiltrationAtLeast background.syntheticTower ((B+1)+1)
    (positiveHSourceDesuspend T he hf N c B W ε d -
      positiveHSourceDesuspend T he hf N c B W ε a) at hdiff
  rw [←positive_h_source_desuspend_sub] at hdiff
  obtain ⟨e,hefil,heimage⟩ := positive_second_last_residual
    T he hf hg hh hT c q hq B W hmid ε (d-a) hdiff
  obtain ⟨e₂,herrorTop⟩ := last_layer_ordinary_image_eq_finite_may_top
    T.X T.Y T.f c q hq B W (positiveHSourceDesuspend T he hf N c B W ε e) hefil
  let error := (background.classical.map T.f).pageMap 2 (B+q+1,W+q) e₂
  have herrorRaw := native_ordinary_image_eq_raw_image T he hf N c hN B W ε hε eY heY e
  rw [herrorTop] at herrorRaw
  have hcommon := congrArg (fun k => k ≫ eY.hom) hi
  have htop := finite_may_signed_target_eq_top_at_level T.Y c q hq B W v ey eY hey heY
  have hcommon' : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N ≫ eY.hom =
      ordinarySuspendedRepresentative _ (W-B) (W-c) (finiteMayTopLabel T.Y c q hq B W v) := by
    simpa only [Category.assoc] using hcommon.trans htop
  let f := XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
    (normalizedTriangle background T he).mor₁) N ≫ eY.hom
  have hresidual : e ≫ f = (d-a) ≫ f := by
    simpa only [f,Category.assoc] using congrArg (fun b => b ≫ eY.hom) heimage
  have himage : d ≫ f = ordinarySuspendedRepresentative _ (W-B) (W-c)
      (finiteMayTopLabel T.Y c q hq B W (v+error)) := by
    have hsum : d ≫ f = a ≫ f + e ≫ f := by
      rw [hresidual,Preadditive.sub_comp]
      abel
    rw [hsum]
    change a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N ≫ eY.hom +
      e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N ≫ eY.hom = _
    rw [hcommon',herrorRaw,finite_may_top_label_add,ordinary_suspended_representative_add]
  have hdecoded : IsCycle background T.Y (c+(q+1)) (s,t)
      ((background.classical.map T.f).pageMap 2 (s,t) x) ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s,t) (B+q+1,W+q)
        ((background.classical.map T.f).pageMap 2 (s,t) x) (v+error) := by
    apply ordinary_boundary_image_decode_coordinates T he hf N hN s t (B+q+1) (W+q)
      (W-B) (W-c) (by dsimp [B,N]; omega) (by dsimp [W,N]; omega)
      (by dsimp [B,W]; omega) (by dsimp [W]; omega) x (v+error) ex eY hex heY
      (finiteMayTopLabel T.Y c q hq B W (v+error))
      (finite_may_top_label_detects T.Y c q hq B W (v+error))
    apply homotopy_regrade_injective (show t-s=W-B by dsimp [B,W]; omega)
      (show t+1=W-c by dsimp [W]; omega)
    simpa only [d,f,regrade_comp,regrade_transitive,positive_g_regrade_self,Category.assoc] using himage
  refine ⟨hdecoded.1,?_⟩
  exact differential_target_of_positive_candidate_kernel T hg (c+(q+1)+1)
    (s,t) (B+q+1) (W+q) _ (v+error) v error P hP hdecoded.2 hv
    (by have hz : (v+error)-v-error=0 := by abel
        rw [hz]
        exact (boundaries background T.Y (c+(q+1)+1-1) _).zero_mem)
    (positive_second_triangle_composite_zero T hf hg hh hT (B+q+1) (W+q) e₂)
    (by simpa only [add_sub_cancel_right] using hker)

/-- The positive-g page-class variant retains the whole original middle
H-image condition and restricted candidate kernel. -/
public theorem differential_of_page_classes_and_candidate_kernel_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u u' : Ambient background T.X ((s+(c+1))+1,t+(c+1)))
    (y : Ambient background T.Y (s,t))
    (z : Ambient background T.Z ((s+(c+1))+1,(t+(c+1))+1))
    (v : Ambient background T.Y ((s+(c+1))+q+1,(t+(c+1))+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass ((s+(c+1))+1) ((t+(c+1))+1)
      ((background.classical.map T.h).pageMap 2 ((s+(c+1))+1,(t+(c+1))+1) z) (by simpa using u'))
    (huu : u'-u ∈ boundaries background T.X (c+1)
      ((s+(c+1))+1,t+(c+1)))
    (hyy : y-(background.classical.map T.f).pageMap 2 (s,t) x ∈
      boundaries background T.Y (c+1) (s,t))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      ((c+1)+1) (s,t) ((s+(c+1))+1,t+(c+1)) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) ((s+(c+1))+1,(t+(c+1))+1)
      (((s+(c+1))+q+1)+1,((t+(c+1))+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        ((s+(c+1))+q+1) ((t+(c+1))+q) v))
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ a : Ambient background T.X ((s+(c+1))+1+j,(t+(c+1))+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j)
          ((s+(c+1))+1+j,(t+(c+1))+j) →
        ∃ z' : Ambient background T.Z ((s+(c+1))+1+j,(t+(c+1))+j+1),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j)
            ((s+(c+1))+1+j,(t+(c+1))+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T
            ((s+(c+1))+1+j) ((t+(c+1))+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) ((s+(c+1))+1+j,(t+(c+1))+j))
    (P : Submodule ℤ (Ambient background T.Y ((s+(c+1))+q+1,(t+(c+1))+q)))
    (hP : permanentCycles background T.Y ((s+(c+1))+q+1,(t+(c+1))+q) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ a ∈ P,
      positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        ((s+(c+1))+q+1) ((t+(c+1))+q) a=0 →
      a ∈ boundaries background T.Y (c+(q+1))
        ((s+(c+1))+q+1,(t+(c+1))+q)) :
    IsCycle background T.Y (c+(q+1)) (s,t) y ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s,t)
        ((s+(c+1))+q+1,(t+(c+1))+q) y v := by
  have hdxA : DifferentialAt background T.X ((c+1)+1)
      (s,t) ((s+(c+1))+1,t+(c+1)) x u := ⟨by omega,hdx⟩
  have hdx' : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      ((c+1)+1) (s,t) ((s+(c+1))+1,t+(c+1)) x u' :=
    (differentialAt_of_congruent background T.X hdxA ⟨by omega,by
      simpa only [show ((c:ℤ)+1)+1-1=c+1 by omega] using huu⟩).2
  obtain ⟨_,hd⟩ := differential_of_middle_images_and_candidate_kernel_second
    T he hf hg hh c q hq s t x u' z v hu hdx' hdz hmid P hP hv hker
  have hd' := differential_of_earlier_boundaries T.Y (c+(q+1)+1)
    (c+1) (c+1) (s,t) ((s+(c+1))+q+1,(t+(c+1))+q)
    _ y v v hd (by omega) (by omega) hyy
    (by simpa only [sub_self] using (boundaries background T.Y (c+1)
      ((s+(c+1))+q+1,(t+(c+1))+q)).zero_mem)
  exact ⟨by simpa only [show (c:ℤ)+((q:ℤ)+1)+1-1=c+((q:ℤ)+1) by omega] using
    (cycles_of_differential T.Y _ _ _ _ _ hd').1,hd'⟩

/-- The complete positive-h criterion uses the actual positive H operation
in every middle layer and the original restricted candidate kernel. -/
public theorem differential_of_middle_images_and_candidate_kernel_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u : Ambient background T.X ((s+(c+1))+1,t+(c+1)))
    (z : Ambient background T.Z (s+(c+1),t+(c+1)))
    (v : Ambient background T.Y ((s+(c+1))+q+1,(t+(c+1))+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass ((s+(c+1))+1) ((t+(c+1))+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
        (s+(c+1)) (t+(c+1)) z) (by simpa using u))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      ((c+1)+1) (s,t) ((s+(c+1))+1,t+(c+1)) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+(c+1),t+(c+1)) ((s+(c+1))+q+1,(t+(c+1))+q) z
      ((background.classical.map T.g).pageMap 2 ((s+(c+1))+q+1,(t+(c+1))+q) v))
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ a : Ambient background T.X (((s+(c+1))+1)+j-1+1,(t+(c+1))+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j)
          (((s+(c+1))+1)+j-1+1,(t+(c+1))+j) →
        ∃ z' : Ambient background T.Z (((s+(c+1))+1)+j-1,(t+(c+1))+j),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j)
            (((s+(c+1))+1)+j-1,(t+(c+1))+j) ∧
        ∃ u' : Ambient background T.X (((s+(c+1))+1)+j-1+1,(t+(c+1))+j),
          (background.classicalSuspension T.X).DesuspendsClass
            (((s+(c+1))+1)+j-1+1) ((t+(c+1))+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              (((s+(c+1))+1)+j-1) ((t+(c+1))+j) z')
            (by simpa only [add_sub_cancel_right] using u') ∧
          a-u' ∈ boundaries background T.X ((j:ℤ)+1)
            (((s+(c+1))+1)+j-1+1,(t+(c+1))+j))
    (P : Submodule ℤ (Ambient background T.Y ((s+(c+1))+q+1,(t+(c+1))+q)))
    (hP : permanentCycles background T.Y ((s+(c+1))+q+1,(t+(c+1))+q) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ a ∈ P,
      (background.classical.map T.g).pageMap 2 ((s+(c+1))+q+1,(t+(c+1))+q) a=0 →
      a ∈ boundaries background T.Y (c+(q+1))
        ((s+(c+1))+q+1,(t+(c+1))+q)) :
    let y := (background.classical.map T.f).pageMap 2 (s,t) x
    IsCycle background T.Y (c+(q+1)) (s,t) y ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s,t)
        ((s+(c+1))+q+1,(t+(c+1))+q) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  let N := c+(q+1)
  have hN : 0<N := by dsimp [N]; omega
  let B := s+(c+1)
  let W := t+(c+1)
  obtain ⟨ex,hex⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.X.obj background.auxiliary)) N
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) (q+1)
  obtain ⟨eY,heY⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) N
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) N
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  let d := homotopyRegrade (show t-s=W-B by dsimp [B,W]; omega)
    (show t+1=W-c by dsimp [W]; omega)
    (ordinaryNormalizedFirstFiniteBoundary T he hf N hN s t ex x)
  have hd := ordinary_first_finite_boundary_source_detects T he hf (c+1) N c
    (by omega) hN (by omega) s t x u hdx ex hex ε hε
  obtain ⟨a,ha,hi,_,_⟩ := positive_third_finite_core T he hT hf hg hh
    c q hq B W z u v hu hdz ey hey ε hε
  have hdiff := detects_sub_filtration
    (background.convergence (.quotient N (.nu T.X))) (B+1,W,W-c) hd ha
  change FiltrationAtLeast background.syntheticTower ((B+1)+1)
    (positiveHSourceDesuspend T he hf N c B W ε d -
      positiveHSourceDesuspend T he hf N c B W ε a) at hdiff
  rw [←positive_h_source_desuspend_sub] at hdiff
  have hres := middle_positive_h_residual_same_image T he hf hg hh hT
    c (q+1) (by omega) (B+1) W (fun j hj hjq b hb => by
      obtain ⟨z',hz',u',hu',hbu⟩ := hmid j hj hjq b hb
      exact ⟨z',hz',u',hu',boundaries_monotone background T.X _ (by omega) hbu⟩) ε
  rw [show B+1-1=B by omega] at hres
  obtain ⟨e,hefil,heimage⟩ := hres (d-a) hdiff
  have hefil' : FiltrationAtLeast background.syntheticTower (B+q+1)
      (positiveHSourceDesuspend T he hf N c B W ε e) := by
    simpa only [show (B+1)+(q+1:ℕ)-1=B+q+1 by omega] using hefil
  obtain ⟨e₂,herrorTop⟩ := last_layer_ordinary_image_eq_finite_may_top
    T.X T.Y T.f c q hq B W (positiveHSourceDesuspend T he hf N c B W ε e) hefil'
  let error := (background.classical.map T.f).pageMap 2 (B+q+1,W+q) e₂
  have herrorRaw := native_ordinary_image_eq_raw_image T he hf N c hN B W ε hε eY heY e
  rw [herrorTop] at herrorRaw
  have hcommon := congrArg (fun k => k ≫ eY.hom) hi
  have htop := finite_may_signed_target_eq_top_at_level T.Y c q hq B W v ey eY hey heY
  have hcommon' : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N ≫ eY.hom =
      ordinarySuspendedRepresentative _ (W-B) (W-c) (finiteMayTopLabel T.Y c q hq B W v) := by
    simpa only [Category.assoc] using hcommon.trans htop
  let f := XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
    (normalizedTriangle background T he).mor₁) N ≫ eY.hom
  have hresidual : e ≫ f = (d-a) ≫ f := by
    simpa only [f,Category.assoc] using congrArg (fun b => b ≫ eY.hom) heimage
  have himage : d ≫ f = ordinarySuspendedRepresentative _ (W-B) (W-c)
      (finiteMayTopLabel T.Y c q hq B W (v+error)) := by
    have hsum : d ≫ f = a ≫ f + e ≫ f := by
      rw [hresidual,Preadditive.sub_comp]
      abel
    rw [hsum]
    change a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N ≫ eY.hom +
      e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N ≫ eY.hom = _
    rw [hcommon',herrorRaw,finite_may_top_label_add,ordinary_suspended_representative_add]
  have hdecoded : IsCycle background T.Y (c+(q+1)) (s,t)
      ((background.classical.map T.f).pageMap 2 (s,t) x) ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s,t) (B+q+1,W+q)
        ((background.classical.map T.f).pageMap 2 (s,t) x) (v+error) := by
    apply ordinary_boundary_image_decode_coordinates T he hf N hN s t (B+q+1) (W+q)
      (W-B) (W-c) (by dsimp [B,N]; omega) (by dsimp [W,N]; omega)
      (by dsimp [B,W]; omega) (by dsimp [W]; omega) x (v+error) ex eY hex heY
      (finiteMayTopLabel T.Y c q hq B W (v+error))
      (finite_may_top_label_detects T.Y c q hq B W (v+error))
    apply homotopy_regrade_injective (show t-s=W-B by dsimp [B,W]; omega)
      (show t+1=W-c by dsimp [W]; omega)
    simpa only [d,f,regrade_comp,regrade_transitive,positive_g_regrade_self,Category.assoc] using himage
  refine ⟨hdecoded.1,?_⟩
  exact differential_target_of_permanent_candidate_kernel T.Y T.Z T.g (c+(q+1)+1)
    (s,t) (B+q+1,W+q) _ (v+error) v error P hP hdecoded.2 hv
    (by have hz : (v+error)-v-error=0 := by abel
        rw [hz]
        exact (boundaries background T.Y (c+(q+1)+1-1) _).zero_mem)
    (ordinary_triangle_composite_zero T (B+q+1) (W+q) e₂)
    (by simpa only [add_sub_cancel_right] using hker)

/-- The positive-h page-class variant uses the actual positive H operation
and retains the original restricted candidate condition. -/
public theorem differential_of_page_classes_and_candidate_kernel_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u u' : Ambient background T.X ((s+(c+1))+1,t+(c+1)))
    (y : Ambient background T.Y (s,t))
    (z : Ambient background T.Z (s+(c+1),t+(c+1)))
    (v : Ambient background T.Y ((s+(c+1))+q+1,(t+(c+1))+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass ((s+(c+1))+1) ((t+(c+1))+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
        (s+(c+1)) (t+(c+1)) z) (by simpa using u'))
    (huu : u'-u ∈ boundaries background T.X (c+1)
      ((s+(c+1))+1,t+(c+1)))
    (hyy : y-(background.classical.map T.f).pageMap 2 (s,t) x ∈
      boundaries background T.Y (c+1) (s,t))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      ((c+1)+1) (s,t) ((s+(c+1))+1,t+(c+1)) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+(c+1),t+(c+1)) ((s+(c+1))+q+1,(t+(c+1))+q) z
      ((background.classical.map T.g).pageMap 2 ((s+(c+1))+q+1,(t+(c+1))+q) v))
    (hmid : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      ∀ a : Ambient background T.X (((s+(c+1))+1)+j-1+1,(t+(c+1))+j),
        a ∈ cycles background T.X (((q+1:ℕ):ℤ)-j)
          (((s+(c+1))+1)+j-1+1,(t+(c+1))+j) →
        ∃ z' : Ambient background T.Z (((s+(c+1))+1)+j-1,(t+(c+1))+j),
          z' ∈ cycles background T.Z (((q+1:ℕ):ℤ)-j)
            (((s+(c+1))+1)+j-1,(t+(c+1))+j) ∧
        ∃ u' : Ambient background T.X (((s+(c+1))+1)+j-1+1,(t+(c+1))+j),
          (background.classicalSuspension T.X).DesuspendsClass
            (((s+(c+1))+1)+j-1+1) ((t+(c+1))+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              (((s+(c+1))+1)+j-1) ((t+(c+1))+j) z')
            (by simpa only [add_sub_cancel_right] using u') ∧
          a-u' ∈ boundaries background T.X ((j:ℤ)+1)
            (((s+(c+1))+1)+j-1+1,(t+(c+1))+j))
    (P : Submodule ℤ (Ambient background T.Y ((s+(c+1))+q+1,(t+(c+1))+q)))
    (hP : permanentCycles background T.Y ((s+(c+1))+q+1,(t+(c+1))+q) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ a ∈ P,
      (background.classical.map T.g).pageMap 2 ((s+(c+1))+q+1,(t+(c+1))+q) a=0 →
      a ∈ boundaries background T.Y (c+(q+1))
        ((s+(c+1))+q+1,(t+(c+1))+q)) :
    IsCycle background T.Y (c+(q+1)) (s,t) y ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s,t)
        ((s+(c+1))+q+1,(t+(c+1))+q) y v := by
  have hdxA : DifferentialAt background T.X ((c+1)+1)
      (s,t) ((s+(c+1))+1,t+(c+1)) x u := ⟨by omega,hdx⟩
  have hdx' : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      ((c+1)+1) (s,t) ((s+(c+1))+1,t+(c+1)) x u' :=
    (differentialAt_of_congruent background T.X hdxA ⟨by omega,by
      simpa only [show ((c:ℤ)+1)+1-1=c+1 by omega] using huu⟩).2
  obtain ⟨_,hd⟩ := differential_of_middle_images_and_candidate_kernel_third
    T he hf hg hh c q hq s t x u' z v hu hdx' hdz hmid P hP hv hker
  have hd' := differential_of_earlier_boundaries T.Y (c+(q+1)+1)
    (c+1) (c+1) (s,t) ((s+(c+1))+q+1,(t+(c+1))+q)
    _ y v v hd (by omega) (by omega) hyy
    (by simpa only [sub_self] using (boundaries background T.Y (c+1)
      ((s+(c+1))+q+1,(t+(c+1))+q)).zero_mem)
  exact ⟨by simpa only [show (c:ℤ)+((q:ℤ)+1)+1-1=c+((q:ℤ)+1) by omega] using
    (cycles_of_differential T.Y _ _ _ _ _ hd').1,hd'⟩

/-- Last-layer comparison for a raw source under the common-representative
and same-image last-residual hypotheses. It preserves d and applies
to source-restricted middle-subspace criteria. -/
private theorem positive_first_residual_image_target
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (c q : ℕ) (hq : 0<q) (S V : ℤ)
    (v : Ambient background T.Y (S+q+1,(V+1)+q))
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
    (eY : XModLambdaN ((background.nu.functor.obj (T.Y.obj background.auxiliary))⟦(1:ℤ)⟧) (c+(q+1)) ≅
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (c+(q+1)))⟦(1:ℤ)⟧)
    (heY : XModLambdaN.incl _ (c+(q+1)) ≫ eY.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (c+(q+1))))
    (d a e : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+(q+1))))
    (hefil : FiltrationAtLeast background.syntheticTower (S+q)
      (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε e))
    (haimage : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+(q+1)) ≫ eY.hom =
      homotopyRegrade (show (V+1)-S=V-S+1 by omega)
        (show (V+1)-c=V-c+1 by omega)
        (ordinarySuspendedRepresentative _ ((V+1)-S) ((V+1)-c)
          (finiteMayTopLabel T.Y c q hq S (V+1) v)))
    (heimage : e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+(q+1)) =
      (d-a) ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+(q+1))) :
    ∃ error : Ambient background T.Y (S+q+1,(V+1)+q),
      (background.classical.map T.g).pageMap 2 (S+q+1,(V+1)+q) error=0 ∧
      d ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+(q+1)) ≫ eY.hom =
      homotopyRegrade (show (V+1)-S=V-S+1 by omega)
        (show (V+1)-c=V-c+1 by omega)
        (ordinarySuspendedRepresentative _ ((V+1)-S) ((V+1)-c)
          (finiteMayTopLabel T.Y c q hq S (V+1) (v+error))) := by
  obtain ⟨e₂,error,herror,herrorTop⟩ := last_layer_positive_image_eq_finite_may_top
    T hf c q hq S V εp hεp (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε e) hefil
  have herrorRaw := native_positive_image_eq_finite_may_top
    T he hf c q hq S V ε εp hε hεp eY heY e error herrorTop
  rw [←ordinary_suspended_representative_regrade _ ((V+1)-S) (V-S+1)
    ((V+1)-c) (V-c+1) (by omega) (by omega)
    (finiteMayTopLabel T.Y c q hq S (V+1) error)] at herrorRaw
  have heG : (background.classical.map T.g).pageMap 2 (S+q+1,(V+1)+q) error=0 := by
    have hb := (KIP126.Literature.Standard.E2Exactness.e2ExactAtY
      T hf hg hh (S+q) (V+q)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+q) (V+q) e₂)).mpr ⟨e₂,rfl⟩
    have transport (p p' : ℤ×ℤ) (hp : p=p')
        (a : Ambient background T.Y p) (b : Ambient background T.Y p') (hab : HEq a b)
        (hb : (background.classical.map T.g).pageMap 2 p' b=0) :
        (background.classical.map T.g).pageMap 2 p a=0 := by
      subst p'
      simpa only [eq_of_heq hab] using hb
    exact transport _ _ (by congr 1; omega) _ _ herror hb
  refine ⟨error,heG,?_⟩
  let f := XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
    (normalizedTriangle background T he).mor₁) (c+(q+1)) ≫ eY.hom
  have hresidual : e ≫ f = (d-a) ≫ f := by
    simpa only [f,Category.assoc] using congrArg (fun b => b ≫ eY.hom) heimage
  have hsum : d ≫ f = a ≫ f + e ≫ f := by
    rw [hresidual,Preadditive.sub_comp]
    abel
  change d ≫ f = _
  rw [hsum]
  change a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
    (normalizedTriangle background T he).mor₁) (c+(q+1)) ≫ eY.hom +
    e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
    (normalizedTriangle background T he).mor₁) (c+(q+1)) ≫ eY.hom = _
  rw [haimage,herrorRaw,finite_may_top_label_add,
    ordinary_suspended_representative_add,regrade_add]

end
end KIP126.ProofTools.Internal.SyntheticCoverage
