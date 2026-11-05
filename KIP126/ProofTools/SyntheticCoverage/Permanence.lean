module

public import KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch

public import KIP126.ProofTools.MahowaldLeibniz.PositiveBranches

public import KIP126.ProofTools.Language

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.Paper.ExtensionRepresentatives
import all KIP126.ProofTools.FiniteLifting.LevelClassicalLift
import all KIP126.ProofTools.MahowaldLeibniz.LastLayer
import all KIP126.ProofTools.MahowaldLeibniz.OrdinaryLastLayer
import all KIP126.ProofTools.SyntheticCoverage.FullImage
import all KIP126.ProofTools.SyntheticCoverage.StrictSource
import all KIP126.ProofTools.SyntheticCoverage.Differentials
import all KIP126.ProofTools.SyntheticCoverage.CommonLift
import KIP126.SpectralSequence.Computation.State.Proofs
import KIP126.Literature.Standard.LambdaInversion

/-! Finite representative comparison for synthetic coverage arguments.
The ordinary-first-arrow two-layer permanence results use the E2 fold.
The filtered-group comparison controls complete higher-source subgroups.
The lemmas use finite lambda quotients and retain the specified full source. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Control of the entire higher source subgroup
preserves the target grade of every representative with the given source
grade. The nonzero target grade is preserved as well. -/
public theorem finite_filtered_image_comparison
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (F : ℤ → AddSubgroup A) (G : ℤ → AddSubgroup B)
    (hG : Antitone G) (φ : A →+ B) (s p : ℤ)
    (hcontrol : ∀ z, z ∈ F (s+1) → φ z ∈ G (p+1))
    (a c : A) (hsame : a-c ∈ F (s+1)) (hc : φ c ∈ G p) :
    φ a ∈ G p ∧ φ a-φ c ∈ G (p+1) ∧
      (φ a ∈ G (p+1) ↔ φ c ∈ G (p+1)) := by
  have hd : φ a-φ c ∈ G (p+1) := by
    simpa only [map_sub] using hcontrol (a-c) hsame
  refine ⟨?_,hd,?_⟩
  · simpa only [sub_add_cancel] using
      (G p).add_mem (hG (show p ≤ p+1 by omega) hd) hc
  · constructor
    · intro ha
      simpa only [sub_sub_cancel] using (G (p+1)).sub_mem ha hd
    · intro hc'
      simpa only [sub_add_cancel] using (G (p+1)).add_mem hd hc'

/-- The same E-infinity label detects every representative differing by the
next actual filtration subgroup. Zero labels and true boundaries are allowed. -/
private theorem detects_of_next_filtration_difference
    (X : SyntheticObject) (i : Tridegree)
    (y : (background.family.obj (X.obj background.nu background.auxiliary)).E₂ i)
    (a b : BiHom (i.2.1-i.1) i.2.2 (X.obj background.nu background.auxiliary))
    (hb : Detects (background.convergence X) i y b)
    (hd : a-b ∈ background.syntheticTower.filtrationSubmodule
      (X.obj background.nu background.auxiliary) (i.1+1) (i.2.1-i.1,i.2.2)) :
    Detects (background.convergence X) i y a := by
  obtain ⟨e,he,br,hbr,hbe⟩ := hb
  have hbmem : b ∈ background.syntheticTower.filtrationSubmodule
      (X.obj background.nu background.auxiliary) i.1 (i.2.1-i.1,i.2.2) := by
    have hh : b ∈ ModuleCat.subobjectModule _
        ((background.syntheticTower.filtration (X.obj background.nu background.auxiliary)).F
          i.1 (i.2.1-i.1,i.2.2)) := ⟨br,hbr⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hh
  have ha : a ∈ background.syntheticTower.filtrationSubmodule
      (X.obj background.nu background.auxiliary) i.1 (i.2.1-i.1,i.2.2) := by
    simpa only [sub_add_cancel] using
      (background.syntheticTower.filtrationSubmodule
        (X.obj background.nu background.auxiliary) i.1 (i.2.1-i.1,i.2.2)).add_mem
          (background.syntheticTower.filtrationSubmodule_antitone _ _
            (show i.1 ≤ i.1+1 by omega) hd) hbmem
  obtain ⟨ar,har⟩ := filtration_representative_exists background.syntheticTower
    (X.obj background.nu background.auxiliary) (i.2.1-i.1,i.2.2) i.1 a ha
  refine ⟨e,he,ar,har,hbe.trans ?_⟩
  symm
  apply (element_grade_equal_iff
    (background.syntheticTower.filtration (X.obj background.nu background.auxiliary))
      i.1 (i.2.1-i.1,i.2.2) ar br).mpr
  rw [har,hbr]
  simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hd

/-- Higher-source image comparison at the actual finite lambda quotient. The finite
candidate and the projection of the specified full source have the same
source grade; control includes all higher finite sources. Naturality
identifies the resulting target with the projection of the same full image. -/
private theorem finite_target_of_higher_source_control
    (A B : SyntheticObject)
    (g : A.obj background.nu background.auxiliary ⟶ B.obj background.nu background.auxiliary)
    (N : ℕ) (s p t w : ℤ)
    (y : (background.family.obj ((SyntheticObject.quotient N B).obj
      background.nu background.auxiliary)).E₂ (p,t,w))
    (a : BiHom (t-p) w (A.obj background.nu background.auxiliary))
    (c : BiHom (t-p) w (XModLambdaN (A.obj background.nu background.auxiliary) N))
    (hsame : a ≫ XModLambdaN.incl _ N-c ∈
      background.syntheticTower.filtrationSubmodule
        (XModLambdaN (A.obj background.nu background.auxiliary) N) (s+1) (t-p,w))
    (hcontrol : ∀ z : BiHom (t-p) w
        (XModLambdaN (A.obj background.nu background.auxiliary) N),
      z ∈ background.syntheticTower.filtrationSubmodule
        (XModLambdaN (A.obj background.nu background.auxiliary) N) (s+1) (t-p,w) →
      z ≫ XModLambdaN.map g N ∈ background.syntheticTower.filtrationSubmodule
        (XModLambdaN (B.obj background.nu background.auxiliary) N) (p+1) (t-p,w))
    (hc : Detects (background.convergence (.quotient N B)) (p,t,w) y
      (c ≫ XModLambdaN.map g N)) :
    Detects (background.convergence (.quotient N B)) (p,t,w) y
      ((a ≫ g) ≫ XModLambdaN.incl _ N) := by
  have hd := hcontrol (a ≫ XModLambdaN.incl _ N-c) hsame
  rw [Preadditive.sub_comp,Category.assoc,←XModLambdaN.incl_naturality,
    ←Category.assoc] at hd
  exact detects_of_next_filtration_difference (.quotient N B) (p,t,w) y _ _ hc hd

/-- A visible ordinary E₂ label from the finite comparison is permanent
and detects the realization of the specified full image. -/
private theorem finite_visible_target_of_higher_source_control
    (R : RealizationCoordinates background)
    (hcomp : LambdaInversionAdamsComparison background R)
    (A : SyntheticObject) (Y : (AdamsObject (coefficients := background.coefficients)))
    (g : A.obj background.nu background.auxiliary ⟶ background.nu.functor.obj (Y.obj background.auxiliary))
    (N : ℕ) (hN : 0 < N) (s p t w : ℤ)
    (hw : 0 ≤ t-w ∧ t-w < N)
    (y : Ambient background Y (p,t))
    (a : BiHom (t-p) w (A.obj background.nu background.auxiliary))
    (c : BiHom (t-p) w (XModLambdaN (A.obj background.nu background.auxiliary) N))
    (hsame : a ≫ XModLambdaN.incl _ N-c ∈
      background.syntheticTower.filtrationSubmodule
        (XModLambdaN (A.obj background.nu background.auxiliary) N) (s+1) (t-p,w))
    (hcontrol : ∀ z : BiHom (t-p) w
        (XModLambdaN (A.obj background.nu background.auxiliary) N),
      z ∈ background.syntheticTower.filtrationSubmodule
        (XModLambdaN (A.obj background.nu background.auxiliary) N) (s+1) (t-p,w) →
      z ≫ XModLambdaN.map g N ∈ background.syntheticTower.filtrationSubmodule
        (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N) (p+1) (t-p,w))
    (hc : Detects (background.convergence (.quotient N (.nu Y))) (p,t,w)
      ((background.family.quotientProjection (background.nu.functor.obj (Y.obj background.auxiliary)) N).pageMap
        2 (p,t,w) (nuWeightLabel background Y p t w (by omega) y))
      (c ≫ XModLambdaN.map g N)) :
    IsPermanent background Y (p,t) y ∧
      ClassicalDetects (background.classicalConvergence Y) (p,t) y
        ((R.sphere (t-p) w).hom ≫ background.recovery.realization.map (a ≫ g) ≫
          (hcomp.nu Y).target.hom) := by
  have hd := hcontrol (a ≫ XModLambdaN.incl _ N-c) hsame
  rw [Preadditive.sub_comp,Category.assoc,←XModLambdaN.incl_naturality,
    ←Category.assoc] at hd
  have hfinite := detects_of_next_filtration_difference (.quotient N (.nu Y))
    (p,t,w) _ _ _ hc hd
  have hy := KIP126.ProofTools.finite_target_from_full_lift_is_permanent
    Y N hN p t w hw y (a ≫ g) hfinite
  have hfull := finite_projection_detects_reflect Y N hN p t w hw y (a ≫ g) hfinite
  have hclass := (hcomp.nu Y).detects p t w _ (a ≫ g) hfull
  have hweight : t-((t-w).toNat:ℤ)=w := by
    rw [Int.toNat_of_nonneg hw.1]
    omega
  dsimp only [nuWeightLabel] at hclass
  rw [KIP126.ProofTools.Paper.paper_e2Map_regrade background _ p t _ w hweight,
    hcomp.nu_e2] at hclass
  exact ⟨hy,hclass⟩

/-- Coefficient comparison for two-layer permanence, including longer
last layers. Exactness gives a source error, and coefficient insertion
annihilates the specified target difference. -/
private theorem coefficient_kernel_of_common_finite_image
    (A B : SyntheticSpectrum) (g : A ⟶ B)
    (N i : ℕ) (hi : 0 < i) (hiN : i < N) (m w : ℤ)
    (a : BiHom m w A) (c : BiHom m w (XModLambdaN A N))
    (b : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj B))
    (v : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN B (N-i))))
    (hsame : a ≫ XModLambdaN.incl A i =
      c ≫ (background.quotients.tower A).rho i N hiN.le)
    (himage : c ≫ XModLambdaN.map g N =
      v ≫ ((background.quotients.tower B).triangle hi hiN).lambdaMap)
    (hfull : b ≫ lambdaPow i B = a ≫ g) :
    ∃ e : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
        (XModLambdaN A (N-i))),
      a ≫ XModLambdaN.incl A N-c =
        e ≫ ((background.quotients.tower A).triangle hi hiN).lambdaMap ∧
      (b ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl B (N-i)) -
          v - e ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.map g (N-i))) ≫
        ((background.quotients.tower B).triangle hi hiN).lambdaMap = 0 := by
  let T := (background.quotients.tower A).triangle hi hiN
  have hzero : (a ≫ XModLambdaN.incl A N-c) ≫ T.rho = 0 := by
    dsimp only [T]
    rw [(background.quotients.tower A).triangle_rho hi hiN,Preadditive.sub_comp,
      Category.assoc,(background.quotients.tower A).rho_quotient,hsame,sub_self]
  obtain ⟨e,he⟩ := (Triangle.mk T.lambdaMap T.rho T.delta).coyoneda_exact₂
    T.distinguished (a ≫ XModLambdaN.incl A N-c) hzero
  change BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
    (XModLambdaN A (N-i))) at e
  change a ≫ XModLambdaN.incl A N-c =
    e ≫ ((background.quotients.tower A).triangle hi hiN).lambdaMap at he
  have heimage :
      (e ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.map g (N-i))) ≫
        ((background.quotients.tower B).triangle hi hiN).lambdaMap =
      (a ≫ g) ≫ XModLambdaN.incl B N-c ≫ XModLambdaN.map g N := by
    rw [Category.assoc,(background.quotients.natural g).lambda_naturality hi hiN,
      ←Category.assoc,←he,Preadditive.sub_comp,Category.assoc,
      ←XModLambdaN.incl_naturality,←Category.assoc]
  have hbimage :
      (b ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl B (N-i))) ≫
        ((background.quotients.tower B).triangle hi hiN).lambdaMap =
      (a ≫ g) ≫ XModLambdaN.incl B N := by
    rw [Category.assoc,((background.quotients.tower B).triangle hi hiN).lambda_quotient,
      ←Category.assoc,hfull]
  refine ⟨e,he,?_⟩
  rw [Preadditive.sub_comp,Preadditive.sub_comp,hbimage,←himage,heimage,sub_self]

private theorem finite_top_label_sub
    (X : (AdamsObject (coefficients := background.coefficients))) (d : ℕ) (hd : 0 < d) (s t : ℤ)
    (x y : Ambient background X (s,t)) :
    finiteTopLabel X d hd s t (x-y) =
      finiteTopLabel X d hd s t x-finiteTopLabel X d hd s t y := by
  have hfirst : nativeFirstLabel X s t (x-y) =
      nativeFirstLabel X s t x-nativeFirstLabel X s t y := by
    unfold nativeFirstLabel
    rw [KIP126.ProofTools.Internal.Leibniz.firstLabel_sub,Preadditive.sub_comp]
  unfold finiteTopLabel finiteTopOfFirst
  rw [hfirst]
  simp only [shiftHomotopyClass,Functor.map_sub,Preadditive.comp_sub,
    KIP126.ProofTools.Internal.Mahowald.homotopy_regrade_sub,Preadditive.sub_comp]

/-- The last-layer difference is exactly a true early boundary, with the
inclusive library cutoff d+1 (the document writes B_{<d+2}). In particular,
for two layers d=1 this is B_{<3}, not B_{<2}. -/
private theorem finite_top_difference_zero_iff_boundary
    (X : (AdamsObject (coefficients := background.coefficients))) (d : ℕ) (hd : 0 < d) (s t : ℤ)
    (w v z : Ambient background X (s,t)) :
    finiteTopLabel X d hd s t w-finiteTopLabel X d hd s t v-
        finiteTopLabel X d hd s t z = 0 ↔
      w-v-z ∈ boundaries background X (d+1) (s,t) := by
  rw [←finite_top_label_sub,←finite_top_label_sub]
  exact finiteTopLabel_zero_iff_boundary X d hd s t (w-v-z)

/-- Every Q2 class with zero first projection is an actual highest-layer
label. The filtration required by highest-layer recognition follows from
coefficient exactness and the bottom filtration of shifted Q1. -/
private theorem two_layer_first_kernel_is_top_label
    (X : (AdamsObject (coefficients := background.coefficients))) (p t : ℤ)
    (a : BiHom (t-p) (t-1)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 2))
    (ha : a ≫ (background.quotients.tower _).rho 1 2 (by decide) = 0) :
    ∃ e : Ambient background X (p,t), a = finiteTopLabel X 1 (by decide) p t e := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let T := (background.quotients.tower A).triangle (show 0<1 by decide) (show 1<2 by decide)
  have hz : a ≫ T.rho = 0 := by
    simpa only [T,(background.quotients.tower A).triangle_rho] using ha
  obtain ⟨e,he⟩ := (Triangle.mk T.lambdaMap T.rho T.delta).coyoneda_exact₂
    T.distinguished a hz
  change BiHom (t-p) (t-1)
    ((SyntheticCategory.biShift (0,-(1:ℤ))).obj (XModLambdaN A 1)) at e
  have heF := KIP126.ProofTools.Internal.Leibniz.shifted_quotient_bottom_filtration
    X 1 (by decide) (-1) (t-p) (t-1) e
  have heP : FiltrationAtLeast background.syntheticTower p e := by
    convert heF using 1; omega
  have haP := map_preserves_filtration (background.convergentMap
    (.shift (0,-1) (.quotient 1 (.nu X))) (.quotient 2 (.nu X)) T.lambdaMap)
      (t-p,t-1) p e heP
  change FiltrationAtLeast background.syntheticTower p (e ≫ T.lambdaMap) at haP
  change a = e ≫ T.lambdaMap at he
  rw [←he] at haP
  exact finiteTopLabel_exists X 1 (by decide) p t a haP

private theorem lambda_first_label_projection_eq_top
    (X : (AdamsObject (coefficients := background.coefficients))) (p t : ℤ)
    (b : BiHom (t-p) t (background.nu.functor.obj (X.obj background.auxiliary)))
    (w : Ambient background X (p,t))
    (hb : b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel X p t w) :
    lambdaMultiply 1 b ≫ XModLambdaN.incl _ 2 =
      finiteTopLabel X 1 (by decide) p t w := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  rw [KIP126.ProofTools.Internal.FiniteLifting.lambda_multiply_raw]
  unfold finiteTopLabel finiteTopOfFirst finiteTopInclusion oneInclusionCast
  simp only [Nat.reduceAdd]
  rw [←hb]
  simp only [shiftHomotopyClass,Functor.map_comp,regrade_precomp,Category.assoc]
  rw [←((background.quotients.tower A).triangle (show 0<1 by decide)
    (show 1<2 by decide)).lambda_quotient]

/-- The complete two-layer error for an ordinary first arrow. Its denominator
is the actual d2 boundary subgroup. Source errors range over the entire E2
group, including elements which are not permanent. -/
private theorem ordinary_two_layer_error_is_boundary
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (p t : ℤ)
    (a : BiHom (t-p) (t-1) (background.nu.functor.obj (X.obj background.auxiliary)))
    (c : BiHom (t-p) (t-1)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 2))
    (b : BiHom (t-p) t (background.nu.functor.obj (Y.obj background.auxiliary)))
    (w v : Ambient background Y (p,t))
    (hsame : a ≫ XModLambdaN.incl _ 1 =
      c ≫ (background.quotients.tower _).rho 1 2 (by decide))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map f) 2 =
      finiteTopLabel Y 1 (by decide) p t v)
    (hb : lambdaMultiply 1 b = a ≫ background.nu.functor.map f)
    (hw : b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel Y p t w) :
    ∃ e : Ambient background X (p,t),
      w-v-(background.classical.map f).pageMap 2 (p,t) e ∈ boundaries background Y 2 (p,t) := by
  have hz : (a ≫ XModLambdaN.incl _ 2-c) ≫
      (background.quotients.tower _).rho 1 2 (by decide) = 0 := by
    rw [Preadditive.sub_comp,Category.assoc,
      (background.quotients.tower _).rho_quotient,hsame,sub_self]
  obtain ⟨e,he⟩ := two_layer_first_kernel_is_top_label X p t
    (a ≫ XModLambdaN.incl _ 2-c) hz
  have himage :
      (a ≫ XModLambdaN.incl _ 2-c) ≫ XModLambdaN.map (background.nu.functor.map f) 2 =
      finiteTopLabel Y 1 (by decide) p t ((background.classical.map f).pageMap 2 (p,t) e) := by
    rw [he,finite_top_label_ordinary_natural]
  have ht := lambda_first_label_projection_eq_top Y p t b w hw
  rw [hb] at ht
  rw [Preadditive.sub_comp,Category.assoc,←XModLambdaN.incl_naturality,
    ←Category.assoc,ht,hc] at himage
  refine ⟨e,(finite_top_difference_zero_iff_boundary Y 1 (by decide) p t w v
    ((background.classical.map f).pageMap 2 (p,t) e)).mp ?_⟩
  exact sub_eq_zero.mpr himage

/-- The final-boundary submodule with the initial-page projection used
by `IsFinalBoundary`. -/
public def finalBoundaries (Y : (AdamsObject (coefficients := background.coefficients))) (p : Bidegree) :
    Submodule ℤ (Ambient background Y p) :=
  let E := background.classical.obj (Y.obj background.auxiliary)
  let D := E.ssData p
  let n : WithTop ℕ := ↑(2-E.r₀).toNat
  LinearMap.range (Subobject.ofLE (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) ≫
    Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ D.pageπ n).hom

private theorem mem_finalBoundaries_iff (Y : (AdamsObject (coefficients := background.coefficients))) (p : Bidegree)
    (z : Ambient background Y p) :
    z ∈ finalBoundaries Y p ↔
      IsFinalBoundary (background.classical.obj (Y.obj background.auxiliary)) p z := Iff.rfl

private theorem finalBoundaries_le_permanentCycles (Y : (AdamsObject (coefficients := background.coefficients))) (p : Bidegree) :
    finalBoundaries Y p ≤ permanentCycles background Y p := by
  rintro z ⟨b,hb⟩
  let D := (background.classical.obj (Y.obj background.auxiliary)).ssData p
  apply KIP126.ProofTools.Paper.NuNumericalExtensions.permanent_member_of_cycle Y p z
  exact ⟨Subobject.ofLE (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) b,hb⟩

private theorem boundaries_le_finalBoundaries (Y : (AdamsObject (coefficients := background.coefficients))) (p : Bidegree) (r : ℤ) :
    boundaries background Y r p ≤ finalBoundaries Y p := by
  rintro z ⟨b,hb⟩
  let E := background.classical.obj (Y.obj background.auxiliary)
  let D := E.ssData p
  let n : WithTop ℕ := ↑(2-E.r₀).toNat
  have hn : n=0 := by dsimp [n,E]; rw [background.classical.firstPage]; rfl
  let j := Subobject.ofLE (D.B (↑(r-1).toNat)) (D.B ⊤) (D.B_mono le_top)
  refine ⟨j b,?_⟩
  change (j ≫ Subobject.ofLE (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) ≫
    Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ D.pageπ n) b = z
  rw [normalizeInitialProjection D n ⊤ hn le_top]
  change ((j ≫ Subobject.ofLE (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) ≫
    Subobject.ofLE (D.Z ⊤) (D.Z 0) (D.Z_anti bot_le)) ≫ D.pageπ 0 ≫ _) b = z
  have hj : j ≫ Subobject.ofLE (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) ≫
      Subobject.ofLE (D.Z ⊤) (D.Z 0) (D.Z_anti bot_le) =
      Subobject.ofLE (D.B (↑(r-1).toNat)) (D.Z 0)
        ((D.B_le_Z _).trans (D.Z_anti bot_le)) := by
    simp only [j,Subobject.ofLE_comp_ofLE]
  rw [hj]
  exact hb

/-- Replacement by a true-final-boundary congruent permanent label
preserves detection of the specified classical homotopy class,
including a zero final label. -/
private theorem classical_detects_of_final_boundary_difference
    (Y : (AdamsObject (coefficients := background.coefficients))) (p : Bidegree)
    (w v : Ambient background Y p)
    (a : HomotopyGroup (p.2-p.1) (Y.obj background.auxiliary))
    (hw : ClassicalDetects (background.classicalConvergence Y) p w a)
    (hd : IsFinalBoundary (background.classical.obj (Y.obj background.auxiliary)) p (w-v)) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) p v ∧
      ClassicalDetects (background.classicalConvergence Y) p v a := by
  let E := background.classical.obj (Y.obj background.auxiliary)
  let D := E.ssData p
  let n : WithTop ℕ := ↑(2-E.r₀).toNat
  obtain ⟨z,hz,ar,har,hgrade⟩ := hw
  obtain ⟨b,hb⟩ := hd
  let j := Subobject.ofLE (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤)
  let e := j b
  have he : (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫
      D.pageπ n) e = w-v := hb
  have hzv : (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫
      D.pageπ n) (z-e) = v := by
    rw [map_sub,hz,he]
    abel
  have hezero : D.pageπ ⊤ e = 0 :=
    (D.pageπ_eq_zero_iff ⊤ e).mpr ⟨b,rfl⟩
  refine ⟨⟨z-e,hzv⟩,z-e,hzv,ar,har,?_⟩
  change ((background.classicalConvergence Y).identification p).hom
    (D.pageπ ⊤ (z-e)) = _
  rw [map_sub,hezero,sub_zero]
  exact hgrade

/-- The terminal image condition removes the complete E2 source error inside P.
Its early error is promoted to a true final boundary, preserving detection
of this same classical class. -/
private theorem classical_detects_of_terminal_image
    (X Y : (AdamsObject (coefficients := background.coefficients))) (q p : Bidegree)
    (F : Ambient background X q →ₗ[ℤ] Ambient background Y p)
    (P : Submodule ℤ (Ambient background Y p))
    (hP : permanentCycles background Y p ≤ P)
    (hterminal : F.range ⊓ P ≤ finalBoundaries Y p)
    (w v : Ambient background Y p) (hw : w ∈ permanentCycles background Y p) (hv : v ∈ P)
    (e : Ambient background X q) (r : ℤ)
    (herr : w-v-F e ∈ boundaries background Y r p)
    (a : HomotopyGroup (p.2-p.1) (Y.obj background.auxiliary))
    (hdet : ClassicalDetects (background.classicalConvergence Y) p w a) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) p v ∧
      ClassicalDetects (background.classicalConvergence Y) p v a := by
  have herrFinal := boundaries_le_finalBoundaries Y p r herr
  have herrP := hP (finalBoundaries_le_permanentCycles Y p herrFinal)
  have hFeP : F e ∈ P := by
    have h := P.sub_mem (P.sub_mem (hP hw) hv) herrP
    simpa only [sub_sub_cancel] using h
  have hFe := hterminal (show F e ∈ F.range ⊓ P from ⟨⟨e,rfl⟩,hFeP⟩)
  have hdiff : w-v ∈ finalBoundaries Y p := by
    simpa only [sub_add_cancel] using (finalBoundaries Y p).add_mem herrFinal hFe
  exact classical_detects_of_final_boundary_difference Y p w v a hdet hdiff

private theorem two_layer_top_first_zero
    (Y : (AdamsObject (coefficients := background.coefficients))) (p t : ℤ) (v : Ambient background Y (p,t)) :
    finiteTopLabel Y 1 (by decide) p t v ≫
      (background.quotients.tower _).rho 1 2 (by decide) = 0 := by
  let A := background.nu.functor.obj (Y.obj background.auxiliary)
  let T := (background.quotients.tower A).triangle (show 0<1 by decide) (show 1<2 by decide)
  have hz : T.lambdaMap ≫ T.rho = 0 :=
    comp_distTriang_mor_zero₁₂ (Triangle.mk T.lambdaMap T.rho T.delta) T.distinguished
  rw [(background.quotients.tower A).triangle_rho] at hz
  unfold finiteTopLabel finiteTopOfFirst finiteTopInclusion oneInclusionCast
  rw [Category.assoc]
  dsimp only [T,A] at hz
  rw [hz,comp_zero]

/-- The ordinary-arrow two-layer permanence conclusion assumes a common
finite representative c. It uses every source-error direction and preserves
the specified full source image. Obtaining c from an E₂ zigzag requires
the specified triangle-lifting comparison. -/
private theorem ordinary_two_layer_finite_source_permanence
    (R : RealizationCoordinates background)
    (hcomp : LambdaInversionAdamsComparison background R)
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (p t : ℤ)
    (a : BiHom (t-p) (t-1) (background.nu.functor.obj (X.obj background.auxiliary)))
    (c : BiHom (t-p) (t-1)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 2))
    (v : Ambient background Y (p,t)) (P : Submodule ℤ (Ambient background Y (p,t)))
    (hP : permanentCycles background Y (p,t) ≤ P) (hv : v ∈ P)
    (hterminal : ((background.classical.map f).pageMap 2 (p,t)).hom.range ⊓ P ≤
      finalBoundaries Y (p,t))
    (hsame : a ≫ XModLambdaN.incl _ 1 =
      c ≫ (background.quotients.tower _).rho 1 2 (by decide))
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map f) 2 =
      finiteTopLabel Y 1 (by decide) p t v) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) (p,t) v ∧
      ClassicalDetects (background.classicalConvergence Y) (p,t) v
        ((R.sphere (t-p) (t-1)).hom ≫
          background.recovery.realization.map (a ≫ background.nu.functor.map f) ≫
            (hcomp.nu Y).target.hom) := by
  have hz : (a ≫ background.nu.functor.map f) ≫ XModLambdaN.incl _ 1 = 0 := by
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hsame,
      Category.assoc,(background.quotients.natural (background.nu.functor.map f)).rho_naturality,
      ←Category.assoc,hc]
    exact two_layer_top_first_zero Y p t v
  obtain ⟨b,hb,w,hw,hwp,hdet⟩ := full_image_first_label_detects R hcomp
    (background.nu.functor.obj (X.obj background.auxiliary)) Y (background.nu.functor.map f) p t a hz
  obtain ⟨e,herr⟩ := ordinary_two_layer_error_is_boundary X Y f p t a c b w v
    hsame hc hb hw
  exact classical_detects_of_terminal_image X Y (p,t) (p,t)
    ((background.classical.map f).pageMap 2 (p,t)).hom P hP hterminal w v hwp hv e 2 herr _ hdet

/-- The ordinary-arrow two-layer argument for every specified strict
classical source. The full synthetic lift is constructed from the specified
comparison, given the common finite triangle lift.
The realization coordinate is the one used by that comparison. -/
private theorem ordinary_two_layer_permanence_of_common_lift
    (hcomp : LambdaInversionAdamsComparison background KIP126.Literature.Standard.realizationData)
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t : ℤ) (x : Ambient background X (s,t))
    (a : HomotopyGroup (t-s) (X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (X.obj background.auxiliary)) (s,t) x)
    (ha : ClassicalDetects (background.classicalConvergence X) (s,t) x a)
    (hfx : (background.classical.map f).pageMap 2 (s,t) x = 0)
    (v : Ambient background Y (s+1,t+1))
    (P : Submodule ℤ (Ambient background Y (s+1,t+1)))
    (hP : permanentCycles background Y (s+1,t+1) ≤ P) (hv : v ∈ P)
    (hterminal : ((background.classical.map f).pageMap 2 (s+1,t+1)).hom.range ⊓ P ≤
      finalBoundaries Y (s+1,t+1))
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 2))
    (hfirst : c ≫ (background.quotients.tower _).rho 1 2 (by decide) =
      nativeFirstLabel X s t x)
    (himage : c ≫ XModLambdaN.map (background.nu.functor.map f) 2 =
      homotopyRegrade (show (t+1)-(s+1)=t-s by omega) (show (t+1)-1=t by omega)
        (finiteTopLabel Y 1 (by decide) (s+1) (t+1) v)) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) (s+1,t+1) v ∧
      ClassicalDetects (background.classicalConvergence Y) (s+1,t+1) v
        (eqToHom (congrArg (Sphere (C := Spectrum))
          (show (t+1)-(s+1)=t-s by omega)) ≫ a ≫ f) := by
  obtain ⟨b,hb,u,hu,w,hw,hwp,hdet⟩ :=
    prescribed_ordinary_image_first_label hcomp X Y f s t x a hx ha hfx
  let b' : BiHom ((t+1)-(s+1)) ((t+1)-1)
      (background.nu.functor.obj (X.obj background.auxiliary)) :=
    homotopyRegrade (by omega) (by omega) b
  let c' : BiHom ((t+1)-(s+1)) ((t+1)-1)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 2) :=
    homotopyRegrade (by omega) (by omega) c
  have hsame : b' ≫ XModLambdaN.incl _ 1 =
      c' ≫ (background.quotients.tower _).rho 1 2 (by decide) := by
    dsimp only [b',c']
    rw [←regrade_comp,←regrade_comp,hb,hfirst]
  have hc : c' ≫ XModLambdaN.map (background.nu.functor.map f) 2 =
      finiteTopLabel Y 1 (by decide) (s+1) (t+1) v := by
    dsimp only [c']
    rw [←regrade_comp,himage,KIP126.ProofTools.Internal.Leibniz.normalized_homotopy_regrade_trans]
    rfl
  have hu' : lambdaMultiply 1 u = b' ≫ background.nu.functor.map f := by
    simpa only [b',regrade_comp] using hu
  obtain ⟨e,herr⟩ := ordinary_two_layer_error_is_boundary X Y f (s+1) (t+1)
    b' c' u w v hsame hc hu' hw
  exact classical_detects_of_terminal_image X Y (s+1,t+1) (s+1,t+1)
    ((background.classical.map f).pageMap 2 (s+1,t+1)).hom P hP hterminal
    w v hwp hv e 2 herr _ hdet

/-- The whole-kernel premise of the two-layer proposition implies its
terminal image premise because the two consecutive actual first-layer maps
compose to zero. The source range includes every E2 direction. -/
private theorem terminal_image_condition_of_kernel
    (X Y : (AdamsObject (coefficients := background.coefficients))) (q p : Bidegree)
    {V : Type*} [AddCommGroup V] [Module ℤ V]
    (F : Ambient background X q →ₗ[ℤ] Ambient background Y p)
    (G : Ambient background Y p →ₗ[ℤ] V)
    (P : Submodule ℤ (Ambient background Y p))
    (hGF : G.comp F = 0) (hkernel : P ⊓ G.ker ≤ finalBoundaries Y p) :
    F.range ⊓ P ≤ finalBoundaries Y p := by
  rintro z ⟨⟨e,rfl⟩,heP⟩
  apply hkernel
  refine ⟨heP,?_⟩
  change G (F e) = 0
  exact LinearMap.congr_fun hGF e

/-- The positive-h whole-kernel condition implies the terminal image
condition, by the zero composite of the triangle maps. -/
private theorem ordinary_terminal_image_of_triangle_kernel
    (T : TriangleData background.auxiliary) (s t : ℤ)
    (P : Submodule ℤ (Ambient background T.Y (s,t)))
    (hker : ∀ z : Ambient background T.Y (s,t), z ∈ P →
      (background.classical.map T.g).pageMap 2 (s,t) z = 0 →
      IsFinalBoundary (background.classical.obj (T.Y.obj background.auxiliary)) (s,t) z) :
    ((background.classical.map T.f).pageMap 2 (s,t)).hom.range ⊓ P ≤ finalBoundaries T.Y (s,t) := by
  rintro z ⟨⟨e,rfl⟩,heP⟩
  exact hker _ heP (ordinary_triangle_composite_zero T s t e)

/-- The same kernel-to-image implication with the actual positive G2
operation, keeping its shifted target bidegree. -/
private theorem positive_second_terminal_image_of_triangle_kernel
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]))
    (s t : ℤ) (P : Submodule ℤ (Ambient background T.Y (s,t)))
    (hker : ∀ z : Ambient background T.Y (s,t), z ∈ P →
      positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) s t z = 0 →
      IsFinalBoundary (background.classical.obj (T.Y.obj background.auxiliary)) (s,t) z) :
    ((background.classical.map T.f).pageMap 2 (s,t)).hom.range ⊓ P ≤ finalBoundaries T.Y (s,t) := by
  rintro z ⟨⟨e,rfl⟩,heP⟩
  exact hker _ heP (positive_second_triangle_composite_zero T hf hg hh hT s t e)


/-- Two-layer permanence for (alpha,beta,gamma)=(0,0,1).
The actual H2 and d2 inputs construct the common finite representative;
the conclusion retains every specified class strictly detected by x. -/
public theorem two_layer_permanence_positive_h
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (s t : ℤ) (_hs : 0 ≤ s)
    (z : Ambient background T.Z (s,t)) (x : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+1+1,t+1))
    (hH : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      2 (s,t) (s+1+1,t+1) z ((background.classical.map T.g).pageMap 2 (s+1+1,t+1) v))
    (a : HomotopyGroup (t-(s+1)) (T.X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s+1,t) x)
    (ha : ClassicalDetects (background.classicalConvergence T.X) (s+1,t) x a)
    (hfx : (background.classical.map T.f).pageMap 2 (s+1,t) x=0)
    (P : Submodule ℤ (Ambient background T.Y (s+1+1,t+1)))
    (hP : permanentCycles background T.Y (s+1+1,t+1) ≤ P) (hv : v ∈ P)
    (hker : ∀ z : Ambient background T.Y (s+1+1,t+1), z ∈ P →
      (background.classical.map T.g).pageMap 2 (s+1+1,t+1) z=0 →
      IsFinalBoundary (background.classical.obj (T.Y.obj background.auxiliary)) (s+1+1,t+1) z) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+1+1,t+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+1+1,t+1) v
        (eqToHom (congrArg (Sphere (C := Spectrum))
          (show (t+1)-(s+1+1)=t-(s+1) by omega)) ≫ a ≫ T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨c,hfirst,himage⟩ := two_layer_common_lift_positive_h T (by simp [hf,hg,hh])
    hT hf hg hh s t z x v hH hd
  exact ordinary_two_layer_permanence_of_common_lift hcomp T.X T.Y T.f (s+1) t x a hx ha
    hfx v P hP hv (ordinary_terminal_image_of_triangle_kernel T (s+1+1) (t+1) P hker)
    c hfirst himage

/-- Two-layer permanence for (alpha,beta,gamma)=(0,1,0).
The positive second operation and its complete kernel are the actual ones
of the same compatible normalized triangle. -/
public theorem two_layer_permanence_positive_g
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (s t : ℤ) (_hs : 0 ≤ s+1)
    (z : Ambient background T.Z (s+1,t+1)) (x : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+1+1,t+1))
    (hH : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((background.classical.map T.h).pageMap 2 (s+1,t+1) z) (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      2 (s+1,t+1) ((s+1+1)+1,(t+1)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (s+1+1) (t+1) v))
    (a : HomotopyGroup (t-(s+1)) (T.X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s+1,t) x)
    (ha : ClassicalDetects (background.classicalConvergence T.X) (s+1,t) x a)
    (hfx : (background.classical.map T.f).pageMap 2 (s+1,t) x=0)
    (P : Submodule ℤ (Ambient background T.Y (s+1+1,t+1)))
    (hP : permanentCycles background T.Y (s+1+1,t+1) ≤ P) (hv : v ∈ P)
    (hker : ∀ z : Ambient background T.Y (s+1+1,t+1), z ∈ P →
      positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (s+1+1) (t+1) z=0 →
      IsFinalBoundary (background.classical.obj (T.Y.obj background.auxiliary)) (s+1+1,t+1) z) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+1+1,t+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+1+1,t+1) v
        (eqToHom (congrArg (Sphere (C := Spectrum))
          (show (t+1)-(s+1+1)=t-(s+1) by omega)) ≫ a ≫ T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨c,hfirst,himage⟩ := two_layer_common_lift_positive_g T (by simp [hf,hg,hh])
    hT hf hg hh s t z x v hH hd
  exact ordinary_two_layer_permanence_of_common_lift hcomp T.X T.Y T.f (s+1) t x a hx ha
    hfx v P hP hv (positive_second_terminal_image_of_triangle_kernel T hf hg hh hT
      (s+1+1) (t+1) P hker) c hfirst himage

/-- The quotient-kernel condition eliminates the last ambiguity inside
the candidate subspace, using boundary predicates of the ordinary Adams
sequence of Y. -/
private theorem classical_detects_of_quotient_kernel
    (Y : (AdamsObject (coefficients := background.coefficients))) (p : Bidegree)
    {V : Type*} [AddCommGroup V]
    (G : Ambient background Y p →+ V) (BZ : AddSubgroup V)
    (P : AddSubgroup (Ambient background Y p))
    (hkernel : ∀ z, z ∈ P → G z ∈ BZ →
      IsFinalBoundary (background.classical.obj (Y.obj background.auxiliary)) p z)
    (w v : Ambient background Y p) (hwP : w ∈ P) (hvP : v ∈ P)
    (hG : G w-G v ∈ BZ)
    (a : HomotopyGroup (p.2-p.1) (Y.obj background.auxiliary))
    (hw : ClassicalDetects (background.classicalConvergence Y) p w a) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) p v ∧
      ClassicalDetects (background.classicalConvergence Y) p v a := by
  exact classical_detects_of_final_boundary_difference Y p w v a hw
    (hkernel (w-v) (P.sub_mem hwP hvP) (by simpa only [map_sub] using hG))

end
end KIP126.ProofTools.Internal.SyntheticCoverage
