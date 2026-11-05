module
import all KIP126.Literature.BocksteinOriginalSuccessor
import all KIP126.Literature.BocksteinComparisonInput
import all KIP126.Literature.BocksteinBoundaryInput
public import KIP126.AdamsSynthetic.Completed.Background
import KIP126.AdamsSynthetic.Completed.Filtration
import KIP126.AdamsSynthetic.Completed.Separation
import KIP126.AdamsSynthetic.Completed.ClassicalSupport
public import KIP126.Literature.ModelResults
import all KIP126.Literature.ModelResults
import all KIP126.Literature.Classical
import all KIP126.Literature.ClassicalRange
import all KIP126.Literature.EInfinity
import all KIP126.Literature.Triangles
import all KIP126.Literature.May

public import KIP126.AdamsSynthetic.Completed.SpectrumScope
public import KIP126.Literature.Standard.ClassicalInputs
import all KIP126.Literature.Standard.ClassicalInputs
public import KIP126.Literature.Standard.AdamsComparison
import all KIP126.Literature.Standard.AdamsComparison
public import KIP126.Literature.Standard.NormalizedTriangles
import all KIP126.Literature.Standard.NormalizedTriangles

/-! FiniteLift on the fixed literature background. -/

@[expose] section
set_option autoImplicit false
noncomputable section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)

section FiniteLiftConstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/- Finite lifting through the infinity-page presentation,
common-representative labels, restriction maps and separated
finite-quotient filtration. -/
private theorem filtration_at_zero (X : SyntheticSpectrum) (m w : ℤ)
    (a : BiHom m w X) : FiltrationAtLeast background.syntheticTower 0 a := by
  refine ⟨a ≫ (background.syntheticTower.tower X).zeroIso.inv, ?_⟩
  change (a ≫ (background.syntheticTower.tower X).zeroIso.inv) ≫
    (background.syntheticTower.tower X).projection 0 = a
  simp only [AbstractAdamsTower.projection, Int.toNat_zero,
    (background.syntheticTower.tower X).map_self]
  erw [Category.assoc, Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private theorem filtration_of_infinity_zero (X : SyntheticObject)
    (s t m w : ℤ) (hst : s ≤ t)
    (hz : ∀ j, s ≤ j → j < t → IsZero
      (((background.family.obj (X.obj background.nu background.auxiliary)).sequence.ssData (j,m+j,w)).eInfty))
    (a : BiHom m w (X.obj background.nu background.auxiliary)) :
    FiltrationAtLeast background.syntheticTower s a ↔
      FiltrationAtLeast background.syntheticTower t a := by
  have hgraded (j : ℤ) (hj : s ≤ j) (hjt : j < t) :
      IsZero ((background.syntheticTower.filtration (X.obj background.nu background.auxiliary)).associatedGraded j (m,w)) :=
    (hz j hj hjt).of_iso (towerGradedIso (background.convergence X) (m,w) j).symm
  have he := (background.syntheticTower.filtration (X.obj background.nu background.auxiliary)).eq_of_associatedGraded_isZero
    s t (m,w) hst hgraded
  have he' := congrArg (fun Q => a ∈
    (ModuleCat.subobjectModule (syntheticHomotopy (X.obj background.nu background.auxiliary) (m,w))) Q) he
  simpa only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply,
    FiltrationAtLeast] using Iff.of_eq he'

private theorem finite_infinity_zero (X : AdamsObject) (q : ℕ) (hq : 0 < q)
    (s t w : ℤ) (hw : ¬ (0 ≤ t-w ∧ t-w < q)) :
    IsZero (((background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) q).sequence.ssData
      (s,t,w)).eInfty) := by
  haveI : Subsingleton (finiteEInftyModel background X q (s,t) w) := by
    simp only [finiteEInftyModel, hw, ite_false]
    infer_instance
  haveI : Subsingleton (((background.family.quotient
      (background.nu.functor.obj (X.obj background.auxiliary)) q).sequence.ssData (s,t,w)).eInfty) :=
    (eInfinity_finite X q hq (s,t) w).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem finite_high_filtration_zero (X : AdamsObject) (q : ℕ) (hq : 0 < q)
    (m w s : ℤ) (hs : (q:ℤ) ≤ m+s-w)
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : FiltrationAtLeast background.syntheticTower s a) : a = 0 := by
  apply KIP126.AdamsSynthetic.Completed.synthetic_homotopy_separated (.nu X) q m w a
  intro j
  by_cases hj : s ≤ (j:ℤ)
  · exact (filtration_of_infinity_zero (.quotient q (.nu X)) s j m w hj
      (fun k hk _ => finite_infinity_zero X q hq k (m+k) w (by omega)) a).mp ha
  · exact background.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) ha

private theorem finite_filtration_exhaustive (X : AdamsObject) (q : ℕ) (hq : 0 < q)
    (s t : ℤ) (a : BiHom (t-s) t
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q)) :
    FiltrationAtLeast background.syntheticTower s a := by
  have hzero := filtration_at_zero _ (t-s) t a
  by_cases hs : s ≤ 0
  · exact background.syntheticTower.filtrationSubmodule_antitone _ (t-s,t) hs hzero
  · exact (filtration_of_infinity_zero (.quotient q (.nu X)) 0 s (t-s) t
      (by omega) (fun k _ hk => finite_infinity_zero X q hq k (t-s+k) t (by omega)) a).mp hzero

private theorem finite_lift_detects_map {A B : SyntheticObject}
    (g : A.obj background.nu background.auxiliary ⟶ B.obj background.nu background.auxiliary)
    (i : Tridegree) {x : (background.family.obj (A.obj background.nu background.auxiliary)).Page 2 i}
    {a : BiHom (i.2.1-i.1) i.2.2 (A.obj background.nu background.auxiliary)}
    (h : Detects (background.convergence A) i x a) :
    Detects (background.convergence B) i (background.family.pageMap g 2 i x) (a ≫ g) := by
  let M := background.convergentMap A B g
  obtain ⟨e, he, b, hb, hgr⟩ := h
  let hc := M.comparison.filtration_compat i.1 (i.2.1-i.1,i.2.2)
  let b' := hc.choose b
  refine ⟨(background.family.map g).eInftyMap i e, rhoInfinityRepresentativeMap g i he, b', ?_, ?_⟩
  · have hmap := ConcreteCategory.congr_hom hc.choose_spec b
    have heq := ConcreteCategory.congr_hom
      (congrFun M.abutment_eq (i.2.1-i.1,i.2.2))
      (((background.syntheticTower.filtration (A.obj background.nu background.auxiliary)).F
        i.1 (i.2.1-i.1,i.2.2)).arrow b)
    change ((background.syntheticTower.filtration (B.obj background.nu background.auxiliary)).F
      i.1 (i.2.1-i.1,i.2.2)).arrow b' = _
    exact hmap.trans (heq.trans (congrArg (fun z => z ≫ g) hb))
  · have hm := M.comparison.iso_compat i
    simp only [SyntheticTowerConvergence.toConvergence, Filtration.transportGraded_self,
      Category.comp_id] at hm
    rw [M.infinity_eq] at hm
    have hm' := ConcreteCategory.congr_hom hm e
    change ((background.convergence B).identification i).hom ((background.family.map g).eInftyMap i e) =
      Filtration.inducedAssocGradedMap M.comparison.aMap M.comparison.filtration_compat
        i.1 (i.2.1-i.1,i.2.2) (((background.convergence A).identification i).hom e) at hm'
    rw [hgr] at hm'
    have hg : (background.syntheticTower.filtration (A.obj background.nu background.auxiliary)).toAssociatedGraded
        i.1 (i.2.1-i.1,i.2.2) ≫
        Filtration.inducedAssocGradedMap M.comparison.aMap M.comparison.filtration_compat
          i.1 (i.2.1-i.1,i.2.2) =
        hc.choose ≫ (background.syntheticTower.filtration (B.obj background.nu background.auxiliary)).toAssociatedGraded
          i.1 (i.2.1-i.1,i.2.2) := by
      exact cokernel.π_desc _ _ _
    exact hm'.trans (ConcreteCategory.congr_hom hg b)

private def finiteLabel (X : AdamsObject) (q : ℕ) (s t : ℤ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :=
  (background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap
    2 (s,t,t) (nuWeightLabel background X s t t le_rfl x)

private theorem finite_detects_unique (X : AdamsObject) (s t : ℤ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (a b : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1))
    (ha : Detects (background.convergence (.quotient 1 (.nu X))) (s,t,t) (finiteLabel X 1 s t x) a)
    (hb : Detects (background.convergence (.quotient 1 (.nu X))) (s,t,t) (finiteLabel X 1 s t x) b) :
    a = b := by
  apply sub_eq_zero.mp
  exact finite_high_filtration_zero X 1 (by decide) (t-s) t (s+1) (by omega) (a-b)
    (detects_sub_filtration (background.convergence (.quotient 1 (.nu X))) (s,t,t) ha hb)

private theorem finite_detects_rho (X : AdamsObject) (q : ℕ) (hq : 0 < q)
    (s t : ℤ) (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : Detects (background.convergence (.quotient q (.nu X))) (s,t,t) (finiteLabel X q s t x) a) :
    Detects (background.convergence (.quotient 1 (.nu X))) (s,t,t) (finiteLabel X 1 s t x)
      (a ≫ (background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho 1 q hq) := by
  have h := finite_lift_detects_map (A := .quotient q (.nu X)) (B := .quotient 1 (.nu X))
    ((background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho 1 q hq) (s,t,t) ha
  have hl := rhoFiniteLabelMap X 1 q hq s t t (nuWeightLabel background X s t t le_rfl x)
  change background.family.pageMap _ 2 _ (finiteLabel X q s t x) = finiteLabel X 1 s t x at hl
  exact Eq.mp (congrArg (fun z => Detects (background.convergence (.quotient 1 (.nu X)))
    (s,t,t) z (a ≫ (background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho 1 q hq)) hl) h

private def nativeLabel (X : AdamsObject) (s t : ℤ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :
    BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1) :=
  KIP126.Literature.firstLabel background X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1

private theorem native_label_injective (X : AdamsObject) (s t : ℤ) :
    Function.Injective (nativeLabel X s t) := by
  intro x y h
  haveI : IsIso (XModLambdaN.map
    (SyntheticCategory.biShift_zero.hom.app (background.nu.functor.obj (X.obj background.auxiliary))) 1) := by
    change IsIso ((background.quotients.functoriality.functor 1).map
      (SyntheticCategory.biShift_zero.hom.app _))
    infer_instance
  have he : KIP126.Literature.firstLabel background X s t x = KIP126.Literature.firstLabel background X s t y :=
    (cancel_mono (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)).mp h
  have cast_inj {A : ℤ → Type} {u v : ℤ} (h : u=v) :
      Function.Injective (fun z : A u => Eq.mp (congrArg A h) z) := (Equiv.cast _).injective
  apply (background.firstQuotient X 0 s t).symm.injective
  exact cast_inj (A := fun w => BiHom (t-s) w (XModLambdaN (KIP126.Literature.nuZero background X) 1))
    (Int.add_zero t) he

private def trPage {X : SyntheticSpectrum} {s t w w' : ℤ} (h : w=w')
    (x : (background.family.obj X).Page 2 (s,t,w)) : (background.family.obj X).Page 2 (s,t,w') :=
  cast (congrArg (fun q => ↥((background.family.obj X).Page 2 (s,t,q))) h) x

private theorem detects_tr (X : SyntheticObject) {s t w w' : ℤ} (h : w=w')
    {x : (background.family.obj (X.obj background.nu background.auxiliary)).Page 2 (s,t,w)}
    {a : BiHom (t-s) w (X.obj background.nu background.auxiliary)}
    (hd : Detects (background.convergence X) (s,t,w) x a) :
    Detects (background.convergence X) (s,t,w') (trPage h x)
      (cast (congrArg (fun q => BiHom (t-s) q (X.obj background.nu background.auxiliary)) h) a) := by
  subst w'
  exact hd

private theorem page_map_tr {X Y : SyntheticSpectrum} (f : X ⟶ Y) {s t w w' : ℤ}
    (h : w=w') (x : (background.family.obj X).Page 2 (s,t,w)) :
    trPage h (background.family.pageMap f 2 (s,t,w) x) =
      background.family.pageMap f 2 (s,t,w') (trPage h x) := by
  subst w'
  rfl

private theorem native_label_detects (X : AdamsObject) (s t : ℤ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :
    Detects (background.convergence (.quotient 1 (.nu X))) (s,t,t)
      (finiteLabel X 1 s t x) (nativeLabel X s t x) := by
  let V := background.nu.functor.obj (X.obj background.auxiliary)
  let Z := (SyntheticCategory.biShift (0,0)).obj V
  let e := SyntheticCategory.biShift_zero.app V
  let q := (background.quotients.functoriality.functor 1).mapIso e
  let u0 : (background.family.obj Z).Page 2 (s,t,t+0) := by
    simpa only [Nat.cast_zero, sub_zero] using background.comparison.nuE2 X 0 s t 0 x
  let u := trPage (Int.add_zero t) u0
  have hd : Detects (background.convergence (.quotient 1 (.shift (0,0) (.nu X)))) (s,t,t)
      (background.family.pageMap (XModLambdaN.incl Z 1) 2 (s,t,t) u)
      (KIP126.Literature.firstLabel background X s t x) := by
    have h := detects_tr (.quotient 1 (.shift (0,0) (.nu X))) (Int.add_zero t)
      (background.comparisonCompatible.first_quotient X 0 s t x)
    have htr := page_map_tr (XModLambdaN.incl Z 1) (Int.add_zero t) u0
    exact Eq.mp (congrArg (fun z => Detects (background.convergence (.quotient 1 (.shift (0,0) (.nu X))))
      (s,t,t) z (KIP126.Literature.firstLabel background X s t x)) htr) h
  have hm := finite_lift_detects_map (A := .quotient 1 (.shift (0,0) (.nu X)))
    (B := .quotient 1 (.nu X)) q.hom (s,t,t) hd
  have hn : background.family.pageMap e.hom 2 (s,t,t) u = nuWeightLabel background X s t t le_rfl x := by
    have hregrade {A : SyntheticAdamsSS.{0}} {i j : Tridegree} (h : i=j) (a : A.E₂ i) :
        HEq (regradeE2 h a) a := by subst j; rfl
    have hdepth (n : ℕ) (hn : n=0) :
        HEq (targetNuLabel background X s t n x) (targetNuLabel background X s t 0 x) := by
      subst n
      rfl
    have hweight : HEq (nuWeightLabel background X s t t le_rfl x) (targetNuLabel background X s t 0 x) :=
      (hregrade _ _).trans (hdepth (t-t).toNat (by omega))
    let v : (background.family.obj Z).Page 2 (s,t,t-(0:ℕ)) := by
      simpa only [add_zero] using background.comparison.nuE2 X 0 s t 0 x
    have hv : trPage (show t-(0:ℕ)=t by simp) v = u := by
      simp only [v, u, u0, trPage, eq_mp_eq_cast, cast_cast]
    have hmap := page_map_tr e.hom (show t-(0:ℕ)=t by simp) v
    have hmap' : trPage (show t-(0:ℕ)=t by simp) (targetNuLabel background X s t 0 x) =
        background.family.pageMap e.hom 2 (s,t,t) u := hmap.trans (congrArg _ hv)
    apply eq_of_heq
    exact ((cast_heq _ _).symm.trans (heq_of_eq hmap')).symm.trans hweight.symm
  have hp : background.family.pageMap q.hom 2 (s,t,t)
      (background.family.pageMap (XModLambdaN.incl Z 1) 2 (s,t,t) u) =
        finiteLabel X 1 s t x := by
    change ((background.family.map (XModLambdaN.incl Z 1)).pageMap 2 (s,t,t) ≫
      (background.family.map q.hom).pageMap 2 (s,t,t)) u = _
    rw [← SpectralSequenceMorphism.pageMap_comp, ← background.family.map_comp]
    change (background.family.map (XModLambdaN.incl Z 1 ≫ XModLambdaN.map e.hom 1)).pageMap 2 (s,t,t) u = _
    rw [← XModLambdaN.incl_naturality, background.family.map_comp,
      SpectralSequenceMorphism.pageMap_comp]
    change background.family.pageMap (XModLambdaN.incl V 1) 2 (s,t,t)
      (background.family.pageMap e.hom 2 (s,t,t) u) = _
    rw [hn]
    rfl
  exact Eq.mp (congrArg (fun z => Detects (background.convergence (.quotient 1 (.nu X)))
    (s,t,t) z (nativeLabel X s t x)) hp) hm

private theorem generic_reaches_cycle
    (E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ))
    (h0 : E.r₀=2) (q : ℕ) (hq : 0 < q) (p : ℤ × ℤ) (x : E.Page 2 p) :
    ReachesPage E (q+1) p x ↔
      ∃ z : (Subobject.underlying.obj ((E.ssData p).Z (↑((q:ℤ)-1).toNat : WithTop ℕ)) : ModuleCat ℤ),
        (Subobject.ofLE _ _ ((E.ssData p).Z_anti (show (0:WithTop ℕ) ≤ ↑((q:ℤ)-1).toNat from bot_le)) ≫
          (E.ssData p).pageπ 0 ≫ eqToHom (by
            change (E.ssData p).page 0 = (E.ssData p).page (↑(2-E.r₀).toNat : WithTop ℕ)
            rw [h0]
            rfl)) z = x := by
  rcases E with ⟨⟨r₀,D,δ,d⟩,dd,Zs,Bs⟩
  dsimp at h0
  subst r₀
  have hidx : ((q:ℤ)+1-2).toNat = ((q:ℤ)-1).toNat := by omega
  change (∃ xr : (D p).page (↑((q:ℤ)+1-2).toNat : WithTop ℕ),
    ∃ hr : (2:ℤ) ≤ q+1,
    ∃ z : (Subobject.underlying.obj ((D p).Z (↑((q:ℤ)+1-2).toNat : WithTop ℕ)) : ModuleCat ℤ),
      (Subobject.ofLE _ _ ((D p).Z_anti (show (0:WithTop ℕ) ≤ ↑((q:ℤ)+1-2).toNat from bot_le)) ≫
        (D p).pageπ 0) z = x ∧ (D p).pageπ _ z = xr) ↔
    ∃ z : (Subobject.underlying.obj ((D p).Z (↑((q:ℤ)-1).toNat : WithTop ℕ)) : ModuleCat ℤ),
      (Subobject.ofLE _ _ ((D p).Z_anti (show (0:WithTop ℕ) ≤ ↑((q:ℤ)-1).toNat from bot_le)) ≫
        (D p).pageπ 0) z = x
  rw [hidx]
  constructor
  · rintro ⟨xr,hr,z,hz,hzr⟩
    exact ⟨z,hz⟩
  · rintro ⟨z,hz⟩
    exact ⟨_,by omega,z,hz,rfl⟩

private theorem cycle_iff_reaches (X : AdamsObject) (q : ℕ) (hq : 0 < q)
    (s t : ℤ) (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :
    x ∈ KIP126.Literature.cycles background X q (s,t) ↔
      ReachesPage (background.classical.obj (X.obj background.auxiliary)) (q+1) (s,t) x := by
  exact (generic_reaches_cycle _ (background.classical.firstPage _) q hq (s,t) x).symm

private theorem finite_detected_class (X : AdamsObject) (q : ℕ) (hq : 0 < q)
    (s t : ℤ) (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (hx : x ∈ KIP126.Literature.cycles background X q (s,t)) :
    ∃ a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q),
      Detects (background.convergence (.quotient q (.nu X))) (s,t,t) (finiteLabel X q s t x) a := by
  let z := (infinityFiniteWindow X q hq (s,t) t (by constructor <;> omega)).symm
    (subquotientClass (KIP126.Literature.cycles background X (q-t+t) (s,t))
      (KIP126.Literature.boundaries background X (1+t-t) (s,t))
      ⟨x, by simpa only [sub_add_cancel] using hx⟩)
  have hrep : HasInfinityRepresentative
      (background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) q) 2 (s,t,t)
      (finiteLabel X q s t x) z := by
    apply (eInfinity_finite_labels X q hq s t t (by constructor <;> omega) x z).mpr
    exact ⟨by simpa only [sub_add_cancel] using hx, AddEquiv.apply_symm_apply _ _⟩
  let F := (background.convergence (.quotient q (.nu X))).filtration
  haveI : Epi (F.toAssociatedGraded s (t-s,t)) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨b,hb⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s (t-s,t))).mp
    inferInstance (((background.convergence (.quotient q (.nu X))).identification (s,t,t)).hom z)
  exact ⟨(F.F s (t-s,t)).arrow b, z, hrep, b, rfl, hb.symm⟩

private theorem finite_every_class_detected (X : AdamsObject) (q : ℕ) (hq : 0 < q)
    (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q)) :
    ∃ x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t),
      x ∈ KIP126.Literature.cycles background X q (s,t) ∧
      Detects (background.convergence (.quotient q (.nu X))) (s,t,t) (finiteLabel X q s t x) a := by
  have ha := finite_filtration_exhaustive X q hq s t a
  have ha' : a ∈ ModuleCat.subobjectModule _
      ((background.convergence (.quotient q (.nu X))).filtration.F s (t-s,t)) := by
    simpa only [SyntheticTowerConvergence.filtration, SyntheticTowerPresentation.filtration,
      OrderIso.apply_symm_apply, FiltrationAtLeast, SyntheticObject.obj, syntheticHomotopy] using ha
  obtain ⟨b,hb⟩ := ha'
  let z := ((background.convergence (.quotient q (.nu X))).identification (s,t,t)).inv
    ((background.convergence (.quotient q (.nu X))).filtration.toAssociatedGraded s (t-s,t) b)
  obtain ⟨u,hu⟩ := rhoInfinityRepresentativeExists
    (background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) q) (s,t,t) z
  obtain ⟨x,hx⟩ := rhoFiniteLabelSurjective X q hq s t t (by constructor <;> omega) u
  have hx' : finiteLabel X q s t x = u := hx
  have hrep : HasInfinityRepresentative
      (background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) q) 2 (s,t,t)
      (finiteLabel X q s t x) z :=
    Eq.mp (congrArg (fun v => HasInfinityRepresentative
      (background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) q) 2 (s,t,t) v z) hx'.symm) hu
  obtain ⟨hcycle,_⟩ :=
    (eInfinity_finite_labels X q hq s t t (by constructor <;> omega) x z).mp hrep
  refine ⟨x, by simpa only [sub_add_cancel] using hcycle, z, hrep, b, hb, ?_⟩
  exact ConcreteCategory.congr_hom
    (((background.convergence (.quotient q (.nu X))).identification (s,t,t)).inv_hom_id)
    ((background.convergence (.quotient q (.nu X))).filtration.toAssociatedGraded s (t-s,t) b)

private theorem native_finite_lift (X : AdamsObject) (q : ℕ) (hq : 0 < q)
    (s t : ℤ) (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :
    ReachesPage (background.classical.obj (X.obj background.auxiliary)) (q+1) (s,t) x ↔
      ∃ a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q),
        a ≫ (background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho 1 q hq =
          nativeLabel X s t x := by
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := finite_detected_class X q hq s t x ((cycle_iff_reaches X q hq s t x).mpr hx)
    exact ⟨a, finite_detects_unique X s t x _ _
      (finite_detects_rho X q hq s t x a ha) (native_label_detects X s t x)⟩
  · rintro ⟨a,ha⟩
    obtain ⟨y,hy,hya⟩ := finite_every_class_detected X q hq s t a
    have he := finite_detects_unique X s t y _ _
      (finite_detects_rho X q hq s t y a hya) (native_label_detects X s t y)
    have hxy : y=x := native_label_injective X s t (he.symm.trans ha)
    subst y
    exact (cycle_iff_reaches X q hq s t x).mp hy

private theorem finite_lift_from_infinity : KIP126.Literature.FiniteLiftCriterion background := by
  intro X q hq s t x
  rw [native_finite_lift X q hq s t x]
  let V := background.nu.functor.obj (X.obj background.auxiliary)
  let Z := KIP126.Literature.nuZero background X
  let e : Z ≅ V := SyntheticCategory.biShift_zero.app V
  let e₁ := (background.quotients.functoriality.functor 1).mapIso e
  let eQ := (background.quotients.functoriality.functor q).mapIso e
  let rhoV := (background.quotients.tower V).rho 1 q hq
  let rhoZ := (background.quotients.tower Z).rho 1 q hq
  have hnat : rhoZ ≫ e₁.hom = eQ.hom ≫ rhoV :=
    (background.quotients.natural e.hom).rho_naturality hq
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a ≫ eQ.inv, ?_⟩
    apply (cancel_mono e₁.hom).mp
    change ((a ≫ eQ.inv) ≫ rhoZ) ≫ e₁.hom =
      KIP126.Literature.firstLabel background X s t x ≫ e₁.hom
    calc
      _ = a ≫ eQ.inv ≫ (rhoZ ≫ e₁.hom) := by simp only [Category.assoc]
      _ = a ≫ eQ.inv ≫ eQ.hom ≫ rhoV := by rw [hnat]
      _ = a ≫ rhoV := by simp only [Iso.inv_hom_id_assoc]
      _ = _ := ha
  · rintro ⟨a,ha⟩
    refine ⟨a ≫ eQ.hom, ?_⟩
    change (a ≫ eQ.hom) ≫ rhoV = KIP126.Literature.firstLabel background X s t x ≫ e₁.hom
    calc
      _ = a ≫ (eQ.hom ≫ rhoV) := Category.assoc _ _ _
      _ = a ≫ rhoZ ≫ e₁.hom := by rw [←hnat]
      _ = _ := by rw [←Category.assoc, ha]

end FiniteLiftConstruction

section DifferentialRigidityConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/- The unshifted comparison is an actual fixed-label consequence of the
specified lambda-inversion morphism. Transport to every shifted nu label
is expressed by differential_rigidity below. -/
private def RRep {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    (E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι)
    (r : ℤ) (p : ι) (x : E.Page 2 p) (y : E.Page r p) : Prop :=
  ∃ hr : 2 ≤ r,
    let D := E.ssData p
    let n : WithTop ℕ := ↑(2-E.r₀).toNat
    let m : WithTop ℕ := ↑(r-E.r₀).toNat
    ∃ z : (Subobject.underlying.obj (D.Z m) : ModuleCat ℤ),
      (Subobject.ofLE _ _ (D.Z_anti (by
        dsimp [n,m]; exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat by omega))) ≫
          D.pageπ n) z = x ∧ D.pageπ m z = y

private def RReach {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    (E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι)
    (r : ℤ) (p : ι) (x : E.Page 2 p) : Prop := ∃ y, RRep E r p x y

private theorem rrep_two {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    (E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι) (p : ι) (x : E.Page 2 p) :
    RRep E 2 p x x := by
  let D := E.ssData p
  let n : WithTop ℕ := ↑(2-E.r₀).toNat
  haveI : Epi (D.pageπ n) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (D.pageπ n)).mp inferInstance x
  exact ⟨le_refl 2,z,by simp only [Subobject.ofLE_refl,Category.id_comp]; rfl, rfl⟩

private theorem rrep_unique {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι} {r : ℤ} {p : ι}
    {x : E.Page 2 p} {y z : E.Page r p} (hy : RRep E r p x y) (hz : RRep E r p x z) :
    y=z := by
  obtain ⟨hr,y',hxy,hy⟩ := hy
  obtain ⟨_,z',hxz,hz⟩ := hz
  exact hy.symm.trans (((E.ssData p).page_eq_of_early_page_eq _ _
    (by exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat by omega)) y' z'
      (hxy.trans hxz.symm)).trans hz)

private theorem rrep_map {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι}
    (f : FromFirstMorphism E F) {r : ℤ} {p : ι}
    {x : E.Page 2 p} {y : E.Page r p} (h : RRep E r p x y) :
    RRep F r p (f.pageMap 2 p x) (f.pageMap r p y) := by
  have hstart := f.r₀_eq
  rcases E with ⟨⟨r₀,D,δ,d⟩,dd,Zs,Bs⟩
  rcases F with ⟨⟨r₀',D',δ',d'⟩,dd',Zs',Bs'⟩
  dsimp at hstart
  subst r₀'
  obtain ⟨hr,z,hx,hy⟩ := h
  let n : WithTop ℕ := ↑(2-r₀).toNat
  let m : WithTop ℕ := ↑(r-r₀).toNat
  have hnm : n ≤ m := by
    dsimp [n,m]; exact_mod_cast (show (2-r₀).toNat ≤ (r-r₀).toNat by omega)
  let g := f.toSSDataMorphism
  refine ⟨hr,g.cycleMap p m z,?_,?_⟩
  · have hs := g.cycleMap_ofLE_assoc p hnm ((D' p).pageπ n)
    have hp := g.pageπ_pageMap p n
    have heq : (Subobject.ofLE _ _ ((D p).Z_anti hnm) ≫ (D p).pageπ n) ≫
        g.pageMap p n = g.cycleMap p m ≫
          Subobject.ofLE _ _ ((D' p).Z_anti hnm) ≫ (D' p).pageπ n := by
      rw [Category.assoc,hp]; exact hs
    simpa only [FromFirstMorphism.pageMap,SSDataMorphism.pageMapAt,
      ModuleCat.comp_apply,hx,eqToHom_refl,Category.comp_id,n,m,g]
      using (ConcreteCategory.congr_hom heq z).symm
  · simpa only [FromFirstMorphism.pageMap,SSDataMorphism.pageMapAt,
      ModuleCat.comp_apply,hy,eqToHom_refl,Category.comp_id,n,m,g]
      using (ConcreteCategory.congr_hom (g.pageπ_pageMap p m) z).symm

private theorem rreach_before {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι} {r t : ℤ} {p : ι}
    {x : E.Page 2 p} (hr : 2 ≤ r) (hrt : r ≤ t) (ht : RReach E t p x) :
    RReach E r p x := by
  obtain ⟨_,_,z,hz,_⟩ := ht
  let D := E.ssData p
  have hrt' : (↑(r-E.r₀).toNat : WithTop ℕ) ≤ ↑(t-E.r₀).toNat := by
    exact_mod_cast (show (r-E.r₀).toNat ≤ (t-E.r₀).toNat by omega)
  let zr := (Subobject.ofLE (D.Z ↑(t-E.r₀).toNat) (D.Z ↑(r-E.r₀).toNat) (D.Z_anti hrt')) z
  refine ⟨D.pageπ _ zr,hr,zr,?_,rfl⟩
  dsimp only [zr]
  rw [← CategoryTheory.comp_apply,← Category.assoc,Subobject.ofLE_comp_ofLE]
  exact hz

private theorem rrep_d_zero_of_later {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι} {r t : ℤ} {p : ι}
    {x : E.Page 2 p} {a : E.Page r p} (hr0 : E.r₀ ≤ r) (hrt : r<t)
    (ha : RRep E r p x a) (ht : RReach E t p x) : E.d r p a = 0 := by
  obtain ⟨b,ht2,z,hz,_⟩ := ht
  let D := E.ssData p
  let nt : WithTop ℕ := ↑(t-E.r₀).toNat
  let nr : WithTop ℕ := ↑(r-E.r₀).toNat
  let ns : WithTop ℕ := ↑((r-E.r₀).toNat+1)
  have hrs : nr ≤ ns := by dsimp [nr,ns]; exact_mod_cast Nat.le_succ (r-E.r₀).toNat
  have hst : ns ≤ nt := by
    dsimp [ns,nt]; exact_mod_cast (show (r-E.r₀).toNat+1 ≤ (t-E.r₀).toNat by omega)
  let zr := (Subobject.ofLE (D.Z nt) (D.Z nr) (D.Z_anti (hrs.trans hst))) z
  have hrep : RRep E r p x (D.pageπ nr zr) := by
    refine ⟨ha.1,zr,?_,rfl⟩
    dsimp only [zr]
    rw [← CategoryTheory.comp_apply,← Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz
  rw [rrep_unique ha hrep]
  change D.pageπ nr zr ∈ LinearMap.ker (E.d r p).hom
  rw [← subobjectModule_kernel,E.Z_succ r p hr0,subobjectModule_image]
  refine ⟨(Subobject.ofLE (D.Z nt) (D.Z ns) (D.Z_anti hst)) z,?_⟩
  change (Subobject.ofLE (D.Z ns) (D.Z nr) (D.Z_anti hrs) ≫ D.pageπ nr)
    ((Subobject.ofLE (D.Z nt) (D.Z ns) (D.Z_anti hst)) z) = D.pageπ nr zr
  rw [← CategoryTheory.comp_apply,← Category.assoc,Subobject.ofLE_comp_ofLE]
  rfl
private theorem rreach_next {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι} {r : ℤ} {p : ι}
    {x : E.Page 2 p} {a : E.Page r p} (hr0 : E.r₀ ≤ r)
    (ha : RRep E r p x a) (hd : E.d r p a=0) : RReach E (r+1) p x := by
  obtain ⟨hr,z,hz,hza⟩ := ha
  let D := E.ssData p
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  let m : WithTop ℕ := ↑((r-E.r₀).toNat+1)
  have hn : n ≤ m := by dsimp [n,m]; exact_mod_cast Nat.le_succ (r-E.r₀).toNat
  have hm : (↑(r+1-E.r₀).toNat : WithTop ℕ)=m := by dsimp [m]; congr 1; omega
  let j := Subobject.ofLE (D.Z m) (D.Z n) (D.Z_anti hn)
  have hmem : a ∈ LinearMap.ker (E.d r p).hom := hd
  rw [← subobjectModule_kernel,E.Z_succ r p hr0,subobjectModule_image] at hmem
  obtain ⟨z',hz'⟩ := hmem
  change (j ≫ D.pageπ n) z'=a at hz'
  have hzero : D.pageπ n (z-j z')=0 := by
    rw [map_sub,hza]; exact sub_eq_zero.mpr hz'.symm
  obtain ⟨b,hb⟩ := (D.pageπ_eq_zero_iff n (z-j z')).mp hzero
  have hb_le : D.B n ≤ D.Z m :=
    (D.B_mono le_top).trans ((D.B_le_Z ⊤).trans (D.Z_anti le_top))
  let b' := Subobject.ofLE (D.B n) (D.Z m) hb_le b
  have hjb : j b' = Subobject.ofLE (D.B n) (D.Z n) (D.B_le_Z n) b := by
    change (Subobject.ofLE (D.B n) (D.Z m) hb_le ≫ j) b=_
    dsimp only [j]
    rw [Subobject.ofLE_comp_ofLE]
  have hjz : j (z'+b')=z := by rw [map_add,hjb,hb]; abel
  let P (l : WithTop ℕ) : Prop := ∃ hl : (↑(2-E.r₀).toNat : WithTop ℕ) ≤ l,
    ∃ zz : (Subobject.underlying.obj (D.Z l) : ModuleCat.{0} ℤ),
      (Subobject.ofLE (D.Z l) (D.Z ↑(2-E.r₀).toNat) (D.Z_anti hl) ≫
        D.pageπ ↑(2-E.r₀).toNat) zz=x
  have hc : P m := by
    refine ⟨by dsimp [m]; exact_mod_cast (show
      (2-E.r₀).toNat ≤ (r-E.r₀).toNat+1 by omega),z'+b',?_⟩
    rw [← hjz] at hz
    change (j ≫ Subobject.ofLE _ _ _ ≫ D.pageπ _) (z'+b')=x at hz
    simpa only [j,← Category.assoc,Subobject.ofLE_comp_ofLE] using hz
  have hc' : P ↑(r+1-E.r₀).toNat := Eq.mpr (congrArg P hm) hc
  obtain ⟨hl,zz,hzz⟩ := hc'
  exact ⟨D.pageπ _ zz,by omega,zz,hzz,rfl⟩

set_option maxHeartbeats 80000 in
private theorem rreach_reflect {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι}
    (f : FromFirstMorphism E F) (hfirst : E.r₀ ≤ 2) (p : ι)
    (hinj : ∀ j : ℤ, 2 ≤ j → Function.Injective (f.pageMap j (p+E.diffDeg j)))
    (r : ℤ) (hr : 2 ≤ r) (x : E.Page 2 p) :
    RReach F r p (f.pageMap 2 p x) → RReach E r p x := by
  have aux (n : ℕ) : RReach F ((n:ℤ)+2) p (f.pageMap 2 p x) →
      RReach E ((n:ℤ)+2) p x := by
    induction n with
    | zero => intro _; exact ⟨x,rrep_two E p x⟩
    | succ n ih =>
      intro hnext
      have hnext' : RReach F ((n:ℤ)+2+1) p (f.pageMap 2 p x) := by
        convert hnext using 1 <;> push_cast <;> ring
      obtain ⟨a,ha⟩ := ih (rreach_before (by omega) (by omega) hnext')
      have hfzero : F.d ((n:ℤ)+2) p (f.pageMap ((n:ℤ)+2) p a)=0 :=
        rrep_d_zero_of_later (by rw [← f.r₀_eq]; omega) (by omega) (rrep_map f ha) hnext'
      have hezero : E.d ((n:ℤ)+2) p a=0 := by
        apply hinj ((n:ℤ)+2) (by omega)
        let e : F.Page ((n:ℤ)+2) (p+E.diffDeg ((n:ℤ)+2)) ⟶
            F.Page ((n:ℤ)+2) (p+F.diffDeg ((n:ℤ)+2)) := eqToHom (by rw [f.diffDeg_eq])
        apply ((ModuleCat.mono_iff_injective e).mp inferInstance)
        have hd := ConcreteCategory.congr_hom (f.pageMap_comm_d ((n:ℤ)+2) (by omega) p) a
        simpa only [ModuleCat.comp_apply,hfzero,map_zero,e] using hd.symm
      have hres := rreach_next (by omega) ha hezero
      convert hres using 1 <;> push_cast <;> ring
  have hindex : ((r-2).toNat:ℤ)+2=r := by rw [Int.toNat_of_nonneg (by omega)]; omega
  simpa only [hindex] using aux (r-2).toNat

private def RDiff {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    (E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι) (r : ℤ) (p q : ι)
    (x : E.Page 2 p) (y : E.Page 2 q) : Prop :=
  ∃ h : p+E.diffDeg r=q, ∃ xr : E.Page r p, ∃ yr : E.Page r q,
    RRep E r p x xr ∧ RRep E r q y yr ∧
      (E.d r p ≫ eqToHom (congrArg (E.Page r) h)) xr=yr

set_option maxHeartbeats 80000 in
private theorem rdiff_iff {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι}
    (f : FromFirstMorphism E F) (hfirst : E.r₀ ≤ 2) (r : ℤ) (hr : 2 ≤ r) (p q : ι)
    (hinjp : ∀ j : ℤ, 2 ≤ j → Function.Injective (f.pageMap j (p+E.diffDeg j)))
    (hinjq : ∀ j : ℤ, 2 ≤ j → Function.Injective (f.pageMap j (q+E.diffDeg j)))
    (x : E.Page 2 p) (y : E.Page 2 q) :
    RDiff E r p q x y ↔ RDiff F r p q (f.pageMap 2 p x) (f.pageMap 2 q y) := by
  constructor
  · rintro ⟨hdeg,xr,yr,hx,hy,hd⟩
    have hdeg' : p+F.diffDeg r=q := by rw [← f.diffDeg_eq]; exact hdeg
    refine ⟨hdeg',f.pageMap r p xr,f.pageMap r q yr,rrep_map f hx,rrep_map f hy,?_⟩
    have heq : f.pageMap r p ≫ F.d r p ≫ eqToHom (congrArg (F.Page r) hdeg') =
        (E.d r p ≫ eqToHom (congrArg (E.Page r) hdeg)) ≫ f.pageMap r q := by
      rw [← Category.assoc,f.pageMap_comm_d r (by omega),Category.assoc]
      cases hdeg
      simp only [Category.assoc,eqToHom_trans,eqToHom_refl,Category.comp_id]
    simpa only [ModuleCat.comp_apply,hd] using ConcreteCategory.congr_hom heq xr
  · rintro ⟨hdeg',xr,yr,hx,hy,hd⟩
    have hdeg : p+E.diffDeg r=q := by rw [f.diffDeg_eq]; exact hdeg'
    obtain ⟨a,ha⟩ := rreach_reflect f hfirst p hinjp r hr x ⟨xr,hx⟩
    obtain ⟨b,hb⟩ := rreach_reflect f hfirst q hinjq r hr y ⟨yr,hy⟩
    have hax : f.pageMap r p a=xr := rrep_unique (rrep_map f ha) hx
    have hby : f.pageMap r q b=yr := rrep_unique (rrep_map f hb) hy
    refine ⟨hdeg,a,b,ha,hb,?_⟩
    have hi : Function.Injective (f.pageMap r q) := by rw [← hdeg]; exact hinjp r hr
    apply hi
    have heq : f.pageMap r p ≫ F.d r p ≫ eqToHom (congrArg (F.Page r) hdeg') =
        (E.d r p ≫ eqToHom (congrArg (E.Page r) hdeg)) ≫ f.pageMap r q := by
      rw [← Category.assoc,f.pageMap_comm_d r (by omega),Category.assoc]
      cases hdeg
      simp only [Category.assoc,eqToHom_trans,eqToHom_refl,Category.comp_id]
    have he := ConcreteCategory.congr_hom heq a
    simpa only [ModuleCat.comp_apply,hax,hby,hd] using he.symm

private theorem rdiff_inflation (X : AdamsObject) (r s t w : ℤ) (hr : 2 ≤ r)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (y : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s+r,t+r-1)) :
    RDiff (freeClassicalInflation X) r (s,t,w) (s+r,t+r-1,w) x y ↔
      HasDifferential (background.classical.obj (X.obj background.auxiliary)) r
        (s,t) (s+r,t+r-1) x y := by
  have hd : (s,t)+(background.classical.obj (X.obj background.auxiliary)).diffDeg r=(s+r,t+r-1) := by
    rw [background.classical.differentialDegree]
    ext <;> simp only [Prod.fst_add,Prod.snd_add] <;> omega
  have hd' : (s,t,w)+(freeClassicalInflation X).diffDeg r=(s+r,t+r-1,w) := by
    change (s,t,w)+syntheticAdamsRawShift r=_
    ext <;> simp only [syntheticAdamsRawShift,Prod.fst_add,Prod.snd_add] <;> omega
  constructor
  · rintro ⟨_,a,b,ha,hb,hab⟩
    refine ⟨hd,a,b,ha,hb,?_⟩
    simpa only [freeClassicalInflation,freeInflate,freeForgetWeight,
      AddMonoidHom.coe_mk,ZeroHom.coe_mk,Category.assoc,eqToHom_trans] using hab
  · rintro ⟨_,a,b,ha,hb,hab⟩
    refine ⟨hd',a,b,ha,hb,?_⟩
    simpa only [freeClassicalInflation,freeInflate,freeForgetWeight,
      AddMonoidHom.coe_mk,ZeroHom.coe_mk,Category.assoc,eqToHom_trans] using hab

private theorem differentials_unshifted (X : AdamsObject) (r s t w : ℤ)
    (hr : 2 ≤ r) (hw : w ≤ t)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (y : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s+r,t+r-1)) :
    HasDifferential (background.classical.obj (X.obj background.auxiliary)) r
        (s,t) (s+r,t+r-1) x y ↔
      SyntheticHasDifferential (background.family.nu background.nu (X.obj background.auxiliary)) r
        (s,t,w) (s+r,t+r-1,w)
        (nuWeightLabel background X s t w hw x)
        (nuWeightLabel background X (s+r) (t+r-1) w (by omega) y) := by
  let E := (background.family.nu background.nu (X.obj background.auxiliary)).sequence
  let f := freeInversionMorphism X
  have hi (s' t' : ℤ) (ht' : w ≤ t') (j : ℤ) (hj : 2 ≤ j) :
      Function.Injective (f.pageMap j ((s',t',w)+E.diffDeg j)) := by
    have hp : (s',t',w)+E.diffDeg j=(s'+j,t'+j-1,w) := by
      rw [(background.family.nu background.nu (X.obj background.auxiliary)).differentialDegree]
      ext <;> simp only [syntheticAdamsRawShift,Prod.fst_add,Prod.snd_add] <;> omega
    rw [hp]
    dsimp only [f]
    rw [freeInversionMorphism_pageMap]
    letI := freeInversionIsIso X j hj (s'+j) (t'+j-1) w (by omega)
    exact (ConcreteCategory.bijective_of_isIso _).1
  have h := rdiff_iff f (by rw [(background.family.nu background.nu (X.obj background.auxiliary)).firstPage])
    r hr (s,t,w) (s+r,t+r-1,w) (hi s t hw) (hi (s+r) (t+r-1) (by omega))
    (nuWeightLabel background X s t w hw x)
    (nuWeightLabel background X (s+r) (t+r-1) w (by omega) y)
  dsimp only [f] at h
  rw [freeInversionMorphism_pageMap,freeInversionMorphism_pageMap] at h
  erw [inversion_e2 X s t w hw x,inversion_e2 X (s+r) (t+r-1) w (by omega) y] at h
  rw [rdiff_inflation X r s t w hr x y] at h
  exact h.symm


private theorem dependent_heq {α : Sort _} {β : α → Sort _} (f : ∀ a, β a)
    {a b : α} (h : a=b) : HEq (f a) (f b) := by cases h; rfl

private theorem module_cast_heq {A B : ModuleCat.{0} ℤ} (h : A=B) (a : A) :
    HEq ((eqToHom h) a) a := by cases h; rfl

private theorem weight_label_heq (X : AdamsObject) (s t w : ℤ) (hw : w ≤ t)
    (k : ℕ) (hk : (t-w).toNat=k)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :
    HEq (nuWeightLabel background X s t w hw x) (targetNuLabel background X s t k x) := by
  unfold nuWeightLabel regradeE2
  exact (module_cast_heq _ _).trans
    (dependent_heq (fun j => targetNuLabel background X s t j x) hk)

private theorem rdiff_iso_iff
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Tridegree}
    (e : E ≅ F) (hfirst : E.r₀ ≤ 2) (r : ℤ) (hr : 2 ≤ r) (p q : Tridegree)
    (x : E.Page 2 p) (y : E.Page 2 q) :
    RDiff E r p q x y ↔ RDiff F r p q (e.hom.pageMap 2 p x) (e.hom.pageMap 2 q y) := by
  apply rdiff_iff (firstPageComparisonOfMorphism e.hom) hfirst r hr p q
  · intro j _
    exact (ConcreteCategory.bijective_of_isIso (freeRawPageIso e j (p+E.diffDeg j)).hom).1
  · intro j _
    exact (ConcreteCategory.bijective_of_isIso (freeRawPageIso e j (q+E.diffDeg j)).hom).1

private theorem rdiff_congr_heq
    {E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Tridegree}
    (r : ℤ) {p q p' q' : Tridegree} (hp : p=p') (hq : q=q')
    {x : E.Page 2 p} {y : E.Page 2 q} {x' : E.Page 2 p'} {y' : E.Page 2 q'}
    (hx : HEq x x') (hy : HEq y y') : RDiff E r p q x y ↔ RDiff E r p' q' x' y' := by
  cases hp
  cases hq
  cases eq_of_heq hx
  cases eq_of_heq hy
  rfl

private theorem page_map_heq
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Tridegree}
    (f : E ⟶ F) {p q : Tridegree} (hp : p=q)
    {x : E.Page 2 p} {y : E.Page 2 q} (hx : HEq x y) :
    HEq (f.pageMap 2 p x) (f.pageMap 2 q y) := by
  cases hp
  cases eq_of_heq hx
  rfl

private theorem zero_label_heq (X : AdamsObject) (s t : ℤ) (k : ℕ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :
    HEq ((background.family.map (SyntheticCategory.biShift_zero.hom.app
      (background.nu.functor.obj (X.obj background.auxiliary)))).pageMap 2 (s,t,t+0-k)
        (background.comparison.nuE2 X 0 s t k x))
      (targetNuLabel background X s t k x) := by
  unfold targetNuLabel
  apply page_map_heq _ (by simp only [add_zero])
  exact (cast_heq _ _).symm

private theorem differentials_a_zero (X : AdamsObject) (s t : ℤ) (r k : ℕ)
    (hr : 2 ≤ r)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (y : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s+r,t+r-1)) :
    HasDifferential (background.classical.obj (X.obj background.auxiliary)) r
        (s,t) (s+r,t+r-1) x y ↔
      SyntheticHasDifferential
        (background.family.obj ((SyntheticCategory.biShift (0,0)).obj
          (background.nu.functor.obj (X.obj background.auxiliary)))) r
        (s,t,t+0-k) (s+r,t+r-1,(t+r-1)+0-(k+(r-1) : ℕ))
        (background.comparison.nuE2 X 0 s t k x)
        (background.comparison.nuE2 X 0 (s+r) (t+r-1) (k+(r-1)) y) := by
  let V := background.nu.functor.obj (X.obj background.auxiliary)
  let e := background.family.functor.mapIso (SyntheticCategory.biShift_zero.app V)
  have h := rdiff_iso_iff e (by rw [background.family.firstPage]) (r:ℤ) (by omega)
    (s,t,t+0-k) (s+r,t+r-1,(t+r-1)+0-(k+(r-1):ℕ))
    (background.comparison.nuE2 X 0 s t k x)
    (background.comparison.nuE2 X 0 (s+r) (t+r-1) (k+(r-1)) y)
  have hu := differentials_unshifted X r s t (t-k) (by omega) (by omega) x y
  have hw : (t+(r:ℤ)-1)+0-(k+(r-1):ℕ)=t-k := by
    rw [Nat.cast_add,Nat.cast_sub (by omega : 1 ≤ r)]
    push_cast
    omega
  have hc := rdiff_congr_heq (E := (background.family.obj V).sequence) (r:ℤ)
    (p := (s,t,t+0-k)) (q := (s+r,t+r-1,(t+r-1)+0-(k+(r-1):ℕ)))
    (p' := (s,t,t-k)) (q' := (s+r,t+r-1,t-k))
    (by simp only [add_zero]) (by rw [hw])
    ((zero_label_heq X s t k x).trans (weight_label_heq X s t (t-k) (by omega) k (by omega) x).symm)
    ((zero_label_heq X (s+r) (t+r-1) (k+(r-1)) y).trans
      (weight_label_heq X (s+r) (t+r-1) (t-k) (by omega) (k+(r-1)) (by omega) y).symm)
  exact ((h.trans hc).trans hu.symm).symm


section ComparisonRigidity
open KIP126.Literature.BocksteinRaw KIP126.Literature.Paper38ComparisonInput
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
attribute [local instance] fixedShiftAdditive fixedShiftCommShift fixedShiftTriangulated

private def comparisonMorphism
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Tridegree}
    (f : Paper38OriginalSuccessor.FromFirstMorphism E F) : FromFirstMorphism E F where
  toSSDataMorphism := f.toSSDataMorphism
  r₀_eq := f.r₀_eq
  diffDeg_eq := f.diffDeg_eq
  comm_d := f.comm_d

private theorem affineWeight_injective (a : ℤ) : Function.Injective (affineWeight a) := by
  intro p q h
  apply Prod.ext
  · simpa only [affineWeight] using congrArg (fun z : Tridegree => z.1) h
  · apply Prod.ext
    · simpa only [affineWeight] using congrArg (fun z : Tridegree => z.2.1) h
    · have hh := congrArg (fun z => z.2.2) h
      dsimp [affineWeight] at hh
      omega

private theorem comp_eqToHom_of_heq {C : Type*} [Category C]
    {A B B' : C} (h : B=B') (f : A ⟶ B) (g : A ⟶ B')
    (hf : HEq f g) : f ≫ eqToHom h = g := by
  cases h
  cases hf
  exact Category.comp_id _

private theorem shifted_rdiff_iff (Y : SyntheticSpectrum) (a r : ℤ)
    (p q : Tridegree)
    (x : (shiftedLambdaSequence Y a).Page 2 p)
    (y : (shiftedLambdaSequence Y a).Page 2 q) :
    RDiff (shiftedLambdaSequence Y a) r p q x y ↔
      RDiff (lambdaSequence Y) r (affineWeight a p) (affineWeight a q) x y := by
  let E := lambdaSequence Y
  let F := shiftedLambdaSequence Y a
  have degree : affineWeight a (p+F.diffDeg r) = affineWeight a p+E.diffDeg r :=
    affineWeight_add_degree a r p
  have square (h : p+F.diffDeg r=q)
      (h' : affineWeight a p+E.diffDeg r=affineWeight a q) :
      F.d r p ≫ eqToHom (congrArg (F.Page r) h) =
        E.d r (affineWeight a p) ≫ eqToHom (congrArg (E.Page r) h') := by
    have hs := comp_eqToHom_of_heq
      (congrArg (E.Page r) degree) (F.d r p) (E.d r (affineWeight a p))
      (shiftedLambdaDifferential_heq Y a r p)
    have hh := congrArg (fun z => z ≫ eqToHom (congrArg (E.Page r) h')) hs
    simpa only [Category.assoc, eqToHom_trans] using hh
  constructor
  · rintro ⟨h,u,v,hu,hv,hd⟩
    have h' : affineWeight a p+E.diffDeg r=affineWeight a q := by
      rw [← degree, h]
    refine ⟨h',u,v,hu,hv,?_⟩
    rw [← square h h']
    exact hd
  · rintro ⟨h',u,v,hu,hv,hd⟩
    have h : p+F.diffDeg r=q := affineWeight_injective a (degree.trans h')
    refine ⟨h,u,v,hu,hv,?_⟩
    rw [square h h']
    exact hd


private theorem comparison_initial_inv_base_heq (X : Spectrum) (a s t : ℤ) (k : ℕ)
    (z : BiHom (t-s) t (XModLambdaN (nuZeroSpectrum X) 1)) :
    HEq ((initialQuotientIso X a s t k).inv z)
      ((baseInitialQuotientIso X s t k).inv z) := by
  let f : (w : {w : ℤ // t-w=(k:ℤ)}) →
      (lambdaSequence (nuZeroSpectrum X)).Page 2 (s,t,w.1) :=
    fun w => (lambdaInitialQuotientIso background.quotients.coherence (nuZeroSpectrum X)
      (s,t,w.1) k w.2).inv z
  have hw : (⟨t+a-(k:ℤ)-a, by omega⟩ : {w : ℤ // t-w=(k:ℤ)}) =
      ⟨t-k, by omega⟩ := by apply Subtype.ext; dsimp; omega
  have hh : HEq (f ⟨t+a-(k:ℤ)-a, by omega⟩) (f ⟨t-k, by omega⟩) :=
    @dependent_heq {w : ℤ // t-w=(k:ℤ)}
      (fun w => (lambdaSequence (nuZeroSpectrum X)).Page 2 (s,t,w.1))
      f _ _ hw
  exact hh

private theorem comparison_label_heq (X : AdamsObject) (a s t : ℤ) (k : ℕ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :
    HEq ((comparisonData.hom (X.obj background.auxiliary) a).pageMap 2 (s,t,t+a-k)
        (selectedE2Label X a s t k x))
      ((baseInitialQuotientIso (X.obj background.auxiliary) s t k).inv
        (comparisonData.classicalFirst (X.obj background.auxiliary) s t x)) := by
  have h := comparisonData.e2_selected X a s t k x
  have he : (comparisonData.hom (X.obj background.auxiliary) a).pageMap 2 (s,t,t+a-k)
        (selectedE2Label X a s t k x) =
      (initialQuotientIso (X.obj background.auxiliary) a s t k).inv
        (comparisonData.classicalFirst (X.obj background.auxiliary) s t x) := by
    have hh := congrArg (fun z => (initialQuotientIso (X.obj background.auxiliary) a s t k).inv z) h
    simpa only [initialQuotientValue, Iso.hom_inv_id_apply] using hh
  exact (heq_of_eq he).trans (comparison_initial_inv_base_heq _ a s t k _)

private theorem differentials_from_comparison : DifferentialRigidity background := by
  intro X a s t r k hr x y
  let X₀ := X.obj background.auxiliary
  let f := comparisonMorphism (comparisonData.hom X₀ a)
  have hi (j : ℤ) (hj : 2 ≤ j) (p : Tridegree) :
      Function.Injective (f.pageMap j p) := by
    exact (ConcreteCategory.bijective_of_isIso (comparisonPageIso X₀ a j hj p).hom).1
  have hcmp := rdiff_iff f (by
    exact le_of_eq (background.family.obj ((SyntheticCategory.biShift (0,a)).obj
      (background.nu.functor.obj X₀))).firstPage) (r:ℤ) (by omega)
    (s,t,t+a-k) (s+r,t+r-1,(t+r-1)+a-(k+(r-1):ℕ))
    (fun j hj => hi j hj _) (fun j hj => hi j hj _)
    (selectedE2Label X a s t k x)
    (selectedE2Label X a (s+r) (t+r-1) (k+(r-1)) y)
  have hshift := shifted_rdiff_iff (nuZeroSpectrum X₀) a (r:ℤ)
    (s,t,t+a-k) (s+r,t+r-1,(t+r-1)+a-(k+(r-1):ℕ))
    ((comparisonData.hom X₀ a).pageMap 2 _ (selectedE2Label X a s t k x))
    ((comparisonData.hom X₀ a).pageMap 2 _
      (selectedE2Label X a (s+r) (t+r-1) (k+(r-1)) y))
  have hlabels := rdiff_congr_heq (E := lambdaSequence (nuZeroSpectrum X₀)) (r:ℤ)
    (p := affineWeight a (s,t,t+a-k))
    (q := affineWeight a (s+r,t+r-1,(t+r-1)+a-(k+(r-1):ℕ)))
    (p' := (s,t,t-k))
    (q' := (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ)))
    (by ext <;> dsimp [affineWeight] <;> omega)
    (by ext <;> dsimp [affineWeight] <;> omega)
    (comparison_label_heq X a s t k x)
    (comparison_label_heq X a (s+r) (t+r-1) (k+(r-1)) y)
  have hclass := comparisonData.classical_differential X₀ s t r k hr x y
  exact (hclass.trans hlabels.symm).trans (hshift.symm.trans hcmp.symm)


end ComparisonRigidity

end DifferentialRigidityConstruction

/-- Finite lifting from the actual finite infinity-page labels, convergence,
and separatedness of the same quotient tower. -/
public theorem finite_lift_criterion :
  FiniteLiftCriterion background := by
  exact finite_lift_from_infinity

/-- Derived from finite lifting and the specified comparison and boundary inputs. -/
public theorem bockstein_differential :
  BocksteinDifferential background := by
  exact FiniteBoundaryComparison.bockstein_from_geometric_boundary finite_lift_criterion

/-- Derived with the original labels in every integer weight shift from the
complete comparison input. -/
public theorem differential_rigidity :
  DifferentialRigidity background := by
  exact differentials_from_comparison

end KIP126.Literature.Standard
end
