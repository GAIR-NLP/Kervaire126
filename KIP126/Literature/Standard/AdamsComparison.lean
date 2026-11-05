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

/-! Classical and synthetic Adams pages, finite quotients and infinity windows. -/

@[expose] section
set_option autoImplicit false
noncomputable section
set_option backward.privateInPublic true
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)

/-- The shifted tower on every integer page. -/
public def nuPage_weightShift :
  ∀ (X : AdamsObject) (r s t w : ℤ),
    (background.family.nu background.nu (X.obj background.auxiliary)).Page r (s,t,w) ≅
      (background.family.obj ((SyntheticCategory.biShift (0,-1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary)))).Page r (s,t,w-1) := by
  intro X r s t w
  let two : ℤ := 2
  let F := background.family
  let V := background.nu.functor.obj (X.obj background.auxiliary)
  let shiftedV := (SyntheticCategory.biShift (0,-1)).obj V
  let shift (page : ℤ) (hp : two ≤ page) :
      (F.obj V).Page page (s,t,w) ≅ (F.obj shiftedV).Page page (s,t,w-1) :=
    let q := t-s
    let q0 := q+0
    let a := q+s
    let b := q0+s
    let addS := fun z : ℤ => z+s
    let hq0 : q0=q := Int.add_zero q
    let hba : b=a := @congrArg ℤ ℤ q0 q addS hq0
    let hat : a=t := Int.sub_add_cancel t s
    let isoAt := fun aa bb : ℤ =>
      (F.obj V).Page page (s,aa,w) ≅ (F.obj shiftedV).Page page (s,bb,w-1)
    let raw : isoAt a b :=
      KIP126.AdamsSynthetic.Completed.shift_page (0,-1) (.nu X) page hp (q,w) s
    let same : isoAt a a := Eq.rec (motive := fun z _ => isoAt a z) raw hba
    Eq.rec (motive := fun z _ => isoAt z z) same hat
  by_cases hr : two ≤ r
  · exact shift r hr
  · let hlt : r < two := @Int.lt_of_not_ge two r hr
    let hle : r ≤ two := @Int.le_of_lt r two hlt
    let htwo : two ≤ two := Int.le_refl two
    let pageIso (Y : SyntheticSpectrum) (p : Tridegree) :
        (F.obj Y).Page r p ≅ (F.obj Y).Page two p :=
      let E := F.obj Y
      let c := E.sequence.r₀
      let hfirst : c=two := SyntheticAdamsFamily.firstPage F Y
      let nR := (r-c).toNat
      let nBase := (r-two).toNat
      let nTwo := (two-c).toNat
      let nZero : ℕ := 0
      let P : Prop := nBase=nZero
      let Q : Prop := r ≤ two
      let hiff : P ↔ Q := Int.toNat_sub_eq_zero_iff r two
      let hBase : P := @Iff.mpr P Q hiff hle
      let indexR := fun z : ℤ => (r-z).toNat
      let indexTwo := fun z : ℤ => (two-z).toNat
      let hR : nR=nBase := @congrArg ℤ ℕ c two indexR hfirst
      let hRZero : nR=nZero := @Eq.trans ℕ nR nBase nZero hR hBase
      let hTwo : nTwo=nZero := @congrArg ℤ ℕ c two indexTwo hfirst
      let A := ModuleCat.{0} ℤ
      let D := E.sequence.ssData p
      let pageN : ℕ → A := fun n => D.page (n : WithTop ℕ)
      let objR := pageN nR
      let objTwo := pageN nTwo
      let objZero := pageN nZero
      let hObjR : objR=objZero := @congrArg ℕ A nR nZero pageN hRZero
      let hObjTwo : objTwo=objZero := @congrArg ℕ A nTwo nZero pageN hTwo
      let hObjTwoSymm : objZero=objTwo := @Eq.symm A objTwo objZero hObjTwo
      let hObj : objR=objTwo := @Eq.trans A objR objZero objTwo hObjR hObjTwoSymm
      eqToIso hObj
    exact pageIso V (s,t,w) ≪≫ shift two htwo ≪≫ (pageIso shiftedV (s,t,w-1)).symm



public theorem nuPage_e2 :
  ∀ (X : AdamsObject) (s t : ℤ) (k : ℕ)
      (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)),
    HEq ((nuPage_weightShift X 2 s t (t-k)).hom (targetNuLabel background X s t k x))
      (background.comparison.nuE2 X (-1) s t k x) := by
  sorry

public def nuPageData : NuPageCoordinates background where
  weightShift := nuPage_weightShift
  e2 := nuPage_e2

public def pageLambda := NuPageCoordinates.lambda background nuPageData

section FirstPageComparisonConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private structure FromFirstMorphism
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    (E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι)
    extends SSDataMorphism ι E.ssData F.ssData where
  r₀_eq : E.r₀=F.r₀
  diffDeg_eq : E.diffDeg=F.diffDeg
  comm_d : ∀ (r : ℤ), E.r₀ ≤ r → ∀ p : ι,
    let g := toSSDataMorphism
    g.pageMapAt (E := E.toPreSS) (E' := F.toPreSS) r₀_eq r p ≫ F.d r p =
      E.d r p ≫ g.pageMapAt (E := E.toPreSS) (E' := F.toPreSS) r₀_eq r (p+E.diffDeg r) ≫
        eqToHom (by rw [diffDeg_eq])

private def FromFirstMorphism.pageMap
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι}
    (f : FromFirstMorphism E F) (r : ℤ) (p : ι) :=
  f.toSSDataMorphism.pageMapAt (E := E.toPreSS) (E' := F.toPreSS) f.r₀_eq r p

private theorem FromFirstMorphism.pageMap_comm_d
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι}
    (f : FromFirstMorphism E F) (r : ℤ) (hr : E.r₀ ≤ r) (p : ι) :
    f.pageMap r p ≫ F.d r p = E.d r p ≫ f.pageMap r (p+E.diffDeg r) ≫
      eqToHom (by rw [f.diffDeg_eq]) := f.comm_d r hr p

private def firstPageComparisonOfMorphism
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι}
    (f : SpectralSequenceMorphism E F) : FromFirstMorphism E F where
  toSSDataMorphism := f.toSSDataMorphism
  r₀_eq := f.r₀_eq
  diffDeg_eq := f.diffDeg_eq
  comm_d r _ p := f.pageMap_comm_d r p

private theorem finiteQuotientNextProjectionZero
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    (E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι)
    (r : ℤ) (hr : E.r₀ ≤ r) (p : ι)
    (z : (Subobject.underlying.obj ((E.ssData (p+E.diffDeg r)).Z
      ↑((r-E.r₀).toNat+1)) : ModuleCat.{0} ℤ)) :
    (E.ssData (p+E.diffDeg r)).pageπ ↑((r-E.r₀).toNat+1) z = 0 ↔
      (Subobject.ofLE _ _ ((E.ssData (p+E.diffDeg r)).Z_anti
        (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat)) ≫
          (E.ssData (p+E.diffDeg r)).pageπ ↑(r-E.r₀).toNat) z ∈
        LinearMap.range (E.d r p).hom := by
  let D := E.ssData (p+E.diffDeg r)
  let n := (r-E.r₀).toNat
  have hnm : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
  let i := Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑n) (D.Z_anti hnm)
  let j := Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑n)
    ((D.B_le_Z _).trans (D.Z_anti hnm))
  rw [← subobjectModule_image, E.B_succ r p hr, subobjectModule_image]
  change D.pageπ ↑(n+1) z = 0 ↔ (i ≫ D.pageπ ↑n) z ∈ LinearMap.range (j ≫ D.pageπ ↑n).hom
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _)) z).mp hz
    refine ⟨v, ?_⟩
    rw [← hv]
    change (j ≫ D.pageπ ↑n) v =
      ((Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _)) ≫ i ≫ D.pageπ ↑n) v
    congr 2
    dsimp only [i,j]
    rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
  · rintro ⟨v, hv⟩
    apply (subobject_cokernel_π_eq_zero_iff (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _) z).mpr
    have hz : D.pageπ ↑n (i z-j v) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hv.symm
    have hb := (subobject_cokernel_π_eq_zero_iff (D.B ↑n) (D.Z ↑n) (D.B_le_Z _) _).mp hz
    have hb' := (ModuleCat.subobjectModule D.V).monotone (D.B_mono hnm) hb
    have hv' : (D.Z ↑n).arrow (j v) ∈ (ModuleCat.subobjectModule D.V) (D.B ↑(n+1)) := by
      change (j ≫ (D.Z ↑n).arrow) v ∈ _
      dsimp only [j]
      rw [Subobject.ofLE_arrow]
      exact ⟨v, rfl⟩
    have hh := ((ModuleCat.subobjectModule D.V) (D.B ↑(n+1))).add_mem hb' hv'
    rw [map_sub, sub_add_cancel] at hh
    change (i ≫ (D.Z ↑n).arrow) z ∈ _ at hh
    dsimp only [i] at hh
    rwa [Subobject.ofLE_arrow] at hh

private theorem finiteQuotientNextEqOfEarlierEq (D : SSData (ModuleCat.{0} ℤ))
    (n : ℕ) (a b : (Subobject.underlying.obj (D.Z ↑(n+1)) : ModuleCat.{0} ℤ))
    (h : (Subobject.ofLE _ _ (D.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
      D.pageπ ↑n) a = (Subobject.ofLE _ _ (D.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
      D.pageπ ↑n) b) : D.pageπ ↑(n+1) a = D.pageπ ↑(n+1) b := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (subobject_cokernel_π_eq_zero_iff (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _) _).mpr
  have hz : (Subobject.ofLE _ _ (D.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
      D.pageπ ↑n) (a-b) = 0 := by rw [map_sub, h, sub_self]
  have hb := (subobject_cokernel_π_eq_zero_iff (D.B ↑n) (D.Z ↑n) (D.B_le_Z _) _).mp hz
  have he := ConcreteCategory.congr_hom (Subobject.ofLE_arrow
    (D.Z_anti (show (↑n : WithTop ℕ) ≤ ↑(n+1) by exact_mod_cast Nat.le_succ n))) (a-b)
  change (D.Z ↑n).arrow _ = (D.Z ↑(n+1)).arrow (a-b) at he
  rw [he] at hb
  exact (ModuleCat.subobjectModule D.V).monotone
    (D.B_mono (by exact_mod_cast Nat.le_succ n)) hb

private theorem finiteQuotientSuccessorComparison
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι}
    (f : FromFirstMorphism E F) (r : ℤ) (hr : E.r₀ ≤ r) (q : ι) :
    (Function.Surjective (f.pageMap r q) →
      Function.Injective (f.pageMap r (q+E.diffDeg r)) →
      Function.Injective (f.pageMap (r+1) (q+E.diffDeg r))) ∧
    (Function.Surjective (f.pageMap r (q+E.diffDeg r)) →
      Function.Injective (f.pageMap r (q+E.diffDeg r+E.diffDeg r)) →
      Function.Surjective (f.pageMap (r+1) (q+E.diffDeg r))) := by
  have hfirst := f.r₀_eq
  have hdegree := f.diffDeg_eq
  rcases E with ⟨⟨r₀,D,δ,d⟩,dd,Zs,Bs⟩
  rcases F with ⟨⟨r₀',D',δ',d'⟩,dd',Zs',Bs'⟩
  dsimp at hfirst hdegree
  subst r₀'
  subst δ'
  change r₀ ≤ r at hr
  let E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι := ⟨⟨r₀,D,δ,d⟩,dd,Zs,Bs⟩
  let F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι := ⟨⟨r₀,D',δ,d'⟩,dd',Zs',Bs'⟩
  let p := q+δ r
  let g := f.toSSDataMorphism
  let n := (r-r₀).toNat
  have hs : (r+1-r₀).toNat = n+1 := by dsimp [n]; omega
  let down (T : SSData (ModuleCat.{0} ℤ)) :=
    Subobject.ofLE (T.Z ↑(n+1)) (T.Z ↑n)
      (T.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫ T.pageπ ↑n
  have naturalDown (z : (Subobject.underlying.obj ((D p).Z ↑(n+1)) : ModuleCat.{0} ℤ)) :
      (g.pageMap p ↑n) (down (D p) z) =
        down (D' p) (g.cycleMap p ↑(n+1) z) := by
    have h := g.cycleMap_ofLE_assoc p
      (show (↑n : WithTop ℕ) ≤ ↑(n+1) by exact_mod_cast Nat.le_succ n) ((D' p).pageπ ↑n)
    rw [← g.pageπ_pageMap] at h
    simpa only [down, ModuleCat.comp_apply] using (ConcreteCategory.congr_hom h z)
  have comm (q : ι) (x : (D q).page ↑n) :
      (g.pageMap (q+δ r) ↑n) (d r q x) = d' r q (g.pageMap q ↑n x) := by
    have h := f.pageMap_comm_d r hr q
    simpa only [FromFirstMorphism.pageMap, SSDataMorphism.pageMapAt, eqToHom_refl,
      Category.comp_id, ModuleCat.comp_apply, E, F, g, n] using
        (ConcreteCategory.congr_hom h x).symm
  constructor
  · intro hin hmid
    change Function.Surjective (g.pageMap q ↑n) at hin
    change Function.Injective (g.pageMap p ↑n) at hmid
    change Function.Injective (g.pageMap p ↑(r+1-r₀).toNat)
    rw [hs]
    intro a b hab
    apply sub_eq_zero.mp
    have ha : g.pageMap p ↑(n+1) (a-b) = 0 := by rw [map_sub, hab, sub_self]
    haveI : Epi ((D p).pageπ ↑(n+1)) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective ((D p).pageπ ↑(n+1))).mp inferInstance (a-b)
    rw [← hz] at ha ⊢
    have hzmap : (D' p).pageπ ↑(n+1) (g.cycleMap p ↑(n+1) z) = 0 := by
      simpa only [ModuleCat.comp_apply] using
        (ConcreteCategory.congr_hom (g.pageπ_pageMap p ↑(n+1)) z).symm.trans ha
    have hzin := (finiteQuotientNextProjectionZero F r hr q (g.cycleMap p ↑(n+1) z)).mp hzmap
    change down (D' p) (g.cycleMap p ↑(n+1) z) ∈ LinearMap.range
      (d' r q).hom at hzin
    obtain ⟨b,hb⟩ := hzin
    obtain ⟨c,rfl⟩ := hin b
    have hc := comm q c
    have he : down (D p) z = d r q c := by
      apply hmid
      rw [naturalDown, hc, hb]
    apply (finiteQuotientNextProjectionZero E r hr q z).mpr
    change down (D p) z ∈ LinearMap.range (d r q).hom
    exact ⟨c,he.symm⟩
  · intro hmid hout
    change Function.Surjective (g.pageMap p ↑n) at hmid
    change Function.Injective (g.pageMap (p+δ r) ↑n) at hout
    change Function.Surjective (g.pageMap p ↑(r+1-r₀).toNat)
    rw [hs]
    intro a
    haveI : Epi ((D' p).pageπ ↑(n+1)) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z',rfl⟩ := (ModuleCat.epi_iff_surjective ((D' p).pageπ ↑(n+1))).mp inferInstance a
    obtain ⟨x,hx⟩ := hmid (down (D' p) z')
    have hx0 : d r p x = 0 := by
      apply hout
      rw [map_zero, comm, hx]
      change down (D' p) z' ∈ LinearMap.ker (d' r p).hom
      rw [← subobjectModule_kernel, Zs' r p hr, subobjectModule_image]
      exact ⟨z',rfl⟩
    have hxmem : x ∈ ModuleCat.subobjectModule _ (kernelSubobject (d r p)) := by
      rw [subobjectModule_kernel]
      exact hx0
    rw [Zs r p hr, subobjectModule_image] at hxmem
    obtain ⟨z,hz⟩ := hxmem
    refine ⟨(D p).pageπ ↑(n+1) z, ?_⟩
    have hp := ConcreteCategory.congr_hom (g.pageπ_pageMap p ↑(n+1)) z
    simp only [ModuleCat.comp_apply] at hp
    refine hp.trans (finiteQuotientNextEqOfEarlierEq (D' p) n _ z' ?_)
    change down (D' p) (g.cycleMap p ↑(n+1) z) = down (D' p) z'
    rw [← naturalDown, hz, hx]

end FirstPageComparisonConstruction

universe absorbComparisonU absorbComparisonV absorbComparisonI

set_option backward.isDefEq.respectTransparency false in
/-- Finite representative preservation extends to the intersection of cycles
and the union of boundaries. The ambient maps remain exactly the given maps. -/
private def dataMorphismOfFinite
    {C : Type absorbComparisonU} [Category.{absorbComparisonV} C] [Abelian C]
    {ι : Type absorbComparisonI} [AddCommGroup ι] [DecidableEq ι]
    (D D' : ι → SSData C) (φ : ∀ i, (D i).V ⟶ (D' i).V)
    (hZ : ∀ i (n : ℕ), ∃ (lift : Subobject.underlying.obj ((D i).Z n) ⟶
        Subobject.underlying.obj ((D' i).Z n)),
      lift ≫ ((D' i).Z n).arrow = ((D i).Z n).arrow ≫ φ i)
    (hB : ∀ i (n : ℕ), ∃ (lift : Subobject.underlying.obj ((D i).B n) ⟶
        Subobject.underlying.obj ((D' i).B n)),
      lift ≫ ((D' i).B n).arrow = ((D i).B n).arrow ≫ φ i) :
    SSDataMorphism ι D D' where
  φ := φ
  preserves_Z i r := by
    cases r using WithTop.recTopCoe with
    | coe n => exact hZ i n
    | top =>
      let f := ((D i).Z ⊤).arrow ≫ φ i
      have hI : imageSubobject f ≤ (D' i).Z ⊤ := by
        apply (D' i).Z_top_greatest
        intro n
        apply imageSubobject_le f
          (Subobject.ofLE ((D i).Z ⊤) ((D i).Z n) ((D i).Z_anti le_top) ≫
            (hZ i n).choose)
        rw [Category.assoc, (hZ i n).choose_spec, ← Category.assoc,
          Subobject.ofLE_arrow]
      refine ⟨factorThruImageSubobject f ≫
        Subobject.ofLE (imageSubobject f) ((D' i).Z ⊤) hI, ?_⟩
      rw [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
  preserves_B i r := by
    cases r using WithTop.recTopCoe with
    | coe n => exact hB i n
    | top =>
      let Q := (Subobject.pullback (φ i)).obj ((D' i).B ⊤)
      have hQ : (D i).B ⊤ ≤ Q := by
        apply (D i).B_top_least
        intro n
        apply Subobject.le_of_factors
        apply (pullback_factors_iff (φ i) ((D' i).B ⊤) (((D i).B n).arrow)).mpr
        rw [Subobject.factors_iff]
        have hn : (D' i).B n ≤ (D' i).B ⊤ := (D' i).B_mono le_top
        refine ⟨(hB i n).choose ≫
          Subobject.ofLE ((D' i).B n) ((D' i).B ⊤) hn, ?_⟩
        calc
          ((hB i n).choose ≫ Subobject.ofLE ((D' i).B n) ((D' i).B ⊤) hn) ≫
              ((D' i).B ⊤).arrow =
            (hB i n).choose ≫
              (Subobject.ofLE ((D' i).B n) ((D' i).B ⊤) hn ≫ ((D' i).B ⊤).arrow) :=
            Category.assoc _ _ _
          _ = (hB i n).choose ≫ ((D' i).B n).arrow :=
            congrArg (fun q => (hB i n).choose ≫ q) (Subobject.ofLE_arrow hn)
          _ = ((D i).B n).arrow ≫ φ i := (hB i n).choose_spec
      refine ⟨Subobject.ofLE ((D i).B ⊤) Q hQ ≫
        Subobject.pullbackπ (φ i) ((D' i).B ⊤), ?_⟩
      rw [Category.assoc, (Subobject.isPullback (φ i) ((D' i).B ⊤)).w,
        ← Category.assoc, Subobject.ofLE_arrow]

set_option backward.isDefEq.respectTransparency false in
private theorem dataMorphismOfFinite_ambient
    {C : Type absorbComparisonU} [Category.{absorbComparisonV} C] [Abelian C]
    {ι : Type absorbComparisonI} [AddCommGroup ι] [DecidableEq ι]
    (D D' : ι → SSData C) (φ : ∀ i, (D i).V ⟶ (D' i).V)
    (hZ : ∀ i (n : ℕ), ∃ (lift : Subobject.underlying.obj ((D i).Z n) ⟶
        Subobject.underlying.obj ((D' i).Z n)),
      lift ≫ ((D' i).Z n).arrow = ((D i).Z n).arrow ≫ φ i)
    (hB : ∀ i (n : ℕ), ∃ (lift : Subobject.underlying.obj ((D i).B n) ⟶
        Subobject.underlying.obj ((D' i).B n)),
      lift ≫ ((D' i).B n).arrow = ((D i).B n).arrow ≫ φ i) (i : ι) :
    (dataMorphismOfFinite D D' φ hZ hB).φ i = φ i := rfl


private def inversionConstruction : LambdaInversionComparison background nuPageData where
  data := by sorry
  e2 := by sorry
  differential := by sorry
  lambda := by sorry

/-- The fixed mathematical object on the project background. -/
public def inversion_data :
  ∀ X : AdamsObject,
    SSDataMorphism Tridegree
      (background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData
      (fun i => (background.classical.obj (X.obj background.auxiliary)).ssData (i.1,i.2.1)) := by
  exact inversionConstruction.data


public theorem inversion_e2 :
  ∀ (X : AdamsObject) (s t w : ℤ) (hw : w ≤ t)
      (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)),
    comparisonPageMap background X (inversion_data X) 2 s t w (nuWeightLabel background X s t w hw x) = x := by
  exact inversionConstruction.e2


public theorem inversion_differential :
  ∀ (X : AdamsObject) (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ),
    let map := fun s t => comparisonPageMap background X (inversion_data X) r s t w
    syntheticDifferential background X r s t w ≫ map (s+r) (t+r-1) =
      map s t ≫ classicalDifferential background X r s t := by
  exact inversionConstruction.differential


public theorem inversion_lambda :
  ∀ (X : AdamsObject) (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ),
    let map := fun w => comparisonPageMap background X (inversion_data X) r s t w
    pageLambda X r s t w ≫ map (w-1) = map w := by
  exact inversionConstruction.lambda

public def inversionData : LambdaInversionComparison background nuPageData where
  data := inversion_data
  e2 := inversion_e2
  differential := inversion_differential
  lambda := inversion_lambda

section FreeInversionConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem freeDifferentialTransport
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    (E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι)
    (r : ℤ) {p q : ι} (h : p=q) :
    eqToHom (congrArg (E.Page r) h) ≫ E.d r q =
      E.d r p ≫ eqToHom (congrArg (E.Page r) (congrArg (fun p => p+E.diffDeg r) h)) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private def freeInflate
    {ι κ : Type} [AddCommGroup ι] [DecidableEq ι] [AddCommGroup κ] [DecidableEq κ]
    (E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) κ)
    (τ : ι →+ κ) (δ : ℤ → ι) (hδ : ∀ r, τ (δ r) = E.diffDeg r) :
    KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι where
  r₀ := E.r₀
  ssData p := E.ssData (τ p)
  diffDeg := δ
  d r p := E.d r (τ p) ≫ eqToHom (congrArg (E.Page r)
    (by rw [map_add, hδ]))
  d_comp_d r p := by
    have h := freeDifferentialTransport E r
      (p := τ p+E.diffDeg r) (q := τ (p+δ r)) (by rw [map_add,hδ])
    simp only [← Category.assoc]
    rw [Category.assoc (E.d r (τ p)), h]
    simp only [← Category.assoc, E.d_comp_d, zero_comp]
  Z_succ r p hr := by
    dsimp only
    rw [← E.Z_succ r (τ p) hr]
    apply (ModuleCat.subobjectModule _).injective
    simp only [subobjectModule_kernel]
    ext x
    change (E.d r (τ p) ≫ eqToHom _) x = 0 ↔ E.d r (τ p) x = 0
    rw [ModuleCat.comp_apply]
    exact (ModuleCat.mono_iff_injective (eqToHom _)).mp inferInstance |>.eq_iff' (by simp)
  B_succ r p hr := by
    dsimp only
    have aux (q : κ) (h : τ p+E.diffDeg r=q) :
        imageSubobject (E.d r (τ p) ≫ eqToHom (congrArg (E.Page r) h)) =
          imageSubobject (Subobject.ofLE ((E.ssData q).B ↑((r-E.r₀).toNat+1))
            ((E.ssData q).Z ↑(r-E.r₀).toNat)
            (((E.ssData q).B_le_Z _).trans ((E.ssData q).Z_anti
              (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat))) ≫
                (E.ssData q).pageπ ↑(r-E.r₀).toNat) := by
      cases h
      simpa only [eqToHom_refl, Category.comp_id] using E.B_succ r (τ p) hr
    exact aux _ (by rw [map_add,hδ])

private def freeForgetWeight : Tridegree →+ (ℤ × ℤ) where
  toFun i := (i.1,i.2.1)
  map_zero' := rfl
  map_add' _ _ := rfl

private def freeClassicalInflation (X : AdamsObject (coefficients := background.coefficients)) :=
  freeInflate (background.classical.obj (X.obj background.auxiliary)) freeForgetWeight syntheticAdamsRawShift
    (fun r => (background.classical.differentialDegree _ r).symm)

private theorem freeNormalizePageMap
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {D D' : ι → SSData (ModuleCat.{0} ℤ)} (g : SSDataMorphism ι D D')
    (a b c : ℤ) (ha : a=c) (hb : b=c) (r : ℤ) (p : ι) :
    eqToHom (congrArg (fun z => (D p).page ↑(r-z).toNat) ha) ≫
      g.pageMap p ↑(r-c).toNat ≫
        eqToHom (congrArg (fun z => (D' p).page ↑(r-z).toNat) hb.symm) =
      g.pageMap p ↑(r-a).toNat ≫
        eqToHom (congrArg (fun z => (D' p).page ↑(r-z).toNat) (ha.trans hb.symm)) := by
  cases ha
  cases hb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private def freeInversionRawMap (X : AdamsObject (coefficients := background.coefficients)) (r s t w : ℤ) :=
  (inversion_data X).pageMapAt
    (E := (background.family.nu background.nu (X.obj background.auxiliary)).sequence.toPreSS)
    (E' := (freeClassicalInflation X).toPreSS)
    ((background.family.nu background.nu (X.obj background.auxiliary)).firstPage.trans
      (background.classical.firstPage _).symm) r (s,t,w)

private theorem freeInversionRawMap_eq (X : AdamsObject) (r s t w : ℤ) :
    freeInversionRawMap X r s t w = comparisonPageMap background X (inversion_data X) r s t w := by
  dsimp only [freeInversionRawMap, comparisonPageMap, SSDataMorphism.pageMapAt]
  exact (freeNormalizePageMap (inversion_data X) _ _ 2
    (background.family.nu background.nu (X.obj background.auxiliary)).firstPage
    (background.classical.firstPage _) r (s,t,w)).symm

private theorem freeDegreeMapNatural
    {ι : Type} {A B : ι → ModuleCat.{0} ℤ}
    (m : ∀ i, A i ⟶ B i) {p q : ι} (h : p=q) :
    eqToHom (congrArg A h) ≫ m q = m p ≫ eqToHom (congrArg B h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem freeLocalDifferentialSquare
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι}
    (r : ℤ) (p q : ι) (hδ : E.diffDeg r=F.diffDeg r)
    (m : ∀ i, E.Page r i ⟶ F.Page r i)
    (hs : p+E.diffDeg r=q) (ht : p+F.diffDeg r=q)
    (h : (E.d r p ≫ eqToHom (congrArg (E.Page r) hs)) ≫ m q =
      m p ≫ (F.d r p ≫ eqToHom (congrArg (F.Page r) ht))) :
    m p ≫ F.d r p = E.d r p ≫ m (p+E.diffDeg r) ≫
      eqToHom (congrArg (F.Page r) (congrArg (fun d => p+d) hδ)) := by
  apply (cancel_mono (eqToHom (congrArg (F.Page r) ht))).mp
  simp only [Category.assoc, eqToHom_trans]
  have hn := freeDegreeMapNatural m hs
  rw [Category.assoc, hn] at h
  simpa only [Category.assoc] using h.symm

private def freeInversionMorphism (X : AdamsObject) :
    FromFirstMorphism
      (background.family.nu background.nu (X.obj background.auxiliary)).sequence (freeClassicalInflation X) where
  toSSDataMorphism := inversion_data X
  r₀_eq := (background.family.nu background.nu (X.obj background.auxiliary)).firstPage.trans
    (background.classical.firstPage _).symm
  diffDeg_eq := funext (background.family.nu background.nu (X.obj background.auxiliary)).differentialDegree
  comm_d r hr p := by
    rcases p with ⟨s,t,w⟩
    have hr2 : 2 ≤ r := by
      simpa only [(background.family.nu background.nu (X.obj background.auxiliary)).firstPage] using hr
    let E := (background.family.nu background.nu (X.obj background.auxiliary)).sequence
    let F := freeClassicalInflation X
    let m := fun i : Tridegree => freeInversionRawMap X r i.1 i.2.1 i.2.2
    change m (s,t,w) ≫ F.d r (s,t,w) =
      E.d r (s,t,w) ≫ m ((s,t,w)+E.diffDeg r) ≫ _
    apply freeLocalDifferentialSquare (E := E) (F := F) r (s,t,w) (s+r,t+r-1,w)
      ((background.family.nu background.nu (X.obj background.auxiliary)).differentialDegree r) m
      (by rw [(background.family.nu background.nu (X.obj background.auxiliary)).differentialDegree];
          ext <;> simp only [syntheticAdamsRawShift, Prod.fst_add, Prod.snd_add] <;> omega)
      (by change (s,t,w)+syntheticAdamsRawShift r = _;
          ext <;> simp only [syntheticAdamsRawShift, Prod.fst_add, Prod.snd_add] <;> omega)
    change (E.d r (s,t,w) ≫ _) ≫ freeInversionRawMap X r (s+r) (t+r-1) w =
      freeInversionRawMap X r s t w ≫ (F.d r (s,t,w) ≫ _)
    rw [freeInversionRawMap_eq, freeInversionRawMap_eq]
    have h := inversion_differential X r hr2 s t w
    dsimp only at h
    delta KIP126.Literature.syntheticDifferential KIP126.Literature.classicalDifferential at h
    delta SyntheticAdamsSS.d at h
    simpa only [E, F, freeClassicalInflation, freeInflate, freeForgetWeight,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, Category.assoc, eqToHom_trans] using h

private theorem freeInversionMorphism_pageMap (X : AdamsObject) (r s t w : ℤ) :
    (freeInversionMorphism X).pageMap r (s,t,w) =
      comparisonPageMap background X (inversion_data X) r s t w := by
  change freeInversionRawMap X r s t w = _
  exact freeInversionRawMap_eq X r s t w

private def freeRawPageIso
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Tridegree}
    (e : E ≅ F) (r : ℤ) (p : Tridegree) : E.Page r p ≅ F.Page r p where
  hom := e.hom.pageMap r p
  inv := e.inv.pageMap r p
  hom_inv_id := by
    rw [← SpectralSequenceMorphism.pageMap_comp, e.hom_inv_id,
      SpectralSequenceMorphism.pageMap_id]
  inv_hom_id := by
    rw [← SpectralSequenceMorphism.pageMap_comp, e.inv_hom_id,
      SpectralSequenceMorphism.pageMap_id]

private theorem freeNuWeightLabelBijective (X : AdamsObject) (s t w : ℤ) (hw : w ≤ t) :
    Function.Bijective (nuWeightLabel background X s t w hw) := by
  let zeroIso := SyntheticCategory.biShift_zero.app
    (background.nu.functor.obj (X.obj background.auxiliary))
  let zeroPage := freeRawPageIso (background.family.functor.mapIso zeroIso) 2
    (s,t,t-(t-w).toNat)
  have hzero : Function.Bijective zeroPage.hom := ConcreteCategory.bijective_of_isIso _
  change Function.Bijective (fun x => nuWeightLabel background X s t w hw x)
  dsimp only [nuWeightLabel, regradeE2, targetNuLabel]
  apply Function.Bijective.comp
  · exact ConcreteCategory.bijective_of_isIso _
  · apply Function.Bijective.comp
    · exact hzero
    · change Function.Bijective
        ((fun z : (background.family.obj ((SyntheticCategory.biShift (0,0)).obj
            (background.nu.functor.obj (X.obj background.auxiliary)))).E₂
              (s,t,t+0-(t-w).toNat) =>
          Eq.mp (by simp only [add_zero]) z) ∘
            (background.comparison.nuE2 X 0 s t (t-w).toNat))
      exact (Equiv.cast _).bijective.comp
        (background.comparison.nuE2 X 0 s t (t-w).toNat).bijective

private theorem freeInversionMorphism_e2_bijective (X : AdamsObject) (s t w : ℤ)
    (hw : w ≤ t) : Function.Bijective ((freeInversionMorphism X).pageMap 2 (s,t,w)) := by
  rw [freeInversionMorphism_pageMap]
  have hlabel := freeNuWeightLabelBijective X s t w hw
  constructor
  · intro a b hab
    obtain ⟨x,rfl⟩ := hlabel.2 a
    obtain ⟨y,rfl⟩ := hlabel.2 b
    apply congrArg (nuWeightLabel background X s t w hw)
    exact (inversion_e2 X s t w hw x).symm.trans (hab.trans (inversion_e2 X s t w hw y))
  · intro x
    exact ⟨nuWeightLabel background X s t w hw x, inversion_e2 X s t w hw x⟩

-- Use the same private witness in the exposed constructor.
set_option backward.privateInPublic true in
private theorem freeInversionIsIso (X : AdamsObject) (r : ℤ) (hr : 2 ≤ r)
    (s t w : ℤ) (hfree : r-2 ≤ t-w) :
    IsIso (comparisonPageMap background X (inversion_data X) r s t w) := by
  let E := (background.family.nu background.nu (X.obj background.auxiliary)).sequence
  let f := freeInversionMorphism X
  have first : E.r₀ = 2 := (background.family.nu background.nu (X.obj background.auxiliary)).firstPage
  have degree (r : ℤ) : E.diffDeg r = syntheticAdamsRawShift r :=
    (background.family.nu background.nu (X.obj background.auxiliary)).differentialDegree r
  have comparison (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) :
      (Function.Surjective (f.pageMap r (s-r,t-r+1,w)) →
        Function.Injective (f.pageMap r (s,t,w)) →
        Function.Injective (f.pageMap (r+1) (s,t,w))) ∧
      (Function.Surjective (f.pageMap r (s,t,w)) →
        Function.Injective (f.pageMap r (s+r,t+r-1,w)) →
        Function.Surjective (f.pageMap (r+1) (s,t,w))) := by
    let q : Tridegree := (s-r,t-r+1,w)
    have hcenter : q+E.diffDeg r = (s,t,w) := by
      rw [degree]
      ext <;> simp only [q, syntheticAdamsRawShift, Prod.fst_add, Prod.snd_add] <;> omega
    have hout : (s,t,w)+E.diffDeg r = (s+r,t+r-1,w) := by
      rw [degree]
      ext <;> simp only [syntheticAdamsRawShift, Prod.fst_add, Prod.snd_add] <;> omega
    let P (p p' : Tridegree) : Prop :=
      (Function.Surjective (f.pageMap r q) →
        Function.Injective (f.pageMap r p) → Function.Injective (f.pageMap (r+1) p)) ∧
      (Function.Surjective (f.pageMap r p) →
        Function.Injective (f.pageMap r p') → Function.Surjective (f.pageMap (r+1) p))
    have h : P (q+E.diffDeg r) (q+E.diffDeg r+E.diffDeg r) :=
      finiteQuotientSuccessorComparison f r (by rw [first]; exact hr) q
    have h' : P (s,t,w) ((s,t,w)+E.diffDeg r) :=
      Eq.mp (congrArg (fun p => P p (p+E.diffDeg r)) hcenter) h
    exact Eq.mp (congrArg (P (s,t,w)) hout) h'
  have pages (k : ℕ) :
      (∀ s t w : ℤ, (k : ℤ) ≤ t-w → Function.Injective (f.pageMap (k+2) (s,t,w))) ∧
      (∀ s t w : ℤ, 0 ≤ t-w → Function.Surjective (f.pageMap (k+2) (s,t,w))) := by
    induction k with
    | zero =>
      constructor
      · intro s t w hnonneg
        change Function.Injective (f.pageMap 2 (s,t,w))
        exact (freeInversionMorphism_e2_bijective X s t w (by omega)).1
      · intro s t w hnonneg
        change Function.Surjective (f.pageMap 2 (s,t,w))
        exact (freeInversionMorphism_e2_bijective X s t w (by omega)).2
    | succ k ih =>
      have hr : (2 : ℤ) ≤ (k : ℤ)+2 := by omega
      constructor
      · intro s t w hfree
        have hin := ih.2 (s-(k+2)) (t-(k+2)+1) w (by omega)
        have hmid := ih.1 s t w (by omega)
        have h := (comparison ((k : ℤ)+2) hr s t w).1 hin hmid
        have hpage : ((Nat.succ k : ℕ) : ℤ)+2 = (k : ℤ)+2+1 := by omega
        exact Eq.mp (congrArg (fun r : ℤ => Function.Injective (f.pageMap r (s,t,w))) hpage.symm) h
      · intro s t w hnonneg
        have hmid := ih.2 s t w hnonneg
        have hout := ih.1 (s+(k+2)) (t+(k+2)-1) w (by omega)
        have h := (comparison ((k : ℤ)+2) hr s t w).2 hmid hout
        have hpage : ((Nat.succ k : ℕ) : ℤ)+2 = (k : ℤ)+2+1 := by omega
        exact Eq.mp (congrArg (fun r : ℤ => Function.Surjective (f.pageMap r (s,t,w))) hpage.symm) h
  let k := (r-2).toNat
  have hk : (k : ℤ)+2 = r := by dsimp [k]; rw [Int.toNat_of_nonneg (by omega)]; omega
  have hbij : Function.Bijective (f.pageMap r (s,t,w)) := by
    rw [← hk]
    exact ⟨(pages k).1 s t w (by omega), (pages k).2 s t w (by omega)⟩
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  rw [← freeInversionMorphism_pageMap X r s t w]
  exact hbij

-- The IsIso witness is private; free_component exposes the resulting isomorphism.
set_option backward.proofsInPublic true in
set_option backward.privateInPublic true in
/-- The fixed inversion map is an isomorphism throughout the free range,
by the joint injectivity/surjectivity comparison induction. -/
public def free_component :
  ∀ (X : AdamsObject) (r : ℤ) (_hr : 2 ≤ r)
    (s t w : ℤ) (_h : r-2 ≤ t-w),
    (background.family.nu background.nu (X.obj background.auxiliary)).Page r (s,t,w) ≅
      (background.classical.obj (X.obj background.auxiliary)).Page r (s,t) := by
  intro X r hr s t w h
  letI : IsIso (comparisonPageMap background X (inversion_data X) r s t w) := by
    exact freeInversionIsIso X r hr s t w h
  exact asIso (comparisonPageMap background X (inversion_data X) r s t w)

/-- Compatibility is inherited from the same fixed inversion comparison. -/
public theorem free_e2 :
  ∀ (X : AdamsObject) (s t w : ℤ) (hw : w ≤ t)
      (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)),
    (free_component X 2 (by omega) s t w (by omega)).hom (nuWeightLabel background X s t w hw x) = x := by
  intro X s t w hw x
  exact inversion_e2 X s t w hw x

/-- Compatibility is inherited from the same fixed inversion comparison. -/
public theorem free_lambda :
  ∀ (X : AdamsObject) (r : ℤ) (hr : 2 ≤ r)
      (s t w : ℤ) (h : r-2 ≤ t-w),
    pageLambda X r s t w ≫ (free_component X r hr s t (w-1) (by omega)).hom =
      (free_component X r hr s t w h).hom := by
  intro X r hr s t w h
  exact inversion_lambda X r hr s t w

/-- Compatibility is inherited from the same fixed inversion comparison. -/
public theorem free_differential :
  ∀ (X : AdamsObject) (r : ℤ) (hr : 2 ≤ r)
      (s t w : ℤ) (h : r-2 ≤ t-w),
    syntheticDifferential background X r s t w ≫
        (free_component X r hr (s+r) (t+r-1) w (by omega)).hom =
      (free_component X r hr s t w h).hom ≫ classicalDifferential background X r s t := by
  intro X r hr s t w h
  exact inversion_differential X r hr s t w

public def freeData : FreeLambdaPages background nuPageData where
  component := free_component
  e2 := free_e2
  lambda := free_lambda
  differential := free_differential

public def classicalLift := FreeLambdaPages.classicalLift background freeData

public abbrev classicalLift_differential := FreeLambdaPages.classicalLift_differential background freeData

public abbrev classicalLift_lambda := FreeLambdaPages.classicalLift_lambda background freeData

/-- The constructed free comparison uses precisely this inversion map. -/
public theorem free_inversion :
  ∀ (X : AdamsObject) (r : ℤ) (hr : 2 ≤ r)
    (s t w : ℤ) (h : r-2 ≤ t-w),
    (free_component X r hr s t w h).hom = comparisonPageMap background X (inversion_data X) r s t w := by
  intro X r hr s t w h
  rfl

end FreeInversionConstruction

/-- The actual finite E₂ comparison and its retained-label square are chosen
together; these fields give the retained and safe-range isomorphisms. -/
private structure FiniteQuotientE2Construction
    (X : AdamsObject (coefficients := background.coefficients)) (n : ℕ) where
  component : ∀ s t w : ℤ,
    (background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) n).Page 2 (s,t,w) ≅
      quotientE2Component background X n s t w
  component_retained : ∀ (s t w : ℤ) (h : 0 ≤ t-w ∧ t-w < n)
      (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)),
    HEq ((component s t w).hom
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) n).pageMap
        2 (s,t,w) (nuWeightLabel background X s t w (sub_nonneg.mp h.1) x))) x

private def finiteQuotientE2Construction (X : AdamsObject) (n : ℕ) (_hn : 0 < n) :
    FiniteQuotientE2Construction X n := by
  sorry

/-- The component of the same calibrated finite E₂ comparison. -/
public def finite_quotient_component :
  ∀ (X : AdamsObject) (n : ℕ) (hn : 0 < n),
  ∀ s t w : ℤ,
    (background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) n).Page 2 (s,t,w) ≅
      quotientE2Component background X n s t w :=
  fun X n hn => (finiteQuotientE2Construction X n hn).component


public theorem finite_quotient_component_retained :
  ∀ (X : AdamsObject) (n : ℕ) (hn : 0 < n),
  ∀ (s t w : ℤ) (h : 0 ≤ t-w ∧ t-w < n)
      (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)),
    HEq (((finite_quotient_component X n hn) s t w).hom
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) n).pageMap
        2 (s,t,w) (nuWeightLabel background X s t w (by omega) x))) x := by
  exact fun X n hn => (finiteQuotientE2Construction X n hn).component_retained

private def retainedLabelPageIso
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Tridegree}
    (e : E ≅ F) (r : ℤ) (p : Tridegree) : E.Page r p ≅ F.Page r p where
  hom := e.hom.pageMap r p
  inv := e.inv.pageMap r p
  hom_inv_id := by
    rw [← SpectralSequenceMorphism.pageMap_comp, e.hom_inv_id,
      SpectralSequenceMorphism.pageMap_id]
  inv_hom_id := by
    rw [← SpectralSequenceMorphism.pageMap_comp, e.inv_hom_id,
      SpectralSequenceMorphism.pageMap_id]

private theorem projection_isIso_of_retained_labels
    {A B Q R : ModuleCat.{0} ℤ} (e : Q ≅ R) (f : A ⟶ Q)
    (label : B → A) (hlabel : Function.Bijective label)
    (hR : R = B) (hret : ∀ x : B, HEq (e.hom (f (label x))) x) :
    IsIso f := by
  subst R
  have hret' (x : B) : e.hom (f (label x)) = x := eq_of_heq (hret x)
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso _
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := hlabel.surjective a
    obtain ⟨y, rfl⟩ := hlabel.surjective b
    apply congrArg label
    have hcxy := congrArg e.hom hab
    simpa only [hret'] using hcxy
  · intro b
    refine ⟨label (e.hom b), ?_⟩
    apply he.injective
    exact hret' (e.hom b)

private theorem finiteQuotientRetainedImpl :
  ∀ (X : AdamsObject) (n : ℕ) (hn : 0 < n),
  ∀ (s t w : ℤ), 0 ≤ t-w ∧ t-w < n →
    IsIso ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) n).pageMap 2 (s,t,w)) := by
  intro X n hn s t w hstrip
  have hw : w ≤ t := by omega
  let zeroIso := SyntheticCategory.biShift_zero.app
    (background.nu.functor.obj (X.obj background.auxiliary))
  let zeroPage := retainedLabelPageIso (background.family.functor.mapIso zeroIso) 2
    (s,t,t-(t-w).toNat)
  have hzero : Function.Bijective zeroPage.hom :=
    ConcreteCategory.bijective_of_isIso _
  have hlabel : Function.Bijective (nuWeightLabel background X s t w hw) := by
    change Function.Bijective (fun x => nuWeightLabel background X s t w hw x)
    dsimp only [nuWeightLabel, regradeE2, targetNuLabel]
    apply Function.Bijective.comp
    · exact ConcreteCategory.bijective_of_isIso _
    · apply Function.Bijective.comp
      · exact hzero
      · change Function.Bijective
          ((fun z : (background.family.obj ((SyntheticCategory.biShift (0,0)).obj
              (background.nu.functor.obj (X.obj background.auxiliary)))).E₂
                (s,t,t+0-(t-w).toNat) =>
            Eq.mp (by simp only [add_zero]) z) ∘
              (background.comparison.nuE2 X 0 s t (t-w).toNat))
        exact (Equiv.cast _).bijective.comp
          (background.comparison.nuE2 X 0 s t (t-w).toNat).bijective
  apply projection_isIso_of_retained_labels (finite_quotient_component X n hn s t w)
    ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) n).pageMap
      2 (s,t,w)) (nuWeightLabel background X s t w hw) hlabel
    (by
      change (if 0 ≤ t-w ∧ t-w < n then
        (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t) else ModuleCat.of ℤ PUnit) = _
      exact if_pos hstrip)
  intro x
  exact finite_quotient_component_retained X n hn s t w hstrip x


/-- The actual retained quotient projection is an isomorphism by its component label square. -/
public theorem finite_quotient_retained :
  ∀ (X : AdamsObject) (n : ℕ) (hn : 0 < n),
  ∀ (s t w : ℤ), 0 ≤ t-w ∧ t-w < n →
    IsIso ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) n).pageMap 2 (s,t,w)) := finiteQuotientRetainedImpl

/-- The zero E₂ components remain zero on every later page by monotonicity
of the same cycle and boundary subobjects. -/
public theorem finite_quotient_vanishing :
  ∀ (X : AdamsObject) (n : ℕ), 0 < n →
    ∀ (r : ℤ), 2 ≤ r → ∀ (s t w : ℤ), (t-w < 0 ∨ (n : ℤ) ≤ t-w) →
      IsZero ((background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) n).Page r (s,t,w)) := by
  intro X n hn r hr s t w hout
  let E := (background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) n).sequence
  let D := E.ssData (s,t,w)
  have hstrip : ¬ (0 ≤ t-w ∧ t-w < n) := by omega
  have hzero2 : IsZero (E.Page 2 (s,t,w)) := by
    apply (finite_quotient_component X n hn s t w).isZero_iff.mpr
    change IsZero (if 0 ≤ t-w ∧ t-w < n then
      (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t) else ModuleCat.of ℤ PUnit)
    rw [if_neg hstrip]
    exact ModuleCat.isZero_of_subsingleton _
  have hfirst : E.r₀ = 2 :=
    (background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) n).firstPage
  have hzero0 : IsZero (D.page (↑(0 : ℕ))) := by
    simpa only [D, Page, hfirst, sub_self, Int.toNat_zero] using hzero2
  have hBZ : D.B (↑(0 : ℕ)) = D.Z (↑(0 : ℕ)) :=
    D.eq_of_page_isZero _ hzero0
  change IsZero (D.page ↑(r-E.r₀).toNat)
  apply D.page_isZero_of_eq
  apply le_antisymm (D.B_le_Z _)
  calc
    D.Z ↑(r-E.r₀).toNat ≤ D.Z (↑(0 : ℕ)) := D.Z_anti (by exact bot_le)
    _ = D.B (↑(0 : ℕ)) := hBZ.symm
    _ ≤ D.B ↑(r-E.r₀).toNat := D.B_mono (by exact bot_le)


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The retained E₂ strip propagates by a joint induction: the whole strip
remains injective, while the stated safe substrip remains surjective. -/
public theorem finite_quotient_safe :
  ∀ (X : AdamsObject) (n : ℕ) (hn : 0 < n),
  ∀ (r s t w : ℤ), 2 ≤ r → 0 ≤ t-w → t-w+r-2 < n →
    IsIso ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) n).pageMap r (s,t,w)) := by
  intro X n hn
  let E := (background.family.nu background.nu (X.obj background.auxiliary)).sequence
  let F := (background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) n).sequence
  let f : E ⟶ F := background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) n
  have first : E.r₀ = 2 := (background.family.nu background.nu (X.obj background.auxiliary)).firstPage
  have degree (r : ℤ) : E.diffDeg r = syntheticAdamsRawShift r :=
    (background.family.nu background.nu (X.obj background.auxiliary)).differentialDegree r
  have comparison (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) :
      (Function.Surjective (f.pageMap r (s-r,t-r+1,w)) →
        Function.Injective (f.pageMap r (s,t,w)) →
        Function.Injective (f.pageMap (r+1) (s,t,w))) ∧
      (Function.Surjective (f.pageMap r (s,t,w)) →
        Function.Injective (f.pageMap r (s+r,t+r-1,w)) →
        Function.Surjective (f.pageMap (r+1) (s,t,w))) := by
    let q : Tridegree := (s-r,t-r+1,w)
    have hcenter : q+E.diffDeg r = (s,t,w) := by
      rw [degree]
      ext <;> simp only [q, syntheticAdamsRawShift, Prod.fst_add, Prod.snd_add] <;> omega
    have hout : (s,t,w)+E.diffDeg r = (s+r,t+r-1,w) := by
      rw [degree]
      ext <;> simp only [syntheticAdamsRawShift, Prod.fst_add, Prod.snd_add] <;> omega
    let P (p p' : Tridegree) : Prop :=
      (Function.Surjective (f.pageMap r q) →
        Function.Injective (f.pageMap r p) → Function.Injective (f.pageMap (r+1) p)) ∧
      (Function.Surjective (f.pageMap r p) →
        Function.Injective (f.pageMap r p') → Function.Surjective (f.pageMap (r+1) p))
    have h : P (q+E.diffDeg r) (q+E.diffDeg r+E.diffDeg r) :=
      finiteQuotientSuccessorComparison (firstPageComparisonOfMorphism f) r (by rw [first]; exact hr) q
    have h' : P (s,t,w) ((s,t,w)+E.diffDeg r) :=
      Eq.mp (congrArg (fun p => P p (p+E.diffDeg r)) hcenter) h
    exact Eq.mp (congrArg (P (s,t,w)) hout) h'
  have pages (k : ℕ) :
      (∀ s t w : ℤ, 0 ≤ t-w → t-w < n →
        Function.Injective (f.pageMap (k+2) (s,t,w))) ∧
      (∀ s t w : ℤ, 0 ≤ t-w → t-w+(k+2)-2 < n →
        Function.Surjective (f.pageMap (k+2) (s,t,w))) := by
    induction k with
    | zero =>
      constructor
      · intro s t w hnonneg hlt
        change Function.Injective (f.pageMap 2 (s,t,w))
        haveI : IsIso (f.pageMap 2 (s,t,w)) := finite_quotient_retained X n hn s t w ⟨hnonneg,hlt⟩
        exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance |>.1
      · intro s t w hnonneg hlt
        change Function.Surjective (f.pageMap 2 (s,t,w))
        haveI : IsIso (f.pageMap 2 (s,t,w)) := finite_quotient_retained X n hn s t w ⟨hnonneg,by omega⟩
        exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance |>.2
    | succ k ih =>
      have hr : (2 : ℤ) ≤ (k : ℤ)+2 := by omega
      constructor
      · intro s t w hnonneg hlt
        have hin : Function.Surjective (f.pageMap (k+2) (s-(k+2),t-(k+2)+1,w)) := by
          by_cases hsource : 0 ≤ (t-((k : ℤ)+2)+1)-w
          · exact ih.2 _ _ _ hsource (by omega)
          · have hz := finite_quotient_vanishing X n hn ((k : ℤ)+2) hr
              (s-(k+2)) (t-(k+2)+1) w (Or.inl (by omega))
            haveI := hz.epi (f.pageMap (k+2) (s-(k+2),t-(k+2)+1,w))
            exact (ModuleCat.epi_iff_surjective _).mp inferInstance
        have h := (comparison ((k : ℤ)+2) hr s t w).1 hin (ih.1 _ _ _ hnonneg hlt)
        have hpage : ((Nat.succ k : ℕ) : ℤ)+2 = (k : ℤ)+2+1 := by omega
        exact Eq.mp (congrArg (fun r : ℤ => Function.Injective (f.pageMap r (s,t,w))) hpage.symm) h
      · intro s t w hnonneg hlt
        have hmid := ih.2 s t w hnonneg (by push_cast at hlt; omega)
        have hout := ih.1 (s+(k+2)) (t+(k+2)-1) w (by omega) (by push_cast at hlt; omega)
        have h := (comparison ((k : ℤ)+2) hr s t w).2 hmid hout
        have hpage : ((Nat.succ k : ℕ) : ℤ)+2 = (k : ℤ)+2+1 := by omega
        exact Eq.mp (congrArg (fun r : ℤ => Function.Surjective (f.pageMap r (s,t,w))) hpage.symm) h
  intro r s t w hr hnonneg hlt
  let k := (r-2).toNat
  have hk : (k : ℤ)+2 = r := by dsimp [k]; rw [Int.toNat_of_nonneg (by omega)]; omega
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  rw [← hk]
  exact ⟨(pages k).1 s t w hnonneg (by omega), (pages k).2 s t w hnonneg (by omega)⟩


public theorem above_diagonal :
  ∀ (X : AdamsObject) (r : ℤ), 2 ≤ r →
    ∀ (s t w : ℤ), t < w → IsZero ((background.family.nu background.nu (X.obj background.auxiliary)).Page r (s,t,w)) := by
  sorry


public def finite_quotient :
  ∀ (X : AdamsObject) (n : ℕ), 0 < n → NuModLambdaPageData background X n := fun X n hn => { component := finite_quotient_component X n hn, component_retained := finite_quotient_component_retained X n hn, retained := finite_quotient_retained X n hn, safe := finite_quotient_safe X n hn }


public def infinityShift_comparison :
  ∀ k : ℕ, SyntheticESSShiftComparison background (0,-(k:ℤ)) := fun k => KIP126.AdamsSynthetic.Completed.essShift (0,-(k:ℤ))

/- Naturality from filtered homotopy maps and convergence comparisons
through the filtered-piece shift. -/
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem infinityMapReindex {ι : Type} {A B : ι → ModuleCat.{0} ℤ}
    (φ : ∀ i, A i ⟶ B i) {i j : ι} (h : i=j) :
    φ i ≫ eqToHom (congrArg B h) = eqToHom (congrArg A h) ≫ φ j := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem infinityTransportedSquare
    {A B A' B' A₀ B₀ A₀' B₀' : ModuleCat.{0} ℤ}
    (iA : A₀=A) (iB : B₀=B) (jA : A'=A₀') (jB : B'=B₀')
    (eA : A ≅ A') (eB : B ≅ B')
    (f : A ⟶ B) (f' : A' ⟶ B') (g : A₀ ⟶ B₀) (g' : A₀' ⟶ B₀')
    (h : f ≫ eB.hom = eA.hom ≫ f')
    (hin : g ≫ eqToHom iB = eqToHom iA ≫ f)
    (hout : f' ≫ eqToHom jB = eqToHom jA ≫ g') :
    g ≫ (eqToHom iB ≫ eB.hom ≫ eqToHom jB) =
      (eqToHom iA ≫ eA.hom ≫ eqToHom jA) ≫ g' := by
  calc
    _ = (g ≫ eqToHom iB) ≫ eB.hom ≫ eqToHom jB := by
      simp only [Category.assoc]
    _ = (eqToHom iA ≫ f) ≫ eB.hom ≫ eqToHom jB := by rw [hin]
    _ = eqToHom iA ≫ (f ≫ eB.hom) ≫ eqToHom jB := by
      simp only [Category.assoc]
    _ = eqToHom iA ≫ (eA.hom ≫ f') ≫ eqToHom jB := by rw [h]
    _ = eqToHom iA ≫ eA.hom ≫ (f' ≫ eqToHom jB) := by
      simp only [Category.assoc]
    _ = _ := by rw [hout]; simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem infinityGradedTransportComm
    {A B A' B' : (ℤ × ℤ) → ModuleCat.{0} ℤ}
    {F : Filtration A} {G : Filtration B} {F' : Filtration A'} {G' : Filtration B'}
    {f : FilteredMorphism F G} {f' : FilteredMorphism F' G'}
    {p q : ℤ × ℤ} (e : FilteredMapTransport f f' p q) (s : ℤ) :
    f.inducedGrMap s p ≫ (e.target.gradedIso s).hom =
      (e.source.gradedIso s).hom ≫ f'.inducedGrMap s q := by
  have level_comm : (f.compat s p).choose ≫ (e.target.level s).hom =
      (e.source.level s).hom ≫ (f'.compat s q).choose := by
    apply (cancel_mono (G'.F s q).arrow).mp
    simp only [Category.assoc]
    rw [e.target.level_arrow, (f'.compat s q).choose_spec]
    rw [← Category.assoc, (f.compat s p).choose_spec, Category.assoc,
      ← e.map_comm]
    simpa only [Category.assoc] using congrArg (fun a => a ≫ f'.map q)
      (e.source.level_arrow s).symm
  haveI : Epi (F.toAssociatedGraded s p) := inferInstanceAs (Epi (cokernel.π _))
  apply (cancel_epi (F.toAssociatedGraded s p)).mp
  rw [← Category.assoc, f.quotient_naturality, Category.assoc,
    e.target.projection_comm, ← Category.assoc, level_comm]
  rw [Category.assoc, ← f'.quotient_naturality, ← Category.assoc,
    ← e.source.projection_comm]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem infinityTowerGradedNatural
    {Syn : Type 1} [SyntheticCategory.{1,0} Syn]
    [HasFunctorialCofiber (C := Syn)]
    {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
    {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
    (cx : SyntheticTowerConvergence P X) (cy : SyntheticTowerConvergence P Y)
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s : ℤ) :
    (F.map g).eInftyMap (s,p.1+s,p.2) ≫ (towerGradedIso cy p s).hom =
      (towerGradedIso cx p s).hom ≫ M.filteredMap.inducedGrMap s p := by
  let i : Tridegree := (s,p.1+s,p.2)
  let q : ℤ × ℤ := (p.1+s-s,p.2)
  have hp : q=p := Prod.ext (add_sub_cancel_right p.1 s) rfl
  have h := (M.infinity_action_graded i).symm
  change (F.map g).eInftyMap i ≫
      ((cy.identification i).hom ≫
        eqToHom (congrArg (fun q => cy.filtration.associatedGraded s q) hp)) =
    ((cx.identification i).hom ≫
        eqToHom (congrArg (fun q => cx.filtration.associatedGraded s q) hp)) ≫
      M.filteredMap.inducedGrMap s p
  rw [← Category.assoc, h, Category.assoc,
    infinityMapReindex (fun q => M.filteredMap.inducedGrMap s q) hp]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem infinityTowerNatural
    {C : Type 1} [StableHomotopyCategory.{1,0} C]
    [HasFunctorialCofiber (C := C)]
    {Syn : Type 1} [SyntheticCategory.{1,0} Syn]
    [HasFunctorialCofiber (C := Syn)]
    (D : AdamsSyntheticBackground C Syn) (δ : ℤ × ℤ) (S : SyntheticESSShiftComparison D δ)
    (X Y : SyntheticObject)
    (f : X.obj D.nu D.auxiliary ⟶ Y.obj D.nu D.auxiliary)
    (p : ℤ × ℤ) (s : ℤ) :
    (D.family.map f).eInftyMap (s,p.1+s,p.2) ≫
        (towerInfinityIso (D.convergence Y) (D.convergence (.shift δ Y))
          (S.filtered Y p) s).hom =
      (towerInfinityIso (D.convergence X) (D.convergence (.shift δ X))
          (S.filtered X p) s).hom ≫
        (D.family.map ((SyntheticCategory.biShift δ).map f)).eInftyMap
          (s,(p+δ).1+s,(p+δ).2) := by
  let M := D.convergentMap X Y f
  let M' := D.convergentMap (.shift δ X) (.shift δ Y)
    ((SyntheticCategory.biShift δ).map f)
  have h := infinityGradedTransportComm (S.transport X Y f p) s
  change M.filteredMap.inducedGrMap s p ≫ ((S.filtered Y p).gradedIso s).hom =
    ((S.filtered X p).gradedIso s).hom ≫ M'.filteredMap.inducedGrMap s (p+δ) at h
  have hM' : M'.filteredMap.inducedGrMap s (p+δ) =
      (towerGradedIso (D.convergence (.shift δ X)) (p+δ) s).inv ≫
        (D.family.map ((SyntheticCategory.biShift δ).map f)).eInftyMap
          (s,(p+δ).1+s,(p+δ).2) ≫
        (towerGradedIso (D.convergence (.shift δ Y)) (p+δ) s).hom := by
    calc
      _ = (towerGradedIso (D.convergence (.shift δ X)) (p+δ) s).inv ≫
          ((towerGradedIso (D.convergence (.shift δ X)) (p+δ) s).hom ≫
            M'.filteredMap.inducedGrMap s (p+δ)) := by
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = _ := by
        rw [← infinityTowerGradedNatural (D.convergence (.shift δ X))
          (D.convergence (.shift δ Y)) M' (p+δ) s]
  apply (cancel_mono (towerGradedIso (D.convergence (.shift δ Y)) (p+δ) s).hom).mp
  simp only [towerInfinityIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, infinityTowerGradedNatural (D.convergence X) (D.convergence Y) M]
  rw [Category.assoc, h, hM']

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem infinityShiftNatural
    {C : Type 1} [StableHomotopyCategory.{1,0} C]
    [HasFunctorialCofiber (C := C)]
    {Syn : Type 1} [SyntheticCategory.{1,0} Syn]
    [HasFunctorialCofiber (C := Syn)]
    (D : AdamsSyntheticBackground C Syn) (K : ∀ k : ℕ, SyntheticESSShiftComparison D (0,-(k:ℤ)))
    (X Y : SyntheticObject) (f : X.obj D.nu D.auxiliary ⟶ Y.obj D.nu D.auxiliary)
    (k : ℕ) (p : ℤ × ℤ) (w : ℤ) :
    (D.family.map f).eInftyMap (p.1,p.2,w) ≫ (infinityShift D K Y k p w).hom =
      (infinityShift D K X k p w).hom ≫
        (D.family.map ((SyntheticCategory.biShift (0,-(k:ℤ))).map f)).eInftyMap
          (p.1,p.2,w-k) := by
  let a : Tridegree := (p.1,p.2,w)
  let b : Tridegree := (p.1,(p.2-p.1)+p.1,w)
  let c : Tridegree :=
    (p.1,((p.2-p.1,w)+(0,-(k:ℤ))).1+p.1,((p.2-p.1,w)+(0,-(k:ℤ))).2)
  let d : Tridegree := (p.1,p.2,w-k)
  have hab : a=b := Prod.ext rfl (Prod.ext (sub_add_cancel p.2 p.1).symm rfl)
  have hcd : c=d := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · change (p.2-p.1)+0+p.1=p.2
        omega
      · change w+(-(k:ℤ))=w-k
        omega
  have hin := infinityMapReindex (fun i => (D.family.map f).eInftyMap i) hab
  have hout := infinityMapReindex
    (fun i => (D.family.map ((SyntheticCategory.biShift (0,-(k:ℤ))).map f)).eInftyMap i) hcd
  have h := infinityTowerNatural D (0,-(k:ℤ)) (K k) X Y f (p.2-p.1,w) p.1
  change (D.family.map f).eInftyMap a ≫
      (eqToHom (congrArg (fun i =>
          ((D.family.obj (Y.obj D.nu D.auxiliary)).sequence.ssData i).eInfty) hab) ≫
        (towerInfinityIso (D.convergence Y) (D.convergence (.shift (0,-(k:ℤ)) Y))
          ((K k).filtered Y (p.2-p.1,w)) p.1).hom ≫
        eqToHom (congrArg (fun i =>
          ((D.family.obj ((SyntheticObject.shift (0,-(k:ℤ)) Y).obj D.nu D.auxiliary)).sequence.ssData i).eInfty) hcd)) =
    (eqToHom (congrArg (fun i =>
          ((D.family.obj (X.obj D.nu D.auxiliary)).sequence.ssData i).eInfty) hab) ≫
        (towerInfinityIso (D.convergence X) (D.convergence (.shift (0,-(k:ℤ)) X))
          ((K k).filtered X (p.2-p.1,w)) p.1).hom ≫
        eqToHom (congrArg (fun i =>
          ((D.family.obj ((SyntheticObject.shift (0,-(k:ℤ)) X).obj D.nu D.auxiliary)).sequence.ssData i).eInfty) hcd)) ≫
      (D.family.map ((SyntheticCategory.biShift (0,-(k:ℤ))).map f)).eInftyMap d
  exact infinityTransportedSquare _ _ _ _ _ _ _ _ _ _ h hin hout


public theorem infinityShift_natural :
  ∀ (X Y : SyntheticObject) (f : X.obj background.nu background.auxiliary ⟶ Y.obj background.nu background.auxiliary)
    (k : ℕ) (p : Bidegree) (w : ℤ),
    (background.family.map f).eInftyMap (p.1,p.2,w) ≫ (infinityShift background infinityShift_comparison Y k p w).hom =
      (infinityShift background infinityShift_comparison X k p w).hom ≫
        (background.family.map ((SyntheticCategory.biShift (0,-(k:ℤ))).map f)).eInftyMap (p.1,p.2,w-k) := by
  exact infinityShiftNatural background infinityShift_comparison

public def infinityShiftData : InfinityShiftCoordinates background where
  comparison := infinityShift_comparison
  natural := infinityShift_natural

public def infinityLambda := InfinityShiftCoordinates.lambdaMap background infinityShiftData

public def infinityFiniteLambda := InfinityShiftCoordinates.finiteLambdaMap background infinityShiftData

public def infinityWeightMap := InfinityShiftCoordinates.weightMap background infinityShiftData

private abbrev NuInfinityEquivalences :=
  ∀ (X : AdamsObject) (p : Bidegree) (w : ℤ),
    ((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty ≃+
      nuEInftyModel background X p w

private def nuWindowFromEquivalences (e : NuInfinityEquivalences)
    (X : AdamsObject) (p : Bidegree) (w : ℤ) (hw : w ≤ p.2) :
    ((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty ≃+
      PermanentQuotient background X (1+p.2-w) p :=
  (e X p w).trans (by unfold nuEInftyModel; rw [if_pos hw])

/-- The ν presentation is calibrated on its actual common infinite-cycle
representatives. This selects the equivalence and its label law together. -/
private structure NuInfinityConstruction where
  equivalences : NuInfinityEquivalences
  labels : ∀ (X : AdamsObject) (s t w : ℤ) (hw : w ≤ t)
      (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
      (z : ((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (s,t,w)).eInfty),
    HasInfinityRepresentative _ 2 (s,t,w) (nuWeightLabel background X s t w hw x) z ↔
      ∃ hx : x ∈ permanentCycles background X (s,t),
        nuWindowFromEquivalences equivalences X (s,t) w hw z =
          subquotientClass (permanentCycles background X (s,t))
            (boundaries background X (1+t-w) (s,t)) ⟨x,hx⟩

private def nuInfinityConstruction : NuInfinityConstruction := by
  sorry

private abbrev FiniteInfinityEquivalences :=
  ∀ (X : AdamsObject) (q : ℕ) (_hq : 0 < q) (p : Bidegree) (w : ℤ),
    ((background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) q).sequence.ssData (p.1,p.2,w)).eInfty ≃+
      finiteEInftyModel background X q p w

private def finiteWindowFromEquivalences (e : FiniteInfinityEquivalences)
    (X : AdamsObject) (q : ℕ) (hq : 0 < q) (p : Bidegree) (w : ℤ)
    (hw : 0 ≤ p.2-w ∧ p.2-w < q) :
    ((background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) q).sequence.ssData (p.1,p.2,w)).eInfty ≃+
      CycleQuotient background X (q-p.2+w) (1+p.2-w) p :=
  (e X q hq p w).trans (by unfold finiteEInftyModel; rw [if_pos hw])

/-- The finite presentation, its labels and the actual finite λ map use
one family of equivalences for every positive quotient length. -/
private structure FiniteInfinityConstruction where
  equivalences : FiniteInfinityEquivalences
  labels : ∀ (X : AdamsObject) (q : ℕ) (hq : 0 < q)
      (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w < q)
      (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
      (z : ((background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) q).sequence.ssData (s,t,w)).eInfty),
    HasInfinityRepresentative _ 2 (s,t,w)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,w)
        (nuWeightLabel background X s t w (sub_nonneg.mp hw.1) x)) z ↔
      ∃ hx : x ∈ cycles background X (q-t+w) (s,t),
        finiteWindowFromEquivalences equivalences X q hq (s,t) w hw z =
          subquotientClass (cycles background X (q-t+w) (s,t))
            (boundaries background X (1+t-w) (s,t)) ⟨x,hx⟩
  lambda_finite : ∀ (X : AdamsObject) (q k : ℕ) (hkq : k < q)
      (p : Bidegree) (w : ℤ) (hw : 0 ≤ p.2-w ∧ p.2-w < (q-k : ℕ))
      (hq : 0 < q)
      (hwindow : 0 ≤ p.2-(w-k) ∧ p.2-(w-k) < q)
      (hcycles : (q : ℤ)-p.2+(w-k) ≤ (q-k : ℕ)-p.2+w)
      (hboundaries : 1+p.2-w ≤ 1+p.2-(w-k))
      (hqsub : 0 < q-k)
      (x : ((background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)).sequence.ssData (p.1,p.2,w)).eInfty),
    finiteWindowFromEquivalences equivalences X q hq p (w-k) hwindow (infinityFiniteLambda X q k hkq p w x) =
      quotientMap background X hcycles hboundaries p
        (finiteWindowFromEquivalences equivalences X (q-k) hqsub p w hw x)

private def finiteInfinityConstruction : FiniteInfinityConstruction := by
  sorry

/-- The ν equivalence from the calibrated common-representative construction. -/
public def eInfinity_nu :
  ∀ (X : AdamsObject) (p : Bidegree) (w : ℤ),
    ((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty ≃+
      nuEInftyModel background X p w :=
  nuInfinityConstruction.equivalences

/-- The finite equivalences from one label- and λ-compatible construction. -/
public def eInfinity_finite :
  ∀ (X : AdamsObject) (q : ℕ) (_hq : 0 < q) (p : Bidegree) (w : ℤ),
    ((background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) q).sequence.ssData (p.1,p.2,w)).eInfty ≃+
      finiteEInftyModel background X q p w :=
  finiteInfinityConstruction.equivalences

public def infinityPresentationData : EInfinityPresentation background where
  nu := eInfinity_nu
  finite := eInfinity_finite

public def infinityNuWindow := EInfinityPresentation.nuWindow background infinityPresentationData

public def infinityFiniteWindow := EInfinityPresentation.finiteWindow background infinityPresentationData

public def infinityNuLinear := EInfinityPresentation.nuLinear background infinityPresentationData

public def infinityFiniteLinear := EInfinityPresentation.finiteLinear background infinityPresentationData


public theorem eInfinity_nu_labels :
  ∀ (X : AdamsObject) (s t w : ℤ) (hw : w ≤ t)
      (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
      (z : ((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (s,t,w)).eInfty),
    HasInfinityRepresentative _ 2 (s,t,w) (nuWeightLabel background X s t w hw x) z ↔
      ∃ hx : x ∈ permanentCycles background X (s,t),
        infinityNuWindow X (s,t) w hw z = subquotientClass (permanentCycles background X (s,t)) (boundaries background X (1+t-w) (s,t)) ⟨x,hx⟩ := by
  exact nuInfinityConstruction.labels

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
private theorem lambdaNuWeightMap_eq
    (X : KIP126.Kervaire.Route.AdamsObject) (k : ℕ) (s t w : ℤ)
    (hk : k ≠ 0) (hw : w ≤ t) :
    KIP126.AdamsSynthetic.Completed.weight_map X s t (w-k) w (by omega) hw =
      infinityLambda (.nu X) k (s,t) w := by
  have hnat : (w-(w-(k:ℤ))).toNat = k := by omega
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let δ (j : ℕ) : ℤ × ℤ := (0,-(j:ℤ))
  let p : ℤ × ℤ := (t-s,w)
  let φ (j : ℕ) (hj : w-(j:ℤ) = w-(k:ℤ)) :
      ((background.family.obj A).sequence.ssData (s,t,w)).eInfty ⟶
        ((background.family.obj A).sequence.ssData (s,t,w-k)).eInfty :=
    (eqToIso (congrArg (fun q => ((background.family.obj A).sequence.ssData q).eInfty)
        (show (s,t,w) = (s,p.1+s,p.2) by dsimp only [p]; ext <;> simp (config := { congrConsts := false }))) ≪≫
      towerInfinityIso (background.convergence (.nu X))
        (background.convergence (.shift (δ j) (.nu X)))
        (KIP126.AdamsSynthetic.Completed.shift_filtered (δ j) (.nu X) p) s ≪≫
      eqToIso (congrArg (fun q =>
        ((background.family.obj ((SyntheticCategory.biShift (δ j)).obj A)).sequence.ssData q).eInfty)
        (show (s,(p+δ j).1+s,(p+δ j).2) = (s,t,w-k) by
          dsimp only [p, δ, Prod.fst_add, Prod.snd_add]
          ext <;> simp (config := { congrConsts := false }) only [add_zero, sub_add_cancel]
          omega))).hom ≫
      (background.family.map (lambdaPow j A)).eInftyMap (s,t,w-k)
  have hφ : ∀ (j : ℕ) (hjk : j=k) (hj : w-(j:ℤ) = w-(k:ℤ)),
      φ j hj = φ k rfl := by
    intro j hjk hj
    subst j
    rfl
  have hlambda : infinityLambda (.nu X) k (s,t) w = φ k rfl := by
    exact dif_neg hk
  exact (hφ (w-(w-(k:ℤ))).toNat hnat (by omega)).trans hlambda.symm


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- The same permanent E₂ representative is preserved by the actual λ weight map. -/
public theorem eInfinity_lambda_nu :
  ∀ (X : AdamsObject) (k : ℕ) (p : Bidegree) (w : ℤ) (hw : w ≤ p.2)
      (x : ((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty),
    infinityNuWindow X p (w-k) (by omega) (infinityLambda (.nu X) k p w x) =
      permanentQuotientMap background X (by omega) p (infinityNuWindow X p w hw x) := by
  intro X k p w hw z
  rcases p with ⟨s,t⟩
  by_cases hk : k = 0
  · subst k
    dsimp only [infinityLambda, InfinityShiftCoordinates.lambdaMap]
    simp (config := { congrConsts := false }) only [dite_true]
    have htransport : ∀ (v : ℤ) (h : w = v) (hv : v ≤ t)
        (he : ((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (s,t,w)).eInfty =
          ((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (s,t,v)).eInfty),
        HEq (infinityNuWindow X (s,t) v hv ((eqToHom he) z))
          (infinityNuWindow X (s,t) w hw z) := by
      intro v h hv he
      subst v
      rfl
    have hquot : ∀ (v : ℤ) (h : v = w) (hb : 1+t-w ≤ 1+t-v),
        HEq (permanentQuotientMap background X hb (s,t) (infinityNuWindow X (s,t) w hw z))
          (infinityNuWindow X (s,t) w hw z) := by
      intro v h hb
      subst v
      obtain ⟨a, ha⟩ := Quotient.mk_surjective (infinityNuWindow X (s,t) w hw z)
      rw [← ha]
      rfl
    apply eq_of_heq
    exact (htransport (w-((0:ℕ):ℤ)) (by omega) (by omega) _).trans
      (hquot (w-((0:ℕ):ℤ)) (by omega) _).symm
  · obtain ⟨a, ha⟩ := Quotient.mk_surjective (infinityNuWindow X (s,t) w hw z)
    have hrep := (eInfinity_nu_labels X s t w hw a.val z).mpr ⟨a.property, ha.symm⟩
    have hrep' := KIP126.AdamsSynthetic.Completed.weight_representative
      X s t (w-k) w (by omega) hw a.val z hrep
    rw [lambdaNuWeightMap_eq X k s t w hk hw] at hrep'
    obtain ⟨hperm, hleft⟩ :=
      (eInfinity_nu_labels X s t (w-k) (by omega) a.val _).mp hrep'
    calc
      _ = subquotientClass (permanentCycles background X (s,t))
            (boundaries background X (1+t-(w-k)) (s,t)) ⟨a.val,hperm⟩ := hleft
      _ = permanentQuotientMap background X (by omega) (s,t)
            (subquotientClass (permanentCycles background X (s,t))
              (boundaries background X (1+t-w) (s,t)) a) := rfl
      _ = _ := congrArg (permanentQuotientMap background X (by omega) (s,t)) ha


public theorem eInfinity_lambda_finite :
  ∀ (X : AdamsObject) (q k : ℕ) (hkq : k < q)
      (p : Bidegree) (w : ℤ) (hw : 0 ≤ p.2-w ∧ p.2-w < (q-k : ℕ))
      (x : ((background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)).sequence.ssData (p.1,p.2,w)).eInfty),
    infinityFiniteWindow X q (by omega) p (w-k) (by constructor <;> omega)
        (infinityFiniteLambda X q k hkq p w x) =
      quotientMap background X (by omega) (by omega) p
        (infinityFiniteWindow X (q-k) (by omega) p w hw x) := by
  intro X q k hkq p w hw x
  exact finiteInfinityConstruction.lambda_finite X q k hkq p w hw
    (by omega) (by constructor <;> omega) (by omega) (by omega) (by omega) x


public theorem eInfinity_finite_labels :
  ∀ (X : AdamsObject) (q : ℕ) (hq : 0 < q)
      (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w < q)
      (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
      (z : ((background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) q).sequence.ssData (s,t,w)).eInfty),
    HasInfinityRepresentative _ 2 (s,t,w)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,w)
        (nuWeightLabel background X s t w (by omega) x)) z ↔
      ∃ hx : x ∈ cycles background X (q-t+w) (s,t),
        infinityFiniteWindow X q hq (s,t) w hw z = subquotientClass (cycles background X (q-t+w) (s,t)) (boundaries background X (1+t-w) (s,t)) ⟨x,hx⟩ := by
  exact finiteInfinityConstruction.labels

private theorem rhoNuLabelSurjective (X : AdamsObject) (s t w : ℤ) (hw : w ≤ t) :
    Function.Surjective (nuWeightLabel background X s t w hw) := by
  intro a
  let F := free_component X 2 (by omega) s t w (by omega)
  refine ⟨F.hom a, ?_⟩
  apply (ModuleCat.mono_iff_injective F.hom).mp inferInstance
  exact free_e2 X s t w hw (F.hom a)

private theorem rhoInfinityRepresentativeExists (A : SyntheticAdamsSS.{0})
    (i : Tridegree) (e : (A.sequence.ssData i).eInfty) :
    ∃ x : A.Page 2 i, HasInfinityRepresentative A 2 i x e := by
  let D := A.sequence.ssData i
  haveI : Epi (D.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (D.pageπ ⊤)).mp inferInstance e
  exact ⟨(Subobject.ofLE _ _ (D.Z_anti le_top) ≫
    D.pageπ (↑(2-A.sequence.r₀).toNat : WithTop ℕ)) z, by omega, z, rfl, hz⟩

-- The actual SSData morphism sends one common infinite cycle to another.

private theorem rhoInfinityRepresentativeMorphism
    {E E' : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Tridegree}
    (f : E ⟶ E') (i : Tridegree) {x : E.Page 2 i} {e : (E.ssData i).eInfty}
    (h : ∃ z : (Subobject.underlying.obj ((E.ssData i).Z ⊤) : ModuleCat ℤ),
      (Subobject.ofLE _ _ ((E.ssData i).Z_anti le_top) ≫
        (E.ssData i).pageπ (↑(2-E.r₀).toNat : WithTop ℕ)) z = x ∧
      (E.ssData i).pageπ ⊤ z = e) :
    ∃ z : (Subobject.underlying.obj ((E'.ssData i).Z ⊤) : ModuleCat ℤ),
      (Subobject.ofLE _ _ ((E'.ssData i).Z_anti le_top) ≫
        (E'.ssData i).pageπ (↑(2-E'.r₀).toNat : WithTop ℕ)) z = f.pageMap 2 i x ∧
      (E'.ssData i).pageπ ⊤ z = f.eInftyMap i e := by
  have hstart := f.r₀_eq
  rcases E with ⟨⟨r₀,D,δ,d⟩,dd,Zs,Bs⟩
  rcases E' with ⟨⟨r₀',D',δ',d'⟩,dd',Zs',Bs'⟩
  dsimp at hstart
  subst r₀'
  obtain ⟨z,hz,he⟩ := h
  let n : WithTop ℕ := ↑(2-r₀).toNat
  refine ⟨f.toSSDataMorphism.cycleMap i ⊤ z, ?_, ?_⟩
  · have hs := f.toSSDataMorphism.cycleMap_ofLE_assoc i
      (r := n) (s := ⊤) le_top ((D' i).pageπ n)
    have hp := f.toSSDataMorphism.pageπ_pageMap i n
    have hq : (Subobject.ofLE ((D i).Z ⊤) ((D i).Z n) ((D i).Z_anti le_top) ≫
        (D i).pageπ n) ≫ f.toSSDataMorphism.pageMap i n =
        f.toSSDataMorphism.cycleMap i ⊤ ≫
          Subobject.ofLE ((D' i).Z ⊤) ((D' i).Z n) ((D' i).Z_anti le_top) ≫ (D' i).pageπ n := by
      rw [Category.assoc,hp]
      exact hs
    change ((Subobject.ofLE _ _ _ ≫ (D' i).pageπ n)
      (f.toSSDataMorphism.cycleMap i ⊤ z)) =
      ((f.toSSDataMorphism.pageMap i n ≫ eqToHom _) x)
    simpa only [ModuleCat.comp_apply, hz, eqToHom_refl, Category.comp_id, n]
      using (ConcreteCategory.congr_hom hq z).symm
  · have hp := f.toSSDataMorphism.pageπ_pageMap i ⊤
    change (D' i).pageπ ⊤ (f.toSSDataMorphism.cycleMap i ⊤ z) =
      f.toSSDataMorphism.pageMap i ⊤ e
    simpa only [ModuleCat.comp_apply, he] using
      (ConcreteCategory.congr_hom hp z).symm

private theorem rhoInfinityRepresentativeMap {X Y : SyntheticSpectrum}
    (g : X ⟶ Y) (i : Tridegree) {x : (background.family.obj X).Page 2 i}
    {e : ((background.family.obj X).sequence.ssData i).eInfty}
    (h : HasInfinityRepresentative (background.family.obj X) 2 i x e) :
    HasInfinityRepresentative (background.family.obj Y) 2 i
      (background.family.pageMap g 2 i x) ((background.family.map g).eInftyMap i e) := by
  obtain ⟨hr,z,hz,he⟩ := h
  obtain ⟨z',hz',he'⟩ := rhoInfinityRepresentativeMorphism (background.family.map g) i ⟨z,hz,he⟩
  exact ⟨hr,z',hz',he'⟩

private theorem rhoFiniteLabelSurjective (X : AdamsObject) (q : ℕ) (hq : 0 < q)
    (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w < q) :
    Function.Surjective (fun x =>
      (background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap
        2 (s,t,w) (nuWeightLabel background X s t w (by omega) x)) := by
  haveI := finite_quotient_retained X q hq s t w hw
  exact ((ModuleCat.epi_iff_surjective _).mp inferInstance).comp
    (rhoNuLabelSurjective X s t w (by omega))

private theorem rhoFiniteLabelMap (X : AdamsObject) (i j : ℕ) (hij : i ≤ j)
    (s t w : ℤ) (a : (background.family.nu background.nu (X.obj background.auxiliary)).Page 2 (s,t,w)) :
    background.family.pageMap
        ((background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho i j hij)
        2 (s,t,w)
        ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) j).pageMap
          2 (s,t,w) a) =
      (background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) i).pageMap
        2 (s,t,w) a := by
  let V := background.nu.functor.obj (X.obj background.auxiliary)
  let rho := (background.quotients.tower V).rho i j hij
  change (((background.family.map (XModLambdaN.incl V j)).pageMap 2 (s,t,w)) ≫
    (background.family.map rho).pageMap 2 (s,t,w)) a = _
  rw [← SpectralSequenceMorphism.pageMap_comp, ← background.family.map_comp,
    (background.quotients.tower V).rho_quotient hij]
  rfl

/-- Restriction preserves the common infinite representative and its quotient class. -/
public theorem eInfinity_rho_finite :
  ∀ (X : AdamsObject) (i j : ℕ) (hi : 0 < i) (hij : i ≤ j)
      (p : Bidegree) (w : ℤ) (hw : 0 ≤ p.2-w ∧ p.2-w < i)
      (x : ((background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) j).sequence.ssData (p.1,p.2,w)).eInfty),
    infinityFiniteWindow X i hi p w hw
        ((background.family.map ((background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho i j hij)).eInftyMap (p.1,p.2,w) x) =
      quotientMap background X (by omega) le_rfl p
        (infinityFiniteWindow X j (by omega) p w (by constructor <;> omega) x) := by
  intro X i j hi hij p w hw z
  rcases p with ⟨s,t⟩
  have hj : 0 < j := by omega
  have hwj : 0 ≤ t-w ∧ t-w < j := by constructor <;> omega
  obtain ⟨a,ha⟩ := rhoInfinityRepresentativeExists
    (background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) j) (s,t,w) z
  obtain ⟨x,hx⟩ := rhoFiniteLabelSurjective X j hj s t w hwj a
  rw [← hx] at ha
  obtain ⟨hxj,hfinitej⟩ := (eInfinity_finite_labels X j hj s t w hwj x z).mp ha
  have hmap := rhoInfinityRepresentativeMap
    ((background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho i j hij) (s,t,w) ha
  have hmap' : HasInfinityRepresentative
      (background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) i) 2 (s,t,w)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) i).pageMap
        2 (s,t,w) (nuWeightLabel background X s t w (by omega) x))
      ((background.family.map
        ((background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho i j hij)).eInftyMap
        (s,t,w) z) := by
    have heq := rhoFiniteLabelMap X i j hij s t w (nuWeightLabel background X s t w (by omega) x)
    exact Eq.mp (congrArg (fun a => HasInfinityRepresentative
      (background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) i) 2 (s,t,w) a
      ((background.family.map
        ((background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho i j hij)).eInftyMap
        (s,t,w) z)) heq) hmap
  obtain ⟨hxi,hfinitei⟩ := (eInfinity_finite_labels X i hi s t w hw x _).mp hmap'
  calc
    _ = subquotientClass (KIP126.Literature.cycles background X (i-t+w) (s,t))
        (KIP126.Literature.boundaries background X (1+t-w) (s,t)) ⟨x,hxi⟩ := hfinitei
    _ = KIP126.Literature.quotientMap background X (by omega) le_rfl (s,t)
        (subquotientClass (KIP126.Literature.cycles background X (j-t+w) (s,t))
          (KIP126.Literature.boundaries background X (1+t-w) (s,t)) ⟨x,hxj⟩) := rfl
    _ = _ := congrArg (KIP126.Literature.quotientMap background X (by omega) le_rfl (s,t)) hfinitej.symm

/-- Projection from nu preserves the common infinite representative and its quotient class. -/
public theorem eInfinity_rho_nu :
  ∀ (X : AdamsObject) (q : ℕ) (hq : 0 < q)
      (p : Bidegree) (w : ℤ) (hw : 0 ≤ p.2-w ∧ p.2-w < q)
      (x : ((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty),
    infinityFiniteWindow X q hq p w hw
        ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).eInftyMap (p.1,p.2,w) x) =
      permanentToFinite background X (q-p.2+w) (1+p.2-w) p
        (infinityNuWindow X p w (by omega) x) := by
  intro X q hq p w hw z
  rcases p with ⟨s,t⟩
  obtain ⟨a,ha⟩ := rhoInfinityRepresentativeExists (background.family.nu background.nu (X.obj background.auxiliary)) (s,t,w) z
  obtain ⟨x,hx⟩ := rhoNuLabelSurjective X s t w (by omega) a
  rw [← hx] at ha
  obtain ⟨hxperm,hnu⟩ := (eInfinity_nu_labels X s t w (by omega) x z).mp ha
  have hmap := rhoInfinityRepresentativeMap
    (XModLambdaN.incl (background.nu.functor.obj (X.obj background.auxiliary)) q) (s,t,w) ha
  obtain ⟨hxcycle,hfinite⟩ := (eInfinity_finite_labels X q hq s t w hw x _).mp hmap
  calc
    _ = subquotientClass (KIP126.Literature.cycles background X (q-t+w) (s,t))
        (KIP126.Literature.boundaries background X (1+t-w) (s,t)) ⟨x,hxcycle⟩ := hfinite
    _ = permanentToFinite background X (q-t+w) (1+t-w) (s,t)
        (subquotientClass (KIP126.Literature.permanentCycles background X (s,t))
          (KIP126.Literature.boundaries background X (1+t-w) (s,t)) ⟨x,hxperm⟩) := rfl
    _ = _ := congrArg (permanentToFinite background X (q-t+w) (1+t-w) (s,t)) hnu.symm

private def infinityCompatibilityData : EInfinityCompatibility background infinityPresentationData infinityShiftData where
  lambda_nu := eInfinity_lambda_nu
  lambda_finite := eInfinity_lambda_finite
  rho_finite := eInfinity_rho_finite
  rho_nu := eInfinity_rho_nu
  nu_labels := eInfinity_nu_labels
  finite_labels := eInfinity_finite_labels

public abbrev infinityLambda_zero := InfinityShiftCoordinates.lambdaMap_zero background infinityShiftData

public abbrev infinityFiniteLambda_zero := InfinityShiftCoordinates.finiteLambdaMap_zero background infinityShiftData


public theorem infinityLambda_epi :
  ∀ (X : AdamsObject) (k : ℕ) (p : Bidegree) (w : ℤ), w ≤ p.2 →
    Epi (infinityLambda (.nu X) k p w) := EInfinityCompatibility.lambda_epi background infinityCompatibilityData


public theorem infinityWeightMap_epi :
  ∀ (X : AdamsObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂), w₂ ≤ t →
    Epi (infinityWeightMap X s t w₁ w₂ hw) := EInfinityCompatibility.weight_epi background infinityCompatibilityData

set_option backward.isDefEq.respectTransparency false in
private theorem lambdaRegradedWindowClass
    (X : AdamsObject) (s t w₁ w₂ : ℤ) (k : ℕ)
    (h : w₂-k = w₁)
    (transport :
      ((background.family.obj ((SyntheticObject.nu X).obj background.nu background.auxiliary)).sequence.ssData
        (s,t,w₂-k)).eInfty =
      ((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (s,t,w₁)).eInfty)
    (ht : w₂ ≤ t) (x : KIP126.Literature.permanentCycles background X (s,t))
    (z : ((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (s,t,w₂)).eInfty)
    (hz : infinityNuWindow X (s,t) w₂ ht z =
      subquotientClass (KIP126.Literature.permanentCycles background X (s,t))
        (KIP126.Literature.boundaries background X (1+t-w₂) (s,t)) x) :
    infinityNuWindow X (s,t) w₁ (by omega)
      ((InfinityShiftCoordinates.lambdaMap background infinityShiftData (.nu X) k (s,t) w₂ ≫
        eqToHom transport) z) =
      subquotientClass (KIP126.Literature.permanentCycles background X (s,t))
        (KIP126.Literature.boundaries background X (1+t-w₁) (s,t)) x := by
  subst w₁
  let f := InfinityShiftCoordinates.lambdaMap background infinityShiftData (.nu X) k (s,t) w₂
  have hcast : eqToHom transport =
      𝟙 (((background.family.obj ((SyntheticObject.nu X).obj background.nu background.auxiliary)).sequence.ssData
        ((s,t).1,(s,t).2,w₂-k)).eInfty) := by
    rfl
  have hmap : f ≫ eqToHom transport = f :=
    (congrArg (fun q => f ≫ q) hcast).trans (Category.comp_id f)
  calc
    _ = infinityNuWindow X (s,t) (w₂-k) (by omega)
        (infinityLambda (.nu X) k (s,t) w₂ z) :=
      congrArg (fun (g :
        ((background.family.obj ((SyntheticObject.nu X).obj background.nu background.auxiliary)).sequence.ssData
          ((s,t).1,(s,t).2,w₂)).eInfty ⟶
        ((background.family.obj ((SyntheticObject.nu X).obj background.nu background.auxiliary)).sequence.ssData
          ((s,t).1,(s,t).2,w₂-k)).eInfty) =>
        infinityNuWindow X (s,t) (w₂-k) (by omega) (g z)) hmap
    _ = permanentQuotientMap background X (by omega) (s,t)
        (infinityNuWindow X (s,t) w₂ ht z) :=
      eInfinity_lambda_nu X k (s,t) w₂ ht z
    _ = permanentQuotientMap background X (by omega) (s,t)
        (subquotientClass (KIP126.Literature.permanentCycles background X (s,t))
          (KIP126.Literature.boundaries background X (1+t-w₂) (s,t)) x) :=
      congrArg (permanentQuotientMap background X (by omega) (s,t)) hz
    _ = _ := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem weightWindowClass
    (X : AdamsObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t)
    (x : KIP126.Literature.permanentCycles background X (s,t))
    (z : ((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (s,t,w₂)).eInfty)
    (hz : infinityNuWindow X (s,t) w₂ ht z =
      subquotientClass (KIP126.Literature.permanentCycles background X (s,t))
        (KIP126.Literature.boundaries background X (1+t-w₂) (s,t)) x) :
    infinityNuWindow X (s,t) w₁ (hw.trans ht)
      (infinityWeightMap X s t w₁ w₂ hw z) =
      subquotientClass (KIP126.Literature.permanentCycles background X (s,t))
        (KIP126.Literature.boundaries background X (1+t-w₁) (s,t)) x := by
  unfold infinityWeightMap InfinityShiftCoordinates.weightMap
  exact lambdaRegradedWindowClass X s t w₁ w₂ (w₂-w₁).toNat (by omega) _ ht x z hz

set_option backward.isDefEq.respectTransparency false in
private theorem weightsLambdaImpl :
  ∀ (X : AdamsObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t),
    KIP126.AdamsSynthetic.Completed.weight_map X s t w₁ w₂ hw ht =
      infinityWeightMap X s t w₁ w₂ hw := by
  intro X s t w₁ w₂ hw ht
  ext z
  obtain ⟨x, hx⟩ := Quotient.mk_surjective (infinityNuWindow X (s,t) w₂ ht z)
  have hz : infinityNuWindow X (s,t) w₂ ht z =
      subquotientClass (KIP126.Literature.permanentCycles background X (s,t))
        (KIP126.Literature.boundaries background X (1+t-w₂) (s,t)) x := hx.symm
  have hrep := (eInfinity_nu_labels X s t w₂ ht x.val z).mpr ⟨x.property, hz⟩
  have hweight := KIP126.AdamsSynthetic.Completed.weight_representative
    X s t w₁ w₂ hw ht x.val z hrep
  obtain ⟨hpermanent, hleft⟩ :=
    (eInfinity_nu_labels X s t w₁ (hw.trans ht) x.val _).mp hweight
  apply (infinityNuWindow X (s,t) w₁ (hw.trans ht)).injective
  exact hleft.trans (weightWindowClass X s t w₁ w₂ hw ht x z hz).symm

/-- The specified weight operation equals the actual lambda weight map:
both send the same permanent E₂ representative to its larger boundary quotient. -/
public theorem weights_lambda :
  ∀ (X : AdamsObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t),
    KIP126.AdamsSynthetic.Completed.weight_map X s t w₁ w₂ hw ht =
      infinityWeightMap X s t w₁ w₂ hw := weightsLambdaImpl


public theorem weight_epi :
  ∀ (X : AdamsObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t),
    Epi (KIP126.AdamsSynthetic.Completed.weight_map X s t w₁ w₂ hw ht) := by
  intro X s t w₁ w₂ hw ht
  rw [weights_lambda]
  exact infinityWeightMap_epi X s t w₁ w₂ hw ht

end KIP126.Literature.Standard
end
