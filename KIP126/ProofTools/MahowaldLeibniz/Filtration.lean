module

import all KIP126.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingLabels
import all KIP126.ProofTools.ConvergenceOperations
import all KIP126.ProofTools.DetectionOperations
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionClassLabels
import KIP126.ProofTools.MahowaldLeibniz

/-! Finite-window bridges for the Mahowald--Leibniz comparison,
using the maps and filtrations of the fixed model. -/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

private theorem familyPageMap_comp
    (F : SyntheticAdamsFamily SyntheticSpectrum) {X Y Z : SyntheticSpectrum}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    F.pageMap (f ≫ g) r i = F.pageMap f r i ≫ F.pageMap g r i := by
  change (F.map (f ≫ g)).pageMap r i =
    (F.map f).pageMap r i ≫ (F.map g).pageMap r i
  rw [F.map_comp, SpectralSequenceMorphism.pageMap_comp]

private theorem familyPageMapCast
    {U V : SyntheticSpectrum} (g : U ⟶ V) {p q : Tridegree} (h : p = q)
    (x : (background.family.obj U).E₂ p) :
    background.family.pageMap g 2 q
      (Eq.mp (congrArg (fun a : Tridegree => ((background.family.obj U).E₂ a : Type)) h) x) =
      Eq.mp (congrArg (fun a : Tridegree => ((background.family.obj V).E₂ a : Type)) h)
        (background.family.pageMap g 2 p x) := by
  subst q
  rfl

private theorem targetNuLabelNatural
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t : ℤ) (k : ℕ) (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :
    background.family.pageMap (background.nu.functor.map f) 2 (s,t,t-k)
      (targetNuLabel background X s t k x) =
    targetNuLabel background Y s t k ((background.classical.map f).pageMap 2 (s,t) x) := by
  let p : Tridegree := (s,t,t-k)
  let nuf := background.nu.functor.map f
  let x₀ : (background.family.obj ((SyntheticCategory.biShift (0,0)).obj
      (background.nu.functor.obj (X.obj background.auxiliary)))).E₂ p := by
    simpa only [add_zero] using background.comparison.nuE2 X 0 s t k x
  let y₀ : (background.family.obj ((SyntheticCategory.biShift (0,0)).obj
      (background.nu.functor.obj (Y.obj background.auxiliary)))).E₂ p := by
    simpa only [add_zero] using background.comparison.nuE2 Y 0 s t k
      ((background.classical.map f).pageMap 2 (s,t) x)
  have hxy : background.family.pageMap ((SyntheticCategory.biShift (0,0)).map nuf) 2 p x₀ = y₀ := by
    have hdeg : (s,t,t+0-(k : ℤ)) = p := by dsimp [p]; simp only [add_zero]
    have hraw := background.comparison.nu_natural X Y f 0 s t k x
    have hc := familyPageMapCast ((SyntheticCategory.biShift (0,0)).map nuf) hdeg
      (background.comparison.nuE2 X 0 s t k x)
    exact hc.trans (congrArg
      (fun z => Eq.mp (congrArg (fun a : Tridegree =>
        ((background.family.obj ((SyntheticCategory.biShift (0,0)).obj
          (background.nu.functor.obj (Y.obj background.auxiliary)))).E₂ a : Type)) hdeg) z) hraw)
  let zx := SyntheticCategory.biShift_zero.hom.app
    (background.nu.functor.obj (X.obj background.auxiliary))
  let zy := SyntheticCategory.biShift_zero.hom.app
    (background.nu.functor.obj (Y.obj background.auxiliary))
  have hn : (SyntheticCategory.biShift (0,0)).map nuf ≫ zy = zx ≫ nuf :=
    SyntheticCategory.biShift_zero.hom.naturality nuf
  change background.family.pageMap nuf 2 p (background.family.pageMap zx 2 p x₀) =
    background.family.pageMap zy 2 p y₀
  calc
    _ = background.family.pageMap (zx ≫ nuf) 2 p x₀ :=
      (ConcreteCategory.congr_hom (familyPageMap_comp background.family zx nuf 2 p) x₀).symm
    _ = background.family.pageMap ((SyntheticCategory.biShift (0,0)).map nuf ≫ zy) 2 p x₀ :=
      congrArg (fun g => background.family.pageMap g 2 p x₀) hn.symm
    _ = background.family.pageMap zy 2 p
        (background.family.pageMap ((SyntheticCategory.biShift (0,0)).map nuf) 2 p x₀) :=
      ConcreteCategory.congr_hom
        (familyPageMap_comp background.family ((SyntheticCategory.biShift (0,0)).map nuf) zy 2 p) x₀
    _ = _ := congrArg (background.family.pageMap zy 2 p) hxy

private theorem familyPageMapRegrade
    {U V : SyntheticSpectrum} (g : U ⟶ V) {p q : Tridegree} (h : p = q)
    (x : (background.family.obj U).E₂ p) :
    background.family.pageMap g 2 q (regradeE2 h x) =
      regradeE2 h (background.family.pageMap g 2 p x) := by
  subst q
  rfl

private theorem weightLabelNatural
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t w : ℤ) (hw : w ≤ t)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :
    background.family.pageMap (background.nu.functor.map f) 2 (s,t,w)
      (nuWeightLabel background X s t w hw x) =
    nuWeightLabel background Y s t w hw ((background.classical.map f).pageMap 2 (s,t) x) := by
  unfold nuWeightLabel
  rw [familyPageMapRegrade, targetNuLabelNatural]


/-- Vanishing of the classical cycle quotient annihilates the finite
infinity grade. -/
private theorem finite_infinity_zero_of_cycles_le_boundaries
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q) (s t w : ℤ)
    (hw : 0 ≤ t-w ∧ t-w < q)
    (hzero : cycles background X ((q:ℤ)-t+w) (s,t) ≤
      boundaries background X (1+t-w) (s,t)) :
    IsZero (((background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) q).sequence.ssData
      (s,t,w)).eInfty) := by
  have he (e : ((background.family.quotient
      (background.nu.functor.obj (X.obj background.auxiliary)) q).sequence.ssData (s,t,w)).eInfty) : e=0 := by
    obtain ⟨x,hx,_,hz⟩ := CrossingLabels.finite_grade_label X q hq s t w hw e
    exact hz.mp (hzero hx)
  haveI : Subsingleton (((background.family.quotient
      (background.nu.functor.obj (X.obj background.auxiliary)) q).sequence.ssData (s,t,w)).eInfty) :=
    ⟨fun a b => (he a).trans (he b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The middle-layer conditions collapse the actual source filtration
onto its final visible layer.  The layer c is retained throughout. -/
private theorem finite_filtration_collapse_of_middle_conditions
    (X : AdamsObject (coefficients := background.coefficients)) (c K : ℕ) (hK : 2 ≤ K) (S T : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < K-1 →
      cycles background X ((K:ℤ)-j) (S+j,T+j) ≤
        boundaries background X ((c:ℤ)+j+1) (S+j,T+j))
    (a : BiHom (T-S) (T-c)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (c+K))) :
    FiltrationAtLeast background.syntheticTower (S+1) a ↔
      FiltrationAtLeast background.syntheticTower (S+K-1) a := by
  apply filtration_iff_of_infinity_zero (background.convergence (.quotient (c+K) (.nu X)))
    (S+1) (S+K-1) (T-S) (T-c) (by omega)
  intro k hk hk'
  let j := (k-S).toNat
  have hj : (j:ℤ)=k-S := by dsimp [j]; omega
  have hj1 : 1 ≤ j := by omega
  have hjK : j < K-1 := by omega
  have hzero := finite_infinity_zero_of_cycles_le_boundaries X (c+K) (by omega)
    (S+j) (T+j) (T-c) (by omega) (by
      convert hmid j hj1 hjK using 1 <;> congr 1 <;> omega)
  have hks : S+(j:ℤ)=k := by omega
  have hkt : T+(j:ℤ)=T-S+k := by omega
  simpa only [hks,hkt,SyntheticAdamsFamily.quotient,SyntheticObject.obj] using hzero

/-- The terminal subgroup at the end of this finite level window is zero. -/
private theorem finite_composition_tail_zero
    (X : AdamsObject (coefficients := background.coefficients)) (c K : ℕ) (hK : 0 < K) (S T : ℤ)
    (a : BiHom (T-S) (T-c)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (c+K)))
    (ha : FiltrationAtLeast background.syntheticTower (S+K) a) : a=0 := by
  exact finite_high_filtration_zero X (c+K) (by omega) (T-S) (T-c)
    (S+K) (by omega) a ha

/-- Naturality of the finite quotient label under a classical map. -/
private theorem finite_weight_label_natural
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (s t w : ℤ) (hw : w ≤ t)
    (x : Ambient background X (s,t)) :
    familyPageMap background.family (XModLambdaN.map (background.nu.functor.map f) q) 2 (s,t,w)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,w)
        (nuWeightLabel background X s t w hw x)) =
    (background.family.quotientProjection (background.nu.functor.obj (Y.obj background.auxiliary)) q).pageMap 2 (s,t,w)
      (nuWeightLabel background Y s t w hw ((background.classical.map f).pageMap 2 (s,t) x)) := by
  change background.family.pageMap (XModLambdaN.map (background.nu.functor.map f) q) 2 (s,t,w)
    (background.family.pageMap (XModLambdaN.incl _ q) 2 (s,t,w) _) =
    background.family.pageMap (XModLambdaN.incl _ q) 2 (s,t,w) _
  rw [←ModuleCat.comp_apply,←familyPageMap_comp,←XModLambdaN.incl_naturality,
    familyPageMap_comp,ModuleCat.comp_apply,weightLabelNatural]

/-- Complete cycle surjectivity modulo the precise boundary denominator
induces surjectivity of the actual finite E∞ map. -/
private theorem finite_infinity_surjective_of_cycle_surjective
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (hq : 0 < q) (s t w : ℤ)
    (hw : 0 ≤ t-w ∧ t-w < q)
    (hsurj : ∀ y : Ambient background Y (s,t),
      y ∈ cycles background Y ((q:ℤ)-t+w) (s,t) →
      ∃ x : Ambient background X (s,t), x ∈ cycles background X ((q:ℤ)-t+w) (s,t) ∧
        y-(background.classical.map f).pageMap 2 (s,t) x ∈
          boundaries background Y (1+t-w) (s,t)) :
    Function.Surjective ((background.family.map
      (XModLambdaN.map (background.nu.functor.map f) q)).eInftyMap (s,t,w)).hom := by
  intro e
  obtain ⟨y,hy,hey,_⟩ := CrossingLabels.finite_grade_label Y q hq s t w hw e
  obtain ⟨x,hx,hxy⟩ := hsurj y hy
  let ex := (KIP126.Literature.Standard.infinityFiniteWindow X q hq (s,t) w hw).symm
    (subquotientClass (cycles background X ((q:ℤ)-t+w) (s,t))
      (boundaries background X (1+t-w) (s,t)) ⟨x,hx⟩)
  have hex : HasInfinityRepresentative _ 2 (s,t,w)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,w)
        (nuWeightLabel background X s t w (by omega) x)) ex := by
    apply (KIP126.Literature.Standard.eInfinity_finite_labels X q hq s t w hw x ex).mpr
    exact ⟨hx,AddEquiv.apply_symm_apply _ _⟩
  have hmap := family_infinity_representative_map
    (XModLambdaN.map (background.nu.functor.map f) q) (s,t,w) _ ex hex
  rw [finite_weight_label_natural X Y f q s t w (by omega) x] at hmap
  obtain ⟨hfc,hfl⟩ := (KIP126.Literature.Standard.eInfinity_finite_labels Y q hq s t w hw
    ((background.classical.map f).pageMap 2 (s,t) x) _).mp hmap
  obtain ⟨_,hyl⟩ := (KIP126.Literature.Standard.eInfinity_finite_labels Y q hq s t w hw y e).mp hey
  refine ⟨ex,?_⟩
  apply (KIP126.Literature.Standard.infinityFiniteWindow Y q hq (s,t) w hw).injective
  rw [hfl,hyl]
  symm
  apply sub_eq_zero.mp
  rw [←map_sub]
  exact (CrossingLabels.subquotient_zero_iff _ _ _).mpr hxy

/-- Finite induction on graded cycle surjectivity constructs a filtered
preimage under the quotient map. -/
private theorem finite_filtered_surjective_of_cycle_surjective
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (hq : 0 < q) (m w u : ℤ) (hwindow : 0 ≤ m+u-w)
    (hsurj : ∀ s : ℤ, u ≤ s → s < (q:ℤ)+w-m →
      ∀ y : Ambient background Y (s,m+s),
        y ∈ cycles background Y ((q:ℤ)-(m+s)+w) (s,m+s) →
        ∃ x : Ambient background X (s,m+s),
          x ∈ cycles background X ((q:ℤ)-(m+s)+w) (s,m+s) ∧
          y-(background.classical.map f).pageMap 2 (s,m+s) x ∈
            boundaries background Y (1+(m+s)-w) (s,m+s))
    (z : BiHom m w (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q))
    (hz : FiltrationAtLeast background.syntheticTower u z) :
    ∃ a : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q),
      FiltrationAtLeast background.syntheticTower u a ∧
      a ≫ XModLambdaN.map (background.nu.functor.map f) q = z := by
  let SX : SyntheticObject (coefficients := background.coefficients) := .quotient q (.nu X)
  let SY : SyntheticObject (coefficients := background.coefficients) := .quotient q (.nu Y)
  let fq := XModLambdaN.map (background.nu.functor.map f) q
  let M := background.convergentMap SX SY fq
  let top : ℤ := q+w-m
  induction hd : (top-u).toNat using Nat.strong_induction_on generalizing u z with
  | h d ih =>
    by_cases htop : top ≤ u
    · have hzero : z=0 := finite_high_filtration_zero Y q hq m w u
        (by dsimp [top] at htop; omega) z hz
      refine ⟨0,?_,?_⟩
      · exact (background.syntheticTower.filtrationSubmodule _ u (m,w)).zero_mem
      · simpa only [Limits.zero_comp] using hzero.symm
    · obtain ⟨zr,hzr⟩ := filtration_representative_exists background.syntheticTower
        (SY.obj background.nu background.auxiliary) (m,w) u z hz
      have hepi := finite_infinity_surjective_of_cycle_surjective X Y f q hq
        u (m+u) w (by dsimp [top] at htop; omega)
        (hsurj u le_rfl (by dsimp [top] at htop; omega))
      have hrange : (infinityGradedIso (background.convergence SY) (m,w) u).inv
          ((background.syntheticTower.filtration (SY.obj background.nu background.auxiliary)).toAssociatedGraded
            u (m,w) zr) ∈ Set.range ((background.family.functor.map fq).eInftyMap
              (u,m+u,w)).hom := hepi _
      obtain ⟨a,ha,hrem⟩ := (infinity_image_iff_lift M (m,w) u zr).mp hrange
      change BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q) at a
      rw [hzr] at hrem
      have hd' : (top-(u+1)).toNat < d := by omega
      obtain ⟨a',ha',heq⟩ := ih (top-(u+1)).toNat hd' (u+1) (by omega)
        (fun s hs ht => hsurj s (by omega) ht) (z-a≫fq) hrem rfl
      refine ⟨a+a',?_,?_⟩
      · exact (background.syntheticTower.filtrationSubmodule _ u (m,w)).add_mem ha
          (background.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) ha')
      · change (a+a')≫fq=z
        rw [Preadditive.add_comp,heq]
        abel

/-- Every suspended classical E2 label has a desuspension in the fixed
comparison; the construction uses its actual raw Adams representatives. -/
private theorem exists_desuspendsClass (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ)
    (sx : Ambient background (.shift 1 X) (s,t)) :
    ∃ x : Ambient background X (s,t-1),
      (background.classicalSuspension X).DesuspendsClass s t sx x := by
  let S := background.classicalSuspension X
  let DX := (background.classical.obj (X.obj background.auxiliary)).ssData (s,t-1)
  let DU := (background.classical.obj ((X.obj background.auxiliary)⟦(1:ℤ)⟧)).ssData (s,t)
  let PX := background.classicalTower.sequence (X.obj background.auxiliary)
  let PU := background.classicalTower.sequence ((X.obj background.auxiliary)⟦(1:ℤ)⟧)
  let TX := background.classicalTower.tower (X.obj background.auxiliary)
  let qu : Subobject.underlying.obj (DU.Z 0) ⟶ Ambient background (.shift 1 X) (s,t) := DU.pageπ 0 ≫
    eqToHom (by simp only [Ambient,DU,AdamsObject.obj, ClassicalObject.obj,KIP126.Core.SpectralSequence.Page,
      background.classical.firstPage,sub_self,Int.toNat_zero,Nat.cast_zero])
  haveI : Epi (DU.pageπ 0) := inferInstanceAs (Epi (cokernel.π _))
  haveI : Epi qu := by dsimp only [qu]; infer_instance
  obtain ⟨a,ha⟩ := (ModuleCat.epi_iff_surjective qu).mp inferInstance sx
  let sa := ((PU.ambient (s,t)).hom ((DU.Z 0).arrow a)).val
  let xb := S.desuspendFirstPage s t sa
  have hb_cycle : xb∈TX.cycles 2 (by omega) (s,t-1) :=
    desuspend_mem_raw_cycles X 2 (by omega) s t sa
      (((PU.ambient (s,t)).hom ((DU.Z 0).arrow a)).property)
  let v := (PX.ambient (s,t-1)).inv ⟨xb,hb_cycle⟩
  have hv : v ∈ (ModuleCat.subobjectModule DX.V) (DX.Z 0) := by
    apply (PX.cycles (s,t-1) 0 v).mpr
    have he : (PX.ambient (s,t-1)).hom v = ⟨xb,hb_cycle⟩ := by
      change ((PX.ambient (s,t-1)).inv ≫ (PX.ambient (s,t-1)).hom) _ = _
      rw [Iso.inv_hom_id]
      rfl
    rw [he]
    exact hb_cycle
  obtain ⟨b,hb⟩ := hv
  let qx : Subobject.underlying.obj (DX.Z 0) ⟶ Ambient background X (s,t-1) := DX.pageπ 0 ≫
    eqToHom (by simp only [Ambient,DX,KIP126.Core.SpectralSequence.Page,
      background.classical.firstPage,sub_self,Int.toNat_zero,Nat.cast_zero])
  refine ⟨qx b,a,b,ha,rfl,?_⟩
  have heb : (PX.ambient (s,t-1)).hom ((DX.Z 0).arrow b)=⟨xb,hb_cycle⟩ := by
    rw [hb]
    change ((PX.ambient (s,t-1)).inv ≫ (PX.ambient (s,t-1)).hom) _ = _
    rw [Iso.inv_hom_id]
    rfl
  change xb=((PX.ambient (s,t-1)).hom ((DX.Z 0).arrow b)).val
  rw [heb]

private theorem initial_cycle_class_iff (D : SSData (ModuleCat.{0} ℤ))
    (n : WithTop ℕ) (z : (Subobject.underlying.obj (D.Z 0) : ModuleCat ℤ)) :
    (∃ v : (Subobject.underlying.obj (D.Z n) : ModuleCat ℤ),
      (Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0) v=D.pageπ 0 z) ↔
      (D.Z 0).arrow z∈(ModuleCat.subobjectModule D.V) (D.Z n) := by
  let i := Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le)
  constructor
  · rintro ⟨v,hv⟩
    have hz : D.pageπ 0 (z-i v)=0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hv.symm
    have hb := (subobject_cokernel_π_eq_zero_iff (D.B 0) (D.Z 0) (D.B_le_Z 0) _).mp hz
    have hb' : (D.Z 0).arrow (z-i v)∈(ModuleCat.subobjectModule D.V) (D.Z n) :=
      (ModuleCat.subobjectModule D.V).monotone
        ((D.B_mono le_top).trans ((D.B_le_Z ⊤).trans (D.Z_anti le_top))) hb
    have hv' : (D.Z 0).arrow (i v)∈(ModuleCat.subobjectModule D.V) (D.Z n) := by
      change (i≫(D.Z 0).arrow) v∈_
      rw [Subobject.ofLE_arrow]
      exact ⟨v,rfl⟩
    have h := ((ModuleCat.subobjectModule D.V) (D.Z n)).add_mem hb' hv'
    rw [map_sub,sub_add_cancel] at h
    exact h
  · rintro ⟨v,hv⟩
    refine ⟨v,?_⟩
    have he : i v=z := by
      apply (ModuleCat.mono_iff_injective (D.Z 0).arrow).mp inferInstance
      change (i≫(D.Z 0).arrow) v=(D.Z 0).arrow z
      rw [Subobject.ofLE_arrow]
      exact hv
    change D.pageπ 0 (i v)=D.pageπ 0 z
    rw [he]

private theorem initial_cycle_label_iff (X : AdamsObject (coefficients := background.coefficients)) (c : ℤ) (p : ℤ×ℤ)
    (z : (Subobject.underlying.obj (((background.classical.obj (X.obj background.auxiliary)).ssData p).Z 0) : ModuleCat ℤ)) :
    cycleLabel background X 0 p z∈cycles background X c p ↔
      ((((background.classicalTower.sequence (X.obj background.auxiliary)).ambient p).hom
        ((((background.classical.obj (X.obj background.auxiliary)).ssData p).Z 0).arrow z)).val)∈
          (background.classicalTower.tower (X.obj background.auxiliary)).cycles ((c-1).toNat+2) (by omega) p := by
  let D := (background.classical.obj (X.obj background.auxiliary)).ssData p
  rw [←(background.classicalTower.sequence (X.obj background.auxiliary)).cycles p (c-1).toNat]
  rw [←initial_cycle_class_iff D (↑(c-1).toNat) z]
  change (∃v, cycleLabel background X (↑(c-1).toNat) p v=cycleLabel background X 0 p z) ↔ _
  simp only [cycleLabel,Subobject.ofLE_refl,Category.id_comp]
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨v,?_⟩
    apply (ModuleCat.mono_iff_injective (eqToHom _)).mp inferInstance
    exact hv
  · rintro ⟨v,hv⟩
    refine ⟨v,?_⟩
    exact congrArg (fun a=>(eqToHom _ : D.page 0 ⟶ (background.classical.obj (X.obj background.auxiliary)).Page 2 p) a) hv

/-- The fixed tower suspension preserves exactly the paper cycle index. -/
private theorem desuspendsClass_cycle_iff (X : AdamsObject (coefficients := background.coefficients)) (k s t : ℤ)
    (sx : Ambient background (.shift 1 X) (s,t)) (x : Ambient background X (s,t-1))
    (h : (background.classicalSuspension X).DesuspendsClass s t sx x) :
    sx∈cycles background (.shift 1 X) k (s,t) ↔ x∈cycles background X k (s,t-1) := by
  obtain ⟨a,b,ha,hb,hab⟩ := h
  have ha' : cycleLabel background (.shift 1 X) 0 (s,t) a=sx := by
    simpa only [cycleLabel,Subobject.ofLE_refl,Category.id_comp,AdamsObject.obj, ClassicalObject.obj] using ha
  have hb' : cycleLabel background X 0 (s,t-1) b=x := by
    simpa only [cycleLabel,Subobject.ofLE_refl,Category.id_comp] using hb
  rw [←ha',←hb',initial_cycle_label_iff,initial_cycle_label_iff,←hab]
  exact (desuspend_mem_raw_cycles_iff X ((k-1).toNat+2) (by omega) s t _).symm

/-- The existing public Surj condition supplies complete ordinary h cycle
coverage, including j=K-1 and its full denominator R+K-2. -/
private theorem finite_layer_surj_ordinary_h_cycles
    (T : TriangleData background.auxiliary) (R K : ℕ) (s t : ℤ)
    (hsurj : KIP126.ProofTools.Standard.MahowaldLeibnizFiniteLayerSurjectivity T R K s t)
    (j : ℕ) (hj : 1≤j) (hjK : j<K)
    (y : Ambient background (.shift 1 T.X) (s+R+j,t+R+j))
    (hy : y∈cycles background (.shift 1 T.X) ((K:ℤ)-j) (s+R+j,t+R+j)) :
    ∃ z : Ambient background T.Z (s+R+j,t+R+j),
      z∈cycles background T.Z ((K:ℤ)-j) (s+R+j,t+R+j) ∧
      y-(background.classical.map T.h).pageMap 2 (s+R+j,t+R+j) z ∈
        boundaries background (.shift 1 T.X) ((R:ℤ)+j-1) (s+R+j,t+R+j) := by
  obtain ⟨a,ha⟩ := exists_desuspendsClass T.X (s+R+j) (t+R+j) y
  have hac : IsCycle background T.X ((K:ℤ)-j) (s+R+j,t+R+j-1) a :=
    ⟨by omega,(desuspendsClass_cycle_iff T.X _ _ _ y a ha).mp hy⟩
  obtain ⟨z,hz,b,hb,hab⟩ := hsurj j hj hjK a hac
  refine ⟨z,hz.2,?_⟩
  exact (desuspendsClass_boundary_iff T.X _ _ _ _ _
    (suspension_desuspends_sub T.X _ _ _ _ _ _ ha hb)).mpr hab.2

/-- Finite-layer surjectivity gives filtered preimages
under `Q_(c+K)(nu h)`. -/
private theorem finite_layer_surj_ordinary_h_filtered
    (T : TriangleData background.auxiliary) (c K : ℕ) (hK : 2≤K) (S V : ℤ)
    (hsurj : KIP126.ProofTools.Standard.MahowaldLeibnizFiniteLayerSurjectivity
      T (c+2) K (S-(c+2:ℕ)) (V-(c+2:ℕ)+1))
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN (background.nu.functor.obj ((AdamsObject.shift 1 T.X).obj background.auxiliary)) (c+K)))
    (ha : FiltrationAtLeast background.syntheticTower (S+1) a) :
    ∃ b : BiHom (V-S+1) (V-c+1)
      (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) (c+K)),
      FiltrationAtLeast background.syntheticTower (S+1) b ∧
      b≫XModLambdaN.map (background.nu.functor.map T.h) (c+K)=a := by
  apply finite_filtered_surjective_of_cycle_surjective T.Z (.shift 1 T.X) T.h
    (c+K) (by omega) (V-S+1) (V-c+1) (S+1) (by omega) ?_ a ha
  intro k hk hktop
  let j := (k-S).toNat
  have hj : (j:ℤ)=k-S := by dsimp [j]; omega
  have hj1 : 1≤j := by omega
  have hjK : j<K := by omega
  have h := finite_layer_surj_ordinary_h_cycles T (c+2) K
    (S-(c+2:ℕ)) (V-(c+2:ℕ)+1) hsurj j hj1 hjK
  have hs : S-(c+2:ℕ)+(c+2:ℕ)+(j:ℤ)=k := by omega
  have ht : V-(c+2:ℕ)+1+(c+2:ℕ)+(j:ℤ)=V-S+1+k := by omega
  have hc : (c+K:ℕ)-(V-S+1+k)+(V-(c:ℤ)+1)=(K:ℤ)-j := by omega
  have hb : 1+(V-S+1+k)-(V-(c:ℤ)+1)=(c+2:ℕ)+(j:ℤ)-1 := by omega
  rw [hs,ht] at h
  rw [hc,hb]
  exact h

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
