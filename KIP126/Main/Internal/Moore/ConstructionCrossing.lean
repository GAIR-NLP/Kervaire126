module

import KIP126.AdamsComputation.Moore.Object
import KIP126.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.Moore.SphereCrossing

/-! Filtration comparisons for the Moore crossing. Equal first
restrictions place the source difference in the higher source grade. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.Main.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private theorem moore_shifted_quotient_filtration_floor
    (X : AdamsObject (coefficients := background.coefficients))
    (q : ℕ) (hq : 0 < q) (i m w : ℤ)
    (a : BiHom m w ((SyntheticCategory.biShift (0,i)).obj
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))) :
    FiltrationAtLeast background.syntheticTower (w-m-i) a := by
  let A : SyntheticObject (coefficients := background.coefficients) :=
    .shift (0,i) (.quotient q (.nu X))
  let u : ℤ := w-m-i
  have hzero (j : ℤ) (hj : j < u) :
      IsZero (((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData
        (j,m+j,w)).eInfty) := by
    have hz := finite_infinity_zero_outside X q hq j (m+j) (w-i) (by dsimp [u] at hj; omega)
    let e := towerInfinityIso (background.convergence (.quotient q (.nu X)))
      (background.convergence A)
      ((essShift (0,i)).filtered (.quotient q (.nu X)) (m,w-i)) j
    have he := hz.of_iso e.symm
    simpa only [e,A,Prod.fst_add,Prod.snd_add,add_zero,sub_add_cancel] using he
  have ha0 : FiltrationAtLeast background.syntheticTower 0 a := by
    refine ⟨a ≫ (background.syntheticTower.tower _).zeroIso.inv, ?_⟩
    change (a ≫ (background.syntheticTower.tower _).zeroIso.inv) ≫
      (background.syntheticTower.tower _).projection 0 = a
    simp only [AbstractAdamsTower.projection, Int.toNat_zero,
      (background.syntheticTower.tower _).map_self]
    erw [Category.assoc, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  by_cases hu : u ≤ 0
  · exact background.syntheticTower.filtrationSubmodule_antitone _ (m,w) hu ha0
  · exact (filtration_iff_of_infinity_zero (background.convergence A) 0 u m w (by omega)
      (fun j _ hj => hzero j hj) a).mp ha0

/-- The lambda-triangle kernel with the finite filtration floor. -/
private theorem moore_first_restriction_kernel
    (a : BiHom 124 132
      (XModLambdaN (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 2))
    (ha : a ≫ (background.quotients.tower
      (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum)).rho 1 2 (by decide) = 0) :
    FiltrationAtLeast background.syntheticTower 9 a := by
  let X := KIP126.AdamsComputation.Moore.adamsObject
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let T := (background.quotients.tower A).triangle (by decide : 0<1) (by decide : 1<2)
  have hz : a ≫ T.rho = 0 := by
    dsimp only [T]
    rw [(background.quotients.tower A).triangle_rho]
    exact ha
  obtain ⟨b,hb⟩ := (Triangle.mk T.lambdaMap T.rho T.delta).coyoneda_exact₂ T.distinguished a hz
  have hf : FiltrationAtLeast background.syntheticTower 9 b :=
    moore_shifted_quotient_filtration_floor X 1 (by decide) (-1) 124 132 b
  have hm := map_preserves_filtration
    (background.convergentMap (.shift (0,-1) (.quotient 1 (.nu X)))
      (.quotient 2 (.nu X)) T.lambdaMap) (124,132) 9 b hf
  change FiltrationAtLeast background.syntheticTower 9 (b ≫ T.lambdaMap) at hm
  change a = b ≫ T.lambdaMap at hb
  rwa [←hb] at hm

/-- Both source representatives restrict to the same first-quotient class,
so their actual difference belongs to the source of the crossing map. -/
private theorem moore_source_difference_filtration
    (c4 : BiHom 124 132
      (XModLambdaN (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 4))
    (c0 : BiHom 124 132
      (XModLambdaN (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 2))
    (h : c4 ≫ (background.quotients.tower
        (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum)).rho 1 4 (by decide) =
      c0 ≫ (background.quotients.tower
        (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum)).rho 1 2 (by decide)) :
    FiltrationAtLeast background.syntheticTower 9
      (c4 ≫ (background.quotients.tower
        (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum)).rho 2 4 (by decide)-c0) := by
  apply moore_first_restriction_kernel
  rw [Preadditive.sub_comp,Category.assoc,
    (background.quotients.tower _).rho_comp,h,sub_self]

/-- Once the actual second restriction is nonzero, the fourth-quotient
cycle computation determines the entire detecting label. -/
private theorem moore_fourth_detection_of_second_nonzero
    (V : background.classical.sphere.Page 2 (9,132))
    (hframe : ∀ x : background.classical.sphere.Page 2 (9,132),
      x ∈ cycles background .sphere 3 (9,132) → x=0 ∨ x=V)
    (a : BiHom 123 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 4))
    (ha : FiltrationAtLeast background.syntheticTower 9 a)
    (hnz : a ≫ (background.quotients.tower (S_0_0 : SyntheticSpectrum)).rho 2 4 (by decide) ≠ 0) :
    Detects (background.convergence (.quotient 4 .sphere)) (9,132,131)
      (quotientLabel 4 9 132 1 V) a := by
  obtain ⟨x,hx,hd⟩ := finite_sphere_filtration_has_cycle_label
    4 1 (by decide) (by decide) 9 132 a ha
  rcases hframe x hx with hz | he
  · exfalso
    apply hnz
    have hl : quotientLabel 4 9 132 1 x = 0 := by
      subst x
      simp only [quotientLabel,sphereLabel,map_zero]
    rw [hl] at hd
    have hf := detects_zero_filtration (background.convergence (.quotient 4 .sphere))
      (9,132,131) hd
    have hm := map_preserves_filtration (background.convergentMap (.quotient 4 .sphere)
      (.quotient 2 .sphere) ((background.quotients.tower (S_0_0 : SyntheticSpectrum)).rho 2 4
        (by decide))) (123,131) 10 a hf
    exact sphere_quotient_high_filtration_zero 2 (by decide) 123 131 10 (by decide) _ hm
  · rwa [he] at hd

private theorem moore_zero_homotopy_has_zero_infinity
    (X : SyntheticObject (coefficients := background.coefficients)) (i : Tridegree)
    (x : (background.family.obj (X.obj background.nu background.auxiliary)).E₂ i)
    (hd : Detects (background.convergence X) i x 0) :
    HasInfinityRepresentative (background.family.obj (X.obj background.nu background.auxiliary))
      2 i x 0 := by
  obtain ⟨e,he,a,ha,hgr⟩ := hd
  have hz : a=0 := (ModuleCat.mono_iff_injective
    ((background.convergence X).filtration.F i.1 (i.2.1-i.1,i.2.2)).arrow).mp inferInstance
      (ha.trans (map_zero _).symm)
  rw [hz,map_zero] at hgr
  have he0 : e=0 := ((background.convergence X).identification i).toLinearEquiv.injective
    (hgr.trans (map_zero _).symm)
  rwa [he0] at he

/-- Nonvanishing in the classical B₂ quotient with the specified
crossing denominator. -/
private theorem moore_subquotient_zero_iff {R A : Type*} [Ring R] [AddCommGroup A] [Module R A]
    (Z B : Submodule R A) (y : Z) : subquotientClass Z B y = 0 ↔ y.val ∈ B :=
  Submodule.Quotient.mk_eq_zero _

private theorem moore_second_detection_nonzero
    (x : background.classical.sphere.Page 2 (9,132))
    (hx : x ∉ boundaries background .sphere 2 (9,132))
    (a : BiHom 123 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 2))
    (ha : Detects (background.convergence (.quotient 2 .sphere)) (9,132,131)
      (quotientLabel 2 9 132 1 x) a) : a ≠ 0 := by
  intro hz
  subst a
  have hn := detects_map (.quotient 2 .sphere) (.quotient 2 (.nu .sphere))
    (XModLambdaN.map background.nu.unitIso.inv 2) (9,132,131) _ 0 ha
  erw [sphere_quotient_label_to_nu 2 1 9 132 x,zero_comp] at hn
  have he := moore_zero_homotopy_has_zero_infinity (.quotient 2 (.nu .sphere))
    (9,132,131) (finiteTargetLabel background .sphere 2 9 132 1 x) hn
  obtain ⟨hc,hc0⟩ := (KIP126.Literature.Standard.eInfinity_finite_labels .sphere
    2 (by decide) 9 132 131 (by constructor <;> decide) x 0).mp he
  rw [map_zero] at hc0
  apply hx
  exact (moore_subquotient_zero_iff _ _ ⟨x,hc⟩).mp hc0.symm

/-- The two possible higher-source images cannot cancel the prescribed
initial image when both resulting labels survive modulo B₂.  The initial
label may retain the sign supplied by finite May. -/
private theorem moore_second_sum_nonzero
    (v0 v1 : background.classical.sphere.Page 2 (9,132))
    (h0 : v0 ∉ boundaries background .sphere 2 (9,132))
    (h01 : v0+v1 ∉ boundaries background .sphere 2 (9,132))
    (a b : BiHom 123 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 2))
    (ha : Detects (background.convergence (.quotient 2 .sphere)) (9,132,131)
      (quotientLabel 2 9 132 1 v0) a)
    (hb : Detects (background.convergence (.quotient 2 .sphere)) (9,132,131)
        (quotientLabel 2 9 132 1 0) b ∨
      Detects (background.convergence (.quotient 2 .sphere)) (9,132,131)
        (quotientLabel 2 9 132 1 v1) b) : a+b ≠ 0 := by
  rcases hb with hb | hb
  · apply moore_second_detection_nonzero v0 h0 (a+b)
    simpa only [quotientLabel,sphereLabel,map_zero,add_zero] using
      detects_add (background.convergence (.quotient 2 .sphere)) (9,132,131) ha hb
  · apply moore_second_detection_nonzero (v0+v1) h01 (a+b)
    simpa only [quotientLabel,sphereLabel,map_add] using
      detects_add (background.convergence (.quotient 2 .sphere)) (9,132,131) ha hb

/-- The full higher-source grade is `C₂(9,133)`,
with finite window `Z₁/B₂`. -/
private theorem moore_second_higher_source_label
    (a : BiHom 124 132
      (XModLambdaN (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 2))
    (ha : FiltrationAtLeast background.syntheticTower 9 a) :
    ∃ z : KIP126.AdamsComputation.Moore.Page 9 133,
      z ∈ cycles background KIP126.AdamsComputation.Moore.adamsObject 1 (9,133) ∧
      Detects (background.convergence
        (.quotient 2 (.nu KIP126.AdamsComputation.Moore.adamsObject))) (9,133,132)
        (finiteTargetLabel background KIP126.AdamsComputation.Moore.adamsObject 2 9 133 1 z) a := by
  let X := KIP126.AdamsComputation.Moore.adamsObject
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let C := background.convergence (.quotient 2 (.nu X))
  obtain ⟨aa,haa⟩ := filtration_representative_exists background.syntheticTower
    (XModLambdaN A 2) (124,132) 9 a ha
  let e := (C.identification (9,133,132)).inv
    (C.filtration.toAssociatedGraded 9 (124,132) aa)
  let P := KIP126.Literature.Standard.infinityFiniteWindow X 2 (by decide)
    (9,133) 132 (by constructor <;> decide)
  obtain ⟨z,hz⟩ := Quotient.exists_rep (P e)
  have he : HasInfinityRepresentative (background.family.quotient A 2) 2 (9,133,132)
      (finiteTargetLabel background X 2 9 133 1 z.val) e := by
    apply (finite_target_label_iff X 2 (by decide) 9 133 1 (by decide) z e).mpr
    exact hz.symm
  refine ⟨z.val,z.property,e,he,aa,haa,?_⟩
  exact (C.identification (9,133,132)).toLinearEquiv.apply_symm_apply _

private theorem moore_page_map_cast
    {U V : SyntheticSpectrum} (g : U ⟶ V) {p q : Tridegree} (h : p=q)
    (x : (background.family.obj U).E₂ p) :
    familyPageMap background.family g 2 q
      (Eq.mp (congrArg (fun a : Tridegree => ((background.family.obj U).E₂ a : Type)) h) x) =
      Eq.mp (congrArg (fun a : Tridegree => ((background.family.obj V).E₂ a : Type)) h)
        (familyPageMap background.family g 2 p x) := by
  subst q
  rfl

private theorem moore_nu_label_natural
    (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t : ℤ) (k : ℕ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :
    familyPageMap background.family (background.nu.functor.map f) 2 (s,t,t-k)
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
  have hxy : familyPageMap background.family ((SyntheticCategory.biShift (0,0)).map nuf)
      2 p x₀ = y₀ := by
    have hdeg : (s,t,t+0-(k:ℤ))=p := by dsimp [p]; simp only [add_zero]
    have hraw := background.comparison.nu_natural X Y f 0 s t k x
    have hc := moore_page_map_cast ((SyntheticCategory.biShift (0,0)).map nuf) hdeg
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
  change familyPageMap background.family nuf 2 p (familyPageMap background.family zx 2 p x₀) =
    familyPageMap background.family zy 2 p y₀
  calc
    _ = familyPageMap background.family (zx ≫ nuf) 2 p x₀ :=
      (ConcreteCategory.congr_hom (family_page_comp zx nuf 2 p) x₀)
    _ = familyPageMap background.family ((SyntheticCategory.biShift (0,0)).map nuf ≫ zy) 2 p x₀ :=
      congrArg (fun g => familyPageMap background.family g 2 p x₀) hn.symm
    _ = familyPageMap background.family zy 2 p
        (familyPageMap background.family ((SyntheticCategory.biShift (0,0)).map nuf) 2 p x₀) :=
      (ConcreteCategory.congr_hom
        (family_page_comp ((SyntheticCategory.biShift (0,0)).map nuf) zy 2 p) x₀).symm
    _ = _ := congrArg (familyPageMap background.family zy 2 p) hxy

private theorem moore_finite_label_natural
    (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (s t : ℤ) (k : ℕ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :
    familyPageMap background.family (XModLambdaN.map (background.nu.functor.map f) q)
      2 (s,t,t-k) (finiteTargetLabel background X q s t k x) =
    finiteTargetLabel background Y q s t k ((background.classical.map f).pageMap 2 (s,t) x) := by
  change familyPageMap background.family (XModLambdaN.map (background.nu.functor.map f) q)
      2 (s,t,t-k) (familyPageMap background.family (XModLambdaN.incl _ q) 2 (s,t,t-k) _) =
    familyPageMap background.family (XModLambdaN.incl _ q) 2 (s,t,t-k) _
  rw [←ModuleCat.comp_apply,family_page_comp,←XModLambdaN.incl_naturality,
    ←family_page_comp,ModuleCat.comp_apply,moore_nu_label_natural]

/-- The C₂ top map acts on every higher-source error by its classical E₂ map,
so a bound on this image controls every such error. -/
private theorem moore_second_higher_top_image_label
    (a : BiHom 124 132
      (XModLambdaN (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 2))
    (ha : FiltrationAtLeast background.syntheticTower 9 a) :
    ∃ z : KIP126.AdamsComputation.Moore.Page 9 133,
      z ∈ cycles background KIP126.AdamsComputation.Moore.adamsObject 1 (9,133) ∧
      Detects (background.convergence (.quotient 2 (.nu (.shift 1 .sphere)))) (9,133,132)
        (finiteTargetLabel background (.shift 1 .sphere) 2 9 133 1
          ((background.classical.map KIP126.AdamsComputation.Moore.top).pageMap 2 (9,133) z))
        (a ≫ XModLambdaN.map (background.nu.functor.map KIP126.AdamsComputation.Moore.top) 2) := by
  obtain ⟨z,hz,hd⟩ := moore_second_higher_source_label a ha
  refine ⟨z,hz,?_⟩
  have hm := detects_map (.quotient 2 (.nu KIP126.AdamsComputation.Moore.adamsObject))
    (.quotient 2 (.nu (.shift 1 .sphere)))
    (XModLambdaN.map (background.nu.functor.map KIP126.AdamsComputation.Moore.top) 2)
    (9,133,132) _ a hd
  erw [moore_finite_label_natural KIP126.AdamsComputation.Moore.adamsObject
    (.shift 1 .sphere) KIP126.AdamsComputation.Moore.top 2 9 133 1 z] at hm
  exact hm

private theorem moore_initial_crossing_label_nonzero :
    KIP126.Computation.Table.basis .sphere 9 132 0 ≠ 0 ∧
      KIP126.Computation.Table.basis .sphere 9 132 0 +
        KIP126.Computation.Table.basis .sphere 9 132 1 ≠ 0 := by
  classical
  have hb : ∃ e : background.classical.sphere.Page 2 (9,132) ≃ₗ[ℤ] (Fin 2 →₀ ZMod 2),
      ∀ i : Fin 2, e.symm (Finsupp.single i 1) =
        KIP126.Computation.Table.basis .sphere 9 132 i.val := by
    exact KIP126.Computation.Table.basis_correct
      ⟨.sphere,9,132,["366,1","0,1,352,1"]⟩ (List.mem_of_getElem? (i:=171) rfl)
  obtain ⟨e,he⟩ := hb
  have he0 : e (KIP126.Computation.Table.basis .sphere 9 132 0) =
      Finsupp.single (0 : Fin 2) 1 := by
    exact (congrArg e (he (0:Fin 2))).symm.trans (e.apply_symm_apply _)
  have he1 : e (KIP126.Computation.Table.basis .sphere 9 132 1) =
      Finsupp.single (1 : Fin 2) 1 := by
    exact (congrArg e (he (1:Fin 2))).symm.trans (e.apply_symm_apply _)
  constructor
  · intro hz
    have hc : Finsupp.single (0 : Fin 2) (1 : ZMod 2)=0 :=
      he0.symm.trans ((congrArg e hz).trans (map_zero e))
    have h := congrArg (fun v : Fin 2 →₀ ZMod 2 => v 0) hc
    norm_num at h
  · intro hz
    have hc := congrArg e hz
    erw [map_add,he0,he1,map_zero e] at hc
    have h := congrArg (fun v : Fin 2 →₀ ZMod 2 => v 0) hc
    norm_num at h

/-- Noncancellation from the fixed sphere basis and the B₂ calculation. -/
private theorem moore_actual_second_sum_nonzero
    (a b : BiHom 123 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 2))
    (ha : Detects (background.convergence (.quotient 2 .sphere)) (9,132,131)
      (quotientLabel 2 9 132 1 (KIP126.Computation.Table.basis .sphere 9 132 0)) a)
    (hb : Detects (background.convergence (.quotient 2 .sphere)) (9,132,131)
        (quotientLabel 2 9 132 1 0) b ∨
      Detects (background.convergence (.quotient 2 .sphere)) (9,132,131)
        (quotientLabel 2 9 132 1 (KIP126.Computation.Table.basis .sphere 9 132 1)) b) :
    a+b ≠ 0 := by
  apply moore_second_sum_nonzero _ _ _ _ a b ha hb
  · rw [SphereCrossing.boundaries_two_eq_bot,Submodule.mem_bot]
    exact moore_initial_crossing_label_nonzero.1
  · rw [SphereCrossing.boundaries_two_eq_bot,Submodule.mem_bot]
    exact moore_initial_crossing_label_nonzero.2

private theorem moore_actual_fourth_detection_of_second_nonzero
    (a : BiHom 123 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 4))
    (ha : FiltrationAtLeast background.syntheticTower 9 a)
    (hnz : a ≫ (background.quotients.tower (S_0_0 : SyntheticSpectrum)).rho 2 4 (by decide) ≠ 0) :
    Detects (background.convergence (.quotient 4 .sphere)) (9,132,131)
      (quotientLabel 4 9 132 1 KIP126.Computation.Standard.V) a :=
  moore_fourth_detection_of_second_nonzero KIP126.Computation.Standard.V
    SphereCrossing.cycles_three_cases a ha hnz

end
end KIP126.Main.Internal.Moore
