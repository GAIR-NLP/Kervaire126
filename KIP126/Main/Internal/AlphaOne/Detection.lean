module
import all KIP126.Main.SectionSeven.Predicates
public import KIP126.Main.SectionSeven.AlphaOne
public import KIP126.ProofTools.Representatives
public import KIP126.ProofTools.Operations
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.QuotientCalculus

/-! Existence and restriction of finite-quotient sphere detections. -/
@[expose] section
namespace KIP126.Main.Internal.AlphaOne
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Main.SectionSeven KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald KIP126.Main.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
private theorem detection_exists_of_infinity
    {X : SyntheticSpectrum} (c : SyntheticTowerConvergence background.syntheticTower X)
    (i : Tridegree) (x : (background.family.obj X).E₂ i)
    (e : ((background.family.obj X).sequence.ssData i).eInfty)
    (hx : HasInfinityRepresentative (background.family.obj X) 2 i x e) (hne : e≠0) :
    ∃ a : BiHom (i.2.1-i.1) i.2.2 X, DetectsNonzero c i x a := by
  classical
  let F := background.syntheticTower.filtration X
  haveI : Epi (F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2)) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨a,ha⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2))).mp
    inferInstance ((c.identification i).hom e)
  exact ⟨(F.F i.1 (i.2.1-i.1,i.2.2)).arrow a,⟨e,hx,a,rfl,ha.symm⟩,e,hx,hne⟩


private theorem finite_sphere_detection_exists
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : background.classical.sphere.Page 2 (s,t))
    (hx : x∈KIP126.Literature.cycles background .sphere q (s,t)) (hne : x≠0) :
    ∃ a : BiHom (t-s) (t-0) (XModLambdaN (S_0_0 : SyntheticSpectrum) q), FiniteDetected q hq s t 0 x a := by
  classical
  let P := KIP126.Literature.Standard.infinityFiniteWindow .sphere q hq (s,t) (t-0)
    (by constructor <;> omega)
  let y : KIP126.Literature.cycles background .sphere ((q:ℤ)-t+(t-0)) (s,t) :=
    ⟨x,by simpa only [sub_zero,sub_add_cancel] using hx⟩
  let e := P.symm (KIP126.Literature.subquotientClass _ _ y)
  have he : HasInfinityRepresentative (background.family.quotient (background.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-0)
      (finiteTargetLabel background .sphere q s t 0 x) e := by
    apply (finite_target_label_iff .sphere q hq s t 0 hq y e).mpr
    exact P.apply_symm_apply _
  have en : e≠0 := by
    intro hz
    have hp := congrArg P hz
    change P (P.symm _)=P 0 at hp
    rw [P.apply_symm_apply,map_zero] at hp
    have hm := (subquotientClass_eq_zero_iff _ _ y).mp hp
    have hb : (1:ℤ)+t-(t-0)=1 := by omega
    change x∈KIP126.Literature.boundaries background .sphere (1+t-(t-0)) (s,t) at hm
    rw [hb,boundaries_one background .sphere,Submodule.mem_bot] at hm
    exact hne hm
  let f := XModLambdaN.map background.nu.unitIso.hom q
  let g := XModLambdaN.map background.nu.unitIso.inv q
  have hgf : g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←background.quotients.functoriality.map_comp,Iso.inv_hom_id,background.quotients.functoriality.map_id]
  have hfg : f≫g=𝟙 _ := by
    dsimp only [f,g]
    rw [←background.quotients.functoriality.map_comp,Iso.hom_inv_id,background.quotients.functoriality.map_id]
  let e' := (background.family.functor.map f).eInftyMap (s,t,t-0) e
  have hel : familyPageMap background.family f 2 (s,t,t-0) (finiteTargetLabel background .sphere q s t 0 x)=quotientLabel q s t 0 x :=
    sphere_quotient_label_from_nu q 0 s t x

  have he' : HasInfinityRepresentative (background.family.quotient (S_0_0 : SyntheticSpectrum) q) 2 (s,t,t-0)
      (quotientLabel q s t 0 x) e' := by
    have hh := family_infinity_representative_map f (s,t,t-0) _ _ he
    rw [hel] at hh
    exact hh
  have en' : e'≠0 := by
    intro hz
    apply en
    have hh := congrArg (fun a=>(background.family.functor.map g).eInftyMap (s,t,t-0) a) hz
    change ((background.family.functor.map f).eInftyMap (s,t,t-0) ≫ (background.family.functor.map g).eInftyMap (s,t,t-0)) e=_ at hh
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hfg,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id] at hh
    simpa only [ConcreteCategory.id_apply,map_zero] using hh
  exact detection_exists_of_infinity (background.convergence (.quotient q .sphere)) (s,t,t-0) _ e' he' en'


private theorem finite_sphere_infinity_nonzero
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : background.classical.sphere.Page 2 (s,t))
    (hx : x∈KIP126.Literature.cycles background .sphere q (s,t)) (hne : x≠0)
    (e : ((background.family.quotient (S_0_0 : SyntheticSpectrum) q).sequence.ssData (s,t,t-0)).eInfty)
    (he : HasInfinityRepresentative (background.family.quotient (S_0_0 : SyntheticSpectrum) q) 2 (s,t,t-0)
      (quotientLabel q s t 0 x) e) : e≠0 := by
  classical
  let g := XModLambdaN.map background.nu.unitIso.inv q
  have hh := family_infinity_representative_map g (s,t,t-0) _ _ he
  have hl := sphere_quotient_label_to_nu q 0 s t x
  change familyPageMap background.family g 2 (s,t,t-0) (quotientLabel q s t 0 x)=_ at hl
  rw [hl] at hh
  let y : KIP126.Literature.cycles background .sphere ((q:ℤ)-t+(t-0)) (s,t) :=
    ⟨x,by simpa only [sub_zero,sub_add_cancel] using hx⟩
  have hp := (finite_target_label_iff .sphere q hq s t 0 hq y _).mp hh
  intro he0
  rw [he0,map_zero,map_zero] at hp
  have hm := (subquotientClass_eq_zero_iff _ _ y).mp hp.symm
  have hb : (1:ℤ)+t-(t-0)=1 := by omega
  change x∈KIP126.Literature.boundaries background .sphere (1+t-(t-0)) (s,t) at hm
  rw [hb,boundaries_one background .sphere,Submodule.mem_bot] at hm
  exact hne hm


private theorem finite_sphere_detected_rho
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (hij : i ≤ j) (s t : ℤ)
    (x : background.classical.sphere.Page 2 (s,t))
    (hx : x∈KIP126.Literature.cycles background .sphere i (s,t)) (hne : x≠0)
    (a : BiHom (t-s) (t-0) (XModLambdaN (S_0_0 : SyntheticSpectrum) j))
    (ha : FiniteDetected j hj s t 0 x a) :
    FiniteDetected i hi s t 0 x (a≫(background.quotients.tower S_0_0).rho i j hij) := by
  classical
  let rho := (background.quotients.tower S_0_0).rho i j hij
  have hl : familyPageMap background.family rho 2 (s,t,t-0) (quotientLabel j s t 0 x)=quotientLabel i s t 0 x := by
    change familyPageMap background.family rho 2 (s,t,t-0)
      (familyPageMap background.family (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) j) 2 (s,t,t-0) (background.comparison.sphereE2 s t 0 x))=_
    calc
      _ = familyPageMap background.family (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) j≫rho) 2 (s,t,t-0) (background.comparison.sphereE2 s t 0 x) :=
        ConcreteCategory.congr_hom (family_page_comp (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) j) rho 2 (s,t,t-0)) _
      _ = quotientLabel i s t 0 x := by
        dsimp only [rho]
        rw [FiniteLambdaQuotientTower.rho_quotient]
        rfl
  have hd := detects_map (.quotient j .sphere) (.quotient i .sphere) rho (s,t,t-0) _ a ha.1
  have hd' : Detects (background.convergence (.quotient i .sphere)) (s,t,t-0)
      (quotientLabel i s t 0 x) (a≫rho) := hl ▸ hd
  refine ⟨hd',?_⟩
  obtain ⟨e,he,_⟩ := hd'
  exact ⟨e,he,finite_sphere_infinity_nonzero  i hi s t x hx hne e he⟩


private theorem sphere_lift_finite_detection
    (q : ℕ) (hq : 0<q) (k : ℕ) (s t : ℤ)
    (x : background.classical.sphere.Page 2 (s,t)) (c : BiHom (t-s) t (S_0_0 : SyntheticSpectrum))
    (hc : KIP126.Literature.sphereFirstQuotient background s t (quotientClass 1 c)=x) :
    Detects (background.convergence (.quotient q .sphere)) (s,t,t-k) (quotientLabel q s t k x)
      (lambdaMultiply k (quotientClass q c)) := by
  classical
  have h := background.sphereDetectionCompatible.homotopy_lambda s t k c
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hc
  rw [hc] at h
  have hh := detects_map .sphere (.quotient q .sphere)
    (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) q) (s,t,t-k) _ (lambdaMultiply k c) h
  change Detects (background.convergence (.quotient q .sphere)) (s,t,t-k) (quotientLabel q s t k x)
    (lambdaMultiply k c≫XModLambdaN.incl (S_0_0 : SyntheticSpectrum) q) at hh
  have hcomm : lambdaMultiply k c≫XModLambdaN.incl (S_0_0 : SyntheticSpectrum) q =
      lambdaMultiply k (quotientClass q c) := by
    simp only [lambdaMultiply,quotientClass,Category.assoc]
  rw [hcomm] at hh
  exact hh


end
end KIP126.Main.Internal.AlphaOne
end
