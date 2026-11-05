module
import all KIP126.Main.SectionSeven.Predicates
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.Selected.DetectionOperations
/-! Reflection through finite-quotient restriction with the specified label transports. -/
@[expose] section
namespace KIP126.Main.Internal.FiniteReflection
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.Main.SectionSeven KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
theorem detects_reflect
    (X Y : SyntheticObject) (f : X.obj background.nu background.auxiliary ⟶ Y.obj background.nu background.auxiliary)
    (i : Tridegree)
    (hi : Function.Injective (((background.family.functor.map f).eInftyMap i).hom))
    (x : (background.family.obj (X.obj background.nu background.auxiliary)).E₂ i)
    (e : ((background.family.obj (X.obj background.nu background.auxiliary)).sequence.ssData i).eInfty)
    (he : HasInfinityRepresentative (background.family.obj (X.obj background.nu background.auxiliary)) 2 i x e)
    (a : BiHom (i.2.1-i.1) i.2.2 (X.obj background.nu background.auxiliary))
    (ha : FiltrationAtLeast (background.syntheticTower) i.1 a)
    (hf : DetectsNonzero (background.convergence Y) i (familyPageMap background.family f 2 i x) (a≫f)) :
    DetectsNonzero (background.convergence X) i x a := by
  refine ⟨KIP126.ProofTools.Internal.detects_reflect X Y f i hi x e he a ha hf.1,e,he,?_⟩
  intro he0
  obtain ⟨en,hen,hn⟩ := hf.2
  have hh := hen.unique (family_infinity_representative_map f i x e he)
  exact hn (hh.trans (by rw [he0,map_zero]))
theorem finite_nu_rho_injective (i j : ℕ) (hi : 0 < i) (hij : i ≤ j) (s t w : ℤ)
    (hw : 0≤t-w ∧ t-w < i) : Function.Injective
      ((background.family.map ((background.quotients.tower (background.nu.functor.obj SphereSpectrum)).rho i j hij)).eInftyMap (s,t,w)) :=
  rho_infty_injective .sphere i j hi hij s t w hw.2
theorem finite_sphere_rho_injective (i j : ℕ) (hi : 0 < i) (hij : i ≤ j) (s t w : ℤ)
    (hw : 0≤t-w ∧ t-w < i) :
    Function.Injective (((background.family.functor.map
      ((background.quotients.tower (S_0_0 : SyntheticSpectrum)).rho i j hij)).eInftyMap (s,t,w)).hom) := by
  intro a b hab
  let gj := XModLambdaN.map background.nu.unitIso.inv j
  let fj := XModLambdaN.map background.nu.unitIso.hom j
  let gi := XModLambdaN.map background.nu.unitIso.inv i
  let r := (background.quotients.tower (S_0_0 : SyntheticSpectrum)).rho i j hij
  let r' := (background.quotients.tower (background.nu.functor.obj SphereSpectrum)).rho i j hij
  have hcomm : r≫gi=gj≫r' := (background.quotients.natural background.nu.unitIso.inv).rho_naturality hij
  have hgf : gj≫fj=𝟙 _ := by
    dsimp only [gj,fj]
    rw [←background.quotients.functoriality.map_comp,Iso.inv_hom_id,background.quotients.functoriality.map_id]
  have heq : (background.family.functor.map gj).eInftyMap (s,t,w) a=
      (background.family.functor.map gj).eInftyMap (s,t,w) b := by
    apply finite_nu_rho_injective i j hi hij s t w hw
    have hh := congrArg (fun c=>(background.family.functor.map gi).eInftyMap (s,t,w) c) hab
    change ((background.family.functor.map r).eInftyMap (s,t,w)≫
      (background.family.functor.map gi).eInftyMap (s,t,w)) a =
      ((background.family.functor.map r).eInftyMap (s,t,w)≫
        (background.family.functor.map gi).eInftyMap (s,t,w)) b at hh
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hcomm,
      Functor.map_comp,SpectralSequenceMorphism.eInftyMap_comp] at hh
    exact hh
  have hh := congrArg (fun c=>(background.family.functor.map fj).eInftyMap (s,t,w) c) heq
  change ((background.family.functor.map gj).eInftyMap (s,t,w)≫
      (background.family.functor.map fj).eInftyMap (s,t,w)) a =
      ((background.family.functor.map gj).eInftyMap (s,t,w)≫
        (background.family.functor.map fj).eInftyMap (s,t,w)) b at hh
  rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
    CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id] at hh
  exact hh
theorem finite_sphere_infinity_exists
    (q : ℕ) (hq : 0<q) (k : ℕ) (hk : k<q) (s t : ℤ)
    (x : background.classical.sphere.Page 2 (s,t))
    (hx : x∈cycles background .sphere ((q:ℤ)-k) (s,t)) :
    ∃ e : ((background.family.quotient (S_0_0 : SyntheticSpectrum) q).sequence.ssData (s,t,t-k)).eInfty,
      HasInfinityRepresentative (background.family.quotient (S_0_0 : SyntheticSpectrum) q) 2 (s,t,t-k)
        (quotientLabel q s t k x) e := by
  let P := KIP126.Literature.Standard.infinityFiniteWindow .sphere q hq (s,t) (t-k)
    (by constructor <;> omega)
  let y : cycles background .sphere ((q:ℤ)-t+(t-k)) (s,t) :=
    ⟨x,by rw [show (q:ℤ)-t+(t-k)=(q:ℤ)-k by omega]; exact hx⟩
  let e := P.symm (subquotientClass _ _ y)
  have he : HasInfinityRepresentative (background.family.quotient (background.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
      (finiteTargetLabel background .sphere q s t k x) e := by
    apply (finite_target_label_iff .sphere q hq s t k hk y e).mpr
    exact P.apply_symm_apply _
  let f := XModLambdaN.map background.nu.unitIso.hom q
  let g := XModLambdaN.map background.nu.unitIso.inv q
  have hgf : g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←background.quotients.functoriality.map_comp,Iso.inv_hom_id,background.quotients.functoriality.map_id]
  have hfg : f≫g=𝟙 _ := by
    dsimp only [f,g]
    rw [←background.quotients.functoriality.map_comp,Iso.hom_inv_id,background.quotients.functoriality.map_id]
  let e' := (background.family.functor.map f).eInftyMap (s,t,t-k) e
  have hel : familyPageMap background.family f 2 (s,t,t-k) (finiteTargetLabel background .sphere q s t k x)=quotientLabel q s t k x :=
    sphere_quotient_label_from_nu q k s t x
  have he' : HasInfinityRepresentative (background.family.quotient (S_0_0 : SyntheticSpectrum) q) 2 (s,t,t-k)
      (quotientLabel q s t k x) e' := by
    have hh := family_infinity_representative_map f (s,t,t-k) _ _ he
    rw [hel] at hh
    exact hh
  exact ⟨e',he'⟩
theorem finite_sphere_rho_label (i j k : ℕ) (hij : i ≤ j) (s t : ℤ)
    (x : background.classical.sphere.Page 2 (s,t)) :
    familyPageMap background.family ((background.quotients.tower (S_0_0 : SyntheticSpectrum)).rho i j hij) 2 (s,t,t-k)
      (quotientLabel j s t k x)=quotientLabel i s t k x := by
  let rho := (background.quotients.tower (S_0_0 : SyntheticSpectrum)).rho i j hij
  change familyPageMap background.family rho 2 (s,t,t-k)
    (familyPageMap background.family (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) j) 2 (s,t,t-k) (background.comparison.sphereE2 s t k x))=_
  calc
    _ = familyPageMap background.family (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) j≫rho) 2 (s,t,t-k) (background.comparison.sphereE2 s t k x) :=
      ConcreteCategory.congr_hom (family_page_comp (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) j) rho 2 (s,t,t-k)) _
    _ = quotientLabel i s t k x := by
      dsimp only [rho]
      rw [FiniteLambdaQuotientTower.rho_quotient]
      rfl
theorem finite_sphere_detection_reflect (i j k : ℕ) (hi : 0 < i) (hij : i ≤ j) (hk : k < i) (s t : ℤ)
    (x : background.classical.sphere.Page 2 (s,t))
    (hx : x∈cycles background .sphere ((j:ℤ)-k) (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : SyntheticSpectrum) j))
    (ha : FiltrationAtLeast (background.syntheticTower) s a)
    (hf : FiniteDetected i hi s t k x (a≫(background.quotients.tower (S_0_0 : SyntheticSpectrum)).rho i j hij)) :
    FiniteDetected j (by omega) s t k x a := by
  obtain ⟨e,he⟩ := finite_sphere_infinity_exists j (by omega) k (by omega) s t x hx
  apply detects_reflect (.quotient j .sphere) (.quotient i .sphere)
    ((background.quotients.tower (S_0_0 : SyntheticSpectrum)).rho i j hij) (s,t,t-k)
    (finite_sphere_rho_injective i j hi hij s t (t-k) (by constructor <;> omega))
    (quotientLabel j s t k x) e he a ha
  change DetectsNonzero (background.convergence (.quotient i .sphere)) (s,t,t-k)
    (familyPageMap background.family ((background.quotients.tower (S_0_0 : SyntheticSpectrum)).rho i j hij) 2 (s,t,t-k)
      (quotientLabel j s t k x)) (a≫(background.quotients.tower (S_0_0 : SyntheticSpectrum)).rho i j hij)
  rw [finite_sphere_rho_label i j k hij s t x]
  exact hf
end
end KIP126.Main.Internal.FiniteReflection
