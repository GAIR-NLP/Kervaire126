module

public import KIP126.Main.SectionSeven.Predicates
public import KIP126.ProofTools.Representatives
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.QuotientCalculus

/-! Infinite- and finite-window comparisons for the ν-target argument. -/
@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature KIP126.Main.Internal
open KIP126.ProofTools KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section

theorem boundaries_le_permanent_cycles (X : AdamsObject) (p : ℤ × ℤ) (b : ℤ) :
    boundaries background X b p ≤ permanentCycles background X p := by
  rintro x ⟨z,rfl⟩
  let P := (background.classical.obj (X.obj background.auxiliary)).ssData p
  let i : P.B (↑(b-1).toNat) ≤ P.Z ⊤ := (P.B_mono le_top).trans (P.B_le_Z ⊤)
  refine ⟨Subobject.ofLE _ _ i z,?_⟩
  change (Subobject.ofLE _ _ i ≫ cycleLabel background X ⊤ p) z = _
  simp only [cycleLabel,boundaryLabel,P,←Category.assoc,Subobject.ofLE_comp_ofLE]

theorem permanent_target_label_iff (X : AdamsObject) (s t : ℤ) (k : ℕ)
    (y : permanentCycles background X (s,t))
    (e : ((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (s,t,t-k)).eInfty) :
    HasInfinityRepresentative _ 2 (s,t,t-k) (targetNuLabel background X s t k y.val) e ↔
      KIP126.Literature.Standard.infinityNuWindow X (s,t) (t-k) (by omega) e =
        subquotientClass (permanentCycles background X (s,t))
          (boundaries background X (1+t-(t-k)) (s,t)) y := by
  have hlabel : nuWeightLabel background X s t (t-k) (by omega) y.val =
      targetNuLabel background X s t k y.val := by
    have hk : (t-(t-k)).toNat = k := by omega
    have transport (a b : ℕ) (hab : a=b) (h : (s,t,t-a)=(s,t,t-b)) :
        regradeE2 h (targetNuLabel background X s t a y.val) = targetNuLabel background X s t b y.val := by
      subst b
      rfl
    exact transport _ k hk _
  have h := KIP126.Literature.Standard.eInfinity_nu_labels X s t (t-k) (by omega) y.val e
  rw [hlabel] at h
  exact h.trans ⟨fun ⟨_,he⟩ => he,fun he => ⟨y.property,he⟩⟩

theorem sphere_boundary_detects_zero (k : ℕ) (s t : ℤ)
    (x : background.classical.sphere.Page 2 (s,t))
    (hx : x ∈ boundaries background .sphere (1+k) (s,t)) :
    Detects (background.convergence .sphere) (s,t,t-k) (sphereLabel s t k x) 0 := by
  let z : permanentCycles background .sphere (s,t) :=
    ⟨x,boundaries_le_permanent_cycles .sphere (s,t) (1+k) hx⟩
  have hz : subquotientClass _ (boundaries background .sphere (1+t-(t-k)) (s,t)) z = 0 := by
    apply (subquotientClass_eq_zero_iff _ _ _).mpr
    change x ∈ boundaries background .sphere (1+t-(t-k)) (s,t)
    rwa [show 1+t-(t-k)=(1:ℤ)+k by omega]
  have hn : HasInfinityRepresentative (background.family.nu background.nu SphereSpectrum) 2 (s,t,t-k)
      (targetNuLabel background .sphere s t k x) 0 := by
    apply (permanent_target_label_iff .sphere s t k z 0).mpr
    simpa only [map_zero] using hz.symm
  have h := family_infinity_representative_map background.nu.unitIso.hom (s,t,t-k) _ _ hn
  rw [sphere_label_from_nu,map_zero] at h
  exact ⟨0,h,0,map_zero _,by simp only [map_zero]⟩

theorem finite_sphere_boundary_detects_zero (q k : ℕ) (hq : 0 < q) (hk : k < q)
    (s t : ℤ) (x : background.classical.sphere.Page 2 (s,t))
    (hx : x ∈ boundaries background .sphere (1+k) (s,t)) :
    Detects (background.convergence (.quotient q .sphere)) (s,t,t-k) (quotientLabel q s t k x) 0 := by
  let z : cycles background .sphere ((q:ℤ)-t+(t-k)) (s,t) :=
    ⟨x,boundaries_le_cycles background .sphere (s,t) (1+k) _ hx⟩
  have hz : subquotientClass _ (boundaries background .sphere (1+t-(t-k)) (s,t)) z = 0 := by
    apply (subquotientClass_eq_zero_iff _ _ _).mpr
    change x ∈ boundaries background .sphere (1+t-(t-k)) (s,t)
    rwa [show 1+t-(t-k)=(1:ℤ)+k by omega]
  have hn : HasInfinityRepresentative (background.family.quotient (background.nu.functor.obj SphereSpectrum) q)
      2 (s,t,t-k) (finiteTargetLabel background .sphere q s t k x) 0 := by
    apply (finite_target_label_iff .sphere q hq s t k hk z 0).mpr
    simpa only [map_zero] using hz.symm
  have h := family_infinity_representative_map (XModLambdaN.map background.nu.unitIso.hom q)
    (s,t,t-k) _ _ hn
  rw [sphere_quotient_label_from_nu,map_zero] at h
  exact ⟨0,h,0,map_zero _,by simp only [map_zero]⟩

theorem sphere_infinity_zero_of_permanent_quotient (s t w : ℤ) (hw : 0 ≤ t-w)
    (hc : Subsingleton (PermanentQuotient background .sphere (1+t-w) (s,t))) :
    IsZero (((background.family.obj (S_0_0 : SyntheticSpectrum)).sequence.ssData (s,t,w)).eInfty) := by
  let e := KIP126.Literature.Standard.infinityNuWindow .sphere (s,t) w (by omega)
  haveI := hc
  haveI : Subsingleton (((background.family.nu background.nu SphereSpectrum).sequence.ssData (s,t,w)).eInfty) :=
    e.injective.subsingleton
  have hn := ModuleCat.isZero_of_subsingleton
    (((background.family.nu background.nu SphereSpectrum).sequence.ssData (s,t,w)).eInfty)
  let f := (background.family.map background.nu.unitIso.hom).eInftyMap (s,t,w)
  let g := (background.family.map background.nu.unitIso.inv).eInftyMap (s,t,w)
  have hgf : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←SyntheticAdamsFamily.map_comp,
      Iso.inv_hom_id,SyntheticAdamsFamily.map_id,SpectralSequenceMorphism.eInftyMap_id]
  apply (IsZero.iff_id_eq_zero _).mpr
  exact hgf.symm.trans (by rw [hn.eq_of_src f 0,comp_zero])

theorem nu_target_sphere_gap
    (hpage : Subsingleton (background.classical.sphere.Page 5 (13,138)))
    (a : BiHom 125 135 (S_0_0 : SyntheticSpectrum)) :
    FiltrationAtLeast background.syntheticTower 13 a ↔ FiltrationAtLeast background.syntheticTower 14 a := by
  apply filtration_iff_of_infinity_zero (background.convergence .sphere) 13 14 125 135 (by decide)
  intro j hj hj'
  have : j=13 := by omega
  subst j
  apply sphere_infinity_zero_of_permanent_quotient 13 138 135 (by decide)
  apply subsingleton_of_forall_eq 0
  intro z
  obtain ⟨z,rfl⟩ := Quotient.exists_rep z
  apply (subquotientClass_eq_zero_iff _ _ _).mpr
  have hc := permanentCycles_le_cycles background .sphere (13,138) 4 z.property
  obtain ⟨zr,hzr⟩ := (isCycle_iff_reaches background .sphere 5 (by decide) (13,138) z.val).mp ⟨by decide,hc⟩
  haveI : Subsingleton ((background.classical.obj (AdamsObject.sphere.obj background.auxiliary)).Page 5 (13,138)) := hpage
  have hz : zr=0 := Subsingleton.elim _ _
  rw [hz] at hzr
  exact represents_zero_mem_boundary background .sphere 5 (13,138) z.val hzr

theorem lambda_filtration_preserved {A : SyntheticSpectrum} {m w : ℤ}
    (k : ℕ) (s : ℤ) (a : BiHom m w A)
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    FiltrationAtLeast background.syntheticTower s (lambdaMultiply k a) := by
  obtain ⟨z,hz⟩ := ha
  refine ⟨lambdaMultiply k z,?_⟩
  change lambdaMultiply k z ≫ (background.syntheticTower.tower A).projection s = _
  change z ≫ (background.syntheticTower.tower A).projection s = a at hz
  dsimp only [lambdaMultiply]
  simp only [Category.assoc,hz]

end
end KIP126.Main.SectionSeven.Internal
