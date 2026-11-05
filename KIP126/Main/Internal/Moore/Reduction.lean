module

import all KIP126.Main.Internal.AlphaOne.ErrorFiltration
import all KIP126.Main.Internal.AlphaOne.Layers
import all KIP126.Main.Internal.AlphaOne.Corrections
import all KIP126.Main.Internal.AlphaOne.FiniteWindow
import KIP126.Main.Conditions
import all KIP126.Main.ClassicalReduction
import all KIP126.Main.SectionSeven.TodaNonempty
import all KIP126.Main.SectionSeven.AnyYError
import all KIP126.Main.SectionSeven.AnyYTarget
import all KIP126.Main.SectionSeven.ThetaToda
import all KIP126.Main.SectionSeven.WeakRepresentative
import all KIP126.Main.SectionSeven.WeakYDetection
import all KIP126.Main.SectionSeven.NuTargetFull
import all KIP126.Main.SectionSeven.CofiberRigidity
import all KIP126.Main.SectionSeven.NormalizedNu
import all KIP126.Main.Internal.NuNinth.Assembly
import all KIP126.Main.DifferentialCriterion
import KIP126.SSComputation.Standard

/-! Reduction from a shifted Moore-spectrum representative to fixed-sphere
permanence under the two specified Moore-spectrum survival hypotheses. -/
@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Core.Algebra
open KIP126.Main.SectionSeven KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.Main.Internal KIP126.Main.Internal.AlphaOne KIP126.Main.Internal.Selected
open KIP126.Computation.Table
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem detects_exists_of_infinity
    {X : SyntheticSpectrum} (c : SyntheticTowerConvergence background.syntheticTower X)
    (i : Tridegree) (x : (background.family.obj X).E₂ i)
    (e : ((background.family.obj X).sequence.ssData i).eInfty)
    (hx : HasInfinityRepresentative (background.family.obj X) 2 i x e) :
    ∃ a : BiHom (i.2.1-i.1) i.2.2 X, Detects c i x a := by
  classical
  let F := background.syntheticTower.filtration X
  haveI : Epi (F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2)) :=
    inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨a,ha⟩ :=
    (ModuleCat.epi_iff_surjective (F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2))).mp
      inferInstance ((c.identification i).hom e)
  exact ⟨(F.F i.1 (i.2.1-i.1,i.2.2)).arrow a,e,hx,a,rfl,ha.symm⟩

private theorem shifted_finite_sphere_detection_exists
    (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
    (x : background.classical.sphere.Page 2 (s,t))
    (hx : x∈KIP126.Literature.cycles background .sphere ((q:ℤ)-k) (s,t)) :
    ∃ a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : SyntheticSpectrum) q),
      Detects (background.convergence (.quotient q .sphere)) (s,t,t-k)
        (quotientLabel q s t k x) a := by
  classical
  let P := KIP126.Literature.Standard.infinityFiniteWindow .sphere q hq (s,t) (t-k)
    (by constructor <;> omega)
  let y : KIP126.Literature.cycles background .sphere ((q:ℤ)-t+(t-k)) (s,t) :=
    ⟨x,by simpa only [sub_add_sub_cancel] using hx⟩
  let e := P.symm (KIP126.Literature.subquotientClass _ _ y)
  have he : HasInfinityRepresentative
      (background.family.quotient (background.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
      (finiteTargetLabel background .sphere q s t k x) e := by
    apply (finite_target_label_iff .sphere q hq s t k hkq y e).mpr
    exact P.apply_symm_apply _
  let f := XModLambdaN.map background.nu.unitIso.hom q
  let e' := (background.family.functor.map f).eInftyMap (s,t,t-k) e
  have hel : familyPageMap background.family f 2 (s,t,t-k)
      (finiteTargetLabel background .sphere q s t k x)=quotientLabel q s t k x :=
    sphere_quotient_label_from_nu q k s t x
  have he' : HasInfinityRepresentative
      (background.family.quotient (S_0_0 : SyntheticSpectrum) q) 2 (s,t,t-k)
      (quotientLabel q s t k x) e' := by
    have hh := family_infinity_representative_map f (s,t,t-k) _ _ he
    rw [hel] at hh
    exact hh
  exact detects_exists_of_infinity (background.convergence (.quotient q .sphere))
    (s,t,t-k) _ e' he'

private theorem shifted_detected_rho
    (i j k : ℕ) (hij : i≤j) (s t : ℤ)
    (x : background.classical.sphere.Page 2 (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : SyntheticSpectrum) j))
    (ha : Detects (background.convergence (.quotient j .sphere)) (s,t,t-k)
      (quotientLabel j s t k x) a) :
    Detects (background.convergence (.quotient i .sphere)) (s,t,t-k)
      (quotientLabel i s t k x)
      (a≫(background.quotients.tower S_0_0).rho i j hij) := by
  let rho := (background.quotients.tower S_0_0).rho i j hij
  have hl : familyPageMap background.family rho 2 (s,t,t-k)
      (quotientLabel j s t k x)=quotientLabel i s t k x := by
    change familyPageMap background.family rho 2 (s,t,t-k)
      (familyPageMap background.family (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) j)
        2 (s,t,t-k) (background.comparison.sphereE2 s t k x))=_
    calc
      _ = familyPageMap background.family
          (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) j≫rho) 2 (s,t,t-k)
          (background.comparison.sphereE2 s t k x) :=
        ConcreteCategory.congr_hom
          (family_page_comp (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) j) rho
            2 (s,t,t-k)) _
      _ = quotientLabel i s t k x := by
        dsimp only [rho]
        rw [FiniteLambdaQuotientTower.rho_quotient]
        rfl
  exact hl ▸ detects_map (.quotient j .sphere) (.quotient i .sphere) rho
    (s,t,t-k) _ a ha

private theorem beta_detected_pair
    (V : background.classical.sphere.Page 2 (9,132))
    (hV : V∈KIP126.Literature.cycles background .sphere 8 (9,132)) :
    ∃ b11 : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11),
      Detects (background.convergence (.quotient 11 .sphere)) (9,132,129)
        (quotientLabel 11 9 132 3 V) b11 ∧
      Detects (background.convergence (.quotient 9 .sphere)) (9,132,129)
        (quotientLabel 9 9 132 3 V)
        (b11≫(background.quotients.tower S_0_0).rho 9 11 (by decide)) := by
  obtain ⟨b,hb⟩ := shifted_finite_sphere_detection_exists
    11 3 (by decide) (by decide) 9 132 V hV
  exact ⟨b,hb,shifted_detected_rho 9 11 3 (by decide) 9 132 V b hb⟩

private theorem beta_eta_error_filtration_thirteen
    (U : background.classical.sphere.Page 2 (10,134))
    (V : background.classical.sphere.Page 2 (9,132))
    (source : background.classical.sphere.Page 2 (8,133))
    (hU : U∈KIP126.Literature.cycles background .sphere 8 (10,134))
    (hd : HasDifferential background.classical.sphere 2 (8,133) (10,134)
      source (KIP126.Computation.Standard.product (r := (10,134))
        KIP126.Computation.Standard.h1 V+U))
    (h11 : Subsingleton (background.classical.sphere.Page 5 (11,135)))
    (h12 : Subsingleton (background.classical.sphere.Page 4 (12,136)))
    (b : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (hb : Detects (background.convergence (.quotient 11 .sphere)) (9,132,129)
      (quotientLabel 11 9 132 3 V) b)
    (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum))
    (hu : SphereDetected 10 134 0 U u) :
    FiltrationAtLeast background.syntheticTower 13
      ((show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11) from
          sphereAction KIP126.Literature.Standard.eta b)-
        (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11) from
          lambdaMultiply 3 (quotientClass 11 u))) := by
  classical
  have hlabel := Selected.sphere_zero_weight_label_10_134 U u hu.1
  have he := background.sphereDetectionCompatible.homotopy_lambda 1 2 0
    KIP126.Literature.Standard.eta
  have hη := KIP126.Literature.Standard.eta_label
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hη
  rw [Selected.lambda_zero_1_2,hη] at he
  have hp : Detects (background.convergence (.quotient 11 .sphere)) (10,134,131)
      (quotientLabel 11 10 134 3 (KIP126.Computation.Standard.product (r := (10,134))
        KIP126.Computation.Standard.h1 V))
      (sphereAction KIP126.Literature.Standard.eta b) :=
    KIP126.Literature.Standard.finite_action 11 (by decide) 1 2 9 132 0 3
      KIP126.Computation.Standard.h1 V KIP126.Literature.Standard.eta b he hb
  have hu3 := background.sphereDetectionCompatible.homotopy_lambda 10 134 3 u
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hlabel
  rw [hlabel] at hu3
  have huq := detects_map .sphere (.quotient 11 .sphere)
    (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 11) (10,134,131) _
    (lambdaMultiply 3 u) hu3
  have hcomm : lambdaMultiply 3 u≫XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 11=
      lambdaMultiply 3 (quotientClass 11 u) := by
    simp only [lambdaMultiply,quotientClass,Category.assoc]
  change Detects (background.convergence (.quotient 11 .sphere)) (10,134,131)
    (quotientLabel 11 10 134 3 U)
    (lambdaMultiply 3 u≫XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 11) at huq
  rw [hcomm] at huq
  have hU2 : U+U=0 := by
    apply (KIP126.Computation.Standard.coordinates 10 134 (by decide)).injective
    rw [map_add,map_zero]
    ext i
    exact CharTwo.add_self_eq_zero _
  have hneg : -U=U := neg_eq_iff_add_eq_zero.mpr hU2
  have hd0 := differential_target_later_zero
    (le_of_eq (background.classical.firstPage _)) (by decide : (2:ℤ)<3) hd
  have hbound := represents_zero_mem_boundary background .sphere 3 (10,134) _ hd0
  have hbound4 : KIP126.Computation.Standard.product (r := (10,134))
      KIP126.Computation.Standard.h1 V-U∈
      KIP126.Literature.boundaries background .sphere 4 (10,134) := by
    rw [sub_eq_add_neg,hneg]
    exact KIP126.Literature.boundaries_monotone background .sphere (10,134)
      (by decide : (2:ℤ)≤4) hbound
  have hprod : KIP126.Computation.Standard.product (r := (10,134))
      KIP126.Computation.Standard.h1 V∈
      KIP126.Literature.cycles background .sphere 8 (10,134) := by
    have hboundcycle := KIP126.ProofTools.Internal.Mahowald.boundaries_le_cycles
      background .sphere (10,134) 4 8 hbound4
    have hsum := (KIP126.Literature.cycles background .sphere 8 (10,134)).add_mem
      hboundcycle hU
    simpa only [sub_add_cancel] using hsum
  apply (alpha_error_filtration_gap h11 h12 _).mp
  exact finite_boundary_detects_sub_filtration _ U hprod hU hbound4 _ _ hp huq

private theorem beta_eta_corrections
    (b : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (hb : Detects (background.convergence (.quotient 11 .sphere)) (9,132,129)
      (quotientLabel 11 9 132 3 KIP126.Computation.Standard.V) b) :
    ∀ u : BiHom 124 134 (S_0_0 : SyntheticSpectrum),
      SphereDetected 10 134 0 KIP126.Computation.Standard.U u →
      ∃ (a2 : BiHom 124 137 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
        (a3 : BiHom 125 140 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)),
        sphereAction KIP126.Literature.Standard.eta
            (b≫(background.quotients.tower S_0_0).rho 9 11 (by decide))=
          (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from
            lambdaMultiply 3 (quotientClass 9 u))+
          (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from
            lambdaMultiply 6 a2) ∧
        sphereAction KIP126.Literature.Standard.eta a2=lambdaMultiply 1 a3 := by
  have hpc : IsPermanentCycle background.classical.sphere (13,137)
      KIP126.Computation.Standard.correction := by
    obtain ⟨z,hz,_⟩ := KIP126.Computation.Standard.correction_permanent
    exact ⟨z,hz⟩
  obtain ⟨hp14,hp15⟩ := full_staircase_high_cycles
  obtain ⟨c13,hc13⟩ := sphere_permanent_first_quotient_lift 13 137
    KIP126.Computation.Standard.correction hpc
  obtain ⟨c14,hc14⟩ := sphere_permanent_first_quotient_lift 14 138 _ hp14
  obtain ⟨c15,hc15⟩ := sphere_permanent_first_quotient_lift 15 139 _ hp15
  obtain ⟨d,hd⟩ := eta_correction_lambda_divisible KIP126.Literature.Standard.eta
    c13 KIP126.Computation.Standard.correction KIP126.Literature.Standard.eta_label
    hc13 KIP126.Computation.Standard.h1_correction_zero
  have hU : KIP126.Computation.Standard.U∈KIP126.Literature.cycles
      background .sphere 8 (10,134) := by
    apply KIP126.Literature.permanentCycles_le_cycles background .sphere (10,134) 8
    apply (permanent_cycle_iff_mem .sphere (10,134) _).mp
    obtain ⟨z,hz,_⟩ := KIP126.Computation.Standard.u_permanent
    exact ⟨z,hz⟩
  have hd2 := KIP126.Computation.Standard.d2_x125_8.toHasDifferential
  change HasDifferential background.classical.sphere 2 (8,133) (10,134) _
    (KIP126.Computation.Standard.product (r := (10,134)) KIP126.Computation.Standard.h1
      KIP126.Computation.Standard.V+KIP126.Computation.Standard.U) at hd2
  intro u hu
  have herr := beta_eta_error_filtration_thirteen _ _ _ hU hd2
    KIP126.Computation.Standard.e5_stem124_af11
    KIP126.Computation.Standard.e4_stem124_af12 b hb u hu
  obtain ⟨b13,b14,b15,hbits⟩ := alpha_three_layer_restriction c13 hc13 c14 hc14 c15 hc15 _ herr
  obtain ⟨a2,a3,hs,heta⟩ := alpha_correction_sum KIP126.Literature.Standard.eta
    c13 c14 c15 d hd b13 b14 b15
  refine ⟨a2,a3,?_,heta⟩
  have hsum := hbits.trans hs
  have hrho :
      ((show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11) from
          sphereAction KIP126.Literature.Standard.eta b)-
        (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11) from
          lambdaMultiply 3 (quotientClass 11 u)))≫
          (background.quotients.tower S_0_0).rho 9 11 (by decide)=
      (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from
        sphereAction KIP126.Literature.Standard.eta
          (b≫(background.quotients.tower S_0_0).rho 9 11 (by decide)))-
        (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from
          lambdaMultiply 3 (quotientClass 9 u)) := by
    simp only [Preadditive.sub_comp,lambdaMultiply,sphereAction,quotientClass,
      Category.assoc,FiniteLambdaQuotientTower.rho_quotient]
  rw [hrho] at hsum
  exact sub_eq_iff_eq_add'.mp hsum

private theorem beta_h0_rho_zero_of_filtration_sixteen
    (b : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (hb : FiltrationAtLeast background.syntheticTower 16
      (sphereAction KIP126.Literature.Standard.syntheticH0 b)) :
    sphereAction KIP126.Literature.Standard.syntheticH0
      (b≫(background.quotients.tower S_0_0).rho 9 11 (by decide))=0 := by
  apply sphere_quotient_high_filtration_zero 9 (by decide) 123 130 16 (by decide)
  simpa only [sphereAction,Category.assoc] using
    Selected.map_filtration (.quotient 11 .sphere) (.quotient 9 .sphere)
      ((background.quotients.tower S_0_0).rho 9 11 (by decide))
      (sphereAction KIP126.Literature.Standard.syntheticH0 b) hb

private theorem stem123_upper_low_pages
    :
    Subsingleton ((Normalized.sphere).Page 6 (12,135)) ∧
    Subsingleton ((Normalized.sphere).Page 4 (13,136)) ∧
    Subsingleton ((Normalized.sphere).Page 4 (14,137)) := by
  classical
  let E := Normalized.sphere
  obtain ⟨e16_139,he16_139⟩ := Normalized.basis_correct ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_139
  change ∀i : Fin 3, e16_139.symm (Finsupp.single i 1) = Normalized.basis .sphere 16 139 i.val at he16_139
  obtain ⟨e18_140,he18_140⟩ := Normalized.basis_correct ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl))
  change E.Page 2 (18,140) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e18_140
  change ∀i : Fin 3, e18_140.symm (Finsupp.single i 1) = Normalized.basis .sphere 18 140 i.val at he18_140
  obtain ⟨e15_138,he15_138⟩ := Normalized.basis_correct ⟨.sphere, 15, 138, ["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e15_138
  change ∀i : Fin 3, e15_138.symm (Finsupp.single i 1) = Normalized.basis .sphere 15 138 i.val at he15_138
  obtain ⟨e14_137,he14_137⟩ := Normalized.basis_correct ⟨.sphere, 14, 137, ["23,1,181,1", "0,1,418,1", "0,3,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 215) (by rfl))
  change E.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_137
  change ∀i : Fin 3, e14_137.symm (Finsupp.single i 1) = Normalized.basis .sphere 14 137 i.val at he14_137
  obtain ⟨e13_136,he13_136⟩ := Normalized.basis_correct ⟨.sphere, 13, 136, ["418,1", "417,1", "0,2,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 207) (by rfl))
  change E.Page 2 (13,136) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e13_136
  change ∀i : Fin 3, e13_136.symm (Finsupp.single i 1) = Normalized.basis .sphere 13 136 i.val at he13_136
  obtain ⟨e12_135,he12_135⟩ := Normalized.basis_correct ⟨.sphere, 12, 135, ["408,1", "0,1,386,1", "0,2,69,1,80,1"]⟩ (by
    exact List.mem_of_getElem? (i := 199) (by rfl))
  change E.Page 2 (12,135) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e12_135
  change ∀i : Fin 3, e12_135.symm (Finsupp.single i 1) = Normalized.basis .sphere 12 135 i.val at he12_135
  obtain ⟨e17_139,he17_139⟩ := Normalized.basis_correct ⟨.sphere, 17, 139, ["13,3,76,1", "0,1,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 237) (by rfl))
  change E.Page 2 (17,139) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e17_139
  change ∀i : Fin 2, e17_139.symm (Finsupp.single i 1) = Normalized.basis .sphere 17 139 i.val at he17_139
  obtain ⟨e16_138,he16_138⟩ := Normalized.basis_correct ⟨.sphere, 16, 138, ["437,1", "23,1,189,1", "0,1,424,1"]⟩ (by
    exact List.mem_of_getElem? (i := 229) (by rfl))
  change E.Page 2 (16,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_138
  change ∀i : Fin 3, e16_138.symm (Finsupp.single i 1) = Normalized.basis .sphere 16 138 i.val at he16_138
  have h324 : HasDifferential E 3 (13,137) (16,139) (Normalized.basis .sphere 13 137 2) (Normalized.basis .sphere 16 139 0) := stem123_middle_certificate_d3_s13_t137_basis2
  have h366 : HasDifferential E 2 (14,138) (16,139) (Normalized.basis .sphere 14 138 1) (Normalized.basis .sphere 16 139 1 + Normalized.basis .sphere 16 139 2) := stem123_middle_certificate_d2_s14_t138_basis1
  have h367 : HasDifferential E 2 (14,138) (16,139) (Normalized.basis .sphere 14 138 0 + Normalized.basis .sphere 14 138 1) (Normalized.basis .sphere 16 139 2) := stem123_middle_certificate_d2_s14_t138_basis0_add_basis1
  have h654 : HasDifferential E 3 (15,138) (18,140) (Normalized.basis .sphere 15 138 2) (Normalized.basis .sphere 18 140 2) := stem123_middle_certificate_d3_s15_t138_basis2
  have h250 : HasDifferential E 5 (10,134) (15,138) (Normalized.basis .sphere 10 134 3) (Normalized.basis .sphere 15 138 1) := stem123_middle_certificate_d5_s10_t134_basis3
  have h277 : HasDifferential E 4 (11,135) (15,138) (Normalized.basis .sphere 11 135 1 + Normalized.basis .sphere 11 135 2) (Normalized.basis .sphere 15 138 0) := stem123_middle_certificate_d4_s11_t135_basis1_add_basis2
  have h339 : HasDifferential E 3 (14,137) (17,139) (Normalized.basis .sphere 14 137 1) (Normalized.basis .sphere 17 139 1) := stem123_middle_certificate_d3_s14_t137_basis1
  have h340 : HasDifferential E 3 (14,137) (17,139) (Normalized.basis .sphere 14 137 0) (Normalized.basis .sphere 17 139 0) := stem123_middle_certificate_d3_s14_t137_basis0
  have h304 : HasDifferential E 2 (12,136) (14,137) (Normalized.basis .sphere 12 136 2) (Normalized.basis .sphere 14 137 2) := stem123_middle_certificate_d2_s12_t136_basis2
  have h319 : HasDifferential E 3 (13,136) (16,138) (Normalized.basis .sphere 13 136 1) (Normalized.basis .sphere 16 138 1) := stem123_middle_certificate_d3_s13_t136_basis1
  have h320 : HasDifferential E 3 (13,136) (16,138) (Normalized.basis .sphere 13 136 0) (Normalized.basis .sphere 16 138 0 + Normalized.basis .sphere 16 138 2) := stem123_middle_certificate_d3_s13_t136_basis0
  have h278 : HasDifferential E 2 (11,135) (13,136) (Normalized.basis .sphere 11 135 2) (Normalized.basis .sphere 13 136 2) := stem123_middle_certificate_d2_s11_t135_basis2
  have h297 : HasDifferential E 3 (9,133) (12,135) (Normalized.basis .sphere 9 133 1 + Normalized.basis .sphere 9 133 2) (Normalized.basis .sphere 12 135 0) := stem123_middle_certificate_d3_s9_t133_basis1_add_basis2
  have h298 : HasDifferential E 3 (9,133) (12,135) (Normalized.basis .sphere 9 133 0 + Normalized.basis .sphere 9 133 2) (Normalized.basis .sphere 12 135 1 + Normalized.basis .sphere 12 135 2) := stem123_middle_certificate_d3_s9_t133_basis0_add_basis2
  have h299 : HasDifferential E 5 (7,131) (12,135) (Normalized.basis .sphere 7 131 1) (Normalized.basis .sphere 12 135 2) := stem123_middle_certificate_d5_s7_t131_basis1
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have d2_16 : E.d 2 (16,139)=0 := by
    obtain ⟨_,_,y0,_,hy0,_⟩ := h324
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2;omega)
      (by decide : (2:ℤ)<3) (hrep2 _) ⟨y0,hy0⟩
    have d12 : E.d 2 (16,139) (Normalized.basis .sphere 16 139 1 + Normalized.basis .sphere 16 139 2)=0 := by
      have hd := h366.eq_on_page_two.2
      change E.d 2 (14,138) _ = _ at hd
      rw [←hd]
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
    have d2 : E.d 2 (16,139) (Normalized.basis .sphere 16 139 2)=0 := by
      have hd := h367.eq_on_page_two.2
      change E.d 2 (14,138) _ = _ at hd
      rw [←hd]
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
    have d1 : E.d 2 (16,139) (Normalized.basis .sphere 16 139 1)=0 := by
      simpa only [map_add,d2,add_zero] using d12
    ext a
    change E.d 2 (16,139) a=0
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤2) e16_139
      (fun i => e16_139.symm (Finsupp.single i 1)) (fun i => hrep2 _) a
    rw [hc,map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    fin_cases i <;> simp only [apply_ite,map_zero,he16_139,d0,d1,d2,ite_self]
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    exact represents_add_tail (by assumption) (by assumption)
  have hsub {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)
  have hif {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (c : F2) (h : RepresentsOnPage E r p x a) :
      RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
    split
    · exact RepresentsOnPage.zero h.1
    · exact h
  have e2_map_zero {p : ℤ × ℤ} {N : ℕ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin N →₀ F2))
      (h : ∀ i, E.d 2 p (e.symm (Finsupp.single i 1))=0) : E.d 2 p=0 := by
    ext a
    change E.d 2 p a=0
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤2) e
      (fun i => e.symm (Finsupp.single i 1)) (fun i => hrep2 _) a
    rw [hc,map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [apply_ite,map_zero,h,ite_self]
  have d2_15 : E.d 2 (15,138)=0 := by
    obtain ⟨_,_,b0,_,hb0,_⟩ := h277
    obtain ⟨_,_,b1,_,hb1,_⟩ := h250
    obtain ⟨_,b2,_,hb2,_,_⟩ := h654
    apply e2_map_zero e15_138
    intro i
    fin_cases i
    · rw [he15_138]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨b0,hb0⟩
    · rw [he15_138]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<5) (hrep2 _) ⟨b1,hb1⟩
    · rw [he15_138]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨b2,hb2⟩
  have d2_14 : E.d 2 (14,137)=0 := by
    obtain ⟨_,b0,_,hb0,_,_⟩ := h340
    obtain ⟨_,b1,_,hb1,_,_⟩ := h339
    apply e2_map_zero e14_137
    intro i
    fin_cases i
    · rw [he14_137]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨b0,hb0⟩
    · rw [he14_137]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨b1,hb1⟩
    · rw [he14_137]
      have hd := h304.eq_on_page_two.2
      change E.d 2 (12,136) _ = _ at hd
      rw [←hd]
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (12,136)) _
  have source14 : Subsingleton (E.Page 4 (14,137)) := by
    apply fourth_zero_of_three_basis (by change (2:ℤ)≤2; omega) e14_137 (Normalized.basis .sphere 17 139 0) (Normalized.basis .sphere 17 139 1)
    · rw [he14_137]
      exact h340
    · rw [he14_137]
      exact h339
    · rw [he14_137]
      exact differential_target_later_zero (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) h304
    · exact d2_15
    all_goals intro hz; have hh := congrArg e17_139 hz
    all_goals simp only [map_add,show Normalized.basis .sphere 17 139 0=e17_139.symm (Finsupp.single 0 1) from (he17_139 0).symm,
      show Normalized.basis .sphere 17 139 1=e17_139.symm (Finsupp.single 1 1) from (he17_139 1).symm,
      LinearEquiv.apply_symm_apply,map_zero] at hh
    · have hh' := congrArg (fun f : Fin 2 →₀ F2 => f 0) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
    · have hh' := congrArg (fun f : Fin 2 →₀ F2 => f 1) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
    · have hh' := congrArg (fun f : Fin 2 →₀ F2 => f 0) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
  have source13 : Subsingleton (E.Page 4 (13,136)) := by
    apply fourth_zero_of_three_basis (by change (2:ℤ)≤2; omega) e13_136 (Normalized.basis .sphere 16 138 0+Normalized.basis .sphere 16 138 2)
      (Normalized.basis .sphere 16 138 1)
    · rw [he13_136]
      exact h320
    · rw [he13_136]
      exact h319
    · rw [he13_136]
      exact differential_target_later_zero (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) h278
    · exact d2_14
    all_goals intro hz; have hh := congrArg e16_138 hz
    all_goals simp only [map_add,show Normalized.basis .sphere 16 138 0=e16_138.symm (Finsupp.single 0 1) from (he16_138 0).symm,
      show Normalized.basis .sphere 16 138 1=e16_138.symm (Finsupp.single 1 1) from (he16_138 1).symm,
      show Normalized.basis .sphere 16 138 2=e16_138.symm (Finsupp.single 2 1) from (he16_138 2).symm,
      LinearEquiv.apply_symm_apply,map_zero] at hh
    · have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 0) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
    · have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 1) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
    · have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 0) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
  have source12 : Subsingleton (E.Page 6 (12,135)) := by
    have z0 := differential_target_later_zero (by change (2:ℤ)≤3;omega) (by decide : (3:ℤ)<6) h297
    have z12 := differential_target_later_zero (by change (2:ℤ)≤3;omega) (by decide : (3:ℤ)<6) h298
    have z2 := differential_target_later_zero (by change (2:ℤ)≤5;omega) (by decide : (5:ℤ)<6) h299
    have z1 : RepresentsOnPage E 6 (12,135) (Normalized.basis .sphere 12 135 1) 0 := by
      simpa only [add_sub_cancel_right,sub_self] using hsub z12 z2
    have hv (i : Fin 3) : RepresentsOnPage E 6 (12,135) (e12_135.symm (Finsupp.single i 1)) 0 := by
      fin_cases i
      · simpa only [he12_135] using z0
      · simpa only [he12_135] using z1
      · simpa only [he12_135] using z2
    have all (a : E.Page 6 (12,135)) : a=0 := by
      obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤6) e12_135 (fun _ => 0) hv a
      simpa only [ite_self,Finset.sum_const_zero] using hc
    exact ⟨fun x y => (all x).trans (all y).symm⟩
  exact ⟨source12,source13,source14⟩


private theorem beta_upper_windows :
    ∀ s : ℤ, 12≤s → s≤15 → Subsingleton
      (KIP126.Literature.CycleQuotient background .sphere (18-s) (s-6) (s,s+123)) := by
  obtain ⟨p12,p13,p14⟩ := stem123_upper_low_pages
  intro s hs hs'
  apply quotient_vanishing_actual
  interval_cases s
  · exact stem123_weight130_finite_quotients_cycle_quotient_zero_of_page
      6 6 6 (12,135) (by decide) (by decide) (by decide) p12
  · exact stem123_weight130_finite_quotients_cycle_quotient_zero_of_page
      4 5 7 (13,136) (by decide) (by decide) (by decide) p13
  · exact stem123_weight130_finite_quotients_cycle_quotient_zero_of_page
      4 4 8 (14,137) (by decide) (by decide) (by decide) p14
  · exact stem123_weight130_finite_quotients_stem123_af15_quotient
      stem123_middle_nonzero3

private theorem beta_upper_filtration_gap
    (a : BiHom 123 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11)) :
    FiltrationAtLeast background.syntheticTower 12 a ↔
      FiltrationAtLeast background.syntheticTower 16 a := by
  apply filtration_iff_of_infinity_zero (background.convergence (.quotient 11 .sphere))
    12 16 123 130 (by decide)
  intro j hj hj'
  haveI : Subsingleton (KIP126.Literature.CycleQuotient background .sphere
      (11-(123+j)+130) (1+(123+j)-130) (j,123+j)) := by
    rw [show (11:ℤ)-(123+j)+130=18-j by omega,
      show (1:ℤ)+(123+j)-130=j-6 by omega,add_comm 123 j]
    exact beta_upper_windows j hj (by omega)
  let e := KIP126.Literature.Standard.infinityFiniteWindow .sphere 11 (by decide)
    (j,123+j) 130 (by constructor <;> omega)
  haveI : Subsingleton (((background.family.quotient
      (background.nu.functor.obj SphereSpectrum) 11).sequence.ssData (j,123+j,130)).eInfty) :=
    e.injective.subsingleton
  let hn := ModuleCat.isZero_of_subsingleton
    (((background.family.quotient (background.nu.functor.obj SphereSpectrum) 11).sequence.ssData
      (j,123+j,130)).eInfty)
  let f := (background.family.functor.map
    (XModLambdaN.map background.nu.unitIso.hom 11)).eInftyMap (j,123+j,130)
  let g := (background.family.functor.map
    (XModLambdaN.map background.nu.unitIso.inv 11)).eInftyMap (j,123+j,130)
  have hfg : g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
      ←background.quotients.functoriality.map_comp,background.nu.unitIso.inv_hom_id,
      background.quotients.functoriality.map_id,CategoryTheory.Functor.map_id,
      SpectralSequenceMorphism.eInftyMap_id]
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
  exact hfg.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])

private theorem beta_h0_rho_zero_of_filtration_twelve
    (b : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (hb : FiltrationAtLeast background.syntheticTower 12
      (sphereAction KIP126.Literature.Standard.syntheticH0 b)) :
    sphereAction KIP126.Literature.Standard.syntheticH0
      (b≫(background.quotients.tower S_0_0).rho 9 11 (by decide))=0 := by
  apply beta_h0_rho_zero_of_filtration_sixteen b
  exact (beta_upper_filtration_gap _).mp hb

private theorem detects_implies_filtration
    {X : SyntheticSpectrum} (c : SyntheticTowerConvergence background.syntheticTower X)
    (i : Tridegree) (x : (background.family.obj X).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 X) (ha : Detects c i x a) :
    FiltrationAtLeast background.syntheticTower i.1 a := by
  obtain ⟨_,_,b,hb,_⟩ := ha
  have hm : a∈ModuleCat.subobjectModule _
      ((background.syntheticTower.filtration X).F i.1 (i.2.1-i.1,i.2.2)) := ⟨b,hb⟩
  simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
    FiltrationAtLeast] using hm

private theorem sphere_lambda_zero_h0 (a : BiHom 0 1 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 0 a=a := by
  have hc := background.quotients.coherence.right_unit (0,1) (S_0_0 : SyntheticSpectrum)
  have he : (SyntheticCategory.biShift_comp (0,1) (0,0)).hom.app
      (S_0_0 : SyntheticSpectrum)=
      SyntheticCategory.biShift_zero.hom.app (Smn 0 1 : SyntheticSpectrum) := by
    change (biShiftAddIso (0,1) (0,0) (0,1) (by simp)).hom.app _=_ at hc
    simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
      eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
  dsimp only [lambdaMultiply,lambdaPow]
  simp only [eqToHom_refl,Category.id_comp]
  rw [←he]
  change (SyntheticCategory.biShift_comp (0,1) (0,0)).inv.app
      (S_0_0 : SyntheticSpectrum)≫
      (SyntheticCategory.biShift_comp (0,1) (0,0)).hom.app
        (S_0_0 : SyntheticSpectrum)≫a=a
  rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]

private theorem beta_h0_filtration_ten
    (b : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (V : background.classical.sphere.Page 2 (9,132))
    (hb : Detects (background.convergence (.quotient 11 .sphere)) (9,132,129)
      (quotientLabel 11 9 132 3 V) b) :
    FiltrationAtLeast background.syntheticTower 10
      (sphereAction KIP126.Literature.Standard.syntheticH0 b) := by
  have hh := background.sphereDetectionCompatible.homotopy_lambda 1 1 0
    KIP126.Literature.Standard.syntheticH0
  rw [sphere_lambda_zero_h0] at hh
  have hf0 := detects_implies_filtration (background.convergence .sphere) (1,1,1) _ _ hh
  have hfb := detects_implies_filtration (background.convergence (.quotient 11 .sphere))
    (9,132,129) _ _ hb
  exact KIP126.Literature.Standard.action_filtration (.quotient 11 .sphere)
    0 1 123 129 1 9 KIP126.Literature.Standard.syntheticH0 b hf0 hfb

private theorem beta_first_filtration_gap
    (a : BiHom 123 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11)) :
    FiltrationAtLeast background.syntheticTower 10 a ↔
      FiltrationAtLeast background.syntheticTower 11 a := by
  apply filtration_iff_of_infinity_zero (background.convergence (.quotient 11 .sphere))
    10 11 123 130 (by decide)
  intro j hj hj'
  have hjeq : j=10 := by omega
  subst j
  haveI : Subsingleton (KIP126.Literature.CycleQuotient background .sphere
      (11-(123+10)+130) (1+(123+10)-130) (10,123+10)) := by
    exact quotient_vanishing_actual _ _ _
      stem123_weight130_finite_quotients_stem123_af10_quotient
  let e := KIP126.Literature.Standard.infinityFiniteWindow .sphere 11 (by decide)
    (10,123+10) 130 (by decide)
  haveI : Subsingleton (((background.family.quotient
      (background.nu.functor.obj SphereSpectrum) 11).sequence.ssData (10,123+10,130)).eInfty) :=
    e.injective.subsingleton
  let hn := ModuleCat.isZero_of_subsingleton
    (((background.family.quotient (background.nu.functor.obj SphereSpectrum) 11).sequence.ssData
      (10,123+10,130)).eInfty)
  let f := (background.family.functor.map
    (XModLambdaN.map background.nu.unitIso.hom 11)).eInftyMap (10,123+10,130)
  let g := (background.family.functor.map
    (XModLambdaN.map background.nu.unitIso.inv 11)).eInftyMap (10,123+10,130)
  have hfg : g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
      ←background.quotients.functoriality.map_comp,background.nu.unitIso.inv_hom_id,
      background.quotients.functoriality.map_id,CategoryTheory.Functor.map_id,
      SpectralSequenceMorphism.eInftyMap_id]
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
  exact hfg.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])

private theorem beta_h0_filtration_eleven
    (b : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (V : background.classical.sphere.Page 2 (9,132))
    (hb : Detects (background.convergence (.quotient 11 .sphere)) (9,132,129)
      (quotientLabel 11 9 132 3 V) b) :
    FiltrationAtLeast background.syntheticTower 11
      (sphereAction KIP126.Literature.Standard.syntheticH0 b) :=
  (beta_first_filtration_gap _).mp (beta_h0_filtration_ten b V hb)

end
end KIP126.Main.Internal.Moore
end

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature KIP126.Literature.Route
open KIP126.AdamsSynthetic.Completed KIP126.Main KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.Main.SectionSeven KIP126.Main.SectionSeven.Internal
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.Literature.Standard (eta syntheticH0)
open KIP126.Computation.Standard (T)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
local instance shiftAdditive (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := SyntheticSpectrum) p).Additive := graded_shiftAdditive p

private theorem beta_toda_exists {X : SyntheticSpectrum}
    (b : BiHom 123 129 X) (hb : sphereAction syntheticH0 b = 0) :
    ∃ z : BiHom 125 132 X, ModuleTripleToda b syntheticH0 eta z := by
  have hzero : sphereProduct eta syntheticH0 = 0 := by
    have hc := background.sphereProductCommutative 1 2 0 1 eta syntheticH0
    norm_num [homotopyRegrade] at hc
    rw [hc]
    exact KIP126.Literature.Standard.sphereProduct_syntheticH0_eta
  let F:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (123,129)
  let f:= (SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (123,130)).map eta
  let g:= (SyntheticCategory.biShift_comp (0,1) (123,129)).inv.app (S_0_0:SyntheticSpectrum)≫F.map syntheticH0
  have hfg:f≫g=0 := by
    have hh:=congrArg F.map hzero
    dsimp only [sphereProduct] at hh
    simp only [Functor.map_comp,Functor.map_zero] at hh
    have hh':F.map ((SyntheticCategory.biShift (0,1)).map eta)≫F.map syntheticH0=0 := by
      apply (cancel_epi (F.map ((SyntheticCategory.biShift_comp (1,2) (0,1)).inv.app (S_0_0:SyntheticSpectrum)))).mp
      simpa only [comp_zero] using hh
    have hn:=((SyntheticCategory.biShift_comp (0,1) (123,129)).inv.naturality eta)
    calc
      _ = (SyntheticCategory.biShift_comp (0,1) (123,129)).inv.app (Smn 1 2)≫
          F.map ((SyntheticCategory.biShift (0,1)).map eta)≫F.map syntheticH0 := by
        simpa only [f,g,F,Category.assoc,Functor.comp_map,Prod.mk_add_mk,Int.reduceAdd] using
          congrArg (fun z => z≫F.map syntheticH0) hn
      _ = 0 := by rw [hh',comp_zero]
  have hgb : g≫b=0 := by
    simpa only [g,F,sphereAction,Category.assoc] using hb
  obtain ⟨v,hv⟩:=Toda.exists_relation f g b hfg hgb
  let src:=tripleTodaSource (Syn:=SyntheticSpectrum) 1 2 0 1 123 129
  refine ⟨src.hom≫v,?_⟩
  change Toda.Relation (src.inv≫(src.hom≫v)) f g b
  simpa only [src.inv_hom_id_assoc] using hv

private theorem beta_error_formula_pointed
    (b : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (hb : sphereAction syntheticH0 b=0)
    (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum))
    (a2 : BiHom 124 137 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (a3 : BiHom 125 140 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (hr : sphereAction eta b=
      (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from lambdaMultiply 3 (quotientClass 9 u))+
      (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from lambdaMultiply 6 a2))
    (he : sphereAction eta a2=lambdaMultiply 1 a3)
    (z : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (hz : ModuleTripleToda b syntheticH0 eta z) :
    sphereAction syntheticH0 z=
      (show BiHom 125 133 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from quotientClass 9 (lambdaMultiply 3 (sphereProduct eta u)))+
      (show BiHom 125 133 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from lambdaMultiply 7 a3) := by
  letI:=background.exactness.syntheticTriangulated
  letI:=background.exactness.shiftCommShift (123,129)
  letI:=background.exactness.shiftExact (123,129)
  have hshuffle:=y_detection_toda_module_low_shuffle_exact background.quotients.coherence eta syntheticH0
    KIP126.Literature.Standard.toda_eta_squared KIP126.Literature.Standard.sphereProduct_syntheticH0_eq_zero_in_bidegree_two_three b hb z hz
  rw [y_detection_toda_eta_double_action background.quotients.coherence] at hshuffle
  rw [hshuffle,hr]
  have hadd (v w:BiHom 124 131 (XModLambdaN (S_0_0:SyntheticSpectrum) 9)):
      sphereAction eta (v+w)=sphereAction eta v+sphereAction eta w := by
    simp only [sphereAction,Preadditive.comp_add]
  rw [hadd,y_detection_toda_main_eta_right_three,y_detection_toda_main_eta_right_six,he,y_detection_toda_main_lambda_six_one]
  congr 1
  simp only [quotientClass,sphereProduct,sphereAction,lambdaMultiply,Category.assoc]

private theorem beta_suffices_for_final_contradiction
    (hc3 : Stem126D6Vanishes)
    (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum))
    (hcu : EtaExtensionDetectionAt u)
    (beta : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (hb : sphereAction syntheticH0 beta=0)
    (a2 : BiHom 124 137 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (a3 : BiHom 125 140 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (hr : sphereAction eta beta=
      (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from lambdaMultiply 3 (quotientClass 9 u))+
      (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from lambdaMultiply 6 a2))
    (heta : sphereAction eta a2=lambdaMultiply 1 a3) : False := by
  obtain ⟨z,hz⟩:=beta_toda_exists beta hb
  have htarget : ∃ t : BiHom 125 139 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
      FiniteDetected 9 (by decide) 14 139 0 T t ∧
      sphereAction syntheticH0 z=lambdaMultiply 6 t ∧ lambdaMultiply 6 t≠0 := by
    have hp := KIP126.Computation.Standard.t_permanent_cycle
    obtain ⟨t,ht,he⟩ := anyy_sphere_exact_target_split T hp
      (lambdaMultiply 3 (sphereProduct eta u)) hcu
    have htd := background.sphereDetectionCompatible.homotopy_lambda 14 139 0 t
    change Detects (background.convergence .sphere) (14,139,139)
      (sphereLabel 14 139 0 (KIP126.Literature.sphereFirstQuotient background 14 139 (quotientClass 1 t)))
      (lambdaMultiply 0 t) at htd
    rw [ht,lambda_zero_125_139] at htd
    have htq := detects_map .sphere (.quotient 9 .sphere) (XModLambdaN.incl _ 9) (14,139,139) _ _ htd
    have htn : FiniteDetected 9 (by decide) 14 139 0 T (quotientClass 9 t) := by
      apply sphere_finite_detection_nonzero 9 0 (by decide) (by decide) 14 139 T ?_ ?_ _ htq
      · exact permanentCycles_le_cycles background .sphere (14,139) _ ((permanent_cycle_iff_mem .sphere (14,139) T).mp hp)
      · intro hb
        exact survives_twelve_not_boundary_eleven .sphere (14,139) T
          (KIP126.Main.d6_vanishes_iff_target_survives_twelve.mp hc3)
          (boundaries_monotone background .sphere (14,139) (by decide) hb)
    have hformula := beta_error_formula_pointed beta hb u a2 a3 hr heta z hz
    have heq : sphereAction syntheticH0 z=lambdaMultiply 6 (quotientClass 9 t) := by
      rw [anyy_seventh_error_zero a3,add_zero,←he] at hformula
      simpa only [lambdaMultiply,quotientClass,Category.assoc] using hformula
    refine ⟨quotientClass 9 t,htn,heq,?_⟩
    intro hzero
    apply nu_target_lambda_eight_nonzero hc3 (quotientClass 9 t) htn
    rw [←lambda_two_six_139,hzero]
    simp only [lambdaMultiply,comp_zero]
  obtain ⟨t,ht,he,_⟩:=htarget
  have hdiv : TargetNuDivisible T hopfNu := by
    have hzn := weak_initial_twice_h0_nonzero hc3 syntheticH0 z t ht he
    let theta := KIP126.Literature.Standard.syntheticTheta5
    have htheta : ThetaChoice theta := KIP126.Literature.Standard.syntheticTheta5_detected
    obtain ⟨b,zTheta,hb,hzTheta,hToda⟩ := synthetic_theta_b_toda theta htheta KIP126.Literature.Standard.syntheticTheta5_add_self
    obtain ⟨y,hf,hn⟩ := main_weak_high_representative eta KIP126.Literature.Standard.eta_label
      syntheticH0 theta htheta b hb zTheta hzTheta (theta_b_multiplied_shuffle theta htheta KIP126.Literature.Standard.syntheticTheta5_add_self b zTheta hToda) z hzn
    have hd := background.sphereDetectionCompatible.homotopy_lambda 1 1 0 syntheticH0
    change Detects (background.convergence .sphere) (1,1,1)
      (sphereLabel 1 1 0 (KIP126.Literature.sphereFirstQuotient background 1 1 (quotientClass 1 syntheticH0)))
      (lambdaMultiply 0 syntheticH0) at hd
    have hh0 : KIP126.Literature.sphereFirstQuotient background 1 1 (quotientClass 1 syntheticH0)=KIP126.Computation.Standard.h0 := KIP126.Literature.Standard.syntheticH0_first_quotient_label
    rw [hh0,lambda_zero_0_1] at hd
    have hy := weak_y_detected_of_f11_and_nonzero syntheticH0 hd y hf hn
    exact nu_target_full_of_nonzero hopfNu KIP126.Literature.Standard.nuCofiber_normalized_label
      syntheticH0 KIP126.Literature.Standard.syntheticH0_first_quotient_label
      KIP126.Main.Internal.NuNinth.nu_extension_in_ninth_quotient y hy.1 hn
  obtain ⟨r,hr,hr',hhit⟩:=target_divisibility_forces_cnu_incoming hdiv
  exact KIP126.Computation.Standard.cofiber_target_not_hit_through5.2.2 r hr hr' hhit
end
end KIP126.Main.Internal.Moore
end

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Main KIP126.Main.Internal KIP126.Main.SectionSeven
open KIP126.Literature.Standard (syntheticH0)
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The shifted-lift criterion isolates the needed filtration bound on the
same detected representative. -/
private theorem h6_sq_permanent_of_shifted_lift
    (hbeta : ∃ b : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11),
      Detects (background.convergence (.quotient 11 .sphere)) (9,132,129)
        (quotientLabel 11 9 132 3 KIP126.Computation.Standard.V) b ∧
      FiltrationAtLeast background.syntheticTower 12 (sphereAction syntheticH0 b)) :
    KIP126.Main.H6SquarePermanent := by
  rcases KIP126.Main.permanence_or_d12 with hp | hd
  · exact hp
  · have hc3 := (KIP126.Main.d12_necessary hd).2
    obtain ⟨u,hu,hcu⟩ := (KIP126.Main.d12_implies_square_and_eta hd).2
    obtain ⟨b,hb,hfil⟩ := hbeta
    obtain ⟨a2,a3,heta,he⟩ := beta_eta_corrections b hb u hu
    exact False.elim (beta_suffices_for_final_contradiction hc3 u hcu
      (b ≫ (background.quotients.tower S_0_0).rho 9 11 (by decide))
      (beta_h0_rho_zero_of_filtration_twelve b hfil) a2 a3 heta he)

end
end KIP126.Main.Internal.Moore
end

@[expose] section
namespace KIP126.Main.Internal.Moore.SixthQuotient
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Core.Algebra
open KIP126.Main.SectionSeven KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.Main.Internal KIP126.Main.Internal.AlphaOne KIP126.Main.Internal.Selected
open KIP126.Computation.Table
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem six_source_af10_quotient :
    Subsingleton (CycleQuotient 2 5 (10,133)) := by
  classical
  let E := Normalized.sphere
  have h245 : HasDifferential E 2 (10,133) (12,134)
      (Normalized.basis .sphere 10 133 1) (Normalized.basis .sphere 12 134 2) := stem123_weight130_finite_quotients_d2_s10_t133_basis1
  have h294 : HasDifferential E 2 (10,133) (12,134)
      (Normalized.basis .sphere 10 133 0) (Normalized.basis .sphere 12 134 2) := stem123_weight130_finite_quotients_d2_s10_t133_basis0
  have h244 : HasDifferential E 3 (7,131) (10,133)
      (Normalized.basis .sphere 7 131 0) (Normalized.basis .sphere 10 133 0 + Normalized.basis .sphere 10 133 1) := stem123_weight130_finite_quotients_d3_s7_t131_basis0
  have h243 : HasDifferential E 2 (8,132) (10,133)
      (Normalized.basis .sphere 8 132 0) (Normalized.basis .sphere 10 133 2) := stem123_weight130_finite_quotients_d2_s8_t132_basis0
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,10,133,["372,1", "69,1,80,1", "0,1,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 180) (by rfl))
  change E.Page 2 (10,133) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 10 133 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = Normalized.basis .sphere 10 133 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = Normalized.basis .sphere 10 133 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = Normalized.basis .sphere 10 133 2 := he 2
  obtain ⟨f,hf⟩ := Normalized.basis_correct ⟨.sphere,12,134,["18,1,188,1", "0,1,371,1", "0,1,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 198) (by rfl))
  change E.Page 2 (12,134) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = Normalized.basis .sphere 12 134 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = Normalized.basis .sphere 12 134 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = Normalized.basis .sphere 12 134 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = Normalized.basis .sphere 12 134 2 := hf 2
  let B := boundaries 5 (10,133)
  have b01 : Normalized.basis .sphere 10 133 0+Normalized.basis .sphere 10 133 1∈B := by
    apply boundaries_monotone (10,133) (by decide : (4:ℤ)≤5)
    exact stem123_weight130_finite_quotients_boundary_of_zero_representative (r:=5) (p:=(10,133))
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤3;omega) (by decide) h244)
  have z2 : RepresentsOnPage E 5 (10,133) (Normalized.basis .sphere 10 133 2) 0 :=
      differential_target_later_zero (E:=E) (by change (2:ℤ)≤2;omega) (by decide) h243
  have b2 : Normalized.basis .sphere 10 133 2∈B := by
    exact boundaries_monotone (10,133) (by decide : (4:ℤ)≤5)
      (stem123_weight130_finite_quotients_boundary_of_zero_representative (r:=5) (p:=(10,133)) z2)
  have rep2 (x : E.Page 2 (10,133)) : RepresentsOnPage E 2 (10,133) x x := by
    haveI : Epi ((E.ssData (10,133)).pageπ 0) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective ((E.ssData (10,133)).pageπ 0)).mp inferInstance x
    exact ⟨by decide,z,by simp only [Subobject.ofLE_refl,Category.id_comp]; rfl,rfl⟩
  have hd0 : E.d 2 (10,133) (Normalized.basis .sphere 10 133 0)=Normalized.basis .sphere 12 134 2 := h294.eq_on_page_two.2
  have hd1 : E.d 2 (10,133) (Normalized.basis .sphere 10 133 1)=Normalized.basis .sphere 12 134 2 := h245.eq_on_page_two.2
  have hd2 : E.d 2 (10,133) (Normalized.basis .sphere 10 133 2)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide) (rep2 _) ⟨0,z2⟩
  have ne : Normalized.basis .sphere 12 134 2≠0 := by
    intro hh
    rw [show Normalized.basis .sphere 12 134 2=f.symm (Finsupp.single 2 1) from (hf 2).symm] at hh
    have hh' := congrArg (fun x=>f x 2) hh
    norm_num [Finsupp.single_apply] at hh'
  apply stem123_weight130_finite_quotients_cycle_quotient_zero_of_le
  intro x hx
  have hd : E.d 2 (10,133) x=0 := stem123_weight130_finite_quotients_cycle_differential_zero  (r:=2) (c:=2) (p:=(10,133)) (x:=x) (by decide) (by decide) hx (rep2 x)
  have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2) := by
    ext i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [Finsupp.single_zero,he2,add_zero,zero_add] at hxe
    rw [hxe]
    exact b2
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he1,add_zero,zero_add] at hxe
    rw [hxe]
    exfalso
    rw [hxe] at hd
    simp only [hd1] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he2,zero_add] at hxe
    rw [hxe]
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd1,hd2,add_zero] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he0,add_zero] at hxe
    rw [hxe]
    exfalso
    rw [hxe] at hd
    simp only [hd0] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he2,add_zero] at hxe
    rw [hxe]
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd2,add_zero] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,add_zero] at hxe
    rw [hxe]
    exact b01
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,he0,he1,he2] at hxe
    rw [hxe]
    exact B.add_mem b01 b2




private theorem six_source_filtration_gap
    (a : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 6)) :
    FiltrationAtLeast background.syntheticTower 10 a ↔
      FiltrationAtLeast background.syntheticTower 11 a := by
  apply filtration_iff_of_infinity_zero (background.convergence (.quotient 6 .sphere))
    10 11 123 129 (by decide)
  intro j hj hj'
  have hjeq : j=10 := by omega
  subst j
  haveI : Subsingleton (KIP126.Literature.CycleQuotient background .sphere
      (6-(123+10)+129) (1+(123+10)-129) (10,123+10)) := by
    exact quotient_vanishing_actual _ _ _ six_source_af10_quotient
  let e := KIP126.Literature.Standard.infinityFiniteWindow .sphere 6 (by decide)
    (10,123+10) 129 (by decide)
  haveI : Subsingleton (((background.family.quotient
      (background.nu.functor.obj SphereSpectrum) 6).sequence.ssData (10,123+10,129)).eInfty) :=
    e.injective.subsingleton
  let hn := ModuleCat.isZero_of_subsingleton
    (((background.family.quotient (background.nu.functor.obj SphereSpectrum) 6).sequence.ssData
      (10,123+10,129)).eInfty)
  let f := (background.family.functor.map
    (XModLambdaN.map background.nu.unitIso.hom 6)).eInftyMap (10,123+10,129)
  let g := (background.family.functor.map
    (XModLambdaN.map background.nu.unitIso.inv 6)).eInftyMap (10,123+10,129)
  have hfg : g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
      ←background.quotients.functoriality.map_comp,background.nu.unitIso.inv_hom_id,
      background.quotients.functoriality.map_id,CategoryTheory.Functor.map_id,
      SpectralSequenceMorphism.eInftyMap_id]
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
  exact hfg.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])

private theorem infinity_zero_of_detects_higher_filtration
    {X : SyntheticSpectrum} (c : SyntheticTowerConvergence background.syntheticTower X)
    (i : Tridegree) (x : (background.family.obj X).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 X) (ha : Detects c i x a)
    (hnext : FiltrationAtLeast background.syntheticTower (i.1+1) a)
    (e : ((background.family.obj X).sequence.ssData i).eInfty)
    (he : HasInfinityRepresentative (background.family.obj X) 2 i x e) : e=0 := by
  obtain ⟨f,hf,b,hb,hgr⟩ := ha
  have heq : e=f := he.unique hf
  rw [heq]
  let F := background.syntheticTower.filtration X
  have hmem : a∈ModuleCat.subobjectModule _ (F.F (i.1+1) (i.2.1-i.1,i.2.2)) := by
    simpa only [F,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast] using hnext
  have hgr0 : F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) b=0 := by
    apply (F.toAssociatedGraded_eq_zero_iff i.1 (i.2.1-i.1,i.2.2) b).mpr
    rw [hb]
    exact hmem
  apply (ModuleCat.mono_iff_injective ((c.identification i).hom)).mp inferInstance
  rw [hgr,hgr0,map_zero]

private theorem target_restriction_filtration_injective
    (a : BiHom 123 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (ha : FiltrationAtLeast background.syntheticTower 11 a)
    (hrho : FiltrationAtLeast background.syntheticTower 12
      (a≫(background.quotients.tower S_0_0).rho 6 11 (by decide))) :
    FiltrationAtLeast background.syntheticTower 12 a := by
  obtain ⟨x,hx,hdet⟩ := finite_sphere_filtration_has_cycle_label
    11 4 (by decide) (by decide) 11 134 a ha
  have hdet6 := KIP126.Main.Internal.Moore.shifted_detected_rho 6 11 4 (by decide) 11 134 x a hdet
  obtain ⟨e6,he6,hehom⟩ := hdet6
  have he0 : e6=0 := infinity_zero_of_detects_higher_filtration
    (background.convergence (.quotient 6 .sphere)) (11,134,130) _ _
    ⟨e6,he6,hehom⟩ hrho e6 he6
  let g6 := XModLambdaN.map background.nu.unitIso.inv 6
  have hn6 := family_infinity_representative_map g6 (11,134,130) _ _ he6
  have hl6 := sphere_quotient_label_to_nu 6 4 11 134 x
  change familyPageMap background.family g6 2 (11,134,130)
    (quotientLabel 6 11 134 4 x)=_ at hl6
  rw [hl6,he0,map_zero] at hn6
  let x6 : KIP126.Literature.cycles background .sphere (6-134+(134-4)) (11,134) :=
    ⟨x,KIP126.Literature.cycles_antitone background .sphere (11,134)
      (by decide : (2:ℤ)≤7) hx⟩
  have hclass6 := (finite_target_label_iff .sphere 6 (by decide) 11 134 4
    (by decide) x6 0).mp hn6
  rw [map_zero] at hclass6
  have hboundary : x∈KIP126.Literature.boundaries background .sphere 5 (11,134) :=
    (subquotientClass_eq_zero_iff _ _ x6).mp hclass6.symm
  let x11 : KIP126.Literature.cycles background .sphere (11-134+(134-4)) (11,134) :=
    ⟨x,hx⟩
  have hclass11 : KIP126.Literature.subquotientClass _ _ x11=0 :=
    (subquotientClass_eq_zero_iff _ _ x11).mpr hboundary
  have hpzero : (KIP126.Literature.Standard.infinityFiniteWindow .sphere 11
      (by decide) (11,134) 130 (by decide)) 0=0 := map_zero _
  have hn11 := (finite_target_label_iff .sphere 11 (by decide) 11 134 4
    (by decide) x11 0).mpr (by
      apply hpzero.trans
      simpa only [Nat.cast_ofNat,Int.reduceSub,Int.reduceAdd] using hclass11.symm)
  let f11 := XModLambdaN.map background.nu.unitIso.hom 11
  have hs11 := family_infinity_representative_map f11 (11,134,130) _ _ hn11
  have hl11 := sphere_quotient_label_from_nu 11 4 11 134 x
  change familyPageMap background.family f11 2 (11,134,130)
    (finiteTargetLabel background .sphere 11 11 134 4 x)=_ at hl11
  rw [hl11,map_zero] at hs11
  exact detects_zero_infinity_filtration (background.convergence (.quotient 11 .sphere))
    (11,134,130) hdet hs11

private theorem beta_h0_obstruction_zero_of_six_representative
    (V : background.classical.sphere.Page 2 (9,132))
    (b11 : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (hb11 : Detects (background.convergence (.quotient 11 .sphere)) (9,132,129)
      (quotientLabel 11 9 132 3 V) b11)
    (b6 : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 6))
    (hb6 : Detects (background.convergence (.quotient 6 .sphere)) (9,132,129)
      (quotientLabel 6 9 132 3 V) b6)
    (hzero : sphereAction KIP126.Literature.Standard.syntheticH0 b6=0) :
    FiltrationAtLeast background.syntheticTower 12
      (sphereAction KIP126.Literature.Standard.syntheticH0 b11) := by
  let rho := (background.quotients.tower S_0_0).rho 6 11 (by decide)
  have hrho := KIP126.Main.Internal.Moore.shifted_detected_rho 6 11 3 (by decide) 9 132 V b11 hb11
  have hdiff10 := detects_sub_filtration (background.convergence (.quotient 6 .sphere))
    (9,132,129) hrho hb6
  have hdiff11 := (six_source_filtration_gap _).mp hdiff10
  have hh0 := background.sphereDetectionCompatible.homotopy_lambda 1 1 0
    KIP126.Literature.Standard.syntheticH0
  rw [KIP126.Main.Internal.Moore.sphere_lambda_zero_h0] at hh0
  have hf0 := KIP126.Main.Internal.Moore.detects_implies_filtration (background.convergence .sphere)
    (1,1,1) _ _ hh0
  have hp := KIP126.Literature.Standard.action_filtration (.quotient 6 .sphere)
    0 1 123 129 1 11 KIP126.Literature.Standard.syntheticH0 _ hf0 hdiff11
  have hsub : sphereAction KIP126.Literature.Standard.syntheticH0 (b11≫rho-b6)=
      sphereAction KIP126.Literature.Standard.syntheticH0 (b11≫rho)-
        sphereAction KIP126.Literature.Standard.syntheticH0 b6 := by
    simp only [sphereAction,Preadditive.comp_sub]
  change FiltrationAtLeast background.syntheticTower 12
    (sphereAction KIP126.Literature.Standard.syntheticH0 (b11≫rho-b6)) at hp
  rw [hsub,hzero,sub_zero] at hp
  apply target_restriction_filtration_injective _
    (KIP126.Main.Internal.Moore.beta_h0_filtration_eleven b11 V hb11)
  simpa only [sphereAction,Category.assoc,rho] using hp

end
end KIP126.Main.Internal.Moore.SixthQuotient
end

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Main.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The permanence reduction from the Moore-spectrum Q₆ witness and E₉ survival. -/
private theorem h6_sq_permanent_of_six_representative
    (hV : KIP126.Computation.Standard.V ∈
      KIP126.Literature.cycles background .sphere 8 (9,132))
    (hsix : ∃ b6 : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 6),
      Detects (background.convergence (.quotient 6 .sphere)) (9,132,129)
        (quotientLabel 6 9 132 3 KIP126.Computation.Standard.V) b6 ∧
      sphereAction KIP126.Literature.Standard.syntheticH0 b6=0) :
    KIP126.Main.H6SquarePermanent := by
  obtain ⟨b11,hb11,_⟩ := beta_detected_pair KIP126.Computation.Standard.V hV
  obtain ⟨b6,hb6,hzero⟩ := hsix
  exact h6_sq_permanent_of_shifted_lift ⟨b11,hb11,
    SixthQuotient.beta_h0_obstruction_zero_of_six_representative
      KIP126.Computation.Standard.V b11 hb11 b6 hb6 hzero⟩


/-- The Moore witness also excludes the eta extension directly. -/
private theorem eta_extension_excluded_of_six_representative
    (hV : KIP126.Computation.Standard.V ∈
      KIP126.Literature.cycles background .sphere 8 (9,132))
    (hsix : ∃ b6 : BiHom 123 129 (XModLambdaN (S_0_0 : SyntheticSpectrum) 6),
      Detects (background.convergence (.quotient 6 .sphere)) (9,132,129)
        (quotientLabel 6 9 132 3 KIP126.Computation.Standard.V) b6 ∧
      sphereAction KIP126.Literature.Standard.syntheticH0 b6=0)
    (hc3 : KIP126.Main.Stem126D6Vanishes) :
    ¬ KIP126.Main.EtaExtensionDetection := by
  rintro ⟨u,hu,hcu⟩
  obtain ⟨b11,hb11,_⟩ := beta_detected_pair KIP126.Computation.Standard.V hV
  obtain ⟨b6,hb6,hzero⟩ := hsix
  have hfil := SixthQuotient.beta_h0_obstruction_zero_of_six_representative
    KIP126.Computation.Standard.V b11 hb11 b6 hb6 hzero
  obtain ⟨a2,a3,hr,he⟩ := beta_eta_corrections b11 hb11 u hu
  exact beta_suffices_for_final_contradiction hc3 u hcu
    (b11 ≫ (background.quotients.tower S_0_0).rho 9 11 (by decide))
    (beta_h0_rho_zero_of_filtration_twelve b11 hfil) a2 a3 hr he


end
end KIP126.Main.Internal.Moore
end
