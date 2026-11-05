module

public import KIP126.ProofTools.Paper.ExtensionIndeterminacy
public import KIP126.ProofTools.Paper.ExtensionRepresentatives
import all KIP126.ProofTools.Paper.ExtensionIndeterminacy
import all KIP126.ProofTools.Paper.ExtensionRepresentatives
import all KIP126.ProofTools.ConvergenceOperations
import all KIP126.ProofTools.StretchingRepresentatives
import all KIP126.ProofTools.GeneralizedLeibniz.Filtration
import all KIP126.ProofTools.GeneralizedMahowald.QuotientShift
import all KIP126.ProofTools.Paper.ExtensionEssentialSource

/-! A fixed-target nonliftable short extension, or a crossing in the same
later synthetic extension spectral sequence. -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace KIP126.ProofTools.Paper
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section

/-- This is the cycle-set difference branch, retaining the specified original
target. It is separate from the classical crossing predicate of Definition 5.9. -/
@[expose] public def FiniteExtensionNonliftableShortTo (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ) (x y)
    (Wearly : FiniteExtensionWitness background X Y f rEarlier n s t x y) : Prop :=
  ∃ a : ℕ, 0 < a ∧ (a:ℤ) ≤ n-normalizedExponent background.classicalTower f ∧
    ∃ x' : Ambient background X (s+a,(t-s)+(s+a)),
      x' ∈ cycles background X (((rEarlier-1:ℕ):ℤ)-a) (s+a,(t-s)+(s+a)) ∧
      x' ∉ cycles background X (((rLater-1:ℕ):ℤ)-a) (s+a,(t-s)+(s+a)) ∧
      ∃ z,
        HasInfinityRepresentative _ 2 _
          (finiteExtensionCorrectionLabel X Y f (rEarlier-1) s t a x') z ∧
        TowerExtensionEquation (background.convergentMap
          (.quotient (rEarlier-1) (extensionSourceObject background X Y f))
          (.quotient (rEarlier-1) (.nu Y)) (finiteExtensionMap background X Y f (rEarlier-1)))
          (t-s,t+normalizedExponent background.classicalTower f) (s+a) (n-a) z
          ((eqToHom (congrArg (fun d =>
            ((background.family.obj ((SyntheticObject.quotient (rEarlier-1) (.nu Y)).obj
              background.nu background.auxiliary)).sequence.ssData
              (d,(t-s)+d,t+normalizedExponent background.classicalTower f)).eInfty)
            (show s+n = (s+a)+(n-a) by omega))) Wearly.target)

/-- A leading source that lifts through the actual square cannot support an
essential short early extension when all late higher-source crossings vanish. -/
private theorem essential_short_source_not_in_range
    (Al Bl Ae Be : SyntheticObject (coefficients := background.coefficients))
    (gl : Al.obj background.nu background.auxiliary ⟶ Bl.obj background.nu background.auxiliary)
    (ge : Ae.obj background.nu background.auxiliary ⟶ Be.obj background.nu background.auxiliary)
    (ra : Al.obj background.nu background.auxiliary ⟶ Ae.obj background.nu background.auxiliary)
    (rb : Bl.obj background.nu background.auxiliary ⟶ Be.obj background.nu background.auxiliary)
    (hsquare : ra ≫ ge = gl ≫ rb) (p : ℤ × ℤ) (s n u d : ℤ)
    (hn : 0 ≤ n) (hu : s < u) (htarget : u+d=s+n)
    (hcross : ExtensionNoCrossingRange (background.convergentMap Al Bl gl) p s n s)
    (xe : ((background.family.obj (Ae.obj background.nu background.auxiliary)).sequence.ssData
      (u,p.1+u,p.2)).eInfty)
    (ye : ((background.family.obj (Be.obj background.nu background.auxiliary)).sequence.ssData
      (u+d,p.1+(u+d),p.2)).eInfty)
    (he : TowerEssentialExtension (background.convergentMap Ae Be ge) p u d xe ye)
    (xl : ((background.family.obj (Al.obj background.nu background.auxiliary)).sequence.ssData
      (u,p.1+u,p.2)).eInfty)
    (hxl : (background.family.map ra).eInftyMap (u,p.1+u,p.2) xl = xe) : False := by
  let FL := background.syntheticTower.filtration (Al.obj background.nu background.auxiliary)
  let FE := background.syntheticTower.filtration (Ae.obj background.nu background.auxiliary)
  let GE := background.syntheticTower.filtration (Be.obj background.nu background.auxiliary)
  let IL := infinityGradedIso (background.convergence Al) p u
  let IE := infinityGradedIso (background.convergence Ae) p u
  haveI : Epi (FL.toAssociatedGraded u p) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨ar,har⟩ := (ModuleCat.epi_iff_surjective (FL.toAssociatedGraded u p)).mp
    inferInstance (IL.hom xl)
  let α := (FL.F u p).arrow ar
  have hα : α ∈ background.syntheticTower.filtrationSubmodule (Al.obj background.nu background.auxiliary) u p := by
    have hm : α ∈ ModuleCat.subobjectModule _ (FL.F u p) := ⟨ar,rfl⟩
    simpa only [FL,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hm
  have hαnext := background.syntheticTower.filtrationSubmodule_antitone _ p
    (show s+1 ≤ u by omega) hα
  have hgl := image_correction_in_next (background.convergentMap Al Bl gl) p s n s
    (by omega) hcross α hαnext
    (map_preserves_filtration (background.convergentMap Al Bl gl) p s α
      (background.syntheticTower.filtrationSubmodule_antitone _ p (by omega) hα))
  have hαe := map_preserves_filtration (background.convergentMap Al Ae ra) p u α hα
  obtain ⟨ae,hae⟩ := filtration_representative_exists background.syntheticTower
    (Ae.obj background.nu background.auxiliary) p u (α≫ra) hαe
  have hg := representative_grade_naturality (background.convergentMap Al Ae ra) p u ar ae hae.symm
  rw [har] at hg
  have hc : IL.inv (IL.hom xl)=xl := IL.toLinearEquiv.symm_apply_apply xl
  rw [hc] at hg
  have hge : IE.inv (FE.toAssociatedGraded u p ae)=xe := hg.trans hxl
  have hax : FE.toAssociatedGraded u p ae = IE.hom xe :=
    (IE.toLinearEquiv.apply_symm_apply _).symm.trans (congrArg IE.hom hge)
  have hhigh : (α≫ra)≫ge ∈
      background.syntheticTower.filtrationSubmodule (Be.obj background.nu background.auxiliary) (u+d+1) p := by
    have hh := map_preserves_filtration (background.convergentMap Bl Be rb) p (s+n+1) (α≫gl) hgl
    simpa only [Category.assoc,hsquare,htarget] using hh
  have hlow := background.syntheticTower.filtrationSubmodule_antitone _ p
    (show u+d ≤ u+d+1 by omega) hhigh
  obtain ⟨be,hbe⟩ := filtration_representative_exists background.syntheticTower
    (Be.obj background.nu background.auxiliary) p (u+d) ((α≫ra)≫ge) hlow
  have hzero : GE.toAssociatedGraded (u+d) p be = 0 := by
    have hh := (element_grade_equal_iff GE (u+d) p be 0).mpr (by
      rw [hbe,map_zero,sub_zero]
      simpa only [GE,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hhigh)
    simpa only [map_zero] using hh
  apply ((tower_essential_iff_no_zero _ _ _ _ _ _ he.1).mp he)
  apply (tower_extension_iff (background.convergentMap Ae Be ge) p u d xe 0).mpr
  refine ⟨((tower_extension_iff _ _ _ _ _ _).mp he.1).1,ae,be,?_,hax,?_⟩
  · rw [hae,hbe]
  · simpa only [map_zero] using hzero

private theorem infinity_map_eq_of_homotopy_eq
    (A B : SyntheticObject (coefficients := background.coefficients))
    (f g : A.obj background.nu background.auxiliary ⟶ B.obj background.nu background.auxiliary)
    (p : ℤ × ℤ) (s : ℤ)
    (hfg : ∀ a : BiHom p.1 p.2 (A.obj background.nu background.auxiliary), a≫f=a≫g)
    (z : ((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty) :
    (background.family.map f).eInftyMap (s,p.1+s,p.2) z =
      (background.family.map g).eInftyMap (s,p.1+s,p.2) z := by
  let FA := background.syntheticTower.filtration (A.obj background.nu background.auxiliary)
  let FB := background.syntheticTower.filtration (B.obj background.nu background.auxiliary)
  let IA := infinityGradedIso (background.convergence A) p s
  haveI : Epi (FA.toAssociatedGraded s p) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨ar,har⟩ := (ModuleCat.epi_iff_surjective (FA.toAssociatedGraded s p)).mp
    inferInstance (IA.hom z)
  let α := (FA.F s p).arrow ar
  have hα : α ∈ background.syntheticTower.filtrationSubmodule (A.obj background.nu background.auxiliary) s p := by
    have hh : α ∈ ModuleCat.subobjectModule _ (FA.F s p) := ⟨ar,rfl⟩
    simpa only [FA,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hh
  obtain ⟨br,hbr⟩ := filtration_representative_exists background.syntheticTower
    (B.obj background.nu background.auxiliary) p s (α≫f)
    (map_preserves_filtration (background.convergentMap A B f) p s α hα)
  have hf := representative_grade_naturality (background.convergentMap A B f) p s ar br hbr.symm
  have hg := representative_grade_naturality (background.convergentMap A B g) p s ar br
    ((hfg α).symm.trans hbr.symm)
  rw [har] at hf hg
  have hc : IA.inv (IA.hom z)=z := IA.toLinearEquiv.symm_apply_apply z
  rw [hc] at hf hg
  exact hf.symm.trans hg

private theorem correction_rho_square_infinity (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (i q : ℕ) (hi : 0 < i) (hiq : i ≤ q) (p : ℤ × ℤ) (u : ℤ)
    (z : ((background.family.obj ((SyntheticObject.quotient q (extensionSourceObject background X Y f)).obj
      background.nu background.auxiliary)).sequence.ssData (u,p.1+u,p.2)).eInfty) :
    (background.family.map (correctionShiftIso X Y f i).hom).eInftyMap _
      ((background.family.map ((background.quotients.tower ((extensionSourceObject background X Y f).obj
        background.nu background.auxiliary)).rho i q hiq)).eInftyMap _ z) =
    (background.family.map ((SyntheticCategory.biShift (0,(normalizedExponent background.classicalTower f : ℤ))).map
      ((background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho i q hiq))).eInftyMap _
      ((background.family.map (correctionShiftIso X Y f q).hom).eInftyMap _ z) := by
  let ra := (background.quotients.tower ((extensionSourceObject background X Y f).obj
    background.nu background.auxiliary)).rho i q hiq
  let rn := (background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho i q hiq
  have hh := infinity_map_eq_of_homotopy_eq
    (.quotient q (extensionSourceObject background X Y f))
    (.shift (0,(normalizedExponent background.classicalTower f : ℤ)) (.quotient i (.nu X)))
    (ra≫(correctionShiftIso X Y f i).hom)
    ((correctionShiftIso X Y f q).hom≫
      (SyntheticCategory.biShift (0,(normalizedExponent background.classicalTower f : ℤ))).map rn)
    p u (fun c => by
      simpa only [ra,rn,extensionSourceObject,SyntheticObject.obj,Category.assoc] using
        KIP126.ProofTools.Internal.Mahowald.quotient_shift_restriction_on_spheres X
          (0,(normalizedExponent background.classicalTower f : ℤ)) i q hi hiq
          (correctionShiftIso X Y f i) (correctionShiftIso X Y f q)
          (correctionShiftIso_incl X Y f i) (correctionShiftIso_incl X Y f q) p.1 p.2 c) z
  dsimp only [ra,rn] at hh
  simp only [SyntheticAdamsFamily.map_comp,SpectralSequenceMorphism.eInftyMap_comp,
    ModuleCat.comp_apply] at hh
  exact hh

private theorem correction_unshifted_label_rho (X : AdamsObject (coefficients := background.coefficients))
    (i q : ℕ) (hiq : i ≤ q) (u v : ℤ) (a : ℕ) (x : Ambient background X (u,v)) :
    familyPageMap background.family
      ((background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho i q hiq)
      2 (u,v,v-a) (finiteTargetLabel background X q u v a x) =
      finiteTargetLabel background X i u v a x := by
  unfold finiteTargetLabel
  have hh := congrArg (fun g => familyPageMap background.family g 2 (u,v,v-a))
    ((background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho_quotient hiq)
  rw [←family_page_comp] at hh
  exact ConcreteCategory.congr_hom hh (targetNuLabel background X u v a x)

private theorem target_weight_label (X : AdamsObject (coefficients := background.coefficients)) (u v : ℤ) (a : ℕ)
    (x : Ambient background X (u,v)) :
    nuWeightLabel background X u v (v-a) (by omega) x = targetNuLabel background X u v a x := by
  have hk : (v-(v-(a:ℤ))).toNat=a := by omega
  have transport (b c : ℕ) (he : b=c) (hi : (u,v,v-b)=(u,v,v-c)) :
      regradeE2 hi (targetNuLabel background X u v b x) = targetNuLabel background X u v c x := by
    subst c
    rfl
  exact transport _ a hk _

private theorem unshifted_label_infinity_exists (X : AdamsObject (coefficients := background.coefficients))
    (q : ℕ) (hq : 0 < q) (u v : ℤ) (a : ℕ) (ha : a < q)
    (x : Ambient background X (u,v)) (hx : x∈cycles background X ((q:ℤ)-a) (u,v)) :
    ∃ z : ((background.family.obj ((SyntheticObject.quotient q (.nu X)).obj
      background.nu background.auxiliary)).sequence.ssData (u,v,v-a)).eInfty,
      HasInfinityRepresentative _ 2 _ (finiteTargetLabel background X q u v a x) z := by
  let P := KIP126.Literature.Standard.infinityFiniteWindow X q hq (u,v) (v-a)
    (by constructor <;> omega)
  have hx' : x∈cycles background X ((q:ℤ)-v+(v-a)) (u,v) := by convert hx using 1 <;> congr 1 <;> omega
  let c := subquotientClass (cycles background X ((q:ℤ)-v+(v-a)) (u,v))
    (boundaries background X (1+v-(v-a)) (u,v)) ⟨x,hx'⟩
  let z := P.symm c
  have he := (KIP126.Literature.Standard.eInfinity_finite_labels X q hq u v (v-a)
    (by constructor <;> omega) x z).mpr ⟨hx',P.apply_symm_apply c⟩
  rw [target_weight_label] at he
  exact ⟨z,he⟩

private def correctionInfinity (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (s t : ℤ) (a : ℕ)
    (z : ((background.family.obj ((SyntheticObject.quotient q (.nu X)).obj background.nu background.auxiliary)).sequence.ssData
      (s+a,(t-s)+(s+a),((t-s)+(s+a))-a)).eInfty) :
    ((background.family.obj ((SyntheticObject.quotient q (extensionSourceObject background X Y f)).obj
      background.nu background.auxiliary)).sequence.ssData
      (s+a,(t-s)+(s+a),t+normalizedExponent background.classicalTower f)).eInfty := by
  let e : ℤ := normalizedExponent background.classicalTower f
  let u : ℤ := s+a
  let p : ℤ × ℤ := (t-s,((t-s)+(s+a))-a)
  let z0 : ((background.family.obj ((SyntheticObject.quotient q (.nu X)).obj
      background.nu background.auxiliary)).sequence.ssData (u,p.1+u,p.2)).eInfty := z
  let I := towerInfinityIso (F := background.family) (P := background.syntheticTower) (background.convergence (.quotient q (.nu X)))
    (background.convergence (.shift (0,e) (.quotient q (.nu X))))
    ((essShift (0,e)).filtered (.quotient q (.nu X)) p) u
  let zs : ((background.family.obj ((SyntheticObject.shift (0,e) (.quotient q (.nu X))).obj
      background.nu background.auxiliary)).sequence.ssData (u,(p+(0,e)).1+u,(p+(0,e)).2)).eInfty := I.hom z0
  let hdeg : (u,(p+(0,e)).1+u,(p+(0,e)).2) =
      (s+a,(t-s)+(s+a),t+normalizedExponent background.classicalTower f) := by
    ext <;> dsimp [p,u,e] <;> omega
  let zt := (eqToHom (congrArg (fun i => ((background.family.obj
    ((SyntheticObject.shift (0,e) (.quotient q (.nu X))).obj
      background.nu background.auxiliary)).sequence.ssData i).eInfty) hdeg)) zs
  exact (background.family.map (correctionShiftIso X Y f q).inv).eInftyMap (s+a,(t-s)+(s+a),t+normalizedExponent background.classicalTower f) zt

private theorem correctionInfinity_represents (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (s t : ℤ) (a : ℕ) (x : Ambient background X (s+a,(t-s)+(s+a)))
    (z : ((background.family.obj ((SyntheticObject.quotient q (.nu X)).obj background.nu background.auxiliary)).sequence.ssData
      (s+a,(t-s)+(s+a),((t-s)+(s+a))-a)).eInfty)
    (hz : HasInfinityRepresentative _ 2 _ (finiteTargetLabel background X q (s+a) ((t-s)+(s+a)) a x) z) :
    HasInfinityRepresentative _ 2 _ (finiteExtensionCorrectionLabel X Y f q s t a x)
      (correctionInfinity X Y f q s t a z) := by
  let e : ℤ := normalizedExponent background.classicalTower f
  let u : ℤ := s+a
  let p : ℤ × ℤ := (t-s,((t-s)+(s+a))-a)
  let I := towerInfinityIso (F := background.family) (P := background.syntheticTower)
    (background.convergence (.quotient q (.nu X)))
    (background.convergence (.shift (0,e) (.quotient q (.nu X))))
    ((essShift (0,e)).filtered (.quotient q (.nu X)) p) u
  let hdeg : (u,(p+(0,e)).1+u,(p+(0,e)).2) =
      (s+a,(t-s)+(s+a),t+normalizedExponent background.classicalTower f) := by
    ext <;> dsimp [p,u,e] <;> omega
  let zt := (eqToHom (congrArg (fun i => ((background.family.obj
    ((SyntheticObject.shift (0,e) (.quotient q (.nu X))).obj
      background.nu background.auxiliary)).sequence.ssData i).eInfty) hdeg)) (I.hom z)
  have hs := ((essShift (0,e)).representative_iff
    (.quotient q (.nu X)) 2 (by decide) p u
    (finiteTargetLabel background X q (s+a) ((t-s)+(s+a)) a x) z).mp hz
  have hs' := infinity_representative_regrade hdeg _ _ hs
  have hm := family_infinity_representative_map (correctionShiftIso X Y f q).inv
    (s+a,(t-s)+(s+a),t+normalizedExponent background.classicalTower f) _ zt hs'
  exact hm


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
  simpa only [towerGradedIso, infinityGradedIso, SyntheticAdamsFamily.map, SyntheticTowerConvergence.filtration] using
    (infinity_graded_naturality M p s).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem infinityTowerNatural
    {C : Type 1} [StableHomotopyCategory.{1,0} C]
    [HasFunctorialCofiber (C := C)]
    {Syn : Type 1} [SyntheticCategory.{1,0} Syn]
    [HasFunctorialCofiber (C := Syn)]
    (D : AdamsSyntheticBackground C Syn) (δ : ℤ × ℤ) (S : SyntheticESSShiftComparison D δ)
    (X Y : SyntheticObject (coefficients := D.coefficients))
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

private theorem infinity_map_regrade (A B : SyntheticObject (coefficients := background.coefficients))
    (f : A.obj background.nu background.auxiliary ⟶ B.obj background.nu background.auxiliary)
    {i j : Tridegree} (h : i=j)
    (z : ((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData i).eInfty) :
    (background.family.map f).eInftyMap j
      ((eqToHom (congrArg (fun k => ((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData k).eInfty) h)) z) =
    (eqToHom (congrArg (fun k => ((background.family.obj (B.obj background.nu background.auxiliary)).sequence.ssData k).eInfty) h))
      ((background.family.map f).eInftyMap i z) := by
  subst j
  rfl

private theorem correctionInfinity_rho (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (i q : ℕ) (hi : 0 < i) (hiq : i ≤ q) (s t : ℤ) (a : ℕ)
    (z : ((background.family.obj ((SyntheticObject.quotient q (.nu X)).obj background.nu background.auxiliary)).sequence.ssData
      (s+a,(t-s)+(s+a),((t-s)+(s+a))-a)).eInfty) :
    (background.family.map ((background.quotients.tower ((extensionSourceObject background X Y f).obj
      background.nu background.auxiliary)).rho i q hiq)).eInftyMap _
      (correctionInfinity X Y f q s t a z) =
    correctionInfinity X Y f i s t a
      ((background.family.map ((background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho i q hiq)).eInftyMap _ z) := by
  let e : ℤ := normalizedExponent background.classicalTower f
  let δ : ℤ × ℤ := (0,e)
  let u : ℤ := s+a
  let p₀ : ℤ × ℤ := (t-s,((t-s)+(s+a))-a)
  let p : ℤ × ℤ := (t-s,t+e)
  let hdeg : (u,(p₀+δ).1+u,(p₀+δ).2)=(u,p.1+u,p.2) := by
    ext <;> dsimp [δ,p₀,p,u,e] <;> omega
  let ra := (background.quotients.tower ((extensionSourceObject background X Y f).obj
    background.nu background.auxiliary)).rho i q hiq
  let rn := (background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho i q hiq
  let srn := (SyntheticCategory.biShift δ).map rn
  let IL := towerInfinityIso (background.convergence (.quotient q (.nu X)))
    (background.convergence (.shift δ (.quotient q (.nu X))))
    ((essShift δ).filtered (.quotient q (.nu X)) p₀) u
  let IE := towerInfinityIso (background.convergence (.quotient i (.nu X)))
    (background.convergence (.shift δ (.quotient i (.nu X))))
    ((essShift δ).filtered (.quotient i (.nu X)) p₀) u
  let castL := eqToHom (congrArg (fun k => ((background.family.obj
    ((SyntheticObject.shift δ (.quotient q (.nu X))).obj background.nu background.auxiliary)).sequence.ssData k).eInfty) hdeg)
  let castE := eqToHom (congrArg (fun k => ((background.family.obj
    ((SyntheticObject.shift δ (.quotient i (.nu X))).obj background.nu background.auxiliary)).sequence.ssData k).eInfty) hdeg)
  let zs := castL (IL.hom z)
  let zl := correctionInfinity X Y f q s t a z
  have hQ := correction_rho_square_infinity X Y f i q hi hiq p u zl
  have hcancel : (background.family.map (correctionShiftIso X Y f q).hom).eInftyMap _ zl = zs := by
    dsimp only [zl,correctionInfinity,zs,castL,IL,p₀,δ,u,e,hdeg]
    simp only [←ModuleCat.comp_apply,Category.assoc,←SpectralSequenceMorphism.eInftyMap_comp,
      ←SyntheticAdamsFamily.map_comp,Iso.inv_hom_id,SyntheticAdamsFamily.map_id,
      SpectralSequenceMorphism.eInftyMap_id,Category.comp_id,ConcreteCategory.id_apply]
    rfl
  rw [hcancel] at hQ
  have hNat := ConcreteCategory.congr_hom
    (infinityTowerNatural background δ (essShift δ) (.quotient q (.nu X)) (.quotient i (.nu X)) rn p₀ u) z
  have hshift : (background.family.map srn).eInftyMap (u,p.1+u,p.2) zs =
      castE (IE.hom ((background.family.map rn).eInftyMap _ z)) := by
    have hcast := infinity_map_regrade (.shift δ (.quotient q (.nu X)))
      (.shift δ (.quotient i (.nu X))) srn hdeg (IL.hom z)
    exact hcast.trans (congrArg castE hNat.symm)
  have hh := congrArg ((background.family.map (correctionShiftIso X Y f i).inv).eInftyMap
    (u,p.1+u,p.2)) (hQ.trans hshift)
  have hleft : (background.family.map (correctionShiftIso X Y f i).inv).eInftyMap _
      ((background.family.map (correctionShiftIso X Y f i).hom).eInftyMap _
        ((background.family.map ra).eInftyMap _ zl)) = (background.family.map ra).eInftyMap _ zl := by
    simp only [←ModuleCat.comp_apply,Category.assoc,←SpectralSequenceMorphism.eInftyMap_comp,
      ←SyntheticAdamsFamily.map_comp,Iso.hom_inv_id,SyntheticAdamsFamily.map_id,
      SpectralSequenceMorphism.eInftyMap_id,ConcreteCategory.id_apply]
  rw [hleft] at hh
  exact hh

private theorem correction_source_lift_of_late_cycle (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (i q : ℕ) (hi : 0 < i) (hiq : i ≤ q) (s t : ℤ) (a : ℕ) (ha : a < i)
    (x : Ambient background X (s+a,(t-s)+(s+a)))
    (hx : x∈cycles background X ((q:ℤ)-a) (s+a,(t-s)+(s+a)))
    (z : ((background.family.obj ((SyntheticObject.quotient i (extensionSourceObject background X Y f)).obj
      background.nu background.auxiliary)).sequence.ssData
      (s+a,(t-s)+(s+a),t+normalizedExponent background.classicalTower f)).eInfty)
    (hz : HasInfinityRepresentative _ 2 _ (finiteExtensionCorrectionLabel X Y f i s t a x) z) :
    ∃ zl : ((background.family.obj ((SyntheticObject.quotient q (extensionSourceObject background X Y f)).obj
      background.nu background.auxiliary)).sequence.ssData
      (s+a,(t-s)+(s+a),t+normalizedExponent background.classicalTower f)).eInfty,
      (background.family.map ((background.quotients.tower ((extensionSourceObject background X Y f).obj
        background.nu background.auxiliary)).rho i q hiq)).eInftyMap _ zl = z := by
  obtain ⟨zu,hzu⟩ := unshifted_label_infinity_exists X q (by omega) (s+a) ((t-s)+(s+a)) a
    (by omega) x hx
  let rn := (background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho i q hiq
  have he := family_infinity_representative_map rn _ _ zu hzu
  rw [correction_unshifted_label_rho] at he
  have he' := correctionInfinity_represents X Y f i s t a x _ he
  exact ⟨correctionInfinity X Y f q s t a zu,
    (correctionInfinity_rho X Y f i q hi hiq s t a zu).trans (he'.unique hz)⟩

/-- Proposition 6.20 with the cycle-set difference retained: failure of
essentiality after descent gives a fixed-target nonliftable short extension,
or a crossing in the same later synthetic ESS. -/
public theorem finiteExtension_nonliftableShort_or_lateCrossing (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ) (x y)
    (Wlater : FiniteExtensionWitness background X Y f rLater n s t x y)
    (Wearly : FiniteExtensionWitness background X Y f rEarlier n s t x y)
    (hle : rEarlier ≤ rLater) (hess : Wlater.Essential) (hne : ¬Wearly.Essential) :
    FiniteExtensionNonliftableShortTo X Y f rEarlier rLater n s t x y Wearly ∨
      ¬ ExtensionNoCrossingRange (background.convergentMap
        (.quotient (rLater-1) (extensionSourceObject background X Y f))
        (.quotient (rLater-1) (.nu Y)) (finiteExtensionMap background X Y f (rLater-1)))
        (t-s,t+normalizedExponent background.classicalTower f) s n s := by
  classical
  by_cases hc : ExtensionNoCrossingRange (background.convergentMap
      (.quotient (rLater-1) (extensionSourceObject background X Y f))
      (.quotient (rLater-1) (.nu Y)) (finiteExtensionMap background X Y f (rLater-1)))
      (t-s,t+normalizedExponent background.classicalTower f) s n s
  · have hy := earlier_target_nonzero X Y f rEarlier rLater n s t x y Wlater Wearly hle hess
    obtain ⟨a,ha,han,x',hx',z,hz,hs⟩ := finiteExtension_essential_shorter_source
      X Y f rEarlier n s t x y Wearly hy hne
    by_cases hxl : x'∈cycles background X (((rLater-1:ℕ):ℤ)-a) (s+a,(t-s)+(s+a))
    · have hi : 0<rEarlier-1 := by have := Wearly.page_ge_two; omega
      have haq : a<rEarlier-1 := by have := Wearly.length_upper; omega
      obtain ⟨zl,hzl⟩ := correction_source_lift_of_late_cycle X Y f
        (rEarlier-1) (rLater-1) hi (Nat.sub_le_sub_right hle 1) s t a haq x' hxl z hz
      apply False.elim
      exact essential_short_source_not_in_range
        (.quotient (rLater-1) (extensionSourceObject background X Y f))
        (.quotient (rLater-1) (.nu Y))
        (.quotient (rEarlier-1) (extensionSourceObject background X Y f))
        (.quotient (rEarlier-1) (.nu Y))
        (finiteExtensionMap background X Y f (rLater-1))
        (finiteExtensionMap background X Y f (rEarlier-1))
        ((background.quotients.tower ((extensionSourceObject background X Y f).obj background.nu background.auxiliary)).rho
          (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1))
        ((background.quotients.tower (background.nu.functor.obj (Y.obj background.auxiliary))).rho
          (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1))
        ((background.quotients.natural (background.normalizedMap X Y f).map).rho_naturality
          (Nat.sub_le_sub_right hle 1))
        (t-s,t+normalizedExponent background.classicalTower f) s n (s+a) (n-a)
        (by have := Wearly.length_lower; omega) (by omega) (by omega) hc z _ hs zl hzl
    · exact Or.inl ⟨a,ha,han,x',hx',hxl,z,hz,hs.1⟩
  · exact Or.inr hc

end
end KIP126.ProofTools.Paper
