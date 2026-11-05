module

import all KIP126.ProofTools.Paper.NuNumericalExtensions
import all KIP126.ProofTools.MahowaldLeibniz.Bockstein
import all KIP126.ProofTools.GeneralizedMahowald.ActualNoCrossing
import all KIP126.ProofTools.Paper.OriginalStatements

@[expose] section
namespace KIP126.ProofTools.Internal.FiniteLifting
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Paper.NuNumericalExtensions
open KIP126.AdamsSynthetic.Completed (background Spectrum SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private theorem regrade_comp_map {A B : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w')
    (a : BiHom m w A) (f : A ⟶ B) :
    homotopyRegrade hm hw (a ≫ f) = homotopyRegrade hm hw a ≫ f := by
  subst m'; subst w'; rfl

/-- A finite crossing-free extension sends every full source grade
to the specified finite target. -/
private theorem finite_target_of_full_source
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page : ℕ) (n s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n))
    (W : FiniteExtensionWitness background X Y f page n s t x y)
    (source : ((background.family.obj ((extensionSourceObject background X Y f).obj
      background.nu background.auxiliary)).sequence.ssData
      (s,(t-s)+s,t+normalizedExponent background.classicalTower f)).eInfty)
    (hsource : HasInfinityRepresentative _ 2 _
      (infiniteSourceForExtension background X Y f s t x) source)
    (hnc : ActualNoCrossing
      (background.convergentMap (.quotient (page-1) (extensionSourceObject background X Y f))
        (.quotient (page-1) (.nu Y)) (finiteExtensionMap background X Y f (page-1)))
      (t-s,t+normalizedExponent background.classicalTower f) s n) :
    ∃ a : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
      ((extensionSourceObject background X Y f).obj background.nu background.auxiliary),
      Detects (background.convergence (extensionSourceObject background X Y f))
        (s,(t-s)+s,t+normalizedExponent background.classicalTower f)
        (infiniteSourceForExtension background X Y f s t x)
        (homotopyRegrade (by dsimp; omega) rfl a) ∧
      Detects (background.convergence (.quotient (page-1) (.nu Y)))
        (s+n,(t-s)+(s+n),t+normalizedExponent background.classicalTower f)
        (finiteTargetForExtension background X Y f (page-1) n s t W.length_lower y)
        (homotopyRegrade (by dsimp; omega) rfl
          ((a ≫ (background.normalizedMap X Y f).map) ≫ XModLambdaN.incl _ (page-1))) := by
  let A := extensionSourceObject background X Y f
  let p : ℤ × ℤ := (t-s,t+normalizedExponent background.classicalTower f)
  let F := background.syntheticTower.filtration (A.obj background.nu background.auxiliary)
  haveI : Epi (F.toAssociatedGraded s p) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨ar,har⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s p)).mp
    inferInstance ((infinityGradedIso (background.convergence A) p s).hom source)
  let a : BiHom p.1 p.2 (A.obj background.nu background.auxiliary) := (F.F s p).arrow ar
  have had := source_frame_detects (background.convergence A) p s source _ hsource ar har
  have haq := detects_map A (.quotient (page-1) A) (XModLambdaN.incl _ (page-1))
    (s,p.1+s,p.2) _ _ had
  have hlabel : familyPageMap background.family (XModLambdaN.incl (A.obj background.nu background.auxiliary) (page-1))
      2 (s,p.1+s,p.2) (infiniteSourceForExtension background X Y f s t x) =
      finiteSourceForExtension background X Y f (page-1) s t x := by
    unfold infiniteSourceForExtension finiteSourceForExtension finiteNuLabel
    rw [←page_regrade]
    rfl
  have haq' : Detects (background.convergence (.quotient (page-1) A))
      (s,p.1+s,p.2) (finiteSourceForExtension background X Y f (page-1) s t x)
      ((homotopyRegrade (by dsimp; omega) rfl a) ≫ XModLambdaN.incl _ (page-1)) := by
    exact (congrArg (fun z => Detects (background.convergence (.quotient (page-1) A))
      (s,p.1+s,p.2) z
      ((homotopyRegrade (by dsimp; omega) rfl a) ≫ XModLambdaN.incl _ (page-1))) hlabel).mp haq
  rw [←regrade_comp_map] at haq'
  obtain ⟨source',hsource',arq,harq,hgarq⟩ := frame_of_source_detects
    (background.convergence (.quotient (page-1) A)) p s _
    (a ≫ XModLambdaN.incl _ (page-1)) haq'
  have hs : source'=W.source := hsource'.unique W.source_rep
  rw [hs] at hgarq
  obtain ⟨br,hbr,hgbr⟩ := tower_target_of_any_source_frame
    (background.convergentMap (.quotient (page-1) A) (.quotient (page-1) (.nu Y))
      (finiteExtensionMap background X Y f (page-1))) p s n W.source W.target
    W.equation hnc arq hgarq
  have hb := source_frame_detects (background.convergence (.quotient (page-1) (.nu Y)))
    p (s+n) W.target _ W.target_rep br hgbr
  rw [←hbr,harq] at hb
  have hnat : (a ≫ XModLambdaN.incl _ (page-1)) ≫
      finiteExtensionMap background X Y f (page-1) =
      (a ≫ (background.normalizedMap X Y f).map) ≫ XModLambdaN.incl _ (page-1) := by
    change (a ≫ XModLambdaN.incl
        ((SyntheticCategory.biShift (0,(normalizedExponent background.classicalTower f:ℤ))).obj
          (background.nu.functor.obj (X.obj background.auxiliary))) (page-1)) ≫
        XModLambdaN.map (background.normalizedMap X Y f).map (page-1) =
      (a ≫ (background.normalizedMap X Y f).map) ≫ XModLambdaN.incl _ (page-1)
    simpa only [Category.assoc] using
      congrArg (fun z => a ≫ z)
        (XModLambdaN.incl_naturality (background.normalizedMap X Y f).map (page-1)).symm
  rw [hnat] at hb
  exact ⟨a,had,hb⟩

/-- An E∞ source label supplies the full source; the permanent finite
target and normalized image then define an infinite extension. -/
private theorem finite_extension_to_infinite
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page : ℕ) (n s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n))
    (hx : IsPermanentCycle (background.classical.obj (X.obj background.auxiliary)) (s,t) x)
    (W : FiniteExtensionWitness background X Y f page n s t x y)
    (source : ((background.family.obj ((extensionSourceObject background X Y f).obj
      background.nu background.auxiliary)).sequence.ssData
      (s,(t-s)+s,t+normalizedExponent background.classicalTower f)).eInfty)
    (hsource : HasInfinityRepresentative _ 2 _
      (infiniteSourceForExtension background X Y f s t x) source)
    (hnc : ActualNoCrossing
      (background.convergentMap (.quotient (page-1) (extensionSourceObject background X Y f))
        (.quotient (page-1) (.nu Y)) (finiteExtensionMap background X Y f (page-1)))
      (t-s,t+normalizedExponent background.classicalTower f) s n) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) (s+n,t+n) y ∧
      InfiniteExtension background X Y f n s t x y := by
  obtain ⟨a,ha,hb⟩ := finite_target_of_full_source X Y f page n s t x y W source hsource hnc
  let e : ℤ := normalizedExponent background.classicalTower f
  have hw : 0 ≤ (t+n)-(t+e) ∧ (t+n)-(t+e)<((page-1:ℕ):ℤ) := by
    have := W.length_lower
    have := W.length_upper
    have := W.page_ge_two
    constructor <;> dsimp [e] <;> omega
  have hq : 0<page-1 := by have := W.page_ge_two; omega
  have hi : (s+n,(t-s)+(s+n),t+e)=(s+n,t+n,t+e) := by
    ext <;> dsimp <;> omega
  have hb' := detects_transport hi _ _ hb
  have htarget : regradeE2 hi
      (finiteTargetForExtension background X Y f (page-1) n s t W.length_lower y) =
      (background.family.quotientProjection (background.nu.functor.obj (Y.obj background.auxiliary)) (page-1)).pageMap
        2 (s+n,t+n,t+e) (nuWeightLabel background Y (s+n) (t+n) (t+e) (by omega) y) := by
    have hproj : familyPageMap background.family
        (XModLambdaN.incl (background.nu.functor.obj (Y.obj background.auxiliary)) (page-1))
        2 (s+n,(t-s)+(s+n),t+e)
        (infiniteTargetForExtension background X Y f n s t W.length_lower y) =
        finiteTargetForExtension background X Y f (page-1) n s t W.length_lower y := by
      unfold infiniteTargetForExtension finiteTargetForExtension finiteTargetLabel
      rw [←page_regrade]
      rfl
    rw [←hproj,page_regrade]
    congr 1
    exact eq_of_heq ((regradeE2_heq hi _).trans
      (infinite_target_nuWeight_heq X Y f n s t W.length_lower y))
  rw [htarget] at hb'
  rw [normalized_homotopy_regrade_trans,regrade_comp_map] at hb'
  let b : BiHom ((t+n)-(s+n)) (t+e) (background.nu.functor.obj (Y.obj background.auxiliary)) :=
    homotopyRegrade (by omega) rfl (a ≫ (background.normalizedMap X Y f).map)
  have hbfinite : Detects (background.convergence (.quotient (page-1) (.nu Y)))
      (s+n,t+n,t+e)
      ((background.family.quotientProjection (background.nu.functor.obj (Y.obj background.auxiliary)) (page-1)).pageMap
        2 (s+n,t+n,t+e) (nuWeightLabel background Y (s+n) (t+n) (t+e) (by omega) y))
      (b ≫ XModLambdaN.incl _ (page-1)) := hb'
  have hy := finite_target_from_full_lift_is_permanent Y (page-1) hq (s+n) (t+n) (t+e)
    hw y b hbfinite
  have hbfull := finite_projection_detects_reflect Y (page-1) hq (s+n) (t+n) (t+e)
    hw y b hbfinite
  have hs : (s,(t-s)+s,t+e)=(s,t,t+e) := by simp
  have ha' := detects_transport hs _ _ ha
  have hsourceLabel : regradeE2 hs (infiniteSourceForExtension background X Y f s t x) =
      regradeE2 (by simp [e]) (background.comparison.nuE2 X (normalizedExponent background.classicalTower f) s t 0 x) := by
    unfold infiniteSourceForExtension
    rw [normalized_regrade_trans]
  rw [hsourceLabel,normalized_homotopy_regrade_trans] at ha'
  dsimp only [e,homotopyRegrade] at ha'
  have hpair : fullDetectedPairAt X Y n s t x y (normalizedExponent background.classicalTower f)
      (background.normalizedMap X Y f).map := by
    refine ⟨W.length_lower,a,a ≫ (background.normalizedMap X Y f).map,?_,hbfull,rfl⟩
    exact ha'
  have hyp := permanent_cycle_of_member Y (s+n,t+n) y hy
  exact ⟨hyp,actual_detected_pair_infinite X Y f n s t x y hx hyp hpair⟩

/-- Classical source permanence supplies the full source grade. -/
private theorem finite_extension_of_permanent_to_infinite
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page : ℕ) (n s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n))
    (hx : IsPermanentCycle (background.classical.obj (X.obj background.auxiliary)) (s,t) x)
    (W : FiniteExtensionWitness background X Y f page n s t x y)
    (hnc : ActualNoCrossing
      (background.convergentMap (.quotient (page-1) (extensionSourceObject background X Y f))
        (.quotient (page-1) (.nu Y)) (finiteExtensionMap background X Y f (page-1)))
      (t-s,t+normalizedExponent background.classicalTower f) s n) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) (s+n,t+n) y ∧
      InfiniteExtension background X Y f n s t x y := by
  obtain ⟨source,hsource⟩ := shifted_full_source_exists X
    (normalizedExponent background.classicalTower f) s t x
    (permanent_member_of_cycle X (s,t) x hx)
  have hi : (s,t,t+(normalizedExponent background.classicalTower f:ℤ)-(0:ℕ)) =
      (s,(t-s)+s,t+normalizedExponent background.classicalTower f) := by simp
  have hs := representative_transport hi _ _ hsource
  exact finite_extension_to_infinite X Y f page n s t x y hx W _ hs hnc

/-- Realization transports the complete synthetic extension to one classical
source representative and its actual image, with both specified detections. -/
private theorem finite_extension_of_permanent_to_classical
    (R : RealizationCoordinates background)
    (hcomp : LambdaInversionAdamsComparison background R)
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (page : ℕ) (n s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n))
    (hx : IsPermanentCycle (background.classical.obj (X.obj background.auxiliary)) (s,t) x)
    (W : FiniteExtensionWitness background X Y f page n s t x y)
    (hnc : ActualNoCrossing
      (background.convergentMap (.quotient (page-1) (extensionSourceObject background X Y f))
        (.quotient (page-1) (.nu Y)) (finiteExtensionMap background X Y f (page-1)))
      (t-s,t+normalizedExponent background.classicalTower f) s n) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) (s+n,t+n) y ∧
      InfiniteExtension background X Y f n s t x y ∧
      ∃ a : HomotopyGroup (t-s) (X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence X) (s,t) x a ∧
        ClassicalDetects (background.classicalConvergence Y) (s+n,t+n) y
          (eqToHom (congrArg (Sphere (C := Spectrum))
            (show (t+n)-(s+n)=t-s by omega)) ≫ a ≫ f) := by
  obtain ⟨hy,he⟩ := finite_extension_of_permanent_to_infinite X Y f page n s t x y hx W hnc
  refine ⟨hy,he,?_⟩
  exact KIP126.ProofTools.Paper.infinite_extension_to_classical_extension background R hcomp X Y f n s t
    ⟨x,permanent_member_of_cycle X (s,t) x hx⟩
    ⟨y,permanent_member_of_cycle Y (s+n,t+n) y hy⟩ he

end
end KIP126.ProofTools.Internal.FiniteLifting
