module

import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelLabels
import all KIP126.ProofTools.GeneralizedMahowald.FiniteComparison
import all KIP126.ProofTools.GeneralizedLeibniz.SquareRepresentatives
import all KIP126.ProofTools.GeneralizedMahowald.HSource
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelConclusion

/-! Reflection of the finite Mahowald source label through rho
and inclusion-compatible suspension comparisons. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The specified shift comparison supplies the inverse actual class. -/
private theorem shift_class_surjective (V : SyntheticObject (coefficients := background.coefficients)) (δ p : ℤ×ℤ)
    (b : BiHom (p+δ).1 (p+δ).2 ((SyntheticObject.shift δ V).obj background.nu background.auxiliary)) :
    ∃ a : BiHom p.1 p.2 (V.obj background.nu background.auxiliary),
      shiftHomotopyClass δ p a=b := by
  let E := ((essShift δ).filtered V p).ambient
  let a := E.inv b
  refine ⟨a,?_⟩
  have h : E.hom a=b := E.toLinearEquiv.apply_symm_apply b
  exact ((essShift δ).ambient_eq V p a).symm.trans h

/-- Reverse a specified shifted detection, preserving its actual representative. -/
private theorem deshift_detected_representative
    (V : SyntheticObject (coefficients := background.coefficients)) (δ p : ℤ×ℤ) (s : ℤ)
    (x : (background.family.obj (V.obj background.nu background.auxiliary)).E₂ (s,p.1+s,p.2))
    (b : BiHom (p+δ).1 (p+δ).2 ((SyntheticObject.shift δ V).obj background.nu background.auxiliary))
    (hb : Detects (background.convergence (.shift δ V)) (s,(p+δ).1+s,(p+δ).2)
      (((essShift δ).page V 2 (by decide) p s).hom x)
      (homotopyRegrade (by dsimp; omega) rfl b)) :
    ∃ a : BiHom p.1 p.2 (V.obj background.nu background.auxiliary),
      shiftHomotopyClass δ p a=b ∧
      Detects (background.convergence V) (s,p.1+s,p.2) x
        (homotopyRegrade (by dsimp; omega) rfl a) := by
  obtain ⟨a,ha⟩ := shift_class_surjective V δ p b
  refine ⟨a,ha,?_⟩
  apply detects_of_shift V δ p s x a
  simpa only [ha] using hb

private theorem shift_class_injective (V : SyntheticObject (coefficients := background.coefficients)) (δ p : ℤ×ℤ) :
    Function.Injective (shiftHomotopyClass δ p (X:=V.obj background.nu background.auxiliary)) := by
  intro a b hab
  apply ((essShift δ).filtered V p).ambient.toLinearEquiv.injective
  change ((essShift δ).filtered V p).ambient.hom a =
    ((essShift δ).filtered V p).ambient.hom b
  simpa only [(essShift δ).ambient_eq V p a,(essShift δ).ambient_eq V p b] using hab

private theorem shift_class_comp (V W : SyntheticObject (coefficients := background.coefficients)) (δ p : ℤ×ℤ)
    (f : V.obj background.nu background.auxiliary ⟶ W.obj background.nu background.auxiliary)
    (a : BiHom p.1 p.2 (V.obj background.nu background.auxiliary)) :
    shiftHomotopyClass δ p (a≫f)=
      shiftHomotopyClass δ p a≫(SyntheticCategory.biShift δ).map f := by
  simp only [shiftHomotopyClass,Functor.map_comp,Category.assoc]


/-- The intrinsic source label becomes exactly the shifted native finite label
under its fixed quotient comparison. -/
private theorem source_label_quotient_shift
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (e s t : ℤ) (K : ℕ)
    (x : Ambient background X (s,t)) :
    familyPageMap background.family (levelQuotientShiftIso X e q).hom 2
      (s,(t-s)+s,t+e-K)
      (KIP126.ProofTools.Standard.levelFiniteSourceLabel X q e s t K x) =
      regradeE2 (by ext <;> dsimp <;> omega)
        (((essShift (0,e)).page (.quotient q (.nu X)) 2 (by decide) (t-s,t-K) s).hom
          (regradeE2 (by simp) (finiteTargetLabel background X q s t K x))) := by
  change (familyPageMap background.family (levelQuotientShiftIso X e q).hom 2 _)
    ((familyPageMap background.family (levelQuotientShiftIso X e q).inv 2 _) _) = _
  rw [←ModuleCat.comp_apply,family_page_comp,Iso.inv_hom_id]
  simp only [familyPageMap,SyntheticAdamsFamily.pageMap,SyntheticAdamsFamily.map_id,
    SpectralSequenceMorphism.pageMap_id,ModuleCat.id_apply]

/-- Reflect an actual intrinsic-source detection to the native representative
from which its normalized representative was constructed. -/
private theorem normalized_source_detects_reflect
    (X : AdamsObject (coefficients := background.coefficients)) (q K : ℕ) (e s t : ℤ)
    (x : Ambient background X (s,t))
    (c : BiHom (t-s) (t-K) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (hc : Detects (background.convergence (.quotient q (.shift (0,e) (.nu X))))
      (s,(t-s)+s,t+e-K)
      (KIP126.ProofTools.Standard.levelFiniteSourceLabel X q e s t K x)
      (homotopyRegrade (by dsimp; omega) rfl
        (finiteLevelNormalizedRepresentative X e q K s t c))) :
    Detects (background.convergence (.quotient q (.nu X))) (s,t,t-K)
      (finiteTargetLabel background X q s t K x) c := by
  let V : SyntheticObject (coefficients := background.coefficients) := .quotient q (.nu X)
  let δ : ℤ×ℤ := (0,e)
  let p : ℤ×ℤ := (t-s,t-K)
  let i : Tridegree := (s,(t-s)+s,t+e-K)
  have hmap := detects_map (.quotient q (.shift (0,e) (.nu X))) (.shift δ V)
    (levelQuotientShiftIso X e q).hom i _ _ hc
  dsimp only [i,V,δ,SyntheticObject.obj] at hmap
  rw [source_label_quotient_shift] at hmap
  have hi : i=(s,(p+δ).1+s,(p+δ).2) := by ext <;> dsimp [i,p,δ] <;> omega
  have hshift := detects_transport hi _ _ hmap
  have hshift' : Detects (background.convergence (.shift δ V))
      (s,(p+δ).1+s,(p+δ).2)
      (((essShift δ).page V 2 (by decide) p s).hom
        (regradeE2 (by simp [p]) (finiteTargetLabel background X q s t K x)))
      (homotopyRegrade (by dsimp; omega) rfl (shiftHomotopyClass δ p c)) := by
    convert hshift using 1
    · simp only [normalized_regrade_trans]
      rfl
    · simp only [finiteLevelNormalizedRepresentative,regrade_precomp,
        Category.assoc,Iso.inv_hom_id,Category.comp_id]
      simp only [←Category.assoc,eqToHom_trans]
      rfl
  have hnative := detects_of_shift V δ p s _ c hshift'
  have hi0 : (s,p.1+s,p.2)=(s,t,t-K) := by simp [p]
  have hout := detects_transport hi0 _ _ hnative
  convert hout using 1
  · simp only [normalized_regrade_trans]
    rfl
  · simp only [regrade_precomp,←Category.assoc,eqToHom_trans,eqToHom_refl,
      Category.id_comp]


private def finiteSourceNativeInverse (X : AdamsObject (coefficients := background.coefficients)) (q K : ℕ) (e s t : ℤ)
    (a : BiHom (t-s) (t+e-K)
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q)) :
    BiHom (t-s) (t-K) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q) :=
  quotientUnshift X (0,e) (t-s,t-K) q (levelQuotientShiftIso X e q)
    (homotopyRegrade (by simp) (by dsimp; omega) a)

private theorem finite_source_native_inverse_recover
    (X : AdamsObject (coefficients := background.coefficients)) (q K : ℕ) (e s t : ℤ)
    (a : BiHom (t-s) (t+e-K)
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q)) :
    finiteLevelNormalizedRepresentative X e q K s t
      (finiteSourceNativeInverse X q K e s t a)=a := by
  unfold finiteLevelNormalizedRepresentative finiteSourceNativeInverse
  rw [←regrade_comp,shift_quotient_unshift,homotopy_regrade_inverse]

private theorem finite_source_native_inverse_rho
    (X : AdamsObject (coefficients := background.coefficients)) (A N K : ℕ) (hA : 0 < A) (hAN : A ≤ N) (e s t : ℤ)
    (c : BiHom (t-s) (t+e-K)
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) N)) :
    finiteSourceNativeInverse X N K e s t c ≫ (background.quotients.tower _).rho A N hAN =
      finiteSourceNativeInverse X A K e s t (c≫(background.quotients.tower _).rho A N hAN) := by
  unfold finiteSourceNativeInverse
  rw [quotient_unshift_restriction X (0,e) (t-s,t-K) A N hA hAN
    (levelQuotientShiftIso X e A) (levelQuotientShiftIso X e N)
    (level_quotient_shift_incl X e A) (level_quotient_shift_incl X e N),regrade_comp]

/-- Rho reflection of the specified intrinsic source label at arbitrary weight
shift and lambda layer. The representative c is unchanged in the strong
quotient; the original classical x gains its full cycle qualification.
-/
private theorem inside_shift_source_rho_reflection
    (X : AdamsObject (coefficients := background.coefficients)) (A N K : ℕ) (hAN : A ≤ N) (hKA : K < A)
    (e s t : ℤ) (x : Ambient background X (s,t))
    (a : BiHom (t-s) (t+e-K)
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) A))
    (c : BiHom (t-s) (t+e-K)
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) N))
    (ha : Detects (background.convergence (.quotient A (.shift (0,e) (.nu X))))
      (s,(t-s)+s,t+e-K)
      (KIP126.ProofTools.Standard.levelFiniteSourceLabel X A e s t K x)
      (homotopyRegrade (by dsimp; omega) rfl a))
    (hρ : c≫(background.quotients.tower _).rho A N hAN=a) :
    Detects (background.convergence (.quotient N (.shift (0,e) (.nu X))))
      (s,(t-s)+s,t+e-K)
      (KIP126.ProofTools.Standard.levelFiniteSourceLabel X N e s t K x)
      (homotopyRegrade (by dsimp; omega) rfl c) ∧
      x ∈ cycles background X ((N:ℤ)-K) (s,t) := by
  let a0 := finiteSourceNativeInverse X A K e s t a
  let c0 := finiteSourceNativeInverse X N K e s t c
  have ha0 := normalized_source_detects_reflect X A K e s t x a0 (by
    simpa only [a0,finite_source_native_inverse_recover] using ha)
  have hρ0 : c0≫(background.quotients.tower _).rho A N hAN=a0 := by
    dsimp only [a0,c0]
    rw [finite_source_native_inverse_rho X A N K (by omega) hAN e s t c,hρ]
  obtain ⟨hc0,hx⟩ := finite_rho_lift_label_and_cycles X A N K hAN hKA s t x a0 ha0 c0 hρ0
  have hc := finite_level_normalized_representative_detects X e N K s t x c0 hc0
  refine ⟨?_,hx⟩
  simpa only [c0,finite_source_native_inverse_recover] using hc


/-- Suspended source-label comparison for the same strong-quotient class c.
For every inclusion-compatible suspension comparison, the spherewise
comparison theorem supplies the rho square. -/
private theorem finite_suspended_source_label_reflection
    (X : AdamsObject (coefficients := background.coefficients)) (e : ℤ) (A N K : ℕ) (hAN : A ≤ N) (hKA : K < A)
    (s t : ℤ) (p : ℤ×ℤ) (hp : p.1=t-s+1) (hw : p.2=t+e-K)
    (x : Ambient background X (s,t))
    (exA : XModLambdaN (((SyntheticCategory.biShift (0,e)).obj
      (background.nu.functor.obj (X.obj background.auxiliary)))⟦(1:ℤ)⟧) A ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) A)⟦(1:ℤ)⟧)
    (exN : XModLambdaN (((SyntheticCategory.biShift (0,e)).obj
      (background.nu.functor.obj (X.obj background.auxiliary)))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) N)⟦(1:ℤ)⟧)
    (hexA : XModLambdaN.incl _ A≫exA.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ A))
    (hexN : XModLambdaN.incl _ N≫exN.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (a : BiHom p.1 p.2 (XModLambdaN (((SyntheticCategory.biShift (0,e)).obj
      (background.nu.functor.obj (X.obj background.auxiliary)))⟦(1:ℤ)⟧) A))
    (c : BiHom p.1 p.2 (XModLambdaN (((SyntheticCategory.biShift (0,e)).obj
      (background.nu.functor.obj (X.obj background.auxiliary)))⟦(1:ℤ)⟧) N))
    (hρ : c≫(background.quotients.tower _).rho A N hAN=a)
    (ha : Detects (background.convergence (.shift (1,0) (.quotient A (.shift (0,e) (.nu X)))))
      (s,p.1+s,p.2) (finiteConclusionSourceLabel X A K e s t p hp hw x)
      (homotopyRegrade (by dsimp; omega) rfl
        (a≫exA.hom≫(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _))) :
    Detects (background.convergence (.shift (1,0) (.quotient N (.shift (0,e) (.nu X)))))
      (s,p.1+s,p.2) (finiteConclusionSourceLabel X N K e s t p hp hw x)
      (homotopyRegrade (by dsimp; omega) rfl
        (c≫exN.hom≫(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) ∧
      x ∈ cycles background X ((N:ℤ)-K) (s,t) := by
  let VA : SyntheticObject (coefficients := background.coefficients) := .quotient A (.shift (0,e) (.nu X))
  let VN : SyntheticObject (coefficients := background.coefficients) := .quotient N (.shift (0,e) (.nu X))
  let p₀ : ℤ×ℤ := (t-s,t+e-K)
  let δ : ℤ×ℤ := (1,0)
  have hP : p=p₀+δ := by ext <;> dsimp [p₀,δ] <;> omega
  let κ := SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1
  let ac' : BiHom p.1 p.2 ((SyntheticObject.shift δ VA).obj background.nu background.auxiliary) :=
    a≫exA.hom≫κ.inv.app _
  let cc' : BiHom p.1 p.2 ((SyntheticObject.shift δ VN).obj background.nu background.auxiliary) :=
    c≫exN.hom≫κ.inv.app _
  let ac := homotopyRegrade (congrArg Prod.fst hP) (congrArg Prod.snd hP) ac'
  let cc := homotopyRegrade (congrArg Prod.fst hP) (congrArg Prod.snd hP) cc'
  have hsGrade : (s,p.1+s,p.2)=(s,(p₀+δ).1+s,(p₀+δ).2) := by rw [hP]
  have hsLabelA : regradeE2 hsGrade (finiteConclusionSourceLabel X A K e s t p hp hw x) =
      ((essShift δ).page VA 2 (by decide) p₀ s).hom
        (KIP126.ProofTools.Standard.levelFiniteSourceLabel X A e s t K x) := by
    unfold finiteConclusionSourceLabel
    rw [normalized_regrade_trans]
    exact finite_conclusion_shift_label_to_page VA δ p₀ s _ rfl _
  have hsLabelN : regradeE2 hsGrade (finiteConclusionSourceLabel X N K e s t p hp hw x) =
      ((essShift δ).page VN 2 (by decide) p₀ s).hom
        (KIP126.ProofTools.Standard.levelFiniteSourceLabel X N e s t K x) := by
    unfold finiteConclusionSourceLabel
    rw [normalized_regrade_trans]
    exact finite_conclusion_shift_label_to_page VN δ p₀ s _ rfl _
  have haShift := detects_transport hsGrade _ _ ha
  rw [hsLabelA] at haShift
  obtain ⟨an,han,hdan⟩ := deshift_detected_representative VA δ p₀ s
    (KIP126.ProofTools.Standard.levelFiniteSourceLabel X A e s t K x) ac
    (by simpa only [ac,ac',regrade_precomp,←Category.assoc,eqToHom_trans] using haShift)
  obtain ⟨cn,hcn⟩ := shift_class_surjective VN δ p₀ cc
  let rho : VN.obj background.nu background.auxiliary ⟶ VA.obj background.nu background.auxiliary :=
    (background.quotients.tower _).rho A N hAN
  have hr : cn≫rho=an := by
    apply shift_class_injective VA δ p₀
    rw [shift_class_comp VN VA δ p₀ rho cn,hcn,han]
    have hcomp := finite_suspension_restriction_on_spheres X e A N (by omega) hAN
      exA exN hexA hexN p.1 p.2 c
    simp only [←Category.assoc] at hcomp
    rw [hρ] at hcomp
    have hh := congrArg (fun z => z≫κ.inv.app (VA.obj background.nu background.auxiliary)) hcomp
    simp only [Category.assoc] at hh
    have hnat := κ.inv.naturality rho
    dsimp only [rho,VA,VN,SyntheticObject.obj] at hnat hh
    rw [hnat] at hh
    have hh' : cc'≫(SyntheticCategory.biShift δ).map rho=ac' := by
      simpa only [ac',cc',rho,δ,VA,VN,SyntheticObject.obj,Category.assoc] using hh.symm
    simpa only [ac,cc,regrade_precomp,Category.assoc] using
      congrArg (homotopyRegrade (congrArg Prod.fst hP) (congrArg Prod.snd hP)) hh'
  obtain ⟨hcnative,hx⟩ := inside_shift_source_rho_reflection X A N K hAN hKA e s t x
    an cn hdan hr
  have hout := detects_shift VN δ p₀ s
    (KIP126.ProofTools.Standard.levelFiniteSourceLabel X N e s t K x) cn hcnative
  rw [hcn] at hout
  have hout' := detects_transport hsGrade.symm _ _ hout
  refine ⟨?_,hx⟩
  convert hout' using 1
  · rw [←hsLabelN,normalized_regrade_trans]
    rfl
  · simp only [cc,cc',regrade_precomp,←Category.assoc,eqToHom_trans]
    rfl

end
end KIP126.ProofTools.Internal.Mahowald
