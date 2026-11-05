module

import KIP126.Literature.Standard.FiniteQuotientComparison
import all KIP126.ProofTools.SyntheticCoverage.OrdinaryFiniteRows
import all KIP126.ProofTools.SyntheticCoverage.CommonLift

/-! The same-root ordinary input for early-boundary differential comparisons.
The actual finite-quotient comparison constructs one root with its prescribed
first label and selected top coefficient image for arbitrary admissible Adams
objects.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2500000

/-- The zero source-shift coordinate of the same normalized triangle. -/
private def ordinaryNativeTriangle (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0) : Triangle SyntheticSpectrum :=
  Triangle.mk (background.nu.functor.map T.f) (normalizedTriangle background T he).mor₂
    ((normalizedTriangle background T he).mor₃≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (zeroNormalizedSourceIso T he hf).hom)

/-- Transport of the row with its native suspension comparison. -/
private theorem native_unrotated_row_transport
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0) (q : ℕ)
    (eA : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) q≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ q)⟦(1:ℤ)⟧)
    (heA : XModLambdaN.incl _ q≫eA.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q))
    (hrow : Triangle.mk (XModLambdaN.map (normalizedTriangle background T he).mor₁ q)
      (XModLambdaN.map (normalizedTriangle background T he).mor₂ q)
      (XModLambdaN.map (normalizedTriangle background T he).mor₃ q≫eA.hom)∈distTriang SyntheticSpectrum) :
    ∃ eX : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) q≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) q)⟦(1:ℤ)⟧,
      XModLambdaN.incl _ q≫eX.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q) ∧
      Triangle.mk (XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₁ q)
        (XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₂ q)
        (XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₃ q≫eX.hom)∈distTriang SyntheticSpectrum := by
  let N := normalizedTriangle background T he
  let E := zeroNormalizedSourceIso T he hf
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let Q := background.quotients.functoriality.functor q
  let eX := Q.mapIso (S.mapIso E.symm) ≪≫ eA ≪≫ S.mapIso (Q.mapIso E)
  have heX : XModLambdaN.incl _ q≫eX.hom=S.map (XModLambdaN.incl _ q) := by
    dsimp only [eX,Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom,Q,LambdaQuotientFunctoriality.functor]
    rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,←Category.assoc (XModLambdaN.incl _ q),heA]
    change S.map E.inv≫S.map (XModLambdaN.incl _ q)≫S.map (XModLambdaN.map E.hom q)=_
    rw [←Functor.map_comp,←XModLambdaN.incl_naturality,←Functor.map_comp,←Category.assoc,
      Iso.inv_hom_id,Category.id_comp]
  have hnat : XModLambdaN.map (S.map E.hom) q≫eX.hom=eA.hom≫S.map (XModLambdaN.map E.hom q) := by
    dsimp only [eX,Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom,Q,LambdaQuotientFunctoriality.functor]
    rw [←Category.assoc,←background.quotients.functoriality.map_comp,←Functor.map_comp,Iso.hom_inv_id,
      CategoryTheory.Functor.map_id,background.quotients.functoriality.map_id,Category.id_comp]
  let R := Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q)
    (XModLambdaN.map N.mor₃ q≫eA.hom)
  let U := Triangle.mk (XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₁ q)
    (XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₂ q)
    (XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₃ q≫eX.hom)
  have hfmap : E.hom≫background.nu.functor.map T.f=N.mor₁ := by
    rw [←zero_normalized_source_inv_arrow T he hf]
    simp only [E,N,←Category.assoc,Iso.hom_inv_id,Category.id_comp]
  let e : R≅U := Triangle.isoMk _ _ (Q.mapIso E) (Iso.refl _) (Iso.refl _) (by
      symm
      change XModLambdaN.map E.hom q≫XModLambdaN.map (background.nu.functor.map T.f) q=XModLambdaN.map N.mor₁ q≫𝟙 _
      rw [←background.quotients.functoriality.map_comp,hfmap,Category.comp_id])
    (by simp [R,U,ordinaryNativeTriangle,N]) (by
      symm
      change 𝟙 _≫(XModLambdaN.map (N.mor₃≫S.map E.hom) q≫eX.hom)=
        (XModLambdaN.map N.mor₃ q≫eA.hom)≫S.map (XModLambdaN.map E.hom q)
      rw [Category.id_comp,background.quotients.functoriality.map_comp,Category.assoc,hnat]
      simp only [Category.assoc])
  exact ⟨eX,heX,isomorphic_distinguished R hrow U e.symm⟩

/-- Transfer the ordinary no-return condition through the actual zero-source isomorphism. -/
private theorem ordinary_native_no_return
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (i : ℕ) (hi : 0 < i) (m w : ℤ)
    (b : BiHom m w (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (i+1-i)))⟦(1:ℤ)⟧))
    (z : (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (i+1-i)))⟦(1:ℤ)⟧) ⟶
      XModLambdaN (normalizedTriangle background T he).obj₃ i) : b≫z=0 := by
  obtain ⟨e₁,_⟩ := quotient_suspension_inclusion_exists (normalizedTriangle background T he).obj₁ (i+1-i)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let e := (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
    (F.mapIso ((background.quotients.functoriality.functor (i+1-i)).mapIso (zeroNormalizedSourceIso T he hf)))
  have h := ordinary_forward_no_return T he hf i hi m w e₁ (b≫e.inv) (e.hom≫z)
  simpa only [Category.assoc,Iso.inv_hom_id_assoc] using h

/-- Transport the entire finite-lift function through one quotient-length equality. -/
private theorem forward_lift_short_transport
    {A B C S : SyntheticSpectrum} (F : SyntheticSpectrum ⥤ SyntheticSpectrum)
    (i N D E : ℕ) (hDE : D=E) (f : A ⟶ B)
    (rho : XModLambdaN C N ⟶ XModLambdaN C i)
    (g : XModLambdaN B i ⟶ XModLambdaN C i)
    (h : XModLambdaN C N ⟶ (XModLambdaN A N)⟦(1:ℤ)⟧)
    (delta : XModLambdaN B i ⟶ (F.obj (XModLambdaN B D))⟦(1:ℤ)⟧)
    (lambda : F.obj (XModLambdaN A D) ⟶ XModLambdaN A N)
    (H : ∀ (a : S ⟶ XModLambdaN B i) (b : S ⟶ (F.obj (XModLambdaN A D))⟦(1:ℤ)⟧),
      a≫delta=b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (F.map (XModLambdaN.map f D)) →
      ∃ R : S ⟶ XModLambdaN C N, R≫rho=a≫g ∧ R≫h=b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map lambda) :
    let deltaE := Eq.mp (congrArg (fun d => XModLambdaN B i ⟶ (F.obj (XModLambdaN B d))⟦(1:ℤ)⟧) hDE) delta
    let lambdaE := Eq.mp (congrArg (fun d => F.obj (XModLambdaN A d) ⟶ XModLambdaN A N) hDE) lambda
    ∀ (a : S ⟶ XModLambdaN B i) (b : S ⟶ (F.obj (XModLambdaN A E))⟦(1:ℤ)⟧),
      a≫deltaE=b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (F.map (XModLambdaN.map f E)) →
      ∃ R : S ⟶ XModLambdaN C N, R≫rho=a≫g ∧ R≫h=b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map lambdaE := by
  subst E
  exact H

/-- The forward three-by-three chase retains both images of the same root. The actual distinguished row is an explicit input to this internal reduction. -/
private theorem ordinary_forward_lift_of_native_row
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (i : ℕ) (hi : 0 < i) (m w : ℤ)
    (eX : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) (i+1)≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (i+1))⟦(1:ℤ)⟧)
    (hrow : Triangle.mk (XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₁ (i+1))
      (XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₂ (i+1))
      (XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₃ (i+1)≫eX.hom)∈distTriang SyntheticSpectrum) :
    let P := ordinaryNativeTriangle T he hf
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
    let delta : XModLambdaN P.obj₂ i ⟶ (F.obj (XModLambdaN P.obj₂ 1))⟦(1:ℤ)⟧ := by
      simpa only [show i.succ-i=1 by omega] using ((background.quotients.tower P.obj₂).triangle hi (Nat.lt_succ_self i)).delta
    ∀ (a : BiHom m w (XModLambdaN P.obj₂ i)) (b : BiHom m w ((F.obj (XModLambdaN P.obj₁ 1))⟦(1:ℤ)⟧)),
      a≫delta=b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (F.map (XModLambdaN.map P.mor₁ 1)) →
      ∃ R : BiHom m w (XModLambdaN P.obj₃ (i+1)),
        R≫(background.quotients.tower P.obj₃).rho i (i+1) (by omega)=a≫XModLambdaN.map P.mor₂ i ∧
        R≫XModLambdaN.map P.mor₃ (i+1)≫eX.hom=
          b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (finiteTopInclusion P.obj₁ i hi) := by
  have H := forward_lift_of_unrotated_row (ordinaryNativeTriangle T he hf) i 1 hi
    (by decide) eX hrow m w (ordinary_native_no_return T he hf i hi m w)
  let P := ordinaryNativeTriangle T he hf
  have H' := forward_lift_short_transport (SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ)))
    i (i+1) (i+1-i) 1 (by omega) P.mor₁ ((background.quotients.tower P.obj₃).rho i (i+1) (by omega))
    (XModLambdaN.map P.mor₂ i) (XModLambdaN.map P.mor₃ (i+1)≫eX.hom)
    ((background.quotients.tower P.obj₂).triangle hi (Nat.lt_succ_self i)).delta
    ((background.quotients.tower P.obj₁).triangle hi (Nat.lt_succ_self i)).lambdaMap
    (by intro a b hab; obtain ⟨R,hR,hk⟩ := H a b hab; exact ⟨R,hR,by simpa only [Category.assoc] using hk⟩)
  simpa only [top_inclusion_eq_adjacent,Category.assoc] using H'

/-- The selected top coefficient inclusion of the specified classical target. -/
private def ordinaryEarlyTop (X : (AdamsObject (coefficients := background.coefficients))) (i : ℕ) (hi : 0 < i) (s t : ℤ)
    (u : Ambient background X (s+i+1,t+i)) :
    BiHom ((t-s)-1) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (i+1)) :=
  homotopyRegrade (by omega) (by omega) (finiteTopLabel X i hi (s+i+1) (t+i) u)

/-- Identify the canonical suspended coefficient input with the exact selected top class. This is an equality of the actual homotopy classes. -/
private theorem unsigned_native_top_identity
    (X : (AdamsObject (coefficients := background.coefficients))) (i : ℕ) (hi : 0 < i) (s t : ℤ)
    (u : Ambient background X (s+i+1,t+i)) :
    let b := (biSuspensionHomEquiv (t-s) t i (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1)).symm
      (homotopyRegrade (show (t+i)-(s+i+1)=(t-s)-1 by omega) rfl (nativeFirstLabel X (s+i+1) (t+i) u))
    b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (finiteTopInclusion (background.nu.functor.obj (X.obj background.auxiliary)) i hi)=
      ordinarySuspendedRepresentative _ (t-s) t
        (ordinaryEarlyTop X i hi s t u) := by
  dsimp only
  let A := XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1
  let a := homotopyRegrade (show (t+i)-(s+i+1)=(t-s)-1 by omega) rfl
    (nativeFirstLabel X (s+i+1) (t+i) u)
  have htop : ordinaryEarlyTop X i hi s t u=
      vertical_hom ((t-s)-1) t i A a≫finiteTopInclusion _ i hi := by
    have transport (n v m w : ℤ) (hn : n=m-1) (hv : v=w+i)
        (a₀ : BiHom n v A) :
        homotopyRegrade hn (show v-i=w by omega) (finiteTopOfFirst _ i hi n v a₀)=
          vertical_hom (m-1) w i A (homotopyRegrade hn hv a₀)≫finiteTopInclusion _ i hi := by
      subst n
      subst v
      simp only [finiteTopOfFirst,regrade_comp,output_regrade_trans]
      congr 1
      simpa [shiftHomotopyClass,susp_invariance,Iso.homCongr,vertical_hom,top_target_regrade_self,A] using
        susp_regrade_eq (m-1) (w+i) 0 (-(i:ℤ)) (m-1) w (by omega) (by omega) A a₀
    exact transport ((t+i)-(s+i+1)) (t+i) (t-s) t (by omega) rfl
      (nativeFirstLabel X (s+i+1) (t+i) u)
  rw [htop,ordinarySuspendedRepresentative_natural]
  congr 1
  rw [bi_susp_symm_vertical background.quotients.coherence]
  unfold ordinarySuspendedRepresentative
  have hs : homotopyRegrade (show ((t-s)-1)+1=t-s by omega) (show t+0=t by simp)
      (shiftHomotopyClass (1,0) ((t-s)-1,t) (vertical_hom ((t-s)-1) t i A a))=
      (biShiftAddIso ((t-s)-1,t) (1,0) (t-s,t) (by ext <;> simp)).inv.app S_0_0≫
        (SyntheticCategory.biShift (1,0)).map (vertical_hom ((t-s)-1) t i A a) := by
    simpa [shiftHomotopyClass,susp_invariance,Iso.homCongr] using
      susp_regrade_eq ((t-s)-1) t 1 0 (t-s) t (by omega) (by simp) _
        (vertical_hom ((t-s)-1) t i A a)
  rw [hs,Category.assoc,(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.naturality]
  rfl

/-- The given ordinary classical differential supplies a finite square with the same source and target labels. -/
private theorem ordinary_classical_finite_square
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (i : ℕ) (hi : 0 < i) (s t : ℤ)
    (c : Ambient background Y (s,t)) (u : Ambient background X (s+i+1,t+i))
    (hd : HasDifferential (background.classical.obj (Y.obj background.auxiliary))
      (i+1) (s,t) (s+i+1,t+i) c ((background.classical.map f).pageMap 2 (s+i+1,t+i) u)) :
    let A := background.nu.functor.obj (X.obj background.auxiliary)
    let B := background.nu.functor.obj (Y.obj background.auxiliary)
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
    let b := (biSuspensionHomEquiv (t-s) t i (XModLambdaN A 1)).symm
      (homotopyRegrade (show (t+i)-(s+i+1)=(t-s)-1 by omega) rfl (nativeFirstLabel X (s+i+1) (t+i) u))
    let delta : XModLambdaN B i ⟶ (F.obj (XModLambdaN B 1))⟦(1:ℤ)⟧ := by
      simpa only [show i.succ-i=1 by omega] using ((background.quotients.tower B).triangle hi (Nat.lt_succ_self i)).delta
    ∃ a : BiHom (t-s) t (XModLambdaN B i),
      a≫(background.quotients.tower B).rho 1 i hi=nativeFirstLabel Y s t c ∧
      a≫delta=b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (F.map (XModLambdaN.map (background.nu.functor.map f) 1)) := by
  obtain ⟨a,ha,hda⟩ := (differential_iff_specified_finite_lift Y i hi s t c _).mp hd
  refine ⟨a,ha,?_⟩
  apply (biSuspensionHomEquiv (t-s) t i (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) 1)).injective
  rw [bi_susp_natural background.quotients.coherence,AddEquiv.apply_symm_apply,←regrade_comp,native_first_label_natural]
  apply homotopy_regrade_injective (show (t-s)-1=(t+i)-(s+i+1) by omega) rfl
  rw [normalized_homotopy_regrade_trans]
  exact hda

/-- A native finite row gives the specified first and top equations
from the classical differential. -/
private theorem ordinary_first_and_top_of_native_row
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (i : ℕ) (hi : 0 < i) (s t : ℤ)
    (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (s+i+1,t+i))
    (hd : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) (s,t) (s+i+1,t+i) c ((background.classical.map T.f).pageMap 2 (s+i+1,t+i) u))
    (eX : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) (i+1)≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (i+1))⟦(1:ℤ)⟧)
    (hrowX : Triangle.mk (XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₁ (i+1))
      (XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₂ (i+1))
      (XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₃ (i+1)≫eX.hom)∈distTriang SyntheticSpectrum) :
    ∃ R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ (i+1)),
      R≫(background.quotients.tower _).rho 1 (i+1) (by omega)=
        nativeFirstLabel T.Y s t c≫XModLambdaN.map (normalizedTriangle background T he).mor₂ 1 ∧
      R≫XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₃ (i+1)≫eX.hom=
        ordinarySuspendedRepresentative _ (t-s) t (ordinaryEarlyTop T.X i hi s t u) := by
  obtain ⟨a,ha,hab⟩ := ordinary_classical_finite_square T.X T.Y T.f i hi s t c u hd
  obtain ⟨R,hR,hk⟩ := ordinary_forward_lift_of_native_row T he hf i hi (t-s) t eX hrowX a _ hab
  dsimp only [ordinaryNativeTriangle,Triangle.mk] at R hR hk
  refine ⟨R,?_,hk.trans (unsigned_native_top_identity T.X i hi s t u)⟩
  rw [←(background.quotients.tower _).rho_comp hi (Nat.le_succ i),←Category.assoc,hR,Category.assoc,
    ←(background.quotients.natural (normalizedTriangle background T he).mor₂).rho_naturality hi,←Category.assoc]
  exact congrArg (fun a => a≫XModLambdaN.map (normalizedTriangle background T he).mor₂ 1) ha

/-- The finite-quotient comparison and normalized triangle construct
the row for every admissible object. -/
private theorem ordinary_first_and_top_of_differential
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (i : ℕ) (hi : 0 < i) (s t : ℤ)
    (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (s+i+1,t+i))
    (hd : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) (s,t) (s+i+1,t+i) c ((background.classical.map T.f).pageMap 2 (s+i+1,t+i) u)) :
    ∃ eX : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) (i+1)≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (i+1))⟦(1:ℤ)⟧,
      XModLambdaN.incl _ (i+1)≫eX.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (i+1)) ∧
      ∃ R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ (i+1)),
        R≫(background.quotients.tower _).rho 1 (i+1) (by omega)=
          nativeFirstLabel T.Y s t c≫XModLambdaN.map (normalizedTriangle background T he).mor₂ 1 ∧
        R≫XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₃ (i+1)≫eX.hom=
          ordinarySuspendedRepresentative _ (t-s) t (ordinaryEarlyTop T.X i hi s t u) := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T he
  obtain ⟨eA,heA,hrow⟩ := KIP126.Literature.Standard.finite_quotient_horizontal_row
    (normalizedTriangle background T he) hT (i+1) (by omega)
  obtain ⟨eX,heX,hrowX⟩ := native_unrotated_row_transport T he hf (i+1) eA heA hrow
  exact ⟨eX,heX,ordinary_first_and_top_of_native_row T he hf i hi s t c u hd eX hrowX⟩

/-- The literal fixed sphere source, with the actual first label and specified top of the same root. -/
private theorem sphere_ordinary_first_and_top_of_differential
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0) (hX : T.X=.sphere)
    (i : ℕ) (hi : 0 < i) (s t : ℤ)
    (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (s+i+1,t+i))
    (hd : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) (s,t) (s+i+1,t+i) c ((background.classical.map T.f).pageMap 2 (s+i+1,t+i) u)) :
    ∃ eX : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) (i+1)≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (i+1))⟦(1:ℤ)⟧,
      XModLambdaN.incl _ (i+1)≫eX.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (i+1)) ∧
      ∃ R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ (i+1)),
        R≫(background.quotients.tower _).rho 1 (i+1) (by omega)=
          nativeFirstLabel T.Y s t c≫XModLambdaN.map (normalizedTriangle background T he).mor₂ 1 ∧
        R≫XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₃ (i+1)≫eX.hom=
          ordinarySuspendedRepresentative _ (t-s) t
            (ordinaryEarlyTop T.X i hi s t u) := by
  obtain ⟨eA,heA,hrow⟩ := literal_sphere_actual_unrotated_row T he hT hX (i+1) (by omega)
  obtain ⟨eX,heX,hrowX⟩ := native_unrotated_row_transport T he hf (i+1) eA heA hrow
  exact ⟨eX,heX,ordinary_first_and_top_of_native_row T he hf i hi s t c u hd eX hrowX⟩

end
end KIP126.ProofTools.Internal.SyntheticCoverage
