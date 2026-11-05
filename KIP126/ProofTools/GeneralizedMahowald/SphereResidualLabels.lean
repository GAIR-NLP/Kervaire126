module
import all KIP126.ProofTools.GeneralizedMahowald.MayCorrection
import all KIP126.ProofTools.GeneralizedMahowald.SphereMayCorrection

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

private theorem actual_raw_residual_flat_detects_zero
    (Y Z : AdamsObject (coefficients := background.coefficients)) (g : Y.obj background.auxiliary ⟶ Z.obj background.auxiliary)
    (rW r i : ℕ) (hi : 0 < i) (m s t : ℤ) (hm : 0 ≤ m)
    (y : Ambient background Y (s,t)) (yBar : Ambient background Z (s+m,t+m))
    (Wg : FiniteExtensionWitness background Y Z g rW m s t y yBar)
    (p : ℤ×ℤ) (xBar : Ambient background Z p)
    (hd : m=0 → HasDifferential (background.classical.obj (Z.obj background.auxiliary))
      (i+1) p (s+m,t+m) xBar yBar)
    (hyBar : yBar ∈ permanentCycles background Z (s+m,t+m))
    (D : SyntheticObject (coefficients := background.coefficients))
    (hD : D=.shift (0,(i:ℤ)+normalizedExponent background.classicalTower g) (.quotient r (.nu Y)))
    (U : SyntheticSpectrum)
    (eD : U ≅ (SyntheticCategory.biShift (1,-(i:ℤ))).obj (D.obj background.nu background.auxiliary))
    (raw : (background.nu.functor.obj (Z.obj background.auxiliary))⟦(1:ℤ)⟧ ⟶ U) :
    let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    let t₀ := ff.preimage ((biSuspensionIso (i:ℤ)
      (background.nu.functor.obj (Z.obj background.auxiliary))).hom ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (lambdaPow i (background.nu.functor.obj (Z.obj background.auxiliary))) ≫ raw ≫ eD.hom)
    Detects (background.convergence D) (s,t,t+normalizedExponent background.classicalTower g)
      (familyPageMap background.family ((background.normalizedMap Y Z g).map≫t₀) 2
        (s,t,t+normalizedExponent background.classicalTower g)
        (regradeE2 (by simp) (infiniteSourceForExtension background Y Z g s t y))) 0 := by
  dsimp only
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
  let t₀ := ff.preimage ((biSuspensionIso (i:ℤ)
    (background.nu.functor.obj (Z.obj background.auxiliary))).hom ≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (lambdaPow i (background.nu.functor.obj (Z.obj background.auxiliary))) ≫ raw ≫ eD.hom)
  by_cases hm0 : m=0
  · subst m
    have heg : (normalizedExponent background.classicalTower g : ℤ)=0 := by
      have := Wg.length_lower
      omega
    have hD0 : D=.shift (0,(i:ℤ)) (.quotient r (.nu Y)) := by
      rw [hD,heg,add_zero]
    cases hD0
    let E : SyntheticObject (coefficients := background.coefficients) := .quotient r (.nu Y)
    let epsilon : (SyntheticCategory.biShift (0,-(i:ℤ))).obj
        ((SyntheticCategory.biShift (0,(i:ℤ))).obj (E.obj background.nu background.auxiliary)) ≅
        E.obj background.nu background.auxiliary :=
      (biShiftAddIso (0,(i:ℤ)) (0,-(i:ℤ)) (0,0) (by ext <;> simp)).app _ ≪≫
        SyntheticCategory.biShift_zero.app _
    have hz := zero_length_actual_toda_residual_detects_zero Y Z g rW i hi s t y yBar Wg
      p xBar (hd rfl) hyBar E U eD epsilon raw
    have hindex : (s+0,t+0,t+0)=(s,t,t+normalizedExponent background.classicalTower g) := by
      ext <;> dsimp <;> omega
    have hzt := detects_transport hindex _ _ hz
    have regrade_comp {A : SyntheticAdamsSS.{0}} {i j k : Tridegree}
        (h : i=j) (h' : j=k) (z : A.E₂ i) :
        regradeE2 h' (regradeE2 h z) = regradeE2 (h.trans h') z := by
      subst j; subst k; rfl
    have regrade_zero {m m' w w' : ℤ} {V : SyntheticSpectrum}
        (hm : m=m') (hw : w=w') :
        homotopyRegrade hm hw (0 : BiHom m w V)=0 := by
      subst m'; subst w'; rfl
    simp only [page_regrade,regrade_comp,regrade_zero] at hzt
    exact hzt
  · have hmpos : 0<m := by omega
    have hz := positive_extension_postcompose_e2_zero Y Z g rW m s t hmpos y yBar Wg
      (D.obj background.nu background.auxiliary) t₀
    have hz' : familyPageMap background.family ((background.normalizedMap Y Z g).map≫t₀) 2
        (s,t,t+normalizedExponent background.classicalTower g)
        (regradeE2 (by simp) (infiniteSourceForExtension background Y Z g s t y)) = 0 := by
      have hzR := congrArg (regradeE2 (by simp :
        (s,(t-s)+s,t+normalizedExponent background.classicalTower g)=
          (s,t,t+normalizedExponent background.classicalTower g))) hz
      rw [page_regrade] at hzR
      simpa only [regradeE2,map_zero] using hzR
    rw [hz']
    exact ⟨0,HasInfinityRepresentative.zero _ 2 (by omega) _,0,by simp,by simp⟩


private theorem actual_extension_source_native_detects
    (Y Z : AdamsObject (coefficients := background.coefficients)) (g : Y.obj background.auxiliary ⟶ Z.obj background.auxiliary)
    (q : ℕ) (s t : ℤ) (y : Ambient background Y (s,t))
    (ag : BiHom (t-s) (t+normalizedExponent background.classicalTower g)
      (XModLambdaN ((extensionSourceObject background Y Z g).obj background.nu background.auxiliary) q))
    (hag : Detects (background.convergence (.quotient q (extensionSourceObject background Y Z g)))
      (s,(t-s)+s,t+normalizedExponent background.classicalTower g)
      (finiteSourceForExtension background Y Z g q s t y)
      (homotopyRegrade (by simp) rfl ag)) :
    Detects (background.convergence (.quotient q (extensionSourceObject background Y Z g)))
      (s,t,t+normalizedExponent background.classicalTower g)
      (familyPageMap background.family
        (XModLambdaN.incl ((extensionSourceObject background Y Z g).obj background.nu background.auxiliary) q)
        2 (s,t,t+normalizedExponent background.classicalTower g)
        (regradeE2 (by simp) (infiniteSourceForExtension background Y Z g s t y))) ag := by
  let p : Tridegree := (s,(t-s)+s,t+normalizedExponent background.classicalTower g)
  have hsource : finiteSourceForExtension background Y Z g q s t y =
      familyPageMap background.family (XModLambdaN.incl _ q) 2 p
        (infiniteSourceForExtension background Y Z g s t y) := by
    unfold finiteSourceForExtension infiniteSourceForExtension finiteNuLabel
    rw [page_regrade]
    rfl
  have hag' := (congrArg (fun z => Detects
    (background.convergence (.quotient q (extensionSourceObject background Y Z g))) p z
    (homotopyRegrade (show t-s=((t-s)+s)-s by omega) rfl ag)) hsource).mp hag
  have hindex : p=(s,t,t+normalizedExponent background.classicalTower g) := by
    simp only [p,sub_add_cancel]
  have hnative := detects_transport hindex _ _ hag'
  have regrade_comp {m m' m'' w w' w'' : ℤ} {V : SyntheticSpectrum}
      (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
      (z : BiHom m w V) :
      homotopyRegrade hm' hw' (homotopyRegrade hm hw z) =
        homotopyRegrade (hm.trans hm') (hw.trans hw') z := by
    subst m'; subst m''; subst w'; subst w''; rfl
  simp only [page_regrade,regrade_comp] at hnative
  exact hnative

end
end KIP126.ProofTools.Internal.Mahowald
