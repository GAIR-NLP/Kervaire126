module

public import KIP126.Main.ClassicalReduction
public import KIP126.AdamsSynthetic.Completed.ClassicalSupport
import all KIP126.Main.Internal.PageCalculus
import all KIP126.Main.Internal.Selected.LambdaOperations

/-! The implication from the BX condition to d₁₂. The finite target frame
is transported between the indicated pages of the same Adams system. -/
@[expose] section
namespace KIP126.Main.Internal.Selected
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
open KIP126.Computation.Standard (T)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem reaches_next_of_zero
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {r : ℤ} (hr0 : E.r₀ ≤ r) (hr : 2 ≤ r) {p : ℤ × ℤ}
    {x : E.Page 2 p} {a : E.Page r p}
    (ha : RepresentsOnPage E r p x a) (hzero : E.d r p a=0) :
    ReachesPage E (r+1) p x := by
  obtain ⟨_,z,hz2,hza⟩ := ha
  have hz : E.d r p ((E.ssData p).pageπ ↑(r-E.r₀).toNat z)=0 := by
    rw [hza]
    exact hzero
  obtain ⟨zn,hnz⟩ := cycle_successor_lift E r hr0 p z hz
  let A := E.ssData p
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  let m : WithTop ℕ := ↑(r+1-E.r₀).toNat
  have he : (↑((r-E.r₀).toNat+1) : WithTop ℕ)=m := by
    dsimp only [m]
    congr 1
    omega
  have hnm : n≤m := by dsimp only [n,m]; exact_mod_cast (show (r-E.r₀).toNat≤(r+1-E.r₀).toNat by omega)
  have cast_lift (m' : WithTop ℕ) (h : m'=m)
      (v : (Subobject.underlying.obj (A.Z m') : ModuleCat ℤ))
      (hn : n≤m')
      (hv : Subobject.ofLE (A.Z m') (A.Z n) (A.Z_anti hn) v=z) :
      ∃ w : (Subobject.underlying.obj (A.Z m) : ModuleCat ℤ),
        Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm) w=z := by
    subst m'
    exact ⟨v,hv⟩
  obtain ⟨w,hw⟩ := cast_lift _ he zn
    (by dsimp only [n]; exact_mod_cast Nat.le_succ (r-E.r₀).toNat) hnz
  refine ⟨A.pageπ m w,by omega,w,?_,rfl⟩
  calc
    (Subobject.ofLE (A.Z m) (A.Z _) _ ≫ A.pageπ _) w =
      (Subobject.ofLE (A.Z n) (A.Z ↑(2-E.r₀).toNat)
        (A.Z_anti (by dsimp only [n]; exact_mod_cast
          (show (2-E.r₀).toNat≤(r-E.r₀).toNat by omega))) ≫ A.pageπ _)
        ((Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm)) w) := by
          rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    _ = x := by rw [hw]; exact hz2

private theorem h6_twelve_outgoing_nonzero
    (h12 : SurvivesTo background.classical.sphere 12 (2,128) background.standardClasses.standardH6Square)
    (h13 : ¬SurvivesTo background.classical.sphere 13 (2,128) background.standardClasses.standardH6Square) :
    ∃ a, RepresentsOnPage background.classical.sphere 12 (2,128) background.standardClasses.standardH6Square a ∧
      background.classical.sphere.d 12 (2,128) a≠0 := by
  obtain ⟨a,ha,hane⟩ := h12
  refine ⟨a,ha,?_⟩
  intro hzero
  have hr0 : background.classical.sphere.r₀ ≤ 12 := by
    rw [background.classical.firstPage]; decide
  obtain ⟨b,hb⟩ := reaches_next_of_zero hr0 (by decide) ha hzero
  have hnot : ¬HitOnPage background.classical.sphere 12 (2,128) background.standardClasses.standardH6Square := by
    rintro ⟨q,hq,c,d,hd,hdne,hcd⟩
    have hfst : q.1+12=2 := by
      have h := congrArg Prod.fst hq
      simpa only [Prod.fst_add,background.classical.differentialDegree] using h
    haveI : Subsingleton (background.classical.sphere.Page 12 q) :=
      KIP126.AdamsSynthetic.Completed.classical_page_negative .sphere 12 q.1 q.2 (by omega)
    rw [Subsingleton.elim c 0,map_zero] at hcd
    exact hdne hcd.symm
  exact h13 ⟨b,hb,next_nonzero_of_not_hit hr0 (by decide) hb ha hane hnot⟩

private theorem survives_twelve_not_thirteen_d12
    (hframe : ∃ b : background.classical.sphere.Page 12 (14,139),
      RepresentsOnPage background.classical.sphere 12 (14,139) T b ∧
      ∀ y : background.classical.sphere.Page 12 (14,139), y=0 ∨ y=b)
    (h12 : SurvivesTo background.classical.sphere 12 (2,128) background.standardClasses.standardH6Square)
    (h13 : ¬SurvivesTo background.classical.sphere 13 (2,128) background.standardClasses.standardH6Square) : H6SquareSupportsD12 := by
  obtain ⟨a,ha,hdne⟩ := h6_twelve_outgoing_nonzero h12 h13
  obtain ⟨b,hb,hall⟩ := hframe
  have hdeg : (2,128)+background.classical.sphere.diffDeg 12=(14,139) := by
    simp only [background.classical.differentialDegree,Prod.mk_add_mk,Int.reduceSub,Int.reduceAdd]
  let f := background.classical.sphere.d 12 (2,128) ≫
    eqToHom (congrArg (background.classical.sphere.Page 12) hdeg)
  have hfne : f a≠0 := by
    intro hz
    apply hdne
    have h := congrArg (fun z => (eqToHom (congrArg (background.classical.sphere.Page 12) hdeg.symm)) z) hz
    simpa only [f,←ModuleCat.comp_apply,Category.assoc,eqToHom_trans,eqToHom_refl,
      Category.comp_id,map_zero] using h
  have hdb : f a=b := (hall (f a)).resolve_left hfne
  exact ⟨hdeg,a,b,ha,hb,hdb,fun hb0 => hfne (hdb.trans hb0)⟩

private theorem h6_square_d12_of_eta_theta_square_vanishes_mod_lambda_nine_not_ten
    (hframe : ∃ b : background.classical.sphere.Page 12 (14,139),
      RepresentsOnPage background.classical.sphere 12 (14,139) T b ∧
      ∀ y : background.classical.sphere.Page 12 (14,139), y=0 ∨ y=b)
    (h9 : VanishesModLambda 9 (sphereProduct KIP126.Literature.Standard.eta
      (sphereProduct KIP126.Literature.Standard.syntheticTheta5 KIP126.Literature.Standard.syntheticTheta5)))
    (h10 : ¬VanishesModLambda 10 (sphereProduct KIP126.Literature.Standard.eta
      (sphereProduct KIP126.Literature.Standard.syntheticTheta5 KIP126.Literature.Standard.syntheticTheta5))) : H6SquareSupportsD12 := by
  have h12 := (KIP126.Literature.Standard.h6_square_survives_iff_eta_theta_square_vanishes_mod_lambda 9 (by decide)).mpr h9
  have h13 : ¬SurvivesTo background.classical.sphere 13 (2,128) background.standardClasses.standardH6Square := by
    intro hh
    exact h10 ((KIP126.Literature.Standard.h6_square_survives_iff_eta_theta_square_vanishes_mod_lambda 10 (by decide)).mp hh)
  exact survives_twelve_not_thirteen_d12 hframe h12 h13

end
end KIP126.Main.Internal.Selected
