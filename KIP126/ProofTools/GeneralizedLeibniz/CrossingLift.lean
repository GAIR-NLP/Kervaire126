module
import all KIP126.ProofTools.GeneralizedLeibniz.Boundary
import all KIP126.ProofTools.GeneralizedLeibniz.BottomTarget
import all KIP126.ProofTools.GeneralizedMahowald.ShortSource
import all KIP126.ProofTools.GeneralizedMahowald.FinalDivision
import all KIP126.ProofTools.GeneralizedMahowald.ExtensionImage

/-! The smaller-quotient witness and boundary tests in AimPaper Proposition
`prop:cross-f-Er`, including the untruncated boundary test.
Given a divided source whose image lies in the required target filtration,
the finite-window comparisons supply classical cycle labels and an extension
witness at every allowed length. For a counterexample to unrestricted
simultaneous lifting, see `KIP126.ProofTools.CrossingCounterexample`. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
set_option Elab.async false

/-- The actual map on infinity classes in the finite lambda square. The
same construction is used for a normalized source and an unshifted target. -/
private def finiteLambdaInfinity (A : SyntheticObject (coefficients := background.coefficients)) (q i : ℕ)
    (hi : 0 < i) (hiq : i < q) (p : ℤ × ℤ) (s : ℤ)
    (x : ((background.family.obj ((SyntheticObject.quotient (q-i) A).obj
      background.nu background.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty) :
    ((background.family.obj ((SyntheticObject.quotient q A).obj background.nu background.auxiliary)).sequence.ssData
      (s,(p+(0,-(i:ℤ))).1+s,(p+(0,-(i:ℤ))).2)).eInfty := by
  let B := SyntheticObject.quotient (q-i) A
  let δ : ℤ × ℤ := (0,-(i:ℤ))
  let L : ((SyntheticObject.shift δ B).obj background.nu background.auxiliary) ⟶
      ((SyntheticObject.quotient q A).obj background.nu background.auxiliary) :=
    ((background.quotients.tower (A.obj background.nu background.auxiliary)).triangle hi hiq).lambdaMap
  let I : ((background.family.obj (B.obj background.nu background.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty ≅
      ((background.family.obj ((SyntheticObject.shift δ B).obj background.nu background.auxiliary)).sequence.ssData
        (s,(p+δ).1+s,(p+δ).2)).eInfty :=
    towerInfinityIso (background.convergence B) (background.convergence (.shift δ B))
      ((essShift δ).filtered B p) s
  exact (background.family.map L).eInftyMap (s,(p+δ).1+s,(p+δ).2) (I.hom x)

private theorem finite_lambda_infinity_nu_heq (X : AdamsObject (coefficients := background.coefficients))
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (p : ℤ × ℤ) (s : ℤ)
    (x : ((background.family.obj ((SyntheticObject.quotient (q-i) (.nu X)).obj
      background.nu background.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty) :
    HEq (finiteLambdaInfinity (.nu X) q i hi hiq p s x)
      (KIP126.Literature.Standard.infinityFiniteLambda X q i hiq (s,p.1+s) p.2 x) := by
  have hmap {U V : SyntheticSpectrum} (f : U ⟶ V) (a b : Tridegree) (hab : a=b)
      (x : ((background.family.obj U).sequence.ssData a).eInfty)
      (y : ((background.family.obj U).sequence.ssData b).eInfty) (hxy : HEq x y) :
      HEq ((background.family.functor.map f).eInftyMap a x)
        ((background.family.functor.map f).eInftyMap b y) := by
    subst b
    cases hxy
    rfl
  rcases p with ⟨m,w⟩
  simp only [finiteLambdaInfinity,KIP126.Literature.Standard.infinityFiniteLambda,
    InfinityShiftCoordinates.finiteLambdaMap,show i ≠ 0 by omega,↓reduceDIte,ModuleCat.comp_apply]
  exact hmap _ _ _ (by ext <;> dsimp <;> omega) _ _
    (infinityShift_stem_heq (.quotient (q-i) (.nu X)) i m w s x).symm

private theorem finite_lambda_infinity_nonzero_iff_boundary (X : AdamsObject (coefficients := background.coefficients))
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (p : ℤ × ℤ) (s : ℤ)
    (hw : 0 ≤ p.1+s-p.2 ∧ p.1+s-p.2 < (q-i:ℕ))
    (y : Ambient background X (s,p.1+s))
    (e : ((background.family.obj ((SyntheticObject.quotient (q-i) (.nu X)).obj
      background.nu background.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (he : HasInfinityRepresentative _ 2 (s,p.1+s,p.2)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) (q-i)).pageMap
        2 (s,p.1+s,p.2) (nuWeightLabel background X s (p.1+s) p.2 (by omega) y)) e) :
    finiteLambdaInfinity (.nu X) q i hi hiq p s e ≠ 0 ↔
      y ∉ boundaries background X (1+(p.1+s)-(p.2-i)) (s,p.1+s) := by
  let E (a : Tridegree) := ((background.family.obj ((SyntheticObject.quotient q (.nu X)).obj
    background.nu background.auxiliary)).sequence.ssData a).eInfty
  have hp : (s,(p+(0,-(i:ℤ))).1+s,(p+(0,-(i:ℤ))).2) =
      (s,p.1+s,p.2-i) := by ext <;> simp [sub_eq_add_neg]
  let J := eqToHom (congrArg E hp)
  have hEq : J (finiteLambdaInfinity (.nu X) q i hi hiq p s e) =
      KIP126.Literature.Standard.infinityFiniteLambda X q i hiq (s,p.1+s) p.2 e :=
    eq_of_heq ((eqToHom_apply_heq (congrArg E hp) _).trans
      (finite_lambda_infinity_nu_heq X q i hi hiq p s e))
  have hzero : finiteLambdaInfinity (.nu X) q i hi hiq p s e = 0 ↔
      KIP126.Literature.Standard.infinityFiniteLambda X q i hiq (s,p.1+s) p.2 e = 0 := by
    constructor
    · intro hz
      rw [←hEq,hz,map_zero]
    · intro hz
      apply (ModuleCat.mono_iff_injective J).mp inferInstance
      rw [hEq,hz,map_zero]
  exact (not_congr hzero).trans
    (CrossingLabels.lambda_finite_label_nonzero X q i hiq s (p.1+s) p.2 hw y e he)

set_option backward.defeqAttrib.useBackward false in
/-- An essential extension from the mapped source makes its known
preimage extension essential and its lambda target nonzero
in the finite lambda square. -/
private theorem finite_extension_essential_of_lambda_source
    (A B : SyntheticObject (coefficients := background.coefficients)) (g : A.obj background.nu background.auxiliary ⟶ B.obj background.nu background.auxiliary)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (p : ℤ × ℤ) (s n : ℤ)
    (x : ((background.family.obj ((SyntheticObject.quotient (q-i) A).obj
      background.nu background.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((background.family.obj ((SyntheticObject.quotient (q-i) B).obj
      background.nu background.auxiliary)).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (z : ((background.family.obj ((SyntheticObject.quotient q B).obj background.nu background.auxiliary)).sequence.ssData
      (s+n,(p+((0:ℤ),-(i:ℤ))).1+(s+n),(p+((0:ℤ),-(i:ℤ))).2)).eInfty)
    (he : TowerExtensionEquation (F := background.family) (P := background.syntheticTower)
      (cx := background.convergence (.quotient (q-i) A)) (cy := background.convergence (.quotient (q-i) B))
      (background.convergentMap
      (.quotient (q-i) A) (.quotient (q-i) B) (XModLambdaN.map g (q-i))) p s n x y)
    (hess : TowerEssentialExtension (F := background.family) (P := background.syntheticTower)
      (X := (SyntheticObject.quotient q A).obj background.nu background.auxiliary)
      (Y := (SyntheticObject.quotient q B).obj background.nu background.auxiliary)
      (g := XModLambdaN.map g q)
      (cx := background.convergence (.quotient q A)) (cy := background.convergence (.quotient q B))
      (background.convergentMap
      (.quotient q A) (.quotient q B) (XModLambdaN.map g q)) (p+((0:ℤ),-(i:ℤ))) s n
      (finiteLambdaInfinity A q i hi hiq p s x) z) :
    TowerEssentialExtension (F := background.family) (P := background.syntheticTower)
      (cx := background.convergence (.quotient (q-i) A)) (cy := background.convergence (.quotient (q-i) B))
      (background.convergentMap
      (.quotient (q-i) A) (.quotient (q-i) B) (XModLambdaN.map g (q-i))) p s n x y ∧
      finiteLambdaInfinity B q i hi hiq p (s+n) y ≠ 0 := by
  let δ : ℤ × ℤ := (0,-(i:ℤ))
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) δ
  let LA := ((background.quotients.tower (A.obj background.nu background.auxiliary)).triangle hi hiq).lambdaMap
  let LB := ((background.quotients.tower (B.obj background.nu background.auxiliary)).triangle hi hiq).lambdaMap
  let M := background.convergentMap (.quotient (q-i) A) (.quotient (q-i) B)
    (XModLambdaN.map g (q-i))
  let MS := background.convergentMap (.shift δ (.quotient (q-i) A))
    (.shift δ (.quotient (q-i) B)) (F.map (XModLambdaN.map g (q-i)))
  let ML := background.convergentMap (.quotient q A) (.quotient q B)
    (XModLambdaN.map g q)
  have hcomm := (background.quotients.natural g).lambda_naturality hi hiq
  change F.map (XModLambdaN.map g (q-i)) ≫ LB = LA ≫ XModLambdaN.map g q at hcomm
  have hs := ((essShift δ).towerExtensionEquation_iff
    (.quotient (q-i) A) (.quotient (q-i) B) (XModLambdaN.map g (q-i))
    p s n x y).mp he
  obtain ⟨hsmall,hne⟩ := tower_essential_of_mapped_source MS ML
    (background.convergentMap (.shift δ (.quotient (q-i) A)) (.quotient q A) LA)
    (background.convergentMap (.shift δ (.quotient (q-i) B)) (.quotient q B) LB)
    hcomm (p+δ) s n _ _ z hs hess
  refine ⟨?_,hne⟩
  apply (tower_essential_iff_no_zero M p s n x y he).mpr
  intro hzero
  have hs0 := ((essShift δ).towerExtensionEquation_iff
    (.quotient (q-i) A) (.quotient (q-i) B) (XModLambdaN.map g (q-i))
    p s n x 0).mp hzero
  simp only [map_zero] at hs0
  exact ((tower_essential_iff_no_zero MS (p+δ) s n _ _ hsmall.1).mp hsmall) hs0

private theorem finite_weight_label_heq (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ)
    (s t w s' t' w' : ℤ) (hs : s=s') (ht : t=t') (hw : w=w')
    (hwt : w ≤ t) (hwt' : w' ≤ t')
    (y : Ambient background X (s,t)) (y' : Ambient background X (s',t')) (hy : HEq y y') :
    HEq ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap
      2 (s,t,w) (nuWeightLabel background X s t w hwt y))
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap
        2 (s',t',w') (nuWeightLabel background X s' t' w' hwt' y')) := by
  subst s'
  subst t'
  subst w'
  cases hy
  rfl

/-- For a smaller finite witness, nonvanishing of its actual lambda target
is exactly the boundary exclusion appearing in the paper's crossing
definition, with the larger lambda layer retained. -/
private theorem finite_witness_lambda_target_nonzero_iff
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (n s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n))
    (W : FiniteExtensionWitness background X Y f ((q-i)+1) n s t x y) :
    finiteLambdaInfinity (.nu Y) q i hi hiq
        (t-s,t+normalizedExponent background.classicalTower f) (s+n) W.target ≠ 0 ↔
      y ∉ boundaries background Y (1+n+i-normalizedExponent background.classicalTower f) (s+n,t+n) := by
  let e : ℤ := normalizedExponent background.classicalTower f
  let p : ℤ × ℤ := (t-s,t+e)
  have hl := W.length_lower
  have hu := W.length_upper
  have ht : t+n=p.1+(s+n) := by dsimp [p]; omega
  have hp : (s+n,t+n)=(s+n,p.1+(s+n)) := congrArg (fun v => (s+n,v)) ht
  let yn : Ambient background Y (s+n,p.1+(s+n)) :=
    (eqToHom (congrArg (fun a => Ambient background Y a) hp)) y
  have hyn : HEq yn y := eqToHom_apply_heq (congrArg (fun a => Ambient background Y a) hp) y
  have hwt : t+e ≤ t+n := by dsimp [e]; omega
  have hwtn : p.2 ≤ p.1+(s+n) := by dsimp [p,e]; omega
  have hlabel : HEq (finiteTargetForExtension background X Y f (q-i) n s t hl y)
      ((background.family.quotientProjection (background.nu.functor.obj (Y.obj background.auxiliary)) (q-i)).pageMap
        2 (s+n,p.1+(s+n),p.2)
          (nuWeightLabel background Y (s+n) (p.1+(s+n)) p.2 hwtn yn)) := by
    have H := finite_extension_target_weight_label X Y f (q-i) n s t hl y
    exact (regradeE2_heq _ _).symm.trans ((heq_of_eq H).trans
      (finite_weight_label_heq Y (q-i) (s+n) (t+n) (t+e)
        (s+n) (p.1+(s+n)) p.2 rfl ht rfl hwt hwtn y yn hyn.symm))
  have he : HasInfinityRepresentative _ 2 (s+n,p.1+(s+n),p.2)
      ((background.family.quotientProjection (background.nu.functor.obj (Y.obj background.auxiliary)) (q-i)).pageMap
        2 (s+n,p.1+(s+n),p.2)
          (nuWeightLabel background Y (s+n) (p.1+(s+n)) p.2 hwtn yn)) W.target := by
    rw [←eq_of_heq hlabel]
    exact W.target_rep
  have H := finite_lambda_infinity_nonzero_iff_boundary Y q i hi hiq p (s+n)
    (by dsimp [p,e]; constructor <;> omega) yn W.target he
  have transport (v : ℤ) (hv : v=t+n) (z : Ambient background Y (s+n,v)) (hz : HEq z y) :
      z ∉ boundaries background Y (1+v-((t+e)-i)) (s+n,v) ↔
        y ∉ boundaries background Y (1+n+i-e) (s+n,t+n) := by
    subst v
    cases hz
    rw [show 1+(t+n)-((t+e)-i)=1+n+i-e by omega]
  exact H.trans (transport (p.1+(s+n)) ht.symm yn hyn)

/-- Given a smaller-quotient witness lifting the prescribed crossing source,
the large-quotient essential extension supplies essentiality, the exact
boundary exclusion and the page and length bounds. -/
private theorem finite_crossing_of_lifted_witness
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q i b : ℕ) (hi : 0 < i) (hiq : i < q) (N s t : ℤ)
    (x : Ambient background X (s+i,t+i))
    (y : Ambient background Y (s+i+(N-i-b),t+i+(N-i-b)))
    (W : FiniteExtensionWitness background X Y f ((q-i)+1) (N-i-b) (s+i) (t+i) x y) :
    let p : ℤ × ℤ := ((t+i)-(s+i),(t+i)+normalizedExponent background.classicalTower f)
    ∀ z : ((background.family.obj ((SyntheticObject.quotient q (.nu Y)).obj
      background.nu background.auxiliary)).sequence.ssData
      (s+i+(N-i-b),(p+((0:ℤ),-(i:ℤ))).1+(s+i+(N-i-b)),
        (p+((0:ℤ),-(i:ℤ))).2)).eInfty,
      TowerEssentialExtension (background.convergentMap
        (.quotient q (extensionSourceObject background X Y f)) (.quotient q (.nu Y))
        (finiteExtensionMap background X Y f q)) (p+((0:ℤ),-(i:ℤ))) (s+i) (N-i-b)
        (finiteLambdaInfinity (extensionSourceObject background X Y f) q i hi hiq p (s+i) W.source) z →
      FiniteHasCrossing background X Y f (q+1) N s t := by
  intro p z hess
  obtain ⟨hsmall,hne⟩ := finite_extension_essential_of_lambda_source
    (extensionSourceObject background X Y f) (.nu Y) (background.normalizedMap X Y f).map
    q i hi hiq p (s+i) (N-i-b) W.source W.target z W.equation hess
  have hb := (finite_witness_lambda_target_nonzero_iff X Y f q i hi hiq
    (N-i-b) (s+i) (t+i) x y W).mp hne
  have hb' : y ∉ boundaries background Y
      (1+N-b-normalizedExponent background.classicalTower f)
      (s+i+(N-i-b),t+i+(N-i-b)) := by
    rwa [show 1+(N-i-b)+(i:ℤ)-normalizedExponent background.classicalTower f =
      1+N-b-normalizedExponent background.classicalTower f by omega] at hb
  refine ⟨i,b,hi,by omega,?_,x,y,?_⟩
  · have hl := W.length_lower
    omega
  · rw [show (q+1)-i=(q-i)+1 by omega]
    exact ⟨W,hsmall,hb'⟩

/-- An actual source with a sufficiently filtered image gives a finite
extension of arbitrary allowed length, retaining that very image as the
detecting representative of the target. -/
private theorem finite_witness_of_filtered_source_image
    (X Y : AdamsObject (coefficients := background.coefficients)) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (hq : 0 < q) (n s t : ℤ)
    (hn : (normalizedExponent background.classicalTower f : ℤ) ≤ n)
    (hnq : n ≤ (q:ℤ)-1+normalizedExponent background.classicalTower f)
    (a : BiHom (t-s) (t+normalizedExponent background.classicalTower f)
      (XModLambdaN ((extensionSourceObject background X Y f).obj background.nu background.auxiliary) q))
    (himage : FiltrationAtLeast background.syntheticTower (s+n)
      (a ≫ finiteExtensionMap background X Y f q)) :
    ∃ (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n)),
      ∃ _W : FiniteExtensionWitness background X Y f (q+1) n s t x y,
        Detects (background.convergence (.quotient q (extensionSourceObject background X Y f)))
          (s,t,t+normalizedExponent background.classicalTower f)
          (regradeE2 (by simp) (finiteNuLabel background X q
            (normalizedExponent background.classicalTower f) s t 0 x)) a ∧
        Detects (background.convergence (.quotient q (.nu Y)))
          (s+n,t+n,t+normalizedExponent background.classicalTower f)
          ((background.family.quotientProjection (background.nu.functor.obj (Y.obj background.auxiliary)) q).pageMap
            2 (s+n,t+n,t+normalizedExponent background.classicalTower f)
            (nuWeightLabel background Y (s+n) (t+n)
              (t+normalizedExponent background.classicalTower f) (by omega) y))
          (homotopyRegrade (by dsimp; omega) rfl (a ≫ finiteExtensionMap background X Y f q)) := by
  let e : ℤ := normalizedExponent background.classicalTower f
  obtain ⟨x,hx,hax⟩ := normalized_finite_source_label_exists X Y f q hq s t a
  let b : BiHom ((t+n)-(s+n)) (t+e)
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q) :=
    homotopyRegrade (by omega) rfl (a ≫ finiteExtensionMap background X Y f q)
  have hb : FiltrationAtLeast background.syntheticTower (s+n) b :=
    (regrade_filtration_iff (by omega) rfl (s+n) _).mpr himage
  obtain ⟨y,hy,hby⟩ := finite_filtered_target_label Y q hq (s+n) (t+n) (t+e)
    (by dsimp [e]; constructor <;> omega) b hb
  have hsource := source_detects_reindex X q e s t x a hax
  let hp : (s+n,(t-s)+(s+n),t+e) = (s+n,t+n,t+e) := by
    ext <;> first | rfl | (dsimp; omega)
  have htarget' : Detects (background.convergence (.quotient q (.nu Y)))
      (s+n,(t-s)+(s+n),t+e)
      (finiteTargetForExtension background X Y f q n s t hn y)
      (homotopyRegrade (by dsimp; omega) rfl (a ≫ finiteExtensionMap background X Y f q)) := by
    have Hback := detects_transport hp.symm _ _ hby
    convert Hback using 1
    · have H := congrArg (regradeE2 hp.symm)
        (finite_extension_target_weight_label X Y f q n s t hn y)
      rw [e2_regrade_trans] at H
      exact H
    · dsimp only [b]
      rw [homotopy_regrade_comp]
  obtain ⟨xx,yy,hxx,hyy,heq⟩ := extension_equation_of_detected_pair
    (background.convergentMap (.quotient q (extensionSourceObject background X Y f))
      (.quotient q (.nu Y)) (finiteExtensionMap background X Y f q))
      (t-s,t+e) s n (by dsimp [e] at *; omega) _ _ a
      (a ≫ finiteExtensionMap background X Y f q) hsource htarget' rfl
  have hxreach : ReachesPage (background.classical.obj (X.obj background.auxiliary))
      (q+1:ℕ) (s,t) x :=
    (isCycle_iff_reaches background X (q+1:ℕ) (by omega) (s,t) x).mp
      ⟨by omega,by simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hx⟩
  have hyreach : ReachesPage (background.classical.obj (Y.obj background.auxiliary))
      ((q+1:ℕ)-n+normalizedExponent background.classicalTower f) (s+n,t+n) y := by
    apply (isCycle_iff_reaches background Y _ (by omega) (s+n,t+n) y).mp
    refine ⟨by omega,?_⟩
    convert hy using 1
    dsimp [e]
    congr 1
    omega
  refine ⟨x,y,?_,hax,hby⟩
  exact {
    page_ge_two := by omega
    length_lower := hn
    length_upper := by omega
    source_cycle := hxreach
    target_cycle := hyreach
    source := xx
    target := yy
    source_rep := hxx
    target_rep := hyy
    equation := heq }

/-- Boundary ambiguity in the crossing lift: vanishing of the mapped
target grade is equivalent to membership in the larger boundary submodule. -/
private theorem finite_weighted_lambda_high_iff_boundary
    (X : AdamsObject (coefficients := background.coefficients)) (q k : ℕ) (hk : 0 < k) (hkq : k < q)
    (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w < (q-k:ℕ))
    (y : Ambient background X (s,t))
    (b : BiHom (t-s) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)))
    (hb : Detects (background.convergence (.quotient (q-k) (.nu X))) (s,t,w)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) (q-k)).pageMap
        2 (s,t,w) (nuWeightLabel background X s t w (by omega) y)) b) :
    FiltrationAtLeast background.syntheticTower (s+1)
        (finiteWeightedLambdaClass X q k hk hkq s t w b) ↔
      y ∈ boundaries background X (1+t-(w-k)) (s,t) := by
  have hmap := finite_weighted_lambda_detects X q k hk hkq s t w hw y b hb
  obtain ⟨e,he,_⟩ := hb
  have hy := ((KIP126.Literature.Standard.eInfinity_finite_labels X (q-k) (by omega)
    s t w hw y e).mp he).1
  have hy' : y ∈ cycles background X (q-t+(w-k)) (s,t) := by
    convert hy using 1
    congr 1
    omega
  have hzero : HasInfinityRepresentative _ 2 (s,t,w-k)
      ((background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap
        2 (s,t,w-k) (nuWeightLabel background X s t (w-k) (by omega) y)) 0 ↔
      y ∈ boundaries background X (1+t-(w-k)) (s,t) := by
    rw [KIP126.Literature.Standard.eInfinity_finite_labels X q (by omega)
      s t (w-k) (by constructor <;> omega)]
    constructor
    · rintro ⟨hy0,hclass⟩
      apply (CrossingLabels.subquotient_zero_iff _ _ ⟨y,hy0⟩).mp
      exact hclass.symm.trans (map_zero _)
    · intro hboundary
      refine ⟨hy',?_⟩
      rw [map_zero]
      exact ((CrossingLabels.subquotient_zero_iff _ _ ⟨y,hy'⟩).mpr hboundary).symm
  constructor
  · intro hhigh
    exact hzero.mp (detects_high_infinity_zero (.quotient q (.nu X)) (s,t,w-k)
      _ _ hmap hhigh)
  · intro hboundary
    exact detects_zero_infinity_filtration (background.convergence (.quotient q (.nu X)))
      (s,t,w-k) hmap (hzero.mpr hboundary)

/-- The untruncated boundary test for the infinite crossing comparison.
It allows any positive lambda exponent, without a finite-page upper bound. -/
private theorem nu_lambda_high_iff_boundary
    (X : AdamsObject (coefficients := background.coefficients)) (k : ℕ) (hk : 0 < k) (s t : ℤ)
    (y : Ambient background X (s,t)) (hy : y ∈ permanentCycles background X (s,t))
    (a : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)))
    (ha : a ≫ XModLambdaN.incl _ 1 = firstLabel background X s t y ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    FiltrationAtLeast background.syntheticTower (s+1) (lambdaMultiply k a) ↔
      y ∈ boundaries background X (k+1) (s,t) := by
  have hmap := nu_lambda_detects X k hk s t y hy a ha
  have hzero : HasInfinityRepresentative _ 2 (s,t,t-k)
      (nuWeightLabel background X s t (t-k) (by omega) y) 0 ↔
      y ∈ boundaries background X (1+t-(t-k)) (s,t) := by
    rw [KIP126.Literature.Standard.eInfinity_nu_labels X s t (t-k) (by omega)]
    constructor
    · rintro ⟨hy0,hclass⟩
      apply (CrossingLabels.subquotient_zero_iff _ _ ⟨y,hy0⟩).mp
      exact hclass.symm.trans (map_zero _)
    · intro hboundary
      refine ⟨hy,?_⟩
      rw [map_zero]
      exact ((CrossingLabels.subquotient_zero_iff _ _ ⟨y,hy⟩).mpr hboundary).symm
  have hindex : 1+t-(t-k)=(k:ℤ)+1 := by omega
  rw [hindex] at hzero
  constructor
  · intro hhigh
    exact hzero.mp (detects_high_infinity_zero (.nu X) (s,t,t-k) _ _ hmap hhigh)
  · intro hboundary
    exact detects_zero_infinity_filtration (background.convergence (.nu X)) (s,t,t-k)
      hmap (hzero.mpr hboundary)

end
end KIP126.ProofTools.Internal.Leibniz
