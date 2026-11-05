module

import all KIP126.ProofTools.SyntheticCoverage.OrdinaryFiniteRows

/-! Finite quotient rows for sphere and nu-cofiber sources.
The nu-cofiber's two-cell triangle gives global Hom vanishing by exactness.
Object isomorphisms extend these unrotated-row constructions to integer
shifts of the displayed finite-cell sources. -/
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
set_option maxHeartbeats 2000000

private def nu_row_sphere_suspension_iso (m w : ℤ) :
    (Smn (Syn:=SyntheticSpectrum) m w)⟦(1:ℤ)⟧ ≅ Smn (m+1) w :=
  (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app (Smn m w) ≪≫
    (biShiftAddIso (m,w) (1,0) (m+1,w) (by ext <;> simp)).app S_0_0

private theorem nu_row_hom_middle_zero
    (T : Triangle SyntheticSpectrum) (hT : T∈distTriang SyntheticSpectrum)
    (D : SyntheticSpectrum) (hA : ∀ a : T.obj₁⟶D, a=0) (hC : ∀ c : T.obj₃⟶D, c=0)
    (b : T.obj₂⟶D) : b=0 := by
  obtain ⟨c,hc⟩ := T.yoneda_exact₂ hT b (hA _)
  rw [hc,hC c,comp_zero]

private theorem nu_row_sphere_hom_zero
    (Y : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (hq : 0<q) (m w : ℤ) (hw : w+q-1<m)
    {D : SyntheticSpectrum} (e : D≅Smn m w)
    (b : D⟶XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q) : b=0 := by
  have hz : e.inv≫b=0 := finite_high_filtration_zero Y q hq m w 0
    (by omega) (e.inv≫b) (filtration_at_zero background.syntheticTower _ _ _ _)
  exact (cancel_epi e.inv).mp (by simpa using hz)

/-- The actual two-cell triangle has endpoint spheres (0,0) and (4,4).
Both endpoint Hom groups vanish after the indicated shift, so exactness
kills every morphism out of the entire shifted middle object. -/
private theorem nu_cofiber_shifted_obstruction_zero
    (Y : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (hq : 0<q) (m w : ℤ) (hw : w+q≤m+1)
    (b : ((SyntheticCategory.biShift (m,w)).obj
      (background.nu.functor.obj (ClassicalObject.nuCofiber.obj background.auxiliary)))⟦(1:ℤ)⟧⟶
      XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q) : b=0 := by
  let T := (normalizedTriangle background background.auxiliary.nuRouteTriangle
    KIP126.Literature.Standard.nuCofiber_exponent_sum).rotate
  have hT : T∈distTriang SyntheticSpectrum :=
    rot_of_distTriang _ KIP126.Literature.Standard.nuCofiber_distinguished
  let eA : T.obj₁≅Smn (Syn:=SyntheticSpectrum) 0 0 :=
    background.nu.unitIso ≪≫ SyntheticCategory.biShift_zero.symm.app S_0_0
  let eC : T.obj₃≅Smn (Syn:=SyntheticSpectrum) 4 4 := by
    change ((SyntheticCategory.biShift
      (0,(normalizedExponent background.classicalTower background.auxiliary.nuMap:ℤ))).obj
      (background.nu.functor.obj (Sphere (C:=Spectrum) 3)))⟦(1:ℤ)⟧ ≅ _
    rw [KIP126.Literature.Standard.nuCofiber_nu_exponent]
    exact (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      ((SyntheticCategory.biShift (0,(1:ℤ))).mapIso (nuSphereThree background) ≪≫
        (biShiftAddIso (3,3) (0,1) (3,4) (by decide)).app S_0_0) ≪≫
      nu_row_sphere_suspension_iso 3 4
  let eB : T.obj₂≅background.nu.functor.obj (ClassicalObject.nuCofiber.obj background.auxiliary) := by
    change (SyntheticCategory.biShift
      (0,-(normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g:ℤ))).obj
      (background.nu.functor.obj (ClassicalObject.nuCofiber.obj background.auxiliary)) ≅ _
    rw [KIP126.Literature.Standard.nuCofiber_bottom_exponent]
    exact SyntheticCategory.biShift_zero.app _
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (m,w)
  letI : F.Additive := background.exactness.shiftAdditive (m,w)
  letI : F.CommShift ℤ := background.exactness.shiftCommShift (m,w)
  letI : F.IsTriangulated := background.exactness.shiftExact (m,w)
  let U := (F.mapTriangle.obj T)⟦(1:ℤ)⟧
  have hU : U∈distTriang SyntheticSpectrum :=
    Triangle.shift_distinguished _ (F.map_distinguished T hT) 1
  let eUA : U.obj₁≅Smn (Syn:=SyntheticSpectrum) (m+1) w :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      (F.mapIso eA ≪≫ (biShiftAddIso (0,0) (m,w) (m,w) (by ext <;> simp)).app S_0_0) ≪≫
      nu_row_sphere_suspension_iso m w
  let eUC : U.obj₃≅Smn (Syn:=SyntheticSpectrum) (m+5) (w+4) :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      (F.mapIso eC ≪≫
        (biShiftAddIso (4,4) (m,w) (m+4,w+4) (by ext <;> simp [add_comm])).app S_0_0) ≪≫
      nu_row_sphere_suspension_iso (m+4) (w+4) ≪≫eqToIso (by congr 1; omega)
  let eUB : U.obj₂≅((SyntheticCategory.biShift (m,w)).obj
      (background.nu.functor.obj (ClassicalObject.nuCofiber.obj background.auxiliary)))⟦(1:ℤ)⟧ :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso (F.mapIso eB)
  have hz : eUB.hom≫b=0 := nu_row_hom_middle_zero U hU _
    (fun a => nu_row_sphere_hom_zero Y q hq (m+1) w (by omega) eUA a)
    (fun c => nu_row_sphere_hom_zero Y q hq (m+5) (w+4) (by omega) eUC c) _
  exact (cancel_epi eUB.hom).mp (by simpa using hz)

private theorem nu_cofiber_source_obstruction_zero
    (Y : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (hq : 0<q) (a b : ℤ) (hb : b-a≤1)
    {A : SyntheticSpectrum}
    (e : A≅(SyntheticCategory.biShift (a,b)).obj
      (background.nu.functor.obj (ClassicalObject.nuCofiber.obj background.auxiliary)))
    (z : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧⟶
      XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q) : z=0 := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let e₀ := F.mapIso e ≪≫
    (biShiftAddIso (a,b) (0,-(q:ℤ)) (a,b-q) (by ext <;> simp [sub_eq_add_neg])).app _
  let e₁ := (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso e₀
  have hz : e₁.inv≫z=0 := nu_cofiber_shifted_obstruction_zero Y q hq a (b-q) (by omega) _
  exact (cancel_epi e₁.inv).mp (by simpa using hz)

/-- The finite-quotient square commutes on the entire actual source. -/
private theorem nu_cofiber_source_suspension_square
    (Y : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (hq : 0<q) (a b : ℤ) (hb : b-a≤1)
    {A : SyntheticSpectrum}
    (e : A≅(SyntheticCategory.biShift (a,b)).obj
      (background.nu.functor.obj (ClassicalObject.nuCofiber.obj background.auxiliary)))
    (f : A⟶background.nu.functor.obj (Y.obj background.auxiliary))
    (eA : XModLambdaN (A⟦(1:ℤ)⟧) q≅(XModLambdaN A q)⟦(1:ℤ)⟧)
    (eB : XModLambdaN ((background.nu.functor.obj (Y.obj background.auxiliary))⟦(1:ℤ)⟧) q≅
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)⟦(1:ℤ)⟧)
    (heA : XModLambdaN.incl _ q≫eA.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl A q))
    (heB : XModLambdaN.incl _ q≫eB.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q)) :
    XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map f) q≫eB.hom=
      eA.hom≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map f q) := by
  letI := background.exactness.shiftCommShift (0,-(q:ℤ))
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let l := XModLambdaN.map (S.map f) q≫eB.hom
  let r := eA.hom≫S.map (XModLambdaN.map f q)
  have hinc : XModLambdaN.incl _ q≫(l-r)=0 := by
    dsimp only [l,r]
    rw [Preadditive.comp_sub,←Category.assoc,←XModLambdaN.incl_naturality,
      Category.assoc,heB,←Functor.map_comp,XModLambdaN.incl_naturality,
      Functor.map_comp,←heA,Category.assoc,sub_self]
  obtain ⟨z,hz⟩ := (XModLambdaN.cofiberTriangle (A⟦(1:ℤ)⟧) q).yoneda_exact₃
    (XModLambdaN.cofiberTriangle_distinguished _ _) (l-r) hinc
  let χ := S.mapIso ((F.commShiftIso (1:ℤ)).app A)
  let ff := Functor.FullyFaithful.ofFullyFaithful S
  let z₀ := ff.preimage (χ.inv≫z)
  have hz₀ : z₀=0 := nu_cofiber_source_obstruction_zero Y q hq a b hb e z₀
  have hzmap : S.map z₀=χ.inv≫z := ff.map_preimage _
  have hz0 : z=0 := (cancel_epi χ.inv).mp (by rw [←hzmap,hz₀,S.map_zero]; simp)
  apply sub_eq_zero.mp
  change l-r=0
  rw [hz,hz0,comp_zero]

private theorem nu_cofiber_source_actual_unrotated_row
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (a b : ℤ) (hb : b-a≤1)
    (e : (normalizedTriangle background T he).obj₁≅(SyntheticCategory.biShift (a,b)).obj
      (background.nu.functor.obj (ClassicalObject.nuCofiber.obj background.auxiliary)))
    (q : ℕ) (hq : 0<q) :
    ∃ eA : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) q≅
        (XModLambdaN (normalizedTriangle background T he).obj₁ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl _ q≫eA.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q) ∧
      Triangle.mk (XModLambdaN.map (normalizedTriangle background T he).mor₁ q)
        (XModLambdaN.map (normalizedTriangle background T he).mor₂ q)
        (XModLambdaN.map (normalizedTriangle background T he).mor₃ q≫eA.hom)∈distTriang SyntheticSpectrum := by
  obtain ⟨eB,heB,hrow⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row T he q hq
  obtain ⟨eA,heA⟩ := quotient_suspension_inclusion_exists (normalizedTriangle background T he).obj₁ q
  refine ⟨eA,heA,unrotated_row_of_selected_suspension_square _ q eA eB hrow ?_⟩
  exact nu_cofiber_source_suspension_square T.Y q hq a b hb e
    (normalizedTriangle background T he).mor₁ eA eB heA heB

private theorem literal_nu_cofiber_actual_unrotated_row
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he) (hX : T.X=.nuCofiber)
    (q : ℕ) (hq : 0<q) :
    ∃ eA : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) q≅
        (XModLambdaN (normalizedTriangle background T he).obj₁ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl _ q≫eA.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q) ∧
      Triangle.mk (XModLambdaN.map (normalizedTriangle background T he).mor₁ q)
        (XModLambdaN.map (normalizedTriangle background T he).mor₂ q)
        (XModLambdaN.map (normalizedTriangle background T he).mor₃ q≫eA.hom)∈distTriang SyntheticSpectrum := by
  let a : ℤ := normalizedExponent background.classicalTower T.f
  apply nu_cofiber_source_actual_unrotated_row T he hT 0 a
    (by dsimp only [a]; have h := normalizedExponent_le_one background.classicalTower T.f; omega) _ q hq
  change (SyntheticCategory.biShift (0,a)).obj (background.nu.functor.obj (T.X.obj background.auxiliary))≅_
  rw [hX]
  exact Iso.refl _

private def nu_row_diagonal_comp_iso (a b c : ℤ) (h : a+b=c) (X : SyntheticSpectrum) :
    (SyntheticCategory.biShift (b,b)).obj ((SyntheticCategory.biShift (a,a)).obj X)≅
      (SyntheticCategory.biShift (c,c)).obj X :=
  (biShiftAddIso (a,a) (b,b) (c,c) (by ext <;> exact h)).app X

private def nu_row_nu_zero_iso (X : Spectrum) :
    background.nu.functor.obj (X⟦(0:ℤ)⟧)≅(SyntheticCategory.biShift (0,0)).obj (background.nu.functor.obj X) :=
  background.nu.functor.mapIso ((shiftFunctorZero Spectrum ℤ).app X) ≪≫
    SyntheticCategory.biShift_zero.symm.app (background.nu.functor.obj X)

private def nu_row_nu_minus_one_iso (X : Spectrum) :
    background.nu.functor.obj (X⟦(-1:ℤ)⟧)≅(SyntheticCategory.biShift (-1,-1)).obj (background.nu.functor.obj X) := by
  let c : (X⟦(-1:ℤ)⟧)⟦(1:ℤ)⟧≅X := (shiftFunctorCompIsoId Spectrum (-1) 1 (by omega)).app X
  let e : background.nu.functor.obj X≅(SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (X⟦(-1:ℤ)⟧)) :=
    (background.nu.functor.mapIso c).symm ≪≫background.nu.suspensionIso (X⟦(-1:ℤ)⟧)
  exact ((SyntheticCategory.biShift (-1,-1)).mapIso e ≪≫
    nu_row_diagonal_comp_iso 1 (-1) 0 (by omega) _ ≪≫SyntheticCategory.biShift_zero.app _).symm

private def nu_row_nu_nat_iso (X : Spectrum) : (n : ℕ) →
    background.nu.functor.obj (X⟦(n:ℤ)⟧)≅
      (SyntheticCategory.biShift ((n:ℤ),(n:ℤ))).obj (background.nu.functor.obj X)
  | 0 => nu_row_nu_zero_iso X
  | n+1 => background.nu.functor.mapIso
      ((shiftFunctorAdd' Spectrum (n:ℤ) 1 ((n+1:ℕ):ℤ) (by omega)).app X) ≪≫
    background.nu.suspensionIso (X⟦(n:ℤ)⟧) ≪≫
    (SyntheticCategory.biShift (1,1)).mapIso (nu_row_nu_nat_iso X n) ≪≫
    nu_row_diagonal_comp_iso (n:ℤ) 1 ((n+1:ℕ):ℤ) (by omega) _

private def nu_row_nu_neg_nat_iso (X : Spectrum) : (n : ℕ) →
    background.nu.functor.obj (X⟦(-(n:ℤ))⟧)≅
      (SyntheticCategory.biShift (-(n:ℤ),-(n:ℤ))).obj (background.nu.functor.obj X)
  | 0 => nu_row_nu_zero_iso X
  | n+1 => background.nu.functor.mapIso
      ((shiftFunctorAdd' Spectrum (-(n:ℤ)) (-1) (-((n+1:ℕ):ℤ)) (by omega)).app X) ≪≫
    nu_row_nu_minus_one_iso (X⟦(-(n:ℤ))⟧) ≪≫
    (SyntheticCategory.biShift (-1,-1)).mapIso (nu_row_nu_neg_nat_iso X n) ≪≫
    nu_row_diagonal_comp_iso (-(n:ℤ)) (-1) (-((n+1:ℕ):ℤ)) (by omega) _

private def nu_row_nu_int_iso (X : Spectrum) : (n : ℤ) →
    background.nu.functor.obj (X⟦n⟧)≅(SyntheticCategory.biShift (n,n)).obj (background.nu.functor.obj X)
  | .ofNat n => nu_row_nu_nat_iso X n
  | .negSucc n => nu_row_nu_neg_nat_iso X (n+1)

/-- The geometric condition is the actual-isomorphism clause in both
branches of the finite-source case. -/
private theorem finite_cell_source_actual_unrotated_row
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hX : (∃ n : ℤ, Nonempty (T.X.obj background.auxiliary≅Sphere (C:=Spectrum) n)) ∨
      (∃ n : ℤ, Nonempty (T.X.obj background.auxiliary≅
        (ClassicalObject.nuCofiber.obj background.auxiliary)⟦n⟧)))
    (q : ℕ) (hq : 0<q) :
    ∃ eA : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) q≅
        (XModLambdaN (normalizedTriangle background T he).obj₁ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl _ q≫eA.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q) ∧
      Triangle.mk (XModLambdaN.map (normalizedTriangle background T he).mor₁ q)
        (XModLambdaN.map (normalizedTriangle background T he).mor₂ q)
        (XModLambdaN.map (normalizedTriangle background T he).mor₃ q≫eA.hom)∈distTriang SyntheticSpectrum := by
  let a : ℤ := normalizedExponent background.classicalTower T.f
  have ha : a≤1 := by
    dsimp only [a]
    exact_mod_cast normalizedExponent_le_one background.classicalTower T.f
  rcases hX with hs | hc
  · obtain ⟨n,⟨e⟩⟩ := hs
    let eNu : background.nu.functor.obj (T.X.obj background.auxiliary)≅Smn (Syn:=SyntheticSpectrum) n n :=
      background.nu.functor.mapIso e ≪≫nu_row_nu_int_iso SphereSpectrum n ≪≫
        (SyntheticCategory.biShift (n,n)).mapIso background.nu.unitIso
    let eA : (normalizedTriangle background T he).obj₁≅Smn (Syn:=SyntheticSpectrum) n (n+a) :=
      (SyntheticCategory.biShift (0,a)).mapIso eNu ≪≫
        (biShiftAddIso (n,n) (0,a) (n,n+a) (by ext <;> simp)).app _
    exact sphere_source_actual_unrotated_row T he hT n (n+a) (by omega) eA q hq
  · obtain ⟨n,⟨e⟩⟩ := hc
    let eNu := background.nu.functor.mapIso e ≪≫
      nu_row_nu_int_iso (ClassicalObject.nuCofiber.obj background.auxiliary) n
    let eA : (normalizedTriangle background T he).obj₁≅(SyntheticCategory.biShift (n,n+a)).obj
        (background.nu.functor.obj (ClassicalObject.nuCofiber.obj background.auxiliary)) :=
      (SyntheticCategory.biShift (0,a)).mapIso eNu ≪≫
        (biShiftAddIso (n,n) (0,a) (n,n+a) (by ext <;> simp)).app _
    exact nu_cofiber_source_actual_unrotated_row T he hT n (n+a) (by omega) eA q hq

/-- Closure under literal integer shifts, retaining an actual isomorphism
of the same selected classical object at each step. -/
private theorem nu_row_finite_source_case_shift (X : (AdamsObject (coefficients := background.coefficients))) (n : ℤ)
    (hX : (∃ a : ℤ, Nonempty (X.obj background.auxiliary≅Sphere (C:=Spectrum) a)) ∨
      (∃ a : ℤ, Nonempty (X.obj background.auxiliary≅(ClassicalObject.nuCofiber.obj background.auxiliary)⟦a⟧))) :
    (∃ a : ℤ, Nonempty ((AdamsObject.shift n X).obj background.auxiliary≅Sphere (C:=Spectrum) a)) ∨
      (∃ a : ℤ, Nonempty ((AdamsObject.shift n X).obj background.auxiliary≅
        (ClassicalObject.nuCofiber.obj background.auxiliary)⟦a⟧)) := by
  rcases hX with hs | hc
  · obtain ⟨a,⟨e⟩⟩ := hs
    exact Or.inl ⟨a+n,⟨(shiftFunctor Spectrum n).mapIso e ≪≫
      (shiftFunctorAdd Spectrum a n).symm.app SphereSpectrum⟩⟩
  · obtain ⟨a,⟨e⟩⟩ := hc
    exact Or.inr ⟨a+n,⟨(shiftFunctor Spectrum n).mapIso e ≪≫
      (shiftFunctorAdd Spectrum a n).symm.app (ClassicalObject.nuCofiber.obj background.auxiliary)⟩⟩

end
end KIP126.ProofTools.Internal.SyntheticCoverage
