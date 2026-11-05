module

import KIP126.Literature.Standard.FiniteQuotientNormalized
import all KIP126.ProofTools.SyntheticCoverage.OrdinaryRotatedLift

/-! Finite quotient rows and forward common lifts.
The general forward construction takes an unrotated row as input.
For sphere sources, the displayed sphere-coordinate hypothesis supplies
this row. All quotient maps are the selected maps of the fixed background. -/

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

/-- The strict suspension square identifies the rotated row with
the unrotated row by TR2 and a triangle isomorphism. -/
private theorem unrotated_row_of_selected_suspension_square
    (N : Triangle SyntheticSpectrum) (q : ℕ)
    (eA : XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧)
    (eB : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧)
    (hrow : Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
      (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫eB.hom))
        ∈ distTriang SyntheticSpectrum)
    (hNat : XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫eB.hom=
      eA.hom≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map N.mor₁ q)) :
    Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q)
      (XModLambdaN.map N.mor₃ q≫eA.hom) ∈ distTriang SyntheticSpectrum := by
  let R := Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q)
    (XModLambdaN.map N.mor₃ q≫eA.hom)
  let U := Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫eB.hom))
  let e : U ≅ R.rotate := Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) eA
    (by simp [U,R]) (by simp [U,R]) (by
      dsimp only [U,R,Triangle.rotate,Triangle.mk]
      simpa only [Iso.refl_hom,CategoryTheory.Functor.map_id,Category.comp_id,
        CategoryTheory.Functor.map_neg,Preadditive.comp_neg] using
        congrArg (fun k => -k) hNat)
  have hr : R.rotate∈distTriang SyntheticSpectrum :=
    isomorphic_distinguished U hrow R.rotate e.symm
  exact (rotate_distinguished_triangle R).mpr hr

/-- The unrotated row gives the forward construction and both target
equations under the spherewise restriction no-return condition. -/
private theorem forward_lift_of_unrotated_row
    (N : Triangle SyntheticSpectrum) (i q : ℕ) (hi : 0 < i) (hq : 0 < q)
    (eA : XModLambdaN (N.obj₁⟦(1:ℤ)⟧) (i+q) ≅
      (XModLambdaN N.obj₁ (i+q))⟦(1:ℤ)⟧)
    (hrow : Triangle.mk (XModLambdaN.map N.mor₁ (i+q)) (XModLambdaN.map N.mor₂ (i+q))
      (XModLambdaN.map N.mor₃ (i+q)≫eA.hom)∈distTriang SyntheticSpectrum)
    (m w : ℤ)
    (hNoReturn : ∀ (b : BiHom m w (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
        (XModLambdaN N.obj₁ (i+q-i)))⟦(1:ℤ)⟧))
      (z : (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
        (XModLambdaN N.obj₁ (i+q-i)))⟦(1:ℤ)⟧)⟶XModLambdaN N.obj₃ i), b≫z=0)
    (a : BiHom m w (XModLambdaN N.obj₂ i))
    (b : BiHom m w (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN N.obj₁ (i+q-i)))⟦(1:ℤ)⟧))
    (hab : a≫((background.quotients.tower N.obj₂).triangle hi (show i < i+q by omega)).delta=
      b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.map N.mor₁ (i+q-i)))) :
    ∃ R : BiHom m w (XModLambdaN N.obj₃ (i+q)),
      R≫(background.quotients.tower N.obj₃).rho i (i+q) (by omega)=a≫XModLambdaN.map N.mor₂ i ∧
      R≫XModLambdaN.map N.mor₃ (i+q)≫eA.hom=
        b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((background.quotients.tower N.obj₁).triangle hi (show i < i+q by omega)).lambdaMap := by
  letI := background.exactness.syntheticTriangulated
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let CA := (background.quotients.tower N.obj₁).triangle hi (show i < i+q by omega)
  let CB := (background.quotients.tower N.obj₂).triangle hi (show i < i+q by omega)
  have hs : CA.lambdaMap≫XModLambdaN.map N.mor₁ (i+q)=
      F.map (XModLambdaN.map N.mor₁ (i+q-i))≫CB.lambdaMap :=
    ((background.quotients.natural N.mor₁).lambda_naturality hi (show i < i+q by omega)).symm
  have hr : XModLambdaN.map N.mor₂ (i+q)≫(background.quotients.tower N.obj₃).rho i (i+q) (by omega)=
      CB.rho≫XModLambdaN.map N.mor₂ i := by
    rw [(background.quotients.tower N.obj₂).triangle_rho]
    exact ((background.quotients.natural N.mor₂).rho_naturality (show i ≤ i+q by omega)).symm
  obtain ⟨R,hR,hk⟩ := ThreeByThree.common_lift_of_no_return
    (F.map (XModLambdaN.map N.mor₁ (i+q-i))) CB.lambdaMap CA.lambdaMap
    (XModLambdaN.map N.mor₁ (i+q)) (XModLambdaN.map N.mor₂ (i+q))
    (XModLambdaN.map N.mor₃ (i+q)≫eA.hom) CB.rho CB.delta
    (XModLambdaN.map N.mor₂ i) ((background.quotients.tower N.obj₃).rho i (i+q) (by omega))
    CB.distinguished hrow hs hr hNoReturn a b hab
  exact ⟨R,hR,by simpa only [Category.assoc] using hk⟩

/-- Ordinary-first-arrow geometry gives forward no-return. Any objectwise
short suspension comparison transports the specified vanishing. -/
private theorem ordinary_forward_no_return
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (i : ℕ) (hi : 0 < i) (m w : ℤ)
    (e : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (i+1-i) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ (i+1-i))⟦(1:ℤ)⟧)
    (b : BiHom m w (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (normalizedTriangle background T he).obj₁ (i+1-i)))⟦(1:ℤ)⟧))
    (z : (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (normalizedTriangle background T he).obj₁ (i+1-i)))⟦(1:ℤ)⟧) ⟶
      XModLambdaN (normalizedTriangle background T he).obj₃ i) : b≫z=0 := by
  letI := background.exactness.shiftCommShift (0,-(i:ℤ))
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let χ := F.mapIso e ≪≫ (F.commShiftIso (1:ℤ)).app _
  have h := ordinary_rotated_restriction_no_return T he hf i hi m w
    (b≫χ.inv) (χ.hom≫z)
  simpa only [Category.assoc,Iso.inv_hom_id_assoc] using h

/-- The ordinary forward construction with an explicit actual unrotated-row
premise. Both finite maps are the selected maps. -/
private theorem ordinary_forward_lift_of_unrotated_row
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (i : ℕ) (hi : 0 < i)
    (e₁ : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (i+1-i) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ (i+1-i))⟦(1:ℤ)⟧)
    (eN : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (i+1) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ (i+1))⟦(1:ℤ)⟧)
    (hrow : Triangle.mk (XModLambdaN.map (normalizedTriangle background T he).mor₁ (i+1))
      (XModLambdaN.map (normalizedTriangle background T he).mor₂ (i+1))
      (XModLambdaN.map (normalizedTriangle background T he).mor₃ (i+1)≫eN.hom)
        ∈distTriang SyntheticSpectrum)
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN (normalizedTriangle background T he).obj₂ i))
    (b : BiHom m w (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (normalizedTriangle background T he).obj₁ (i+1-i)))⟦(1:ℤ)⟧))
    (hab : a≫((background.quotients.tower (normalizedTriangle background T he).obj₂).triangle
        hi (show i < i+1 by omega)).delta=
      b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map
          (XModLambdaN.map (normalizedTriangle background T he).mor₁ (i+1-i)))) :
    ∃ R : BiHom m w (XModLambdaN (normalizedTriangle background T he).obj₃ (i+1)),
      R≫(background.quotients.tower (normalizedTriangle background T he).obj₃).rho i (i+1) (by omega)=
        a≫XModLambdaN.map (normalizedTriangle background T he).mor₂ i ∧
      R≫XModLambdaN.map (normalizedTriangle background T he).mor₃ (i+1)≫eN.hom=
        b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((background.quotients.tower (normalizedTriangle background T he).obj₁).triangle
            hi (show i < i+1 by omega)).lambdaMap := by
  exact forward_lift_of_unrotated_row (normalizedTriangle background T he) i 1 hi
    (by decide) eN hrow m w (ordinary_forward_no_return T he hf i hi m w e₁) a b hab


/-- For the actual sphere coordinate, finite-window vanishing kills the
whole morphism, because the domain itself is the displayed sphere. -/
private theorem sphere_source_obstruction_zero
    (Y : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (hq : 0 < q) (a b : ℤ) (hb : b-a≤1)
    {A : SyntheticSpectrum} (e : A≅Smn a b)
    (z : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧ ⟶
      XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q) : z=0 := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let e₁ : F.obj A ≅ Smn a (b-q) :=
    F.mapIso e ≪≫ (biShiftAddIso (a,b) (0,-(q:ℤ)) (a,b-q) (by ext <;> simp [sub_eq_add_neg])).app _
  let e₂ : (F.obj A)⟦(1:ℤ)⟧ ≅ Smn (a+1) (b-q) :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso e₁ ≪≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
      (biShiftAddIso (a,b-q) (1,0) (a+1,b-q) (by ext <;> simp)).app _
  have hz : e₂.inv≫z=0 := finite_high_filtration_zero Y q hq (a+1) (b-q) 0
    (by omega) (e₂.inv≫z) (filtration_at_zero background.syntheticTower _ _ _ _)
  exact (cancel_epi e₂.inv).mp (by simpa using hz)

/-- The strict one-arrow suspension square is produced by finite-window
vanishing for this actual sphere source, not by spherewise equality alone. -/
private theorem sphere_source_suspension_square
    (Y : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (hq : 0 < q) (a b : ℤ) (hb : b-a≤1)
    {A : SyntheticSpectrum} (e : A≅Smn a b)
    (f : A ⟶ background.nu.functor.obj (Y.obj background.auxiliary))
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
      Category.assoc,heB,←Functor.map_comp, XModLambdaN.incl_naturality,
      Functor.map_comp,←heA,Category.assoc,sub_self]
  obtain ⟨z,hz⟩ := (XModLambdaN.cofiberTriangle (A⟦(1:ℤ)⟧) q).yoneda_exact₃
    (XModLambdaN.cofiberTriangle_distinguished _ _) (l-r) hinc
  let χ := S.mapIso ((F.commShiftIso (1:ℤ)).app A)
  let ff := Functor.FullyFaithful.ofFullyFaithful S
  let z₀ := ff.preimage (χ.inv≫z)
  have hz₀ : z₀=0 := sphere_source_obstruction_zero Y q hq a b hb e z₀
  have hzmap : S.map z₀=χ.inv≫z := ff.map_preimage _
  have hz0 : z=0 := (cancel_epi χ.inv).mp (by rw [←hzmap,hz₀,S.map_zero]; simp)
  apply sub_eq_zero.mp
  change l-r=0
  rw [hz,hz0,comp_zero]

/-- The actual unrotated quotient row is constructed for normalized triangles
whose first vertex has this specified sphere coordinate. -/
private theorem sphere_source_actual_unrotated_row
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (a b : ℤ) (hb : b-a≤1)
    (e : (normalizedTriangle background T he).obj₁≅Smn a b)
    (q : ℕ) (hq : 0 < q) :
    ∃ eA : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) q≅
        (XModLambdaN (normalizedTriangle background T he).obj₁ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl _ q≫eA.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q) ∧
      Triangle.mk (XModLambdaN.map (normalizedTriangle background T he).mor₁ q)
        (XModLambdaN.map (normalizedTriangle background T he).mor₂ q)
        (XModLambdaN.map (normalizedTriangle background T he).mor₃ q≫eA.hom)∈distTriang SyntheticSpectrum := by
  obtain ⟨eB,heB,hrow⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row T he q hq
  obtain ⟨eA,heA⟩ := quotient_suspension_inclusion_exists (normalizedTriangle background T he).obj₁ q
  refine ⟨eA,heA,unrotated_row_of_selected_suspension_square _ q eA eB hrow ?_⟩
  exact sphere_source_suspension_square T.Y q hq a b hb e
    (normalizedTriangle background T he).mor₁ eA eB heA heB

/-- For the fixed sphere object, the unit comparison supplies
the geometric coordinate. -/
private theorem literal_sphere_actual_unrotated_row
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he) (hX : T.X=.sphere)
    (q : ℕ) (hq : 0 < q) :
    ∃ eA : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) q≅
        (XModLambdaN (normalizedTriangle background T he).obj₁ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl _ q≫eA.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q) ∧
      Triangle.mk (XModLambdaN.map (normalizedTriangle background T he).mor₁ q)
        (XModLambdaN.map (normalizedTriangle background T he).mor₂ q)
        (XModLambdaN.map (normalizedTriangle background T he).mor₃ q≫eA.hom)∈distTriang SyntheticSpectrum := by
  let a : ℤ := normalizedExponent background.classicalTower T.f
  have e : background.nu.functor.obj (T.X.obj background.auxiliary)≅S_0_0 := by
    rw [hX]
    exact background.nu.unitIso
  exact sphere_source_actual_unrotated_row T he hT 0 a
    (by dsimp [a]; have h := normalizedExponent_le_one background.classicalTower T.f; omega)
    ((SyntheticCategory.biShift (0,a)).mapIso e) q hq

end
end KIP126.ProofTools.Internal.SyntheticCoverage
