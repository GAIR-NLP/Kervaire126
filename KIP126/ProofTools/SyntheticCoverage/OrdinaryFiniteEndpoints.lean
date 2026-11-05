module

import all KIP126.ProofTools.SyntheticCoverage.OrdinaryFiniteCellRows

/-! Actual unrotated finite quotient rows when the second and third
classical vertices are shifts of the selected sphere or nu-cofiber.
The first vertex is unrestricted. All vanishing statements concern whole
Hom groups, obtained from the actual distinguished triangle and finite
endpoint geometry, not by identifying spherewise ghosts with zero. -/

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

/-- The actual sphere or selected nu-cofiber, with an integer suspension. -/
private def FiniteRowObject (X : (AdamsObject (coefficients := background.coefficients))) : Prop :=
  (∃ n : ℤ, Nonempty (X.obj background.auxiliary≅Sphere (C:=Spectrum) n)) ∨
    (∃ n : ℤ, Nonempty (X.obj background.auxiliary≅
      (ClassicalObject.nuCofiber.obj background.auxiliary)⟦n⟧))

/-- Either the first vertex has the original finite geometry, or the
other two vertices have it and the distinguished triangle supplies the
needed vanishing for the unrestricted first vertex. -/
private def OrdinaryFiniteSourceCover (T : TriangleData background.auxiliary) : Prop :=
  FiniteRowObject T.X ∨ (FiniteRowObject T.Y ∧ FiniteRowObject T.Z)

private theorem finite_cell_shifted_hom_zero
    (X Y : (AdamsObject (coefficients := background.coefficients)))
    (hX : (∃ n : ℤ, Nonempty (X.obj background.auxiliary≅Sphere (C:=Spectrum) n)) ∨
      (∃ n : ℤ, Nonempty (X.obj background.auxiliary≅
        (ClassicalObject.nuCofiber.obj background.auxiliary)⟦n⟧)))
    (q : ℕ) (hq : 0<q) (m w : ℤ) (hw : w+q≤m)
    (b : (SyntheticCategory.biShift (m,w)).obj (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
      XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q) : b=0 := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (m,w)
  rcases hX with hs | hc
  · obtain ⟨n,⟨e⟩⟩ := hs
    let eNu : background.nu.functor.obj (X.obj background.auxiliary)≅Smn (Syn:=SyntheticSpectrum) n n :=
      background.nu.functor.mapIso e ≪≫nu_row_nu_int_iso SphereSpectrum n ≪≫
        (SyntheticCategory.biShift (n,n)).mapIso background.nu.unitIso
    let eF : F.obj (background.nu.functor.obj (X.obj background.auxiliary))≅Smn (n+m) (n+w) :=
      F.mapIso eNu ≪≫(biShiftAddIso (n,n) (m,w) (n+m,n+w) (by ext <;> rfl)).app _
    exact nu_row_sphere_hom_zero Y q hq (n+m) (n+w) (by omega) eF b
  · obtain ⟨n,⟨e⟩⟩ := hc
    let A := background.nu.functor.obj (ClassicalObject.nuCofiber.obj background.auxiliary)
    let eNu := background.nu.functor.mapIso e ≪≫
      nu_row_nu_int_iso (ClassicalObject.nuCofiber.obj background.auxiliary) n
    let eF : F.obj (background.nu.functor.obj (X.obj background.auxiliary))≅
        (SyntheticCategory.biShift (n+m,n+w)).obj A :=
      F.mapIso eNu ≪≫(biShiftAddIso (n,n) (m,w) (n+m,n+w) (by ext <;> rfl)).app _
    let eS : ((SyntheticCategory.biShift (n+m-1,n+w)).obj A)⟦(1:ℤ)⟧≅
        (SyntheticCategory.biShift (n+m,n+w)).obj A :=
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
        (biShiftAddIso (n+m-1,n+w) (1,0) (n+m,n+w) (by ext <;> dsimp <;> omega)).app A
    have hz : eS.hom≫eF.inv≫b=0 :=
      nu_cofiber_shifted_obstruction_zero Y q hq (n+m-1) (n+w) (by omega) _
    exact (cancel_epi (eS.hom≫eF.inv)).mp (by simpa only [Category.assoc,comp_zero] using hz)

private theorem finite_cell_shifted_suspension_hom_zero
    (X Y : (AdamsObject (coefficients := background.coefficients)))
    (hX : (∃ n : ℤ, Nonempty (X.obj background.auxiliary≅Sphere (C:=Spectrum) n)) ∨
      (∃ n : ℤ, Nonempty (X.obj background.auxiliary≅
        (ClassicalObject.nuCofiber.obj background.auxiliary)⟦n⟧)))
    (q : ℕ) (hq : 0<q) (m w : ℤ) (hw : w+q≤m+1)
    (b : ((SyntheticCategory.biShift (m,w)).obj (background.nu.functor.obj (X.obj background.auxiliary)))⟦(1:ℤ)⟧ ⟶
      XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q) : b=0 := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let e : ((SyntheticCategory.biShift (m,w)).obj A)⟦(1:ℤ)⟧≅
      (SyntheticCategory.biShift (m+1,w)).obj A :=
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
      (biShiftAddIso (m,w) (1,0) (m+1,w) (by ext <;> simp)).app A
  have hz : e.inv≫b=0 := finite_cell_shifted_hom_zero X Y hX q hq (m+1) w hw _
  exact (cancel_epi e.inv).mp (by simpa only [comp_zero] using hz)

/-- Inverse rotation places the unrestricted first vertex between two
actual finite endpoints. Exactness therefore kills the whole obstruction. -/
private theorem finite_endpoints_source_obstruction_zero
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hY : (∃ n : ℤ, Nonempty (T.Y.obj background.auxiliary≅Sphere (C:=Spectrum) n)) ∨
      (∃ n : ℤ, Nonempty (T.Y.obj background.auxiliary≅(ClassicalObject.nuCofiber.obj background.auxiliary)⟦n⟧)))
    (hZ : (∃ n : ℤ, Nonempty (T.Z.obj background.auxiliary≅Sphere (C:=Spectrum) n)) ∨
      (∃ n : ℤ, Nonempty (T.Z.obj background.auxiliary≅(ClassicalObject.nuCofiber.obj background.auxiliary)⟦n⟧)))
    (q : ℕ) (hq : 0<q)
    (b : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (normalizedTriangle background T he).obj₁)⟦(1:ℤ)⟧ ⟶
      XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) q) : b=0 := by
  letI := background.exactness.syntheticTriangulated
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  letI : F.Additive := background.exactness.shiftAdditive (0,-(q:ℤ))
  letI : F.CommShift ℤ := background.exactness.shiftCommShift (0,-(q:ℤ))
  letI : F.IsTriangulated := background.exactness.shiftExact (0,-(q:ℤ))
  let N := normalizedTriangle background T he
  let U := (F.mapTriangle.obj N.invRotate)⟦(1:ℤ)⟧
  have hU : U∈distTriang SyntheticSpectrum :=
    Triangle.shift_distinguished _ (F.map_distinguished _ (inv_rot_of_distTriang N hT)) 1
  let eA : U.obj₁≅F.obj N.obj₃ :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso ((F.commShiftIso (-1:ℤ)).app N.obj₃) ≪≫
      (shiftFunctorCompIsoId SyntheticSpectrum (-1:ℤ) 1 (by omega)).app _
  let eg : ℤ := normalizedExponent background.classicalTower T.g
  let eC : F.obj N.obj₃≅(SyntheticCategory.biShift (0,-eg-(q:ℤ))).obj
      (background.nu.functor.obj (T.Z.obj background.auxiliary)) :=
    (biShiftAddIso (0,-eg) (0,-(q:ℤ)) (0,-eg-(q:ℤ)) (by ext <;> simp [sub_eq_add_neg])).app _
  have heg : 0≤eg := by dsimp only [eg]; positivity
  exact nu_row_hom_middle_zero U hU _ (fun a => by
      have hz : (eA≪≫eC).inv≫a=0 :=
        finite_cell_shifted_hom_zero T.Z T.Y hZ q hq 0 (-eg-(q:ℤ)) (by omega) _
      exact (cancel_epi (eA≪≫eC).inv).mp (by simpa only [comp_zero] using hz))
    (fun c => finite_cell_shifted_suspension_hom_zero T.Y T.Y hY q hq 0 (-(q:ℤ)) (by omega) c) b

private theorem finite_endpoints_source_suspension_square
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hY : (∃ n : ℤ, Nonempty (T.Y.obj background.auxiliary≅Sphere (C:=Spectrum) n)) ∨
      (∃ n : ℤ, Nonempty (T.Y.obj background.auxiliary≅(ClassicalObject.nuCofiber.obj background.auxiliary)⟦n⟧)))
    (hZ : (∃ n : ℤ, Nonempty (T.Z.obj background.auxiliary≅Sphere (C:=Spectrum) n)) ∨
      (∃ n : ℤ, Nonempty (T.Z.obj background.auxiliary≅(ClassicalObject.nuCofiber.obj background.auxiliary)⟦n⟧)))
    (q : ℕ) (hq : 0<q)
    (eA : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) q≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ q)⟦(1:ℤ)⟧)
    (eB : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) q≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ q)⟦(1:ℤ)⟧)
    (heA : XModLambdaN.incl _ q≫eA.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q))
    (heB : XModLambdaN.incl _ q≫eB.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q)) :
    XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalizedTriangle background T he).mor₁) q≫eB.hom=
      eA.hom≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map (normalizedTriangle background T he).mor₁ q) := by
  letI := background.exactness.shiftCommShift (0,-(q:ℤ))
  let N := normalizedTriangle background T he
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let l := XModLambdaN.map (S.map N.mor₁) q≫eB.hom
  let r := eA.hom≫S.map (XModLambdaN.map N.mor₁ q)
  have hinc : XModLambdaN.incl _ q≫(l-r)=0 := by
    dsimp only [l,r]
    rw [Preadditive.comp_sub,←Category.assoc,←XModLambdaN.incl_naturality,
      Category.assoc,heB,←Functor.map_comp,XModLambdaN.incl_naturality,
      Functor.map_comp,←heA,Category.assoc,sub_self]
  obtain ⟨z,hz⟩ := (XModLambdaN.cofiberTriangle (N.obj₁⟦(1:ℤ)⟧) q).yoneda_exact₃
    (XModLambdaN.cofiberTriangle_distinguished _ _) (l-r) hinc
  let χ := S.mapIso ((F.commShiftIso (1:ℤ)).app N.obj₁)
  let ff := Functor.FullyFaithful.ofFullyFaithful S
  let z₀ := ff.preimage (χ.inv≫z)
  have hz₀ : z₀=0 := finite_endpoints_source_obstruction_zero T he hT hY hZ q hq z₀
  have hzmap : S.map z₀=χ.inv≫z := ff.map_preimage _
  have hz0 : z=0 := (cancel_epi χ.inv).mp (by rw [←hzmap,hz₀,S.map_zero]; simp)
  apply sub_eq_zero.mp
  change l-r=0
  rw [hz,hz0,comp_zero]

/-- The unrotated quotient row is distinguished under the displayed
finite-geometry hypotheses on its second and third classical vertices. -/
private theorem finite_endpoints_actual_unrotated_row
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hY : (∃ n : ℤ, Nonempty (T.Y.obj background.auxiliary≅Sphere (C:=Spectrum) n)) ∨
      (∃ n : ℤ, Nonempty (T.Y.obj background.auxiliary≅(ClassicalObject.nuCofiber.obj background.auxiliary)⟦n⟧)))
    (hZ : (∃ n : ℤ, Nonempty (T.Z.obj background.auxiliary≅Sphere (C:=Spectrum) n)) ∨
      (∃ n : ℤ, Nonempty (T.Z.obj background.auxiliary≅(ClassicalObject.nuCofiber.obj background.auxiliary)⟦n⟧)))
    (q : ℕ) (hq : 0<q) :
    ∃ eA : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) q≅
        (XModLambdaN (normalizedTriangle background T he).obj₁ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl _ q≫eA.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q) ∧
      Triangle.mk (XModLambdaN.map (normalizedTriangle background T he).mor₁ q)
        (XModLambdaN.map (normalizedTriangle background T he).mor₂ q)
        (XModLambdaN.map (normalizedTriangle background T he).mor₃ q≫eA.hom)∈distTriang SyntheticSpectrum := by
  obtain ⟨eB,heB,hrow⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row T he q hq
  obtain ⟨eA,heA⟩ := quotient_suspension_inclusion_exists (normalizedTriangle background T he).obj₁ q
  exact ⟨eA,heA,unrotated_row_of_selected_suspension_square _ q eA eB hrow
    (finite_endpoints_source_suspension_square T he hT hY hZ q hq eA eB heA heB)⟩

/-- The enlarged finite geometry condition preserves the selected maps,
the inclusion comparison, and the complete distinguished-row conclusion. -/
private theorem ordinary_source_actual_unrotated_row_of_finite_cover
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hcover : OrdinaryFiniteSourceCover T) (q : ℕ) (hq : 0<q) :
    ∃ eA : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) q≅
        (XModLambdaN (normalizedTriangle background T he).obj₁ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl _ q≫eA.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q) ∧
      Triangle.mk (XModLambdaN.map (normalizedTriangle background T he).mor₁ q)
        (XModLambdaN.map (normalizedTriangle background T he).mor₂ q)
        (XModLambdaN.map (normalizedTriangle background T he).mor₃ q≫eA.hom)∈distTriang SyntheticSpectrum := by
  rcases hcover with hX | ⟨hY,hZ⟩
  · exact finite_cell_source_actual_unrotated_row T he hT hX q hq
  · exact finite_endpoints_actual_unrotated_row T he hT hY hZ q hq

end
end KIP126.ProofTools.Internal.SyntheticCoverage
