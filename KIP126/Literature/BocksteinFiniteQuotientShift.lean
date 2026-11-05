module
import all KIP126.Literature.BocksteinLambdaTower

/-! Private coordinate changes for the same finite lambda quotient triangles. -/
@[expose] section
namespace KIP126.Literature.BocksteinRaw
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Core.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]

private def biShiftSwapIso (a b : ℤ × ℤ) (X : Syn) :
    (SyntheticCategory.biShift b).obj ((SyntheticCategory.biShift a).obj X) ≅
      (SyntheticCategory.biShift a).obj ((SyntheticCategory.biShift b).obj X) :=
  (biShiftAddIso a b (a+b) rfl).app X ≪≫
    ((biShiftAddIso b a (a+b) (add_comm _ _)).symm.app X)

private theorem biShiftSwapIso_eq (a b c : ℤ × ℤ) (h : a+b=c) (X : Syn) :
    biShiftSwapIso a b X =
      (biShiftAddIso a b c h).app X ≪≫
        ((biShiftAddIso b a c (by rw [add_comm]; exact h)).symm.app X) := by
  subst c
  rfl

private theorem biShiftSwap_hexagon (coh : BiShiftCoherence Syn)
    (a b c d : ℤ × ℤ) (h : b+c=d) (X : Syn) :
    (biShiftAddIso b c d h).hom.app ((SyntheticCategory.biShift a).obj X) ≫
      (biShiftSwapIso a d X).hom =
    (SyntheticCategory.biShift c).map (biShiftSwapIso a b X).hom ≫
      (biShiftSwapIso a c ((SyntheticCategory.biShift b).obj X)).hom ≫
      (SyntheticCategory.biShift a).map ((biShiftAddIso b c d h).hom.app X) := by
  have htotal : (a+b)+c=a+d := by rw [← h, add_assoc]
  have htotal' : b+(a+c)=a+d := by rw [← h]; abel
  have h1 := coh.associativity a b c (a+b) d (a+d) rfl h htotal rfl X
  have h2 := coh.associativity b a c (a+b) (a+c) (a+d)
    (add_comm _ _) rfl htotal htotal' X
  have h3 := coh.associativity b c a d (a+c) (a+d)
    h (add_comm _ _) (add_comm _ _) htotal' X
  apply (cancel_mono ((biShiftAddIso d a (a+d) (add_comm _ _)).hom.app X)).mp
  simp only [biShiftSwapIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [Iso.inv_hom_id_app, Category.comp_id]
  rw [h3]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← h2]
  rw [← Category.assoc ((SyntheticCategory.biShift c).map
    ((biShiftAddIso b a (a+b) (add_comm _ _)).inv.app X)),
    ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  exact h1.symm

private theorem biShiftSwap_naturality (a b : ℤ × ℤ) {X Y : Syn} (f : X ⟶ Y) :
    (SyntheticCategory.biShift b).map ((SyntheticCategory.biShift a).map f) ≫
        (biShiftSwapIso a b Y).hom =
      (biShiftSwapIso a b X).hom ≫
        (SyntheticCategory.biShift a).map ((SyntheticCategory.biShift b).map f) := by
  simpa only [biShiftSwapIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.comp_map] using
    ((biShiftAddIso a b (a+b) rfl).hom ≫
      (biShiftAddIso b a (a+b) (add_comm _ _)).inv).naturality f

private def lambdaFiniteShiftSourceIso (a : ℤ × ℤ) (n : ℕ) (X : Syn) :
    (SyntheticCategory.biShift (lambdaDegree n)).obj ((SyntheticCategory.biShift a).obj X) ≅
      (SyntheticCategory.biShift a).obj ((SyntheticCategory.biShift (lambdaDegree n)).obj X) :=
  biShiftSwapIso a (lambdaDegree n) X

private theorem lambdaPow_shift (coh : BiShiftCoherence Syn)
    (a : ℤ × ℤ) (n : ℕ) (X : Syn) :
    lambdaPow n ((SyntheticCategory.biShift a).obj X) =
      (lambdaFiniteShiftSourceIso a n X).hom ≫
        (SyntheticCategory.biShift a).map (lambdaPow n X) := by
  change lambdaPow n ((SyntheticCategory.biShift a).obj X) =
    (biShiftSwapIso a (lambdaDegree n) X).hom ≫
      (SyntheticCategory.biShift a).map (lambdaPow n X)
  induction n with
  | zero =>
    change SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj X) =
      (biShiftSwapIso a 0 X).hom ≫
        (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app X)
    rw [biShiftSwapIso_eq a 0 a (add_zero a)]
    simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Category.assoc]
    rw [← coh.left_unit a X, Iso.inv_hom_id_app, Category.comp_id]
    exact (coh.right_unit a X).symm
  | succ n ih =>
    apply (cancel_epi ((lambdaShiftAddIso 1 n (n+1) (by omega)).hom.app
      ((SyntheticCategory.biShift a).obj X))).mp
    rw [lambdaPow_succ_comparison]
    have hcomm : SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj X) =
        (biShiftSwapIso a (lambdaDegree 1) X).hom ≫
          (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app X) := by
      simpa [biShiftSwapIso, Category.assoc, lambdaDegree] using coh.lambda_comm a X
    rw [hcomm, Functor.map_comp, ih]
    simp only [Category.assoc]
    rw [← Category.assoc ((SyntheticCategory.biShift (lambdaDegree n)).map
      ((SyntheticCategory.biShift a).map (SyntheticCategory.lam.app X)))]
    have hnat := biShiftSwap_naturality a (lambdaDegree n) (SyntheticCategory.lam.app X)
    dsimp only [Functor.id_obj] at hnat
    erw [hnat]
    simp only [Category.assoc]
    have hhex := biShiftSwap_hexagon coh a (lambdaDegree 1) (lambdaDegree n)
      (lambdaDegree (n+1)) (by ext <;> simp [lambdaDegree]) X
    change (SyntheticCategory.biShift (lambdaDegree n)).map
        (biShiftSwapIso a (lambdaDegree 1) X).hom ≫
      (biShiftSwapIso a (lambdaDegree n)
        ((SyntheticCategory.biShift (lambdaDegree 1)).obj X)).hom ≫
      (SyntheticCategory.biShift a).map
        ((SyntheticCategory.biShift (lambdaDegree n)).map (SyntheticCategory.lam.app X)) ≫
      (SyntheticCategory.biShift a).map (lambdaPow n X) = _
    rw [← Functor.map_comp, ← lambdaPow_succ_comparison, Functor.map_comp]
    simpa only [lambdaShiftAddIso, Category.assoc] using
      congrArg (fun f => f ≫ (SyntheticCategory.biShift a).map (lambdaPow (n+1) X))
        hhex.symm


variable [HasFunctorialCofiber (C := Syn)]

private def lambdaFiniteShiftTriangleIso (coh : BiShiftCoherence Syn)
    (a : ℤ × ℤ) (n : ℕ) (X : Syn)
    [(SyntheticCategory.biShift (Syn := Syn) a).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) a).IsTriangulated] :
    XModLambdaN.cofiberTriangle ((SyntheticCategory.biShift a).obj X) n ≅
      (SyntheticCategory.biShift a).mapTriangle.obj (XModLambdaN.cofiberTriangle X n) := by
  let F := SyntheticCategory.biShift (Syn := Syn) a
  refine isoTriangleOfIso₁₂ _ _
    (XModLambdaN.cofiberTriangle_distinguished _ n)
    (F.map_distinguished _ (XModLambdaN.cofiberTriangle_distinguished X n))
    (lambdaFiniteShiftSourceIso a n X) (Iso.refl _) ?_
  change lambdaPow n (F.obj X) ≫ 𝟙 _ =
    (lambdaFiniteShiftSourceIso a n X).hom ≫ F.map (lambdaPow n X)
  rw [Category.comp_id]
  exact lambdaPow_shift coh a n X

private def lambdaFiniteShiftIso (coh : BiShiftCoherence Syn)
    (a : ℤ × ℤ) (n : ℕ) (X : Syn)
    [(SyntheticCategory.biShift (Syn := Syn) a).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) a).IsTriangulated] :
    XModLambdaN ((SyntheticCategory.biShift a).obj X) n ≅
      (SyntheticCategory.biShift a).obj (XModLambdaN X n) :=
  Triangle.π₃.mapIso (lambdaFiniteShiftTriangleIso coh a n X)

private theorem lambdaFiniteShiftIso_incl (coh : BiShiftCoherence Syn)
    (a : ℤ × ℤ) (n : ℕ) (X : Syn)
    [(SyntheticCategory.biShift (Syn := Syn) a).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) a).IsTriangulated] :
    XModLambdaN.incl ((SyntheticCategory.biShift a).obj X) n ≫
        (lambdaFiniteShiftIso coh a n X).hom =
      (SyntheticCategory.biShift a).map (XModLambdaN.incl X n) := by
  have h := (lambdaFiniteShiftTriangleIso coh a n X).hom.comm₂
  change XModLambdaN.incl ((SyntheticCategory.biShift a).obj X) n ≫
    (lambdaFiniteShiftIso coh a n X).hom =
      (lambdaFiniteShiftTriangleIso coh a n X).hom.hom₂ ≫
        (SyntheticCategory.biShift a).map (XModLambdaN.incl X n) at h
  have h2 : (lambdaFiniteShiftTriangleIso coh a n X).hom.hom₂ = 𝟙 _ := by
    simp [lambdaFiniteShiftTriangleIso]
  rw [h2, Category.id_comp] at h
  exact h

private theorem lambdaFiniteShiftIso_proj (coh : BiShiftCoherence Syn)
    (a : ℤ × ℤ) (n : ℕ) (X : Syn)
    [(SyntheticCategory.biShift (Syn := Syn) a).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) a).IsTriangulated] :
    XModLambdaN.proj ((SyntheticCategory.biShift a).obj X) n ≫
        (shiftFunctor Syn (1 : ℤ)).map (lambdaFiniteShiftSourceIso a n X).hom =
      (lambdaFiniteShiftIso coh a n X).hom ≫
        (SyntheticCategory.biShift a).map (XModLambdaN.proj X n) ≫
        ((SyntheticCategory.biShift a).commShiftIso (1 : ℤ)).hom.app
          ((SyntheticCategory.biShift (lambdaDegree n)).obj X) := by
  have h := (lambdaFiniteShiftTriangleIso coh a n X).hom.comm₃
  change XModLambdaN.proj ((SyntheticCategory.biShift a).obj X) n ≫
      (shiftFunctor Syn (1 : ℤ)).map ((lambdaFiniteShiftTriangleIso coh a n X).hom.hom₁) =
    (lambdaFiniteShiftIso coh a n X).hom ≫
      (SyntheticCategory.biShift a).map (XModLambdaN.proj X n) ≫
      ((SyntheticCategory.biShift a).commShiftIso (1 : ℤ)).hom.app
        ((SyntheticCategory.biShift (lambdaDegree n)).obj X) at h
  have h1 : (lambdaFiniteShiftTriangleIso coh a n X).hom.hom₁ =
      (lambdaFiniteShiftSourceIso a n X).hom := by
    simp [lambdaFiniteShiftTriangleIso]
  rw [h1] at h
  exact h

private theorem lambdaFiniteShiftIso_one (coh : BiShiftCoherence Syn)
    (a : ℤ × ℤ) (X : Syn)
    [(SyntheticCategory.biShift (Syn := Syn) a).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) a).IsTriangulated] :
    lambdaFiniteShiftIso coh a 1 X = lambdaOneShiftIso coh a X := by
  rfl

end
end KIP126.Literature.BocksteinRaw
end
