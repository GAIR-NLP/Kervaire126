module

import all KIP126.ProofTools.MahowaldLeibniz.NativeImageSquare
import all KIP126.ProofTools.MahowaldLeibniz.OrdinaryImageSquare
import all KIP126.ProofTools.SyntheticCoverage.TerminalComparison

/-! Nonzero comparison of the raw and native image squares.
The positive comparison retains its sphere automorphism;
top-layer labels establish the required equality. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000

private theorem regrade_isIso {A : SyntheticSpectrum} {m m' w w' : ℤ}
    (hm : m=m') (hw : w=w') (a : BiHom m w A) [IsIso a] :
    IsIso (homotopyRegrade hm hw a) := by
  subst m'; subst w'
  change IsIso a
  infer_instance

private theorem shift_identity_isIso (δ p : ℤ×ℤ) :
    IsIso (shiftHomotopyClass (Syn:=SyntheticSpectrum) δ p (𝟙 (Smn p.1 p.2))) := by
  dsimp only [shiftHomotopyClass]
  erw [CategoryTheory.Functor.map_id,Category.comp_id]
  exact inferInstanceAs (IsIso ((SyntheticCategory.biShift_comp (Syn:=SyntheticSpectrum) p δ).app S_0_0).inv)

private def ordinarySphereIso (m w : ℤ) :
    Smn (Syn:=SyntheticSpectrum) m w ≅ (Smn (m-1) w)⟦(1:ℤ)⟧ := by
  letI := shift_identity_isIso (1,0) (m-1,w)
  letI := regrade_isIso (show ((m-1,w)+(1,0)).1=m by dsimp; omega)
    (show ((m-1,w)+(1,0)).2=w by dsimp; simp)
    (shiftHomotopyClass (1,0) (m-1,w) (𝟙 (Smn (Syn:=SyntheticSpectrum) (m-1) w)))
  let a := ordinarySuspendedRepresentative (Smn (m-1) w) m w (𝟙 _)
  letI : IsIso a := by
    dsimp only [a,ordinarySuspendedRepresentative]
    infer_instance
  exact asIso a

private theorem ordinary_suspended_eq_source_iso (A : SyntheticSpectrum) (m w : ℤ)
    (a : BiHom (m-1) w A) :
    ordinarySuspendedRepresentative A m w a =
      (ordinarySphereIso m w).hom ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map a := by
  exact (by simpa only [ordinarySphereIso,asIso_hom,Category.id_comp] using
    ordinarySuspendedRepresentative_natural a m w (𝟙 _))

/-- The change between sphere suspension conventions acts by the specified
source automorphism. -/
private theorem positive_suspended_image_up_to_sphere
    (X Y : (AdamsObject (coefficients := background.coefficients))) (q : ℕ) (hq : 0<q)
    (f : (SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
        background.nu.functor.obj (Y.obj background.auxiliary))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (εp : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (hε : XModLambdaN.incl _ q ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q))
    (hεp : XModLambdaN.incl _ q ≫ εp.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ q))
    (ey : XModLambdaN ((background.nu.functor.obj (Y.obj background.auxiliary))⟦(1:ℤ)⟧) q ≅
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ q ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q))
    (m w : ℤ)
    (a : BiHom (m+1) (w+1) (XModLambdaN
      (((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary)))⟦(1:ℤ)⟧) q))
    (a₀ : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : shiftHomotopyClass (1,1) (m,w) a₀ =
      a ≫ XModLambdaN.map (positiveOrdinaryIso.hom.app _) q ≫ ε.hom) :
    ∃ u : Smn (Syn:=SyntheticSpectrum) (m+1) (w+1) ≅ Smn (m+1) (w+1),
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map f) q ≫ ey.hom =
      u.hom ≫ ordinarySuspendedRepresentative _ (m+1) (w+1)
        (homotopyRegrade (show m=(m+1)-1 by omega) rfl
          (homotopyRegrade (m':=m) (w':=w+1) (by dsimp; omega) rfl
            (shiftHomotopyClass (0,1) (m,w) a₀) ≫ εp.inv ≫ XModLambdaN.map f q)) := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  let ex := positiveOrdinaryQuotientIso X q ε εp
  have hmap := finite_suspension_normalized_map_on_spheres X Y 1 (by decide) q hq f
    ex ey (positiveOrdinaryQuotientIso_incl X q ε εp hε hεp) hey (m+1) (w+1) a
  let S := Smn (Syn:=SyntheticSpectrum) m w
  let D := shiftFunctor SyntheticSpectrum (1:ℤ)
  let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,1)
  let c : Smn (m+1) (w+1) ⟶ D.obj (G.obj S) :=
    shiftHomotopyClass (1,1) (m,w) (𝟙 S) ≫ positiveOrdinaryIso.inv.app S
  let b : Smn ((m+1)-1) (w+1) ⟶ G.obj S :=
    homotopyRegrade (show m=(m+1)-1 by omega) rfl
      (homotopyRegrade (m':=m) (w':=w+1) (by dsimp; omega) rfl
        (shiftHomotopyClass (0,1) (m,w) (𝟙 S)))
  letI := shift_identity_isIso (1,1) (m,w)
  letI : IsIso c := by dsimp only [c]; infer_instance
  letI := shift_identity_isIso (0,1) (m,w)
  letI : IsIso b := by
    dsimp only [b]
    letI := regrade_isIso (show ((m,w)+(0,1)).1=m by dsimp; omega) rfl
      (shiftHomotopyClass (0,1) (m,w) (𝟙 S))
    exact regrade_isIso (show m=(m+1)-1 by omega) rfl _
  let C := asIso c
  let B := ordinarySphereIso (m+1) (w+1) ≪≫ D.mapIso (asIso b)
  let k := G.map a₀ ≫ εp.inv ≫ XModLambdaN.map f q
  refine ⟨C ≪≫ B.symm,?_⟩
  have hraw : a ≫ XModLambdaN.map (D.map f) q ≫ ey.hom = c ≫ D.map k := by
    rw [hmap]
    dsimp only [ex,positiveOrdinaryQuotientIso,Iso.trans_hom,Functor.mapIso_hom,
      Iso.symm_hom,Iso.app_hom,Iso.app_inv]
    simp only [Category.assoc]
    change a ≫ XModLambdaN.map (positiveOrdinaryIso.hom.app A) q ≫ ε.hom ≫
      positiveOrdinaryIso.inv.app (XModLambdaN A q) ≫ D.map εp.inv ≫ D.map (XModLambdaN.map f q) = _
    have ht := congrArg (fun z => z ≫ positiveOrdinaryIso.inv.app (XModLambdaN A q) ≫
      D.map εp.inv ≫ D.map (XModLambdaN.map f q)) ha
    rw [show a ≫ XModLambdaN.map (positiveOrdinaryIso.hom.app A) q ≫ ε.hom ≫
      positiveOrdinaryIso.inv.app (XModLambdaN A q) ≫ D.map εp.inv ≫ D.map (XModLambdaN.map f q) =
      shiftHomotopyClass (1,1) (m,w) a₀ ≫ positiveOrdinaryIso.inv.app (XModLambdaN A q) ≫
        D.map εp.inv ≫ D.map (XModLambdaN.map f q) from by
          simpa only [Category.assoc] using ht.symm]
    dsimp only [c,k,shiftHomotopyClass]
    rw [Category.assoc,positiveOrdinaryIso.inv.naturality_assoc]
    simp only [Functor.comp_map,Functor.map_comp,Category.assoc]
    erw [CategoryTheory.Functor.map_id,Category.id_comp]
    rfl
  have hb : homotopyRegrade (show m=(m+1)-1 by omega) rfl
      (homotopyRegrade (m':=m) (w':=w+1) (by dsimp; omega) rfl
        (shiftHomotopyClass (0,1) (m,w) a₀) ≫ εp.inv ≫ XModLambdaN.map f q) = b ≫ k := by
    simp only [b,k,G,S,shiftHomotopyClass,regrade_comp,Category.assoc]
    erw [CategoryTheory.Functor.map_id,Category.id_comp]
  rw [hraw,hb,ordinary_suspended_eq_source_iso]
  simp only [Functor.map_comp]
  have hB : B.hom = (ordinarySphereIso (m+1) (w+1)).hom ≫ D.map b := rfl
  simp only [Iso.trans_hom,Iso.symm_hom]
  rw [←Category.assoc (ordinarySphereIso (m+1) (w+1)).hom,←hB]
  simp only [C,asIso_hom,Category.assoc,Iso.inv_hom_id_assoc]
  rfl

private theorem sphere_fixed_regrade {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (a : BiHom m w A)
    (ha : ∀ u : Smn (Syn:=SyntheticSpectrum) m w ≅ Smn m w, u.hom ≫ a=a)
    (u : Smn (Syn:=SyntheticSpectrum) m' w' ≅ Smn m' w') :
    u.hom ≫ homotopyRegrade hm hw a = homotopyRegrade hm hw a := by
  subst m'; subst w'; exact ha u

private theorem ordinary_suspension_sphere_fixed (A : SyntheticSpectrum) (m w : ℤ)
    (a : BiHom (m-1) w A)
    (ha : ∀ u : Smn (Syn:=SyntheticSpectrum) (m-1) w ≅ Smn (m-1) w, u.hom ≫ a=a)
    (u : Smn (Syn:=SyntheticSpectrum) m w ≅ Smn m w) :
    u.hom ≫ ordinarySuspendedRepresentative A m w a =
      ordinarySuspendedRepresentative A m w a := by
  let D := shiftFunctor SyntheticSpectrum (1:ℤ)
  let C := ordinarySphereIso m w
  let ff := Functor.FullyFaithful.ofFullyFaithful D
  let v := ff.preimageIso (C.symm ≪≫ u ≪≫ C)
  have hv : D.map v.hom = C.inv ≫ u.hom ≫ C.hom := ff.map_preimage _
  have h := congrArg D.map (ha v)
  rw [Functor.map_comp,hv] at h
  have h' := congrArg (fun z => C.hom ≫ z) h
  simpa only [ordinary_suspended_eq_source_iso,C,Category.assoc,Iso.hom_inv_id_assoc] using h'

private theorem native_positive_image_up_to_sphere
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (N c : ℕ) (hN : 0<N) (S V : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (εp : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ N))
    (hεp : XModLambdaN.incl _ N ≫ εp.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ N))
    (ey : XModLambdaN ((background.nu.functor.obj (T.Y.obj background.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N)⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ N ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N))
    : ∃ u : Smn (Syn:=SyntheticSpectrum) (V-S+1) (V-c+1) ≅ Smn (V-S+1) (V-c+1),
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) N ≫ ey.hom =
      u.hom ≫ ordinarySuspendedRepresentative _ (V-S+1) (V-c+1)
        (homotopyRegrade (show V-S=(V-S+1)-1 by omega) rfl
          (positiveFiniteImage T hf N εp (V-S) (V-c)
            (rawMaySourceDesuspend T he hf N c S V ε a))) := by
  let a' := a ≫ XModLambdaN.map
    ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalizedPositiveSourceIso T hf).hom) N
  let a₀ := rawMaySourceDesuspend T he hf N c S V ε a
  have hrestore := shift_quotient_unshift T.X (1,1) (V-S,V-c) N ε
    (homotopyRegrade rfl rfl
      (a ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N ≫
        XModLambdaN.map (background.nu.suspensionIso (T.X.obj background.auxiliary)).hom N))
  have hrestore' := congrArg (fun b => b ≫ ε.hom) hrestore
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id] at hrestore'
  have hsource : shiftHomotopyClass (1,1) (V-S,V-c) a₀ =
      a' ≫ XModLambdaN.map (positiveOrdinaryIso.hom.app _) N ≫ ε.hom := by
    have hc : XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedPositiveSourceIso T hf).hom) N ≫
        XModLambdaN.map (positiveOrdinaryIso.hom.app _) N =
      XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N ≫
        XModLambdaN.map (background.nu.suspensionIso (T.X.obj background.auxiliary)).hom N := by
      rw [←background.quotients.functoriality.map_comp,
        normalizedPositiveSourceIso_suspension T he hf,
        background.quotients.functoriality.map_comp]
    have hc' := congrArg (fun z => a ≫ z ≫ ε.hom) hc
    calc
      _ = a ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N ≫
          XModLambdaN.map (background.nu.suspensionIso (T.X.obj background.auxiliary)).hom N ≫ ε.hom := by
            simpa only [a₀,rawMaySourceDesuspend,homotopyRegrade,Category.assoc] using hrestore'
      _ = _ := by simpa only [a',Category.assoc] using hc'.symm
  obtain ⟨u,hu⟩ := positive_suspended_image_up_to_sphere T.X T.Y N hN
    (lastLayerNormalizedMap T hf) ε εp hε hεp ey hey (V-S) (V-c) a' a₀ hsource
  refine ⟨u,?_⟩
  dsimp only [a'] at hu
  rw [Category.assoc,←Category.assoc (XModLambdaN.map _ N),
    ←background.quotients.functoriality.map_comp,←Functor.map_comp,
    normalizedPositiveSourceIso_map T hf] at hu
  simpa only [positiveFiniteImage,a₀,normalizedTriangle,Triangle.mk_mor₁,Category.assoc] using hu

private theorem shifted_representative_is_ordinary (A : SyntheticSpectrum)
    (m n w : ℤ) (hm : m=n-1) (a : BiHom m w A) :
    homotopyRegrade (show ((m,w)+(1,0)).1=n by dsimp; omega)
      (show ((m,w)+(1,0)).2=w by dsimp; simp)
      (shiftHomotopyClass (1,0) (m,w) a) ≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app A =
      ordinarySuspendedRepresentative A n w (homotopyRegrade hm rfl a) := by
  subst m
  rfl

/-- For an ordinary first arrow, the exact raw image is the ordinary
suspension of the image of its specified native desuspension. -/
private theorem native_ordinary_image_eq_raw_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (N c : ℕ) (hN : 0<N) (s t : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ N))
    (ey : XModLambdaN ((background.nu.functor.obj (T.Y.obj background.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N)⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ N ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (a : BiHom (t-s) (t-c)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N)) :
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N ≫ ey.hom =
      ordinarySuspendedRepresentative _ (t-s) (t-c)
        (homotopyRegrade (show t-(s+1)=(t-s)-1 by omega) rfl
          (positiveHSourceDesuspend T he hf N c s t ε a ≫
            XModLambdaN.map (background.nu.functor.map T.f) N)) := by
  let Yν := background.nu.functor.obj (T.Y.obj background.auxiliary)
  let D := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,0)
  let C := SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1
  let εY : XModLambdaN (D.obj Yν) N ≅ D.obj (XModLambdaN Yν N) :=
    (background.quotients.functoriality.functor N).mapIso (C.app Yν) ≪≫ ey ≪≫ (C.app _).symm
  have hεY : XModLambdaN.incl _ N ≫ εY.hom = D.map (XModLambdaN.incl _ N) := by
    change XModLambdaN.incl _ N ≫ XModLambdaN.map (C.hom.app Yν) N ≫ ey.hom ≫ C.inv.app _ = _
    rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,
      ←Category.assoc _ ey.hom,hey,←C.hom.naturality_assoc,
      Iso.hom_inv_id_app,Category.comp_id]
  let a₀ := positiveHSourceDesuspend T he hf N c s t ε a
  let a' := homotopyRegrade (m':=((t-(s+1),t-c)+(1,0)).1)
    (w':=((t-(s+1),t-c)+(1,0)).2) (by dsimp; omega) (by dsimp; omega)
      (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom N)
  have hrestore : shiftHomotopyClass (1,0) (t-(s+1),t-c) a₀ = a' ≫ ε.hom := by
    have h := congrArg (fun u => u ≫ ε.hom)
      (shift_quotient_unshift T.X (1,0) (t-(s+1),t-c) N ε a')
    simpa only [a₀,positiveHSourceDesuspend,a',Category.assoc,Iso.inv_hom_id,
      Category.comp_id] using h
  have hs := shifted_ordinary_quotient_map_on_spheres T.X T.Y T.f N hN (1,0)
    ε εY hε hεY _ _ a'
  have hs' := congrArg (fun z => z ≫ C.hom.app (XModLambdaN Yν N)) hs
  simp only [Category.assoc] at hs'
  have hεYC : εY.hom ≫ C.hom.app (XModLambdaN Yν N) =
      XModLambdaN.map (C.hom.app Yν) N ≫ ey.hom := by
    dsimp only [εY,Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom,Iso.app_hom,Iso.app_inv]
    simp only [Yν,Category.assoc,Iso.inv_hom_id_app,Category.comp_id]
    rfl
  rw [hεYC] at hs'
  rw [←Category.assoc a' ε.hom,hrestore.symm] at hs'
  have hshift : shiftHomotopyClass (1,0) (t-(s+1),t-c) a₀ ≫
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.map (background.nu.functor.map T.f) N) =
      shiftHomotopyClass (1,0) (t-(s+1),t-c)
        (a₀ ≫ XModLambdaN.map (background.nu.functor.map T.f) N) := by
    simp only [shiftHomotopyClass,Functor.map_comp,Category.assoc]
  rw [←Category.assoc (shiftHomotopyClass (1,0) (t-(s+1),t-c) a₀),hshift] at hs'
  have hh := congrArg (homotopyRegrade
    (show ((t-(s+1),t-c)+(1,0)).1=t-s by dsimp; omega)
    (show ((t-(s+1),t-c)+(1,0)).2=t-c by dsimp; omega)) hs'
  simp only [a',regrade_comp,last_layer_regrade_trans] at hh
  rw [normalized_first_suspension_zero T he hf,
    background.quotients.functoriality.map_comp,background.quotients.functoriality.map_comp]
  have hpres : homotopyRegrade
      (show ((t-(s+1),t-c)+(1,0)).1=t-s by dsimp; omega)
      (show ((t-(s+1),t-c)+(1,0)).2=t-c by dsimp; omega)
      (shiftHomotopyClass (1,0) (t-(s+1),t-c)
        (a₀ ≫ XModLambdaN.map (background.nu.functor.map T.f) N)) ≫ C.hom.app _ =
      ordinarySuspendedRepresentative _ (t-s) (t-c)
        (homotopyRegrade (show t-(s+1)=(t-s)-1 by omega) rfl
          (a₀ ≫ XModLambdaN.map (background.nu.functor.map T.f) N)) := by
    exact shifted_representative_is_ordinary _ (t-(s+1)) (t-s) (t-c) (by omega) _
  rw [hpres] at hh
  simpa only [a₀,C,Yν,homotopyRegrade,Category.assoc] using hh

/-- The explicit suspension defect vanishes on a specified highest-layer label. -/
private theorem native_positive_image_eq_finite_may_top
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (c q : ℕ) (hq : 0<q) (S V : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (εp : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (hε : XModLambdaN.incl _ (c+(q+1)) ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (c+(q+1))))
    (hεp : XModLambdaN.incl _ (c+(q+1)) ≫ εp.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (c+(q+1))))
    (ey : XModLambdaN ((background.nu.functor.obj (T.Y.obj background.auxiliary))⟦(1:ℤ)⟧) (c+(q+1)) ≅
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) (c+(q+1)))⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ (c+(q+1)) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (c+(q+1))))
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+(q+1))))
    (error : Ambient background T.Y (S+q+1,(V+1)+q))
    (himage : homotopyRegrade (show V-S=((V+1)-S)-1 by omega)
      (show (V-c)+1=(V+1)-c by omega)
      (positiveFiniteImage T hf (c+(q+1)) εp (V-S) (V-c)
        (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε a)) =
      finiteMayTopLabel T.Y c q hq S (V+1) error) :
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) (c+(q+1)) ≫ ey.hom =
      ordinarySuspendedRepresentative _ (V-S+1) (V-c+1)
        (homotopyRegrade (show ((V+1)-S)-1=(V-S+1)-1 by omega)
          (show (V+1)-c=V-c+1 by omega)
          (finiteMayTopLabel T.Y c q hq S (V+1) error)) := by
  obtain ⟨u,hu⟩ := native_positive_image_up_to_sphere T he hf (c+(q+1)) c
    (by omega) S V ε εp hε hεp ey hey a
  have hlabel := congrArg
    (homotopyRegrade (show ((V+1)-S)-1=(V-S+1)-1 by omega)
      (show (V+1)-c=V-c+1 by omega)) himage
  simp only [last_layer_regrade_trans] at hlabel
  rw [hlabel] at hu
  exact hu.trans (ordinary_suspension_sphere_fixed _ (V-S+1) (V-c+1) _
    (sphere_fixed_regrade _ _ _
      (finite_may_top_label_sphere_automorphism T.Y c q hq S (V+1) error)) u)

end
end KIP126.ProofTools.Internal.SyntheticCoverage
