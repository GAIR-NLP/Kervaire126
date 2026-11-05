module

import all KIP126.ProofTools.SyntheticCoverage.OrdinaryPositiveHTerminal

import all KIP126.ProofTools.SyntheticCoverage.CommonLift
import all KIP126.ProofTools.SyntheticCoverage.HigherEarlyComparison
import all KIP126.ProofTools.SyntheticCoverage.OrdinaryEarlyInput

/-! Internal comparisons for an actual ordinary early root. These helpers
retain the specified finite representatives and selected quotient maps.
The positive-H construction derives the compatible root from the original
middle-cycle and whole-image hypotheses. Its actual early representative
is an input, supplied separately in the finite-source cases. -/
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

private def ordinaryQuotientShiftComparison (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ)
    (e : XModLambdaN ((background.nu.functor.obj (X.obj background.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)⟦(1:ℤ)⟧) :
    XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N) :=
  (background.quotients.functoriality.functor N).mapIso
    ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).app _) ≪≫
      e ≪≫ ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).app _).symm

private theorem ordinary_quotient_shift_comparison_incl (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ)
    (e : XModLambdaN ((background.nu.functor.obj (X.obj background.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)⟦(1:ℤ)⟧)
    (he : XModLambdaN.incl _ N≫e.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (XModLambdaN.incl _ N)) :
    XModLambdaN.incl _ N≫(ordinaryQuotientShiftComparison X N e).hom=
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ N) := by
  let C := SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1
  change XModLambdaN.incl _ N≫XModLambdaN.map (C.hom.app _) N≫e.hom≫C.inv.app _ = _
  rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,
    ←Category.assoc _ e.hom,he,←C.hom.naturality_assoc,
    Iso.hom_inv_id_app,Category.comp_id]

private def ordinarySuspensionEquiv (A : SyntheticSpectrum) (m w : ℤ) :
    BiHom (m-1) w A ≃+ BiHom m w (A⟦(1:ℤ)⟧) :=
  (suspInvarianceAddEquiv (m-1) w 1 0 A).trans
    ((regradeAddEquiv (by omega) (by omega)).trans
      (homPostcompAddEquiv ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).app A)))

private theorem ordinary_suspension_equiv_apply (A : SyntheticSpectrum) (m w : ℤ)
    (a : BiHom (m-1) w A) :
    ordinarySuspensionEquiv A m w a=ordinarySuspendedRepresentative A m w a := by
  simp [ordinarySuspensionEquiv,suspInvarianceAddEquiv,homPostcompAddEquiv,
    regradeAddEquiv,ordinarySuspendedRepresentative,susp_invariance,
    shiftHomotopyClass,Iso.homCongr]

/-- The selected suspension comparisons commute with restriction
on every sphere representative. -/
private theorem ordinary_quotient_suspension_restriction
    (X : (AdamsObject (coefficients := background.coefficients))) (i N : ℕ) (hi : 0 < i) (hiN : i ≤ N)
    (ei : XModLambdaN ((background.nu.functor.obj (X.obj background.auxiliary))⟦(1:ℤ)⟧) i ≅
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) i)⟦(1:ℤ)⟧)
    (eN : XModLambdaN ((background.nu.functor.obj (X.obj background.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)⟦(1:ℤ)⟧)
    (hei : XModLambdaN.incl _ i≫ei.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ i))
    (heN : XModLambdaN.incl _ N≫eN.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (m w : ℤ) (a : BiHom m w (XModLambdaN ((background.nu.functor.obj (X.obj background.auxiliary))⟦(1:ℤ)⟧) N)) :
    a≫(background.quotients.tower _).rho i N hiN≫ei.hom=
      a≫eN.hom≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map ((background.quotients.tower _).rho i N hiN) := by
  let C := SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1
  let b := a≫XModLambdaN.map (C.inv.app _) N
  have h := quotient_shift_restriction_on_spheres X (1,0) i N hi hiN
    (ordinaryQuotientShiftComparison X i ei) (ordinaryQuotientShiftComparison X N eN)
    (ordinary_quotient_shift_comparison_incl X i ei hei)
    (ordinary_quotient_shift_comparison_incl X N eN heN) m w b
  have h' := congrArg (fun z => z≫C.hom.app _) h
  simp only [ordinaryQuotientShiftComparison,Iso.trans_hom,Functor.mapIso_hom,
    Iso.symm_hom,Iso.app_inv,Category.assoc] at h'
  change b≫(background.quotients.tower _).rho i N hiN≫XModLambdaN.map (C.hom.app _) i≫ei.hom≫C.inv.app _≫C.hom.app _ =
    b≫XModLambdaN.map (C.hom.app _) N≫eN.hom≫C.inv.app _≫
      (SyntheticCategory.biShift (1,0)).map ((background.quotients.tower _).rho i N hiN)≫C.hom.app _ at h'
  rw [C.hom.naturality] at h'
  simp only [Iso.inv_hom_id_app_assoc,Iso.inv_hom_id_app,
    Category.comp_id] at h'
  rw [←Category.assoc ((background.quotients.tower _).rho i N hiN),
    (background.quotients.natural (C.hom.app _)).rho_naturality hiN] at h'
  have hb : b≫XModLambdaN.map (C.hom.app _) N=a := by
    dsimp only [b]
    rw [Category.assoc,←background.quotients.functoriality.map_comp,
      Iso.inv_hom_id_app,background.quotients.functoriality.map_id,Category.comp_id]
  simpa only [←Category.assoc,hb] using h'


/-- Naturality for a classical ordinary arrow on the specified finite sphere
representative. Both suspension comparisons preserve the chosen inclusion. -/
private theorem ordinary_quotient_suspension_map
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (N : ℕ) (hN : 0 < N)
    (eX : XModLambdaN ((background.nu.functor.obj (X.obj background.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)⟦(1:ℤ)⟧)
    (eY : XModLambdaN ((background.nu.functor.obj (Y.obj background.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N)⟦(1:ℤ)⟧)
    (heX : XModLambdaN.incl _ N≫eX.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (heY : XModLambdaN.incl _ N≫eY.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (m w : ℤ) (a : BiHom m w (XModLambdaN ((background.nu.functor.obj (X.obj background.auxiliary))⟦(1:ℤ)⟧) N)) :
    a≫XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (background.nu.functor.map f)) N≫eY.hom=
      a≫eX.hom≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map (background.nu.functor.map f) N) := by
  let C := SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1
  let b := a≫XModLambdaN.map (C.inv.app _) N
  have h := shifted_ordinary_quotient_map_on_spheres X Y f N hN (1,0)
    (ordinaryQuotientShiftComparison X N eX) (ordinaryQuotientShiftComparison Y N eY)
    (ordinary_quotient_shift_comparison_incl X N eX heX)
    (ordinary_quotient_shift_comparison_incl Y N eY heY) m w b
  have h' := congrArg (fun z => z≫C.hom.app _) h
  simp only [ordinaryQuotientShiftComparison,Iso.trans_hom,Functor.mapIso_hom,
    Iso.symm_hom,Iso.app_inv,Category.assoc] at h'
  change b≫XModLambdaN.map ((SyntheticCategory.biShift (1,0)).map (background.nu.functor.map f)) N≫
    XModLambdaN.map (C.hom.app _) N≫eY.hom≫C.inv.app _≫C.hom.app _ =
    b≫XModLambdaN.map (C.hom.app _) N≫eX.hom≫C.inv.app _≫
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.map (background.nu.functor.map f) N)≫C.hom.app _ at h'
  rw [C.hom.naturality] at h'
  simp only [Iso.inv_hom_id_app_assoc,Iso.inv_hom_id_app,Category.comp_id] at h'
  have hn : XModLambdaN.map ((SyntheticCategory.biShift (1,0)).map (background.nu.functor.map f)) N≫
      XModLambdaN.map (C.hom.app _) N =
      XModLambdaN.map (C.hom.app _) N≫
        XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (background.nu.functor.map f)) N := by
    rw [←background.quotients.functoriality.map_comp,C.hom.naturality,
      background.quotients.functoriality.map_comp]
  rw [←Category.assoc (XModLambdaN.map ((SyntheticCategory.biShift (1,0)).map (background.nu.functor.map f)) N),hn] at h'
  have hb : b≫XModLambdaN.map (C.hom.app _) N=a := by
    dsimp only [b]
    rw [Category.assoc,←background.quotients.functoriality.map_comp,
      Iso.inv_hom_id_app,background.quotients.functoriality.map_id,Category.comp_id]
  simpa only [←Category.assoc,hb] using h'

/-- A single suspended finite representative produces one native source
with both its prescribed restriction and prescribed ordinary image. -/
private theorem ordinary_native_source_of_suspended
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (i N : ℕ) (hi : 0 < i) (hiN : i ≤ N) (m w : ℤ)
    (ei : XModLambdaN ((background.nu.functor.obj (X.obj background.auxiliary))⟦(1:ℤ)⟧) i ≅
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) i)⟦(1:ℤ)⟧)
    (eN : XModLambdaN ((background.nu.functor.obj (X.obj background.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N)⟦(1:ℤ)⟧)
    (eY : XModLambdaN ((background.nu.functor.obj (Y.obj background.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N)⟦(1:ℤ)⟧)
    (hei : XModLambdaN.incl _ i≫ei.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ i))
    (heN : XModLambdaN.incl _ N≫eN.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (heY : XModLambdaN.incl _ N≫eY.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (d : BiHom m w (XModLambdaN ((background.nu.functor.obj (X.obj background.auxiliary))⟦(1:ℤ)⟧) N))
    (u : BiHom (m-1) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) i))
    (v : BiHom (m-1) w (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N))
    (hu : d≫(background.quotients.tower _).rho i N hiN≫ei.hom=ordinarySuspendedRepresentative _ m w u)
    (hv : d≫XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (background.nu.functor.map f)) N≫eY.hom=
      ordinarySuspendedRepresentative _ m w v) :
    ∃ a : BiHom (m-1) w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N),
      a≫(background.quotients.tower _).rho i N hiN=u ∧ a≫XModLambdaN.map (background.nu.functor.map f) N=v := by
  let a := (ordinarySuspensionEquiv _ m w).symm (d≫eN.hom)
  have ha : ordinarySuspendedRepresentative _ m w a=d≫eN.hom := by
    rw [←ordinary_suspension_equiv_apply,AddEquiv.apply_symm_apply]
  refine ⟨a,?_,?_⟩
  · apply ordinary_suspended_representative_injective _ m w
    rw [ordinarySuspendedRepresentative_natural,ha,Category.assoc]
    exact (ordinary_quotient_suspension_restriction X i N hi hiN ei eN hei heN m w d).symm.trans hu
  · apply ordinary_suspended_representative_injective _ m w
    rw [ordinarySuspendedRepresentative_natural,ha,Category.assoc]
    exact (ordinary_quotient_suspension_map X Y f N (by omega) eN eY heN heY m w d).symm.trans hv


/-- The normalized raw source is transported through the fixed zero-shift
isomorphism. The two prescribed images still belong to this single source. -/
private theorem ordinary_native_source_of_raw
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (i N : ℕ) (hi : 0 < i) (hiN : i ≤ N) (m w : ℤ)
    (ei : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) i ≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) i)⟦(1:ℤ)⟧)
    (eY : XModLambdaN ((background.nu.functor.obj (T.Y.obj background.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N)⟦(1:ℤ)⟧)
    (hei : XModLambdaN.incl _ i≫ei.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ i))
    (heY : XModLambdaN.incl _ N≫eY.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (R : BiHom m w (XModLambdaN (normalizedTriangle background T he).obj₃ i))
    (d : BiHom m w (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N))
    (u : BiHom (m-1) w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) i))
    (v : BiHom (m-1) w (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) N))
    (hd : d≫(background.quotients.tower _).rho i N hiN=R≫XModLambdaN.map (normalizedTriangle background T he).mor₃ i)
    (hu : R≫XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₃ i≫ei.hom=
      ordinarySuspendedRepresentative _ m w u)
    (hv : d≫XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N≫eY.hom=ordinarySuspendedRepresentative _ m w v) :
    ∃ a : BiHom (m-1) w (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N),
      a≫(background.quotients.tower _).rho i N hiN=u ∧ a≫XModLambdaN.map (background.nu.functor.map T.f) N=v := by
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let E := zeroNormalizedSourceIso T he hf
  let dn := d≫XModLambdaN.map (S.map E.hom) N
  obtain ⟨eN,heN⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.X.obj background.auxiliary)) N
  apply ordinary_native_source_of_suspended T.X T.Y T.f i N hi hiN m w
    ei eN eY hei heN heY dn u v
  · dsimp only [dn]
    rw [Category.assoc,←Category.assoc (XModLambdaN.map (S.map E.hom) N),
      ←(background.quotients.natural (S.map E.hom)).rho_naturality hiN,
      ←Category.assoc d]
    simp only [←Category.assoc] at ⊢
    rw [hd]
    simpa only [ordinaryNativeTriangle,Triangle.mk_mor₃,E,S,
      background.quotients.functoriality.map_comp,Category.assoc] using hu
  · have hfmap : E.hom≫background.nu.functor.map T.f=(normalizedTriangle background T he).mor₁ := by
      rw [←zero_normalized_source_inv_arrow T he hf]
      simp only [E,←Category.assoc,Iso.hom_inv_id,Category.id_comp]
    dsimp only [dn]
    rw [Category.assoc,←Category.assoc (XModLambdaN.map (S.map E.hom) N),
      ←background.quotients.functoriality.map_comp,←S.map_comp,hfmap]
    exact hv

/-- Conditional comparison for an actual compatible root. Its compatibility
and actual adjacent equation remain explicit; they are not advertised as
consequences of the original root hypotheses by this internal helper. -/
private theorem ordinary_long_source_of_compatible_root
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (i q : ℕ) (hi : 0 < i) (hiq : i < q) (s t : ℤ)
    (u : Ambient background T.X (s+i+1,t+i))
    (v : Ambient background T.Y (s+q+1,t+q))
    (ei : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) (i+1) ≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (i+1))⟦(1:ℤ)⟧)
    (hei : XModLambdaN.incl _ (i+1)≫ei.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (i+1)))
    (R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ (i+1)))
    (root : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ q))
    (hcompatible : (root≫(background.quotients.tower _).rho (i+1) q (by omega))≫
      XModLambdaN.map (normalizedTriangle background T he).mor₃ (i+1)=
        R≫XModLambdaN.map (normalizedTriangle background T he).mor₃ (i+1))
    (htop : R≫XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₃ (i+1)≫ei.hom=
      ordinarySuspendedRepresentative _ (t-s) t (ordinaryEarlyTop T.X i hi s t u))
    (hdelta : root≫adjacentDelta (normalizedTriangle background T he).obj₃ q (by omega)=
      ((biSuspensionHomEquiv (t-s) t q
          (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel T.Y (s+q+1) (t+q) v)))≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(q:ℤ))).map
            (XModLambdaN.map (normalizedTriangle background T he).mor₂ 1))) :
    ∃ a : BiHom ((t-s)-1) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)),
      a≫(background.quotients.tower _).rho (i+1) (q+1) (by omega)=ordinaryEarlyTop T.X i hi s t u ∧
      a≫XModLambdaN.map (background.nu.functor.map T.f) (q+1)=
        homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega)
          (show (t+q)-q=t by omega) (finiteTopLabel T.Y q (by omega) (s+q+1) (t+q) v) := by
  obtain ⟨ey,hey,_⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he (q+1) (by omega)
  obtain ⟨d,hd,himage⟩ := finite_may_at_normalized_triangle_explicit_lengths T he hT q 1
    (by omega) (by decide) (t-s) t ey hey root _ hdelta
  have hdshort : d≫(background.quotients.tower _).rho (i+1) (q+1) (by omega)=
      R≫XModLambdaN.map (normalizedTriangle background T he).mor₃ (i+1) := by
    rw [←(background.quotients.tower _).rho_comp (show i+1≤q by omega) (show q≤q+1 by omega),
      ←Category.assoc,hd,Category.assoc,
      ←(background.quotients.natural (normalizedTriangle background T he).mor₃).rho_naturality (show i+1≤q by omega),
      ←Category.assoc,hcompatible]
  apply ordinary_native_source_of_raw T he hf (i+1) (q+1) (by omega) (by omega)
    (t-s) t ei ey hei hey R d _ _ hdshort htop
  exact himage.trans (by
    simpa only [normalizedTriangle,Triangle.mk,Preadditive.neg_comp] using
      ordinary_may_signed_top_target T.Y q (by omega) s t v)


/-- The original middle root corrections work for an arbitrary synthetic
last map. A separate last-layer calculation completes this internal step. -/
private theorem ordinary_root_compatible_of_last_vanishing
    (Y Z : (AdamsObject (coefficients := background.coefficients))) (g : Y.obj background.auxiliary ⟶ Z.obj background.auxiliary)
    (D : SyntheticSpectrum) (h : background.nu.functor.obj (Z.obj background.auxiliary) ⟶ D)
    (hgh : background.nu.functor.map g≫h=0)
    (a N : ℕ) (ha : 2 ≤ a) (haN : a ≤ N) (s t : ℤ)
    (hR : ∀ p : ℤ, s+1≤p → p<s+a-1 →
      ∀ z : Ambient background Z (p,t-s+p), z ∈ cycles background Z (a-(p-s).toNat:ℕ) (p,t-s+p) →
      ∃ y : Ambient background Y (p,t-s+p), y ∈ cycles background Y (a-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background Z (p,t-s+p), k ∈ cycles background Z (N+1-(p-s).toNat:ℕ) (p,t-s+p) ∧
        z-(background.classical.map g).pageMap 2 (p,t-s+p) y-k ∈ boundaries background Z ((p-s).toNat+1) (p,t-s+p))
    (hLast : ∀ e : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) a),
      FiltrationAtLeast background.syntheticTower (s+a-1) e → e≫XModLambdaN.map h a=0)
    (R : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) a))
    (root : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) N))
    (hfirst : R≫(background.quotients.tower _).rho 1 a (by omega)=root≫(background.quotients.tower _).rho 1 N (by omega)) :
    ∃ root' : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) N),
      root'≫(background.quotients.tower _).rho 1 N (by omega)=root≫(background.quotients.tower _).rho 1 N (by omega) ∧
      root'≫((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta=
        root≫((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta ∧
      (root'≫(background.quotients.tower _).rho a N haN)≫XModLambdaN.map h a=R≫XModLambdaN.map h a := by
  have herror : FiltrationAtLeast background.syntheticTower (s+1)
      (R-root≫(background.quotients.tower _).rho a N haN) := by
    apply finite_first_kernel_filtration Z a ha s t
    rw [Preadditive.sub_comp,Category.assoc,(background.quotients.tower _).rho_comp,hfirst,sub_self]
  obtain ⟨R',root',_,hRimage,hrootfirst,hrootboundary,hfinal⟩ :=
    higher_ordinary_root_correction_to_last Y Z g D h hgh a N (by omega) haN
      (t-s) t (s+1) (s+a-1) (by omega) (by omega) (by omega)
      (by
        intro p hp hpv
        have hi : (t-s+p-t).toNat=(p-s).toNat := by congr 1; omega
        simpa only [hi] using hR p hp hpv) R root herror
  have hz := hLast (R'-root'≫(background.quotients.tower _).rho a N haN) hfinal
  have heq : R'≫XModLambdaN.map h a=
      (root'≫(background.quotients.tower _).rho a N haN)≫XModLambdaN.map h a :=
    sub_eq_zero.mp (by simpa only [Preadditive.sub_comp] using hz)
  exact ⟨root',hrootfirst,hrootboundary,heq.symm.trans hRimage⟩


/-- Transport of the original ordinary-G root corrections to the actual
normalized third vertex. The final vanishing input is kept explicit here. -/
private theorem normalized_root_compatible_of_last_vanishing
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (a N : ℕ) (ha : 2 ≤ a) (haN : a ≤ N) (s t : ℤ)
    (hR : ∀ p : ℤ, s+1≤p → p<s+a-1 →
      ∀ z : Ambient background T.Z (p,t-s+p), z ∈ cycles background T.Z (a-(p-s).toNat:ℕ) (p,t-s+p) →
      ∃ y : Ambient background T.Y (p,t-s+p), y ∈ cycles background T.Y (a-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background T.Z (p,t-s+p), k ∈ cycles background T.Z (N+1-(p-s).toNat:ℕ) (p,t-s+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,t-s+p) y-k ∈ boundaries background T.Z ((p-s).toNat+1) (p,t-s+p))
    (hLast : ∀ e : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) a),
      FiltrationAtLeast background.syntheticTower (s+a-1) e →
        e≫XModLambdaN.map ((normalizedThirdZeroIso T he hg).inv≫(normalizedTriangle background T he).mor₃) a=0)
    (R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ a))
    (root : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ N))
    (hfirst : R≫(background.quotients.tower _).rho 1 a (by omega)=root≫(background.quotients.tower _).rho 1 N (by omega)) :
    ∃ root' : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ N),
      root'≫(background.quotients.tower _).rho 1 N (by omega)=root≫(background.quotients.tower _).rho 1 N (by omega) ∧
      root'≫((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta=
        root≫((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta ∧
      (root'≫(background.quotients.tower _).rho a N haN)≫XModLambdaN.map (normalizedTriangle background T he).mor₃ a=
        R≫XModLambdaN.map (normalizedTriangle background T he).mor₃ a := by
  let EZ := normalizedThirdZeroIso T he hg
  let h := EZ.inv≫(normalizedTriangle background T he).mor₃
  have hgh : background.nu.functor.map T.g≫h=0 := by
    rw [←normalized_second_arrow_zero T he hg]
    simp only [h,EZ,Category.assoc,Iso.hom_inv_id_assoc]
    exact comp_distTriang_mor_zero₂₃ _ hT
  let Rn := R≫XModLambdaN.map EZ.hom a
  let rootn := root≫XModLambdaN.map EZ.hom N
  have restrict {i n : ℕ} (hin : i≤n)
      (b : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ n)) :
      (b≫XModLambdaN.map EZ.hom n)≫(background.quotients.tower _).rho i n hin=
        (b≫(background.quotients.tower _).rho i n hin)≫XModLambdaN.map EZ.hom i := by
    rw [Category.assoc,←(background.quotients.natural EZ.hom).rho_naturality hin,←Category.assoc]
  have hfirstn : Rn≫(background.quotients.tower _).rho 1 a (by omega)=
      rootn≫(background.quotients.tower _).rho 1 N (by omega) := by
    dsimp only [Rn,rootn]
    rw [restrict,restrict,hfirst]
  obtain ⟨b,hbf,hbd,hbh⟩ := ordinary_root_compatible_of_last_vanishing T.Y T.Z T.g _ h hgh
    a N ha haN s t hR hLast Rn rootn hfirstn
  let braw := b≫XModLambdaN.map EZ.inv N
  have hbraw : braw≫XModLambdaN.map EZ.hom N=b := by
    dsimp only [braw]
    rw [Category.assoc,←background.quotients.functoriality.map_comp,Iso.inv_hom_id,
      background.quotients.functoriality.map_id,Category.comp_id]
  refine ⟨braw,?_,?_,?_⟩
  · apply (cancel_mono ((background.quotients.functoriality.functor 1).mapIso EZ).hom).mp
    change (braw≫(background.quotients.tower _).rho 1 N (by omega))≫XModLambdaN.map EZ.hom 1=
      (root≫(background.quotients.tower _).rho 1 N (by omega))≫XModLambdaN.map EZ.hom 1
    rw [←restrict,←restrict,hbraw]
    exact hbf
  · let I := (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      ((SyntheticCategory.biShift (0,-(N:ℤ))).mapIso
        ((background.quotients.functoriality.functor ((N+1)-N)).mapIso EZ))
    apply (cancel_mono I.hom).mp
    change (braw≫((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta)≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(N:ℤ))).map (XModLambdaN.map EZ.hom ((N+1)-N)))=
      (root≫((background.quotients.tower _).triangle (show 0<N by omega) (Nat.lt_succ_self N)).delta)≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(N:ℤ))).map (XModLambdaN.map EZ.hom ((N+1)-N)))
    simp only [Category.assoc,←(background.quotients.natural EZ.hom).delta_naturality
      (show 0<N by omega) (Nat.lt_succ_self N)]
    rw [←Category.assoc,hbraw]
    simpa only [rootn,Category.assoc] using hbd
  · have hq : XModLambdaN.map EZ.hom a≫XModLambdaN.map h a=
        XModLambdaN.map (normalizedTriangle background T he).mor₃ a := by
      rw [←background.quotients.functoriality.map_comp]
      simp only [h,Iso.hom_inv_id_assoc]
    have ht := congrArg (fun z => z≫XModLambdaN.map h a) (restrict haN braw)
    rw [hbraw] at ht
    have hc := ht.symm.trans hbh
    simpa only [Rn,Category.assoc,hq] using hc


/-- The positive second-arrow differential produces a root in the same raw
coordinates used by the ordinary early representative. Its actual adjacent
equation retains the specified target, before any root correction. -/
private theorem ordinary_positive_g_root_square
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (z : Ambient background T.Z (s+1,t+1)) (v : Ambient background T.Y (s+q+1,t+q))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+1,t+1) ((s+q+1)+1,(t+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) (s+q+1) (t+q) v)) :
    ∃ root : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ q),
      root≫(background.quotients.tower _).rho 1 q hq=
        homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (shiftHomotopyClass (0,-1) ((t+1)-(s+1),t+1)
            (nativeFirstLabel T.Z (s+1) (t+1) z))≫
          (levelQuotientShiftIso T.Z (-1) 1).inv≫
            XModLambdaN.map (normalizedThirdNegativeIso T he hg).inv 1 ∧
      root≫adjacentDelta (normalizedTriangle background T he).obj₃ q hq=
        ((biSuspensionHomEquiv (t-s) t q
            (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1)).symm
          (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
            (nativeFirstLabel T.Y (s+q+1) (t+q) v)))≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map
            ((SyntheticCategory.biShift (0,-(q:ℤ))).map
              (XModLambdaN.map (normalizedTriangle background T he).mor₂ 1)) := by
  obtain ⟨ey,hey,_⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he (q+1) (by omega)
  let v' : Ambient background T.Y ((s+1)+q,(t+1)+q-1) :=
    positiveClassicalRegrade (Prod.ext (by omega) (by omega)) v
  have hd' : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+1,t+1) ((s+1)+q+1,(t+1)+q) z
      (positiveClassicalRegrade (X:=T.Z) (Prod.ext (by omega) (by omega))
        (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
          ((s+1)+q) ((t+1)+q-1) v')) := by
    dsimp only [v']
    rw [positive_first_quotient_operation_regrade T.Y T.Z (normalizedSecondPositiveMap T hg)
      (s+q+1) (t+q) ((s+1)+q) ((t+1)+q-1) (by omega) (by omega),
      positive_classical_regrade_trans]
    exact positive_has_differential_target_regrade T.Z _ _ _ _ _ z _ hd
  obtain ⟨a₀,_,ha₀,hda₀,_,_⟩ := positive_second_differential_may
    T he hT hg q hq (s+1) (t+1) z v' hd' ey hey
  let a := homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
    (show (t+1)-1=t by omega) a₀
  refine ⟨a,?_,?_⟩
  · have h := congrArg (homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
      (show (t+1)-1=t by omega)) ha₀
    simpa only [a,regrade_comp,regrade_transitive] using h
  · have h := congrArg (homotopyRegrade (show (t+1)-(s+1)=t-s by omega)
      (show (t+1)-1=t by omega)) hda₀
    have hv : nativeFirstLabel T.Y ((s+1)+q) ((t+1)+q-1) v'=
        homotopyRegrade (by omega) (by omega) (nativeFirstLabel T.Y (s+q+1) (t+q) v) :=
      native_first_label_transport T.Y (show s+q+1=(s+1)+q by omega)
        (show t+q=(t+1)+q-1 by omega) v
    rw [hv] at h
    simpa only [a,regrade_comp,bi_susp_symm_regrade,regrade_transitive] using h


/-- Positive H: the original root differential, original middle comparisons,
and the whole last H-image condition construct the long native source.
Only the actual early R and its two prescribed calibrations are inputs. -/
private theorem ordinary_long_source_positive_h_of_root
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (i q : ℕ) (hi : 0 < i) (hiq : i < q) (s t : ℤ)
    (z : Ambient background T.Z (s,t)) (u : Ambient background T.X (s+i+1,t+i))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
    (hR : ∀ p : ℤ, s+1≤p → p<s+(i+1)-1 →
      ∀ z : Ambient background T.Z (p,t-s+p), z ∈ cycles background T.Z ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) →
      ∃ y : Ambient background T.Y (p,t-s+p), y ∈ cycles background T.Y ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background T.Z (p,t-s+p), k ∈ cycles background T.Z (q+1-(p-s).toNat:ℕ) (p,t-s+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,t-s+p) y-k ∈ boundaries background T.Z ((p-s).toNat+1) (p,t-s+p))
    (hH : ∀ z : Ambient background T.Z (s+(i+1)-1,t+(i+1)-1),
      positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
        (s+(i+1)-1) (t+(i+1)-1) z ∈
          boundaries background (.shift 1 T.X) (i+1) ((s+(i+1)-1)+1,(t+(i+1)-1)+1))
    (ei : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) (i+1) ≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (i+1))⟦(1:ℤ)⟧)
    (hei : XModLambdaN.incl _ (i+1)≫ei.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (i+1)))
    (R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ (i+1)))
    (hRfirst : R≫(background.quotients.tower _).rho 1 (i+1) (by omega)=
      nativeFirstLabel T.Z s t z≫XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1)
    (hRtop : R≫XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₃ (i+1)≫ei.hom=
      ordinarySuspendedRepresentative _ (t-s) t (ordinaryEarlyTop T.X i hi s t u)) :
    ∃ a : BiHom ((t-s)-1) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)),
      a≫(background.quotients.tower _).rho (i+1) (q+1) (by omega)=ordinaryEarlyTop T.X i hi s t u ∧
      a≫XModLambdaN.map (background.nu.functor.map T.f) (q+1)=
        homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega)
          (show (t+q)-q=t by omega) (finiteTopLabel T.Y q (by omega) (s+q+1) (t+q) v) := by
  obtain ⟨ey,hey,_⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he (q+1) (by omega)
  obtain ⟨root,_,hfirst,hdelta,_,_⟩ := classical_second_differential_may
    T he hT hg q (by omega) s t z v hd ey hey
  obtain ⟨root',_,hsame,hcomp⟩ := normalized_root_compatible_of_last_vanishing T he hT hg
    (i+1) q (by omega) (by omega) s t hR
    (ordinary_positive_h_terminal_zero T he hf hg hh (i+1) (by omega) s t hH)
    R root (hRfirst.trans hfirst.symm)
  have hdelta' := higher_adjacent_delta_equality (normalizedTriangle background T he).obj₃ q
    (by omega) (t-s) t root' root hsame
  exact ordinary_long_source_of_compatible_root T he hT hf i q hi hiq s t u v
    ei hei R root' hcomp hRtop (hdelta'.trans hdelta)

end
end KIP126.ProofTools.Internal.SyntheticCoverage
