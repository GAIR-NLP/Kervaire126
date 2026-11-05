module

import all KIP126.SpectralSequence.FilteredComplex.HomologyTarget.Data
import all KIP126.SpectralSequence.FilteredComplex.SSDataConstruction.Data
import all KIP126.SpectralSequence.Convergence.Proofs

@[expose] section

/-!
# Infinity-page comparison for weak convergence

The infinity page of the bounded filtered-complex spectral sequence is
isomorphic to the associated graded of its homology filtration.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The infinity page is isomorphic to the associated graded of filtered homology. -/
theorem FilteredComplex.weakConvergenceIso_nonempty (FC : FilteredComplex C)
    (bnd : FC.IsBounded) (s k : ℤ) :
    Nonempty ((FC.toSSData bnd s k).eInfty ≅
      FC.homologySSFiltration.associatedGraded s k) := by
    refine ⟨?_⟩
    unfold SSData.eInfty SSData.page Filtration.associatedGraded
    let S := ShortComplex.mk (FC.d (k + 1)) (FC.d (k + 1 - 1)) (FC.d_comp_d (k + 1))
    let e_deg : FC.A k = FC.A (k + 1 - 1) := congr_arg FC.A (show k = k + 1 - 1 by omega)
    let ι_fil := Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k)
    let πV := cokernel.π ι_fil
    let f_Z := (FC.fil s k).arrow ≫ FC.d k
    let kerZ := kernelSubobject f_Z
    let φ_to_X2 := kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg
    have h_lift : φ_to_X2 ≫ S.g = 0 := by
      change (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) ≫ S.g = 0
      simp only [Category.assoc]
      have : eqToHom e_deg ≫ S.g =
          FC.d k ≫ eqToHom (congr_arg FC.A (show k - 1 = (k + 1 - 1) - 1 by omega)) := by
        simp [S]
      rw [this, ← Category.assoc, ← Category.assoc,
        show (kerZ.arrow ≫ (FC.fil s k).arrow) ≫ FC.d k = kerZ.arrow ≫ f_Z
          from by simp only [f_Z, Category.assoc],
        kernelSubobject_arrow_comp, zero_comp]
    let φ_pre := S.liftCycles φ_to_X2 h_lift ≫ S.homologyπ
    let I_s := kernelSubobject S.g ⊓ FC.fil s (k + 1 - 1)
    have h_zero_s : I_s.arrow ≫ S.g = 0 := by
      rw [show I_s.arrow = Subobject.ofLE I_s (kernelSubobject S.g)
          inf_le_left ≫ (kernelSubobject S.g).arrow
        from (Subobject.ofLE_arrow inf_le_left).symm,
        Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    let gen_s := S.liftCycles I_s.arrow h_zero_s ≫ S.homologyπ
    have h_factors_I : I_s.Factors φ_to_X2 := by
      rw [show I_s = kernelSubobject S.g ⊓ FC.fil s (k + 1 - 1) from rfl,
          Subobject.inf_factors φ_to_X2]
      refine ⟨kernelSubobject_factors S.g φ_to_X2 h_lift, ?_⟩
      let e_sub := congr_arg (fun j => Subobject.underlying.obj (FC.fil s j))
          (show k = k + 1 - 1 by omega)
      have h_transport : (FC.fil s k).arrow ≫ eqToHom e_deg = eqToHom e_sub ≫
          (FC.fil s (k + 1 - 1)).arrow := by
        have : ∀ (a b : ℤ) (h : a = b),
            (FC.fil s a).arrow ≫ eqToHom (congr_arg FC.A h) =
            eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil s j)) h) ≫
            (FC.fil s b).arrow := by
          intro a b h; subst h; simp
        exact this k (k + 1 - 1) (by omega)
      have h_φ_eq : φ_to_X2 = (kerZ.arrow ≫ eqToHom e_sub) ≫
          (FC.fil s (k + 1 - 1)).arrow := by
        change kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg =
          (kerZ.arrow ≫ eqToHom e_sub) ≫ (FC.fil s (k + 1 - 1)).arrow
        rw [Category.assoc, h_transport, ← Category.assoc]
      rw [h_φ_eq]
      exact Subobject.factors_comp_arrow _
    let kerZ_to_Is := Subobject.factorThru I_s φ_to_X2 h_factors_I
    have h_kerZ_to_Is : kerZ_to_Is ≫ I_s.arrow = φ_to_X2 :=
      Subobject.factorThru_arrow I_s φ_to_X2 h_factors_I
    have h_func : kerZ_to_Is ≫ gen_s = φ_pre := by
      change kerZ_to_Is ≫ (S.liftCycles I_s.arrow h_zero_s ≫ S.homologyπ) =
        S.liftCycles φ_to_X2 h_lift ≫ S.homologyπ
      rw [← Category.assoc]
      congr 1
      apply (cancel_mono S.iCycles).mp
      rw [Category.assoc, S.liftCycles_i, S.liftCycles_i, h_kerZ_to_Is]
    have h_img_le : imageSubobject φ_pre ≤ imageSubobject gen_s := by
      rw [show φ_pre = kerZ_to_Is ≫ gen_s from h_func.symm]
      exact imageSubobject_comp_le _ _
    have h_fac_Fs : (imageSubobject gen_s).Factors φ_pre := by
      have : φ_pre = (kerZ_to_Is ≫ factorThruImageSubobject gen_s) ≫
          (imageSubobject gen_s).arrow := by
        rw [Category.assoc, imageSubobject_arrow_comp]
        exact h_func.symm
      rw [this]
      exact Subobject.factors_comp_arrow _
    let φ_to_Fs := Subobject.factorThru (imageSubobject gen_s) φ_pre h_fac_Fs
    have h_φ_to_Fs : φ_to_Fs ≫ (imageSubobject gen_s).arrow = φ_pre :=
      Subobject.factorThru_arrow _ _ h_fac_Fs
    let πRHS := cokernel.π (Subobject.ofLE
      (FC.homologySSFiltration.F (s + 1) k)
      (FC.homologySSFiltration.F s k)
      (FC.homologySSFiltration.mono s k))
    let fwd_kerZ := φ_to_Fs ≫ πRHS
    let e_Z := factorThruImageSubobject (kerZ.arrow ≫ πV)
    have h_desc_fwd : kernel.ι e_Z ≫ fwd_kerZ = 0 := by
      have h_ker_πV : kernel.ι e_Z ≫ kerZ.arrow ≫ πV = 0 := by
        have h0 : kernel.ι e_Z ≫ e_Z = 0 := kernel.condition e_Z
        have h1 : factorThruImageSubobject (kerZ.arrow ≫ πV) ≫
            (imageSubobject (kerZ.arrow ≫ πV)).arrow =
            kerZ.arrow ≫ πV := by simp [imageSubobject_arrow_comp]
        calc kernel.ι e_Z ≫ kerZ.arrow ≫ πV
            = kernel.ι e_Z ≫ (e_Z ≫
                (imageSubobject (kerZ.arrow ≫ πV)).arrow) := by rw [h1]
          _ = (kernel.ι e_Z ≫ e_Z) ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow :=
                (Category.assoc _ _ _).symm
          _ = 0 ≫ _ := by rw [h0]
          _ = 0 := zero_comp
      have h_ker_πV' : (kernel.ι e_Z ≫ kerZ.arrow) ≫ cokernel.π ι_fil = 0 := by
        rw [Category.assoc]; exact h_ker_πV
      set lift_s1 := Abelian.monoLift ι_fil (kernel.ι e_Z ≫ kerZ.arrow) h_ker_πV'
      have h_lift_s1 : lift_s1 ≫ ι_fil = kernel.ι e_Z ≫ kerZ.arrow :=
        Abelian.monoLift_comp _ _ _
      set I_s1 := kernelSubobject S.g ⊓ FC.fil (s + 1) (k + 1 - 1)
      have h_zero_s1 : I_s1.arrow ≫ S.g = 0 := by
        rw [show I_s1.arrow = Subobject.ofLE I_s1 (kernelSubobject S.g)
            inf_le_left ≫ (kernelSubobject S.g).arrow
          from (Subobject.ofLE_arrow inf_le_left).symm,
          Category.assoc, kernelSubobject_arrow_comp, comp_zero]
      set gen_s1 := S.liftCycles I_s1.arrow h_zero_s1 ≫ S.homologyπ
      have h_ι_arrow : ι_fil ≫ (FC.fil s k).arrow = (FC.fil (s + 1) k).arrow :=
        Subobject.ofLE_arrow (FC.fil_anti s k)
      have h_transport_s1 : (FC.fil (s + 1) k).arrow ≫ eqToHom e_deg =
          eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil (s + 1) j))
            (show k = k + 1 - 1 by omega)) ≫
          (FC.fil (s + 1) (k + 1 - 1)).arrow := by
        have : ∀ (a b : ℤ) (h : a = b),
            (FC.fil (s + 1) a).arrow ≫ eqToHom (congr_arg FC.A h) =
            eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil (s + 1) j)) h) ≫
            (FC.fil (s + 1) b).arrow := by
          intro a b h; subst h; simp
        exact this k (k + 1 - 1) (by omega)
      have h_ker_lift_sg : (kernel.ι e_Z ≫ φ_to_X2) ≫ S.g = 0 := by
        rw [Category.assoc]; exact (h_lift ▸ comp_zero)
      have h_ker_in_fil_s1 :
          (FC.fil (s + 1) (k + 1 - 1)).Factors (kernel.ι e_Z ≫ φ_to_X2) := by
        have h_eq : kernel.ι e_Z ≫ φ_to_X2 =
            (lift_s1 ≫ eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil (s + 1) j))
              (show k = k + 1 - 1 by omega))) ≫
            (FC.fil (s + 1) (k + 1 - 1)).arrow := by
          change kernel.ι e_Z ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) = _
          rw [show kernel.ι e_Z ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) =
              (kernel.ι e_Z ≫ kerZ.arrow) ≫ ((FC.fil s k).arrow ≫ eqToHom e_deg) by
            simp only [Category.assoc]]
          rw [h_lift_s1.symm]
          rw [show (lift_s1 ≫ ι_fil) ≫ ((FC.fil s k).arrow ≫ eqToHom e_deg) =
              lift_s1 ≫ (ι_fil ≫ (FC.fil s k).arrow) ≫ eqToHom e_deg by
            simp only [Category.assoc]]
          rw [h_ι_arrow, h_transport_s1]
          simp only [Category.assoc]
        rw [h_eq]; exact Subobject.factors_comp_arrow _
      have h_fac_I_s1 : I_s1.Factors (kernel.ι e_Z ≫ φ_to_X2) := by
        rw [show I_s1 = kernelSubobject S.g ⊓ FC.fil (s + 1) (k + 1 - 1) from rfl,
            Subobject.inf_factors]
        exact ⟨kernelSubobject_factors S.g _ h_ker_lift_sg, h_ker_in_fil_s1⟩
      let ker_to_I_s1 := Subobject.factorThru I_s1 (kernel.ι e_Z ≫ φ_to_X2) h_fac_I_s1
      have h_ker_to_I_s1 : ker_to_I_s1 ≫ I_s1.arrow = kernel.ι e_Z ≫ φ_to_X2 :=
        Subobject.factorThru_arrow _ _ _
      have h_func_s1 : ker_to_I_s1 ≫ gen_s1 = kernel.ι e_Z ≫ φ_pre := by
        change ker_to_I_s1 ≫ (S.liftCycles I_s1.arrow h_zero_s1 ≫ S.homologyπ) =
          kernel.ι e_Z ≫ (S.liftCycles φ_to_X2 h_lift ≫ S.homologyπ)
        rw [← Category.assoc, ← Category.assoc]; congr 1
        apply (cancel_mono S.iCycles).mp
        rw [Category.assoc, S.liftCycles_i, Category.assoc, S.liftCycles_i, h_ker_to_I_s1]
      have h_Fs1_le_Fs : FC.homologySSFiltration.F (s + 1) k ≤
          FC.homologySSFiltration.F s k :=
        FC.homologySSFiltration.mono s k
      have h_ofLE_arrow : Subobject.ofLE (FC.homologySSFiltration.F (s + 1) k)
          (FC.homologySSFiltration.F s k) h_Fs1_le_Fs ≫
          (FC.homologySSFiltration.F s k).arrow =
          (FC.homologySSFiltration.F (s + 1) k).arrow :=
        Subobject.ofLE_arrow h_Fs1_le_Fs
      have h_factor_ofLE : kernel.ι e_Z ≫ φ_to_Fs =
          (ker_to_I_s1 ≫ factorThruImageSubobject gen_s1) ≫
          Subobject.ofLE (FC.homologySSFiltration.F (s + 1) k)
            (FC.homologySSFiltration.F s k) h_Fs1_le_Fs := by
        apply (cancel_mono (imageSubobject gen_s).arrow).mp
        rw [Category.assoc, h_φ_to_Fs]
        have h_rhs : ((ker_to_I_s1 ≫ factorThruImageSubobject gen_s1) ≫
            Subobject.ofLE (FC.homologySSFiltration.F (s + 1) k)
              (FC.homologySSFiltration.F s k) h_Fs1_le_Fs) ≫
            (imageSubobject gen_s).arrow =
            ker_to_I_s1 ≫ gen_s1 := by
          change ((ker_to_I_s1 ≫ factorThruImageSubobject gen_s1) ≫
            Subobject.ofLE (FC.homologySSFiltration.F (s + 1) k)
              (FC.homologySSFiltration.F s k) h_Fs1_le_Fs) ≫
            (FC.homologySSFiltration.F s k).arrow = ker_to_I_s1 ≫ gen_s1
          simp only [Category.assoc]
          dsimp only [FilteredComplex.homologySSFiltration] at h_ofLE_arrow ⊢
          rw [h_ofLE_arrow]
          change ker_to_I_s1 ≫ factorThruImageSubobject gen_s1 ≫
            (imageSubobject gen_s1).arrow = ker_to_I_s1 ≫ gen_s1
          rw [imageSubobject_arrow_comp]
        dsimp only [FilteredComplex.homologySSFiltration] at h_rhs ⊢
        rw [h_rhs]
        exact h_func_s1.symm
      change kernel.ι e_Z ≫ (φ_to_Fs ≫ πRHS) = 0
      dsimp only [FilteredComplex.homologySSFiltration] at h_factor_ofLE ⊢
      rw [← Category.assoc, h_factor_ofLE, Category.assoc, Category.assoc]
      erw [show Subobject.ofLE (FC.homologySSFiltration.F (s + 1) k)
            (FC.homologySSFiltration.F s k) h_Fs1_le_Fs ≫ πRHS = 0
        from cokernel.condition _]
      erw [comp_zero, comp_zero]
      rfl
    let fwd_Z := Abelian.epiDesc e_Z fwd_kerZ h_desc_fwd
    have h_fwd_Z : e_Z ≫ fwd_Z = fwd_kerZ := Abelian.comp_epiDesc _ _ _
    have h_fwd_kills_B : Subobject.ofLE
        ((FC.toSSData bnd s k).B ⊤) ((FC.toSSData bnd s k).Z ⊤)
        ((FC.toSSData bnd s k).B_le_Z ⊤) ≫ fwd_Z = 0 := by
      let imgD := imageSubobject (FC.dToK k)
      let I_B := imgD ⊓ FC.fil s k
      let oI := Subobject.ofLE I_B (FC.fil s k) inf_le_right
      have h_oI_zero : oI ≫ f_Z = 0 := by
        change Subobject.ofLE I_B (FC.fil s k) inf_le_right ≫
          (FC.fil s k).arrow ≫ FC.d k = 0
        rw [← Category.assoc, Subobject.ofLE_arrow]
        rw [show I_B.arrow =
            Subobject.ofLE I_B imgD inf_le_left ≫ imgD.arrow
          from (Subobject.ofLE_arrow inf_le_left).symm,
          Category.assoc]
        have : imgD.arrow ≫ FC.d k = 0 := by
          rw [← cancel_epi (factorThruImageSubobject (FC.dToK k))]
          rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp]
          exact FC.dToK_comp_d k
        rw [this, comp_zero]
      let oI_lift := factorThruKernelSubobject f_Z oI h_oI_zero
      have h_oI_lift : oI_lift ≫ kerZ.arrow = oI :=
        factorThruKernelSubobject_comp_arrow f_Z oI h_oI_zero
      have h_fti_ofLE : factorThruImageSubobject (oI ≫ πV) ≫
          Subobject.ofLE ((FC.toSSData bnd s k).B ⊤) ((FC.toSSData bnd s k).Z ⊤)
          ((FC.toSSData bnd s k).B_le_Z ⊤) = oI_lift ≫ e_Z := by
        apply (cancel_mono ((FC.toSSData bnd s k).Z ⊤).arrow).mp
        dsimp only [FilteredComplex.toSSData, FilteredComplex.cycleSubobject,
          FilteredComplex.boundarySubobject] at *
        erw [Category.assoc, Subobject.ofLE_arrow]
        change factorThruImageSubobject (oI ≫ πV) ≫
          ((FC.toSSData bnd s k).B ⊤).arrow = (oI_lift ≫ e_Z) ≫ _
        rw [show ((FC.toSSData bnd s k).B ⊤).arrow =
            (imageSubobject (oI ≫ πV)).arrow from rfl]
        erw [imageSubobject_arrow_comp]
        rw [Category.assoc]
        erw [show e_Z ≫ ((FC.toSSData bnd s k).Z ⊤).arrow =
          kerZ.arrow ≫ πV from imageSubobject_arrow_comp (kerZ.arrow ≫ πV)]
        erw [← Category.assoc, h_oI_lift]
        rfl
      dsimp only [FilteredComplex.toSSData, FilteredComplex.boundarySubobject] at *
      erw [← cancel_epi (factorThruImageSubobject (oI ≫ πV))]
      erw [comp_zero]
      erw [← Category.assoc, h_fti_ofLE]
      erw [Category.assoc, h_fwd_Z]
      change oI_lift ≫ (φ_to_Fs ≫ πRHS) = 0
      rw [← Category.assoc]
      suffices h_oI_φ_to_Fs : oI_lift ≫ φ_to_Fs = 0 by
        rw [h_oI_φ_to_Fs, zero_comp]
      apply (cancel_mono (imageSubobject gen_s).arrow).mp
      rw [Category.assoc, h_φ_to_Fs, zero_comp]
      change oI_lift ≫ (S.liftCycles φ_to_X2 h_lift ≫ S.homologyπ) = 0
      rw [← Category.assoc]
      have h_comp_φ : oI_lift ≫ φ_to_X2 = I_B.arrow ≫ eqToHom e_deg := by
        change oI_lift ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) =
          I_B.arrow ≫ eqToHom e_deg
        rw [← Category.assoc, ← Category.assoc,
          show oI_lift ≫ kerZ.arrow = oI from h_oI_lift,
          show oI ≫ (FC.fil s k).arrow = I_B.arrow
            from Subobject.ofLE_arrow inf_le_right]
      have h_IB_factor : I_B.arrow ≫ eqToHom e_deg =
          Subobject.ofLE I_B imgD inf_le_left ≫ (imgD.arrow ≫ eqToHom e_deg) := by
        rw [← Category.assoc, Subobject.ofLE_arrow]
      have h_imgD_sg : (imgD.arrow ≫ eqToHom e_deg) ≫ S.g = 0 := by
        rw [Category.assoc]
        have h_eqToHom_sg : eqToHom e_deg ≫ S.g =
            FC.d k ≫ eqToHom (congr_arg FC.A (show k - 1 = (k + 1 - 1) - 1 by omega)) := by
          suffices h : ∀ (n : ℤ) (hn : n = k),
              eqToHom (show FC.A k = FC.A n from congr_arg FC.A hn.symm) ≫ FC.d n =
              FC.d k ≫ eqToHom (show FC.A (k - 1) = FC.A (n - 1) from
                congr_arg FC.A (show k - 1 = n - 1 by omega)) by
            convert h (k + 1 - 1) (by omega) using 1
          intro n hn; subst hn; simp [eqToHom_refl, Category.id_comp, Category.comp_id]
        rw [h_eqToHom_sg, ← Category.assoc]
        have : imgD.arrow ≫ FC.d k = 0 := by
          rw [← cancel_epi (factorThruImageSubobject (FC.dToK k))]
          rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp]
          exact FC.dToK_comp_d k
        rw [this, zero_comp]
      have h_imgD_homologyπ :
          S.liftCycles (imgD.arrow ≫ eqToHom e_deg) h_imgD_sg ≫ S.homologyπ = 0 := by
        rw [← cancel_epi (factorThruImageSubobject (FC.dToK k))]
        rw [comp_zero, ← Category.assoc]
        have h_fti_lc : factorThruImageSubobject (FC.dToK k) ≫
            S.liftCycles (imgD.arrow ≫ eqToHom e_deg) h_imgD_sg = S.toCycles := by
          apply (cancel_mono S.iCycles).mp
          rw [Category.assoc, S.liftCycles_i, S.toCycles_i]
          rw [← Category.assoc, imageSubobject_arrow_comp]
          change FC.dToK k ≫ eqToHom e_deg = S.f
          change FC.complex.d (k + 1) k ≫ eqToHom e_deg =
            FC.complex.d (k + 1) (k + 1 - 1)
          exact FC.complex_d_comp_eqToHom (k + 1)
            (show k = k + 1 - 1 by omega)
        rw [h_fti_lc, S.toCycles_comp_homologyπ]
      have h_comp_sg : (oI_lift ≫ φ_to_X2) ≫ S.g = 0 := by
        rw [Category.assoc]; exact h_lift ▸ comp_zero
      have h_IB_sg : (I_B.arrow ≫ eqToHom e_deg) ≫ S.g = 0 := by
        rw [h_comp_φ.symm]; exact h_comp_sg
      have h_lc_func : oI_lift ≫ S.liftCycles φ_to_X2 h_lift =
          S.liftCycles (oI_lift ≫ φ_to_X2) h_comp_sg := by
        apply (cancel_mono S.iCycles).mp
        rw [Category.assoc, S.liftCycles_i, S.liftCycles_i]
      rw [h_lc_func]
      have h_lc_eq : S.liftCycles (oI_lift ≫ φ_to_X2) h_comp_sg =
          S.liftCycles (I_B.arrow ≫ eqToHom e_deg) h_IB_sg := by
        apply (cancel_mono S.iCycles).mp
        rw [S.liftCycles_i, S.liftCycles_i, h_comp_φ]
      rw [h_lc_eq]
      have h_lc_factor : S.liftCycles (I_B.arrow ≫ eqToHom e_deg) h_IB_sg =
          Subobject.ofLE I_B imgD inf_le_left ≫
          S.liftCycles (imgD.arrow ≫ eqToHom e_deg) h_imgD_sg := by
        apply (cancel_mono S.iCycles).mp
        rw [S.liftCycles_i, Category.assoc, S.liftCycles_i, h_IB_factor]
      rw [h_lc_factor, Category.assoc, h_imgD_homologyπ, comp_zero]
    let fwd := cokernel.desc _ fwd_Z h_fwd_kills_B
    let πLHS := cokernel.π (Subobject.ofLE
      ((FC.toSSData bnd s k).B ⊤) ((FC.toSSData bnd s k).Z ⊤)
      ((FC.toSSData bnd s k).B_le_Z ⊤))
    let e_Fs := factorThruImageSubobject gen_s
    let e_deg_inv : FC.A (k + 1 - 1) = FC.A k :=
      congr_arg FC.A (show k + 1 - 1 = k by omega)
    have h_Is_to_fil : (FC.fil s k).Factors (I_s.arrow ≫ eqToHom e_deg_inv) := by
      have h_le : I_s ≤ FC.fil s (k + 1 - 1) := inf_le_right
      have h_arrow : I_s.arrow = Subobject.ofLE I_s (FC.fil s (k + 1 - 1)) h_le ≫
          (FC.fil s (k + 1 - 1)).arrow := (Subobject.ofLE_arrow h_le).symm
      rw [h_arrow, Category.assoc]
      have h_transport2 : (FC.fil s (k + 1 - 1)).arrow ≫ eqToHom e_deg_inv =
          eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil s j))
            (show k + 1 - 1 = k by omega)) ≫ (FC.fil s k).arrow := by
        have : ∀ (a b : ℤ) (h : a = b),
            (FC.fil s a).arrow ≫ eqToHom (congr_arg FC.A h) =
            eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil s j)) h) ≫
            (FC.fil s b).arrow := by
          intro a b h; subst h; simp
        exact this (k + 1 - 1) k (by omega)
      rw [h_transport2, ← Category.assoc]
      exact Subobject.factors_comp_arrow _
    let Is_to_fil := Subobject.factorThru (FC.fil s k) (I_s.arrow ≫ eqToHom e_deg_inv) h_Is_to_fil
    have h_Is_to_fil_eq : Is_to_fil ≫ (FC.fil s k).arrow = I_s.arrow ≫ eqToHom e_deg_inv :=
      Subobject.factorThru_arrow _ _ _
    have h_Is_in_kerZ : Is_to_fil ≫ f_Z = 0 := by
      change Is_to_fil ≫ ((FC.fil s k).arrow ≫ FC.d k) = 0
      rw [← Category.assoc,
        show (Is_to_fil ≫ (FC.fil s k).arrow) =
          I_s.arrow ≫ eqToHom e_deg_inv
        from h_Is_to_fil_eq, Category.assoc]
      have h_transport_d : eqToHom e_deg_inv ≫ FC.d k =
          S.g ≫ eqToHom (congr_arg FC.A (show (k + 1 - 1) - 1 = k - 1 by omega)) := by
        simp [S]
      rw [h_transport_d, ← Category.assoc]
      have h_Is_ker : I_s.arrow ≫ S.g = 0 := h_zero_s
      rw [h_Is_ker, zero_comp]
    let Is_to_kerZ := factorThruKernelSubobject f_Z Is_to_fil h_Is_in_kerZ
    have h_Is_to_kerZ : Is_to_kerZ ≫ kerZ.arrow = Is_to_fil :=
      factorThruKernelSubobject_comp_arrow _ _ _
    let inv_Is := Is_to_kerZ ≫ e_Z ≫ πLHS
    have h_desc_inv : kernel.ι e_Fs ≫ inv_Is = 0 := by
      have h_ker_gen : kernel.ι e_Fs ≫ gen_s = 0 := by
        have h_assoc : kernel.ι e_Fs ≫ e_Fs ≫ (imageSubobject gen_s).arrow = 0 := by
          rw [kernel.condition_assoc, zero_comp]
        rwa [imageSubobject_arrow_comp] at h_assoc
      have h_lc_π : (kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s) ≫ S.homologyπ = 0 := by
        rw [Category.assoc]; exact h_ker_gen
      have h_Sf_dToK : S.f ≫ eqToHom e_deg_inv = FC.dToK k := by
        change FC.complex.d (k + 1) (k + 1 - 1) ≫ eqToHom e_deg_inv =
          FC.complex.d (k + 1) k
        exact FC.complex_d_comp_eqToHom (k + 1)
          (show k + 1 - 1 = k by omega)
      have h_comp_cok_dToK : (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv) ≫
          cokernel.π (FC.dToK k) = 0 := by
        have h_φ_lHπ : (kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s) ≫
            S.leftHomologyπ = 0 := by
          have hπ_eq : S.homologyπ = S.leftHomologyπ ≫ S.leftHomologyIso.hom := by
            rw [← Category.comp_id S.homologyπ,
                ← Iso.inv_hom_id S.leftHomologyIso, ← Category.assoc,
                S.homologyπ_comp_leftHomologyIso_inv]
          rw [← cancel_mono S.leftHomologyIso.hom, Category.assoc, zero_comp, ← hπ_eq]
          exact h_lc_π
        have h_φ_cok_tC : (kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s) ≫
            cokernel.π S.toCycles = 0 := by
          let σ := IsColimit.coconePointUniqueUpToIso S.leftHomologyIsCokernel
              (cokernelIsCokernel S.toCycles)
          have : S.leftHomologyπ ≫ σ.hom = cokernel.π S.toCycles :=
            IsColimit.comp_coconePointUniqueUpToIso_hom S.leftHomologyIsCokernel
              (cokernelIsCokernel S.toCycles) WalkingParallelPair.one
          calc
            (kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s) ≫
                cokernel.π S.toCycles =
                ((kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s) ≫
                  S.leftHomologyπ) ≫ σ.hom :=
                    (congrArg (fun f =>
                      (kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s) ≫ f)
                        this.symm).trans (Category.assoc _ _ _).symm
            _ = 0 := (congrArg (fun f => f ≫ σ.hom) h_φ_lHπ).trans zero_comp
        let κ := kernel.lift (cokernel.π S.toCycles)
            (kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s) h_φ_cok_tC
        have hκ : κ ≫ kernel.ι (cokernel.π S.toCycles) =
            kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s := kernel.lift_ι _ _ _
        have hκ_arrow : κ ≫ (kernel.ι (cokernel.π S.toCycles) ≫ S.iCycles) =
            kernel.ι e_Fs ≫ I_s.arrow := by
          rw [← Category.assoc, hκ, Category.assoc, S.liftCycles_i]
        have h_img_fac : Abelian.factorThruImage S.toCycles ≫
            kernel.ι (cokernel.π S.toCycles) = S.toCycles := Abelian.image.fac S.toCycles
        have h_mid_zero : kernel.ι (cokernel.π S.toCycles) ≫ S.iCycles ≫
            eqToHom e_deg_inv ≫ cokernel.π (FC.dToK k) = 0 := by
          rw [← cancel_epi (Abelian.factorThruImage S.toCycles), comp_zero]
          simp only [← Category.assoc]
          rw [h_img_fac, S.toCycles_i, h_Sf_dToK, cokernel.condition]
        have h_sub : kernel.ι e_Fs ≫ I_s.arrow =
            κ ≫ (kernel.ι (cokernel.π S.toCycles) ≫ S.iCycles) := hκ_arrow.symm
        simp only [← Category.assoc] at h_sub ⊢
        rw [h_sub]
        simp only [Category.assoc]
        rw [h_mid_zero, comp_zero]
      have h_imgD_eq_kerCok : imageSubobject (FC.dToK k) =
          kernelSubobject (cokernel.π (FC.dToK k)) := by
        have hex := ShortComplex.exact_cokernel (FC.dToK k)
        rwa [ShortComplex.exact_iff_image_eq_kernel] at hex
      have h_in_imgD : (imageSubobject (FC.dToK k)).Factors
          (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv) := by
        rw [h_imgD_eq_kerCok, kernelSubobject_factors_iff]
        exact h_comp_cok_dToK
      have h_in_fil : (FC.fil s k).Factors
          (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv) := by
        rw [show kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv =
          (kernel.ι e_Fs ≫ Is_to_fil) ≫ (FC.fil s k).arrow from by
          rw [Category.assoc, h_Is_to_fil_eq]]
        exact Subobject.factors_comp_arrow _
      let imgD := imageSubobject (FC.dToK k)
      let I_B := imgD ⊓ FC.fil s k
      have h_in_IB : I_B.Factors (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv) := by
        rw [show I_B = imgD ⊓ FC.fil s k from rfl, Subobject.inf_factors]
        exact ⟨h_in_imgD, h_in_fil⟩
      let ker_to_IB := I_B.factorThru (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv) h_in_IB
      have h_ker_to_IB : ker_to_IB ≫ I_B.arrow =
          kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv :=
        Subobject.factorThru_arrow _ _ _
      let oI := Subobject.ofLE I_B (FC.fil s k) inf_le_right
      have h_oI_zero : oI ≫ f_Z = 0 := by
        change Subobject.ofLE I_B (FC.fil s k) inf_le_right ≫
          (FC.fil s k).arrow ≫ FC.d k = 0
        rw [← Category.assoc, Subobject.ofLE_arrow]
        rw [show I_B.arrow = Subobject.ofLE I_B imgD inf_le_left ≫ imgD.arrow
          from (Subobject.ofLE_arrow inf_le_left).symm, Category.assoc]
        have : imgD.arrow ≫ FC.d k = 0 := by
          rw [← cancel_epi (factorThruImageSubobject (FC.dToK k))]
          rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp]
          exact FC.dToK_comp_d k
        rw [this, comp_zero]
      let oI_lift := factorThruKernelSubobject f_Z oI h_oI_zero
      have h_oI_lift : oI_lift ≫ kerZ.arrow = oI :=
        factorThruKernelSubobject_comp_arrow f_Z oI h_oI_zero
      have h_factor_kerZ : kernel.ι e_Fs ≫ Is_to_kerZ = ker_to_IB ≫ oI_lift := by
        apply (cancel_mono kerZ.arrow).mp
        simp only [Category.assoc]
        rw [h_oI_lift, h_Is_to_kerZ]
        apply (cancel_mono (FC.fil s k).arrow).mp
        simp only [Category.assoc]
        rw [Subobject.ofLE_arrow, h_ker_to_IB, h_Is_to_fil_eq]
      have h_fti_ofLE : factorThruImageSubobject (oI ≫ πV) ≫
          Subobject.ofLE ((FC.toSSData bnd s k).B ⊤) ((FC.toSSData bnd s k).Z ⊤)
          ((FC.toSSData bnd s k).B_le_Z ⊤) = oI_lift ≫ e_Z := by
        apply (cancel_mono ((FC.toSSData bnd s k).Z ⊤).arrow).mp
        dsimp only [FilteredComplex.toSSData, FilteredComplex.cycleSubobject,
          FilteredComplex.boundarySubobject] at *
        erw [Category.assoc, Subobject.ofLE_arrow]
        change factorThruImageSubobject (oI ≫ πV) ≫
          ((FC.toSSData bnd s k).B ⊤).arrow = (oI_lift ≫ e_Z) ≫ _
        rw [show ((FC.toSSData bnd s k).B ⊤).arrow =
            (imageSubobject (oI ≫ πV)).arrow from rfl]
        erw [imageSubobject_arrow_comp, Category.assoc]
        erw [show e_Z ≫ ((FC.toSSData bnd s k).Z ⊤).arrow =
          kerZ.arrow ≫ πV from imageSubobject_arrow_comp (kerZ.arrow ≫ πV)]
        erw [← Category.assoc, h_oI_lift]
        rfl
      have h_oI_kill : oI_lift ≫ e_Z ≫ πLHS = 0 := by
        dsimp only [FilteredComplex.toSSData, FilteredComplex.cycleSubobject,
          FilteredComplex.boundarySubobject] at h_fti_ofLE ⊢
        erw [← Category.assoc, ← h_fti_ofLE, Category.assoc]
        erw [show Subobject.ofLE ((FC.toSSData bnd s k).B ⊤) ((FC.toSSData bnd s k).Z ⊤)
            ((FC.toSSData bnd s k).B_le_Z ⊤) ≫ πLHS = 0 from cokernel.condition _]
        erw [comp_zero]
        rfl
      change kernel.ι e_Fs ≫ (Is_to_kerZ ≫ e_Z ≫ πLHS) = 0
      rw [← Category.assoc, ← Category.assoc, h_factor_kerZ,
          Category.assoc, Category.assoc, h_oI_kill, comp_zero]
    let inv_Fs := Abelian.epiDesc e_Fs inv_Is h_desc_inv
    have h_inv_Fs : e_Fs ≫ inv_Fs = inv_Is := Abelian.comp_epiDesc _ _ _
    have h_inv_kills_Fs1 : Subobject.ofLE
        (FC.homologySSFiltration.F (s + 1) k)
        (FC.homologySSFiltration.F s k)
        (FC.homologySSFiltration.mono s k) ≫ inv_Fs = 0 := by
      set I_s1 := kernelSubobject S.g ⊓ FC.fil (s + 1) (k + 1 - 1)
      have h_zero_s1 : I_s1.arrow ≫ S.g = 0 := by
        rw [show I_s1.arrow = Subobject.ofLE I_s1 (kernelSubobject S.g)
            inf_le_left ≫ (kernelSubobject S.g).arrow
          from (Subobject.ofLE_arrow inf_le_left).symm,
          Category.assoc, kernelSubobject_arrow_comp, comp_zero]
      set gen_s1 := S.liftCycles I_s1.arrow h_zero_s1 ≫ S.homologyπ
      have hle : I_s1 ≤ I_s := inf_le_inf_left _ (FC.fil_anti s (k + 1 - 1))
      have hlift_s : S.liftCycles I_s1.arrow h_zero_s1 =
          Subobject.ofLE I_s1 I_s hle ≫ S.liftCycles I_s.arrow h_zero_s := by
        apply (cancel_mono S.iCycles).mp
        rw [S.liftCycles_i, Category.assoc, S.liftCycles_i]
        exact (Subobject.ofLE_arrow hle).symm
      have h_gen_factor : gen_s1 =
          Subobject.ofLE I_s1 I_s hle ≫ gen_s := by
        change S.liftCycles I_s1.arrow h_zero_s1 ≫ S.homologyπ =
          Subobject.ofLE I_s1 I_s hle ≫ (S.liftCycles I_s.arrow h_zero_s ≫ S.homologyπ)
        rw [← Category.assoc, hlift_s]
      apply zero_of_epi_comp (factorThruImageSubobject gen_s1)
      have h_fTI_ofLE : factorThruImageSubobject gen_s1 ≫
          Subobject.ofLE (FC.homologySSFiltration.F (s + 1) k)
            (FC.homologySSFiltration.F s k) (FC.homologySSFiltration.mono s k) =
          Subobject.ofLE I_s1 I_s hle ≫ factorThruImageSubobject gen_s := by
        apply (cancel_mono (FC.homologySSFiltration.F s k).arrow).mp
        dsimp only [FilteredComplex.homologySSFiltration] at *
        erw [Category.assoc, Subobject.ofLE_arrow (FC.homologySSFiltration.mono s k)]
        change factorThruImageSubobject gen_s1 ≫ (imageSubobject gen_s1).arrow =
          (Subobject.ofLE I_s1 I_s hle ≫ factorThruImageSubobject gen_s) ≫
            (imageSubobject gen_s).arrow
        rw [imageSubobject_arrow_comp, Category.assoc, imageSubobject_arrow_comp]
        exact h_gen_factor
      dsimp only [FilteredComplex.homologySSFiltration] at h_fTI_ofLE ⊢
      rw [← Category.assoc, h_fTI_ofLE, Category.assoc]
      change Subobject.ofLE I_s1 I_s hle ≫ (e_Fs ≫ inv_Fs) = 0
      rw [h_inv_Fs]
      change Subobject.ofLE I_s1 I_s hle ≫ (Is_to_kerZ ≫ e_Z ≫ πLHS) = 0
      rw [← Category.assoc, ← Category.assoc]
      suffices h_zero : (Subobject.ofLE I_s1 I_s hle ≫ Is_to_kerZ) ≫ e_Z = 0 by
        rw [h_zero, zero_comp]
      apply (cancel_mono (imageSubobject (kerZ.arrow ≫ πV)).arrow).mp
      rw [Category.assoc, imageSubobject_arrow_comp, zero_comp]
      simp only [Category.assoc]
      conv_lhs => rw [← Category.assoc Is_to_kerZ kerZ.arrow πV,
                       h_Is_to_kerZ]
      have h_I_s1_factors : (FC.fil (s + 1) k).Factors (I_s1.arrow ≫ eqToHom e_deg_inv) := by
        have h_le_s1 : I_s1 ≤ FC.fil (s + 1) (k + 1 - 1) := inf_le_right
        have h_arrow_s1 : I_s1.arrow = Subobject.ofLE I_s1 (FC.fil (s + 1) (k + 1 - 1)) h_le_s1 ≫
            (FC.fil (s + 1) (k + 1 - 1)).arrow := (Subobject.ofLE_arrow h_le_s1).symm
        rw [h_arrow_s1, Category.assoc]
        have h_transport_s1 : (FC.fil (s + 1) (k + 1 - 1)).arrow ≫ eqToHom e_deg_inv =
            eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil (s + 1) j))
              (show k + 1 - 1 = k by omega)) ≫ (FC.fil (s + 1) k).arrow := by
          have : ∀ (a b : ℤ) (h : a = b),
              (FC.fil (s + 1) a).arrow ≫ eqToHom (congr_arg FC.A h) =
              eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil (s + 1) j)) h) ≫
              (FC.fil (s + 1) b).arrow := by
            intro a b h; subst h; simp
          exact this (k + 1 - 1) k (by omega)
        rw [h_transport_s1, ← Category.assoc]
        exact Subobject.factors_comp_arrow _
      let lift_s1' := Subobject.factorThru (FC.fil (s + 1) k) (I_s1.arrow ≫ eqToHom e_deg_inv)
          h_I_s1_factors
      have h_lift_s1' : lift_s1' ≫ (FC.fil (s + 1) k).arrow =
          I_s1.arrow ≫ eqToHom e_deg_inv :=
        Subobject.factorThru_arrow _ _ _
      have h_ofLE_Is_to_fil :
          Subobject.ofLE I_s1 I_s hle ≫ Is_to_fil = lift_s1' ≫ ι_fil := by
        apply (cancel_mono (FC.fil s k).arrow).mp
        rw [Category.assoc, h_Is_to_fil_eq]
        rw [← Category.assoc, Subobject.ofLE_arrow hle]
        rw [Category.assoc,
          show ι_fil ≫ (FC.fil s k).arrow = (FC.fil (s + 1) k).arrow
            from Subobject.ofLE_arrow (FC.fil_anti s k)]
        exact h_lift_s1'.symm
      rw [← Category.assoc, h_ofLE_Is_to_fil, Category.assoc]
      rw [show ι_fil ≫ πV = 0 from cokernel.condition ι_fil, comp_zero]
    let inv := cokernel.desc _ inv_Fs h_inv_kills_Fs1
    have h_hom_inv : fwd ≫ inv = 𝟙 _ := by
      apply (cancel_epi πLHS).mp
      dsimp only [FilteredComplex.toSSData, FilteredComplex.boundarySubobject,
        FilteredComplex.cycleSubobject] at *
      erw [Category.comp_id]
      have h_πLHS_fwd : πLHS ≫ fwd = fwd_Z := cokernel.π_desc _ _ _
      erw [← Category.assoc, h_πLHS_fwd]
      apply (cancel_epi e_Z).mp
      erw [← Category.assoc, h_fwd_Z]
      change (φ_to_Fs ≫ πRHS) ≫ inv = e_Z ≫ πLHS
      rw [Category.assoc]
      have h_πRHS_inv : πRHS ≫ inv = inv_Fs := cokernel.π_desc _ _ _
      erw [h_πRHS_inv]
      have h_compat : kerZ_to_Is ≫ e_Fs = φ_to_Fs := by
        apply (cancel_mono (imageSubobject gen_s).arrow).mp
        rw [Category.assoc, imageSubobject_arrow_comp]
        rw [h_func, h_φ_to_Fs]
      erw [← h_compat, Category.assoc, h_inv_Fs]
      change kerZ_to_Is ≫ (Is_to_kerZ ≫ e_Z ≫ πLHS) = e_Z ≫ πLHS
      have h_round : kerZ_to_Is ≫ Is_to_kerZ = 𝟙 _ := by
        apply (cancel_mono kerZ.arrow).mp
        rw [Category.id_comp, Category.assoc, h_Is_to_kerZ]
        apply (cancel_mono (FC.fil s k).arrow).mp
        rw [Category.assoc, h_Is_to_fil_eq]
        rw [← Category.assoc, h_kerZ_to_Is]
        change (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) ≫ eqToHom e_deg_inv =
          kerZ.arrow ≫ (FC.fil s k).arrow
        rw [Category.assoc, Category.assoc]
        congr 1
        simp [eqToHom_trans]
      rw [← Category.assoc, ← Category.assoc, h_round, Category.id_comp]
    have h_inv_hom : inv ≫ fwd = 𝟙 _ := by
      apply (cancel_epi πRHS).mp
      dsimp only [FilteredComplex.homologySSFiltration] at *
      rw [Category.comp_id, ← Category.assoc]
      have h_πRHS_inv' : πRHS ≫ inv = inv_Fs := cokernel.π_desc _ _ _
      erw [h_πRHS_inv']
      apply (cancel_epi e_Fs).mp
      rw [← Category.assoc, h_inv_Fs]
      change (Is_to_kerZ ≫ e_Z ≫ πLHS) ≫ fwd = e_Fs ≫ πRHS
      rw [Category.assoc, Category.assoc]
      have h_πLHS_fwd' : πLHS ≫ fwd = fwd_Z := cokernel.π_desc _ _ _
      erw [h_πLHS_fwd', h_fwd_Z]
      change Is_to_kerZ ≫ (φ_to_Fs ≫ πRHS) = e_Fs ≫ πRHS
      rw [← Category.assoc]
      congr 1
      apply (cancel_mono (imageSubobject gen_s).arrow).mp
      rw [Category.assoc, h_φ_to_Fs, imageSubobject_arrow_comp]
      change Is_to_kerZ ≫ (S.liftCycles φ_to_X2 h_lift ≫ S.homologyπ) =
        S.liftCycles I_s.arrow h_zero_s ≫ S.homologyπ
      rw [← Category.assoc]
      congr 1
      apply (cancel_mono S.iCycles).mp
      rw [Category.assoc, S.liftCycles_i, S.liftCycles_i]
      change Is_to_kerZ ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) = I_s.arrow
      rw [show Is_to_kerZ ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) =
          (Is_to_kerZ ≫ kerZ.arrow) ≫ (FC.fil s k).arrow ≫ eqToHom e_deg by
        simp only [Category.assoc]]
      rw [h_Is_to_kerZ, show Is_to_fil ≫ (FC.fil s k).arrow ≫ eqToHom e_deg =
          (Is_to_fil ≫ (FC.fil s k).arrow) ≫ eqToHom e_deg by rw [Category.assoc]]
      rw [h_Is_to_fil_eq, Category.assoc]
      simp [eqToHom_trans]
    exact ⟨fwd, inv, h_hom_inv, h_inv_hom⟩

end KIP126.Core.SpectralSequence
