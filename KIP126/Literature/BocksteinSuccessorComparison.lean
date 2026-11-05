module

import KIP126.SpectralSequence

/-! Successor-page comparison for the spectral-sequence quotient pages. -/

namespace KIP126.Literature.Paper38Successor

open CategoryTheory CategoryTheory.Limits
open KIP126.Core KIP126.Core.SpectralSequence

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} [AddCommGroup ι] [DecidableEq ι]

noncomputable section

private def leftMap {E F : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E F) (r : ℤ) (k : ι) :
    (E.pageShortComplex r (k - E.diffDeg r)).X₁ ⟶
      (F.pageShortComplex r (k - F.diffDeg r)).X₁ :=
  f.pageMap r (k - E.diffDeg r) ≫ eqToHom (by
    change F.Page r (k - E.diffDeg r) = F.Page r (k - F.diffDeg r)
    rw [f.diffDeg_eq])

private def middleMap {E F : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E F) (r : ℤ) (k : ι) :
    (E.pageShortComplex r (k - E.diffDeg r)).X₂ ⟶
      (F.pageShortComplex r (k - F.diffDeg r)).X₂ :=
  f.pageMap r (k - E.diffDeg r + E.diffDeg r) ≫ eqToHom (by
    change F.Page r (k - E.diffDeg r + E.diffDeg r) =
      F.Page r (k - F.diffDeg r + F.diffDeg r)
    rw [f.diffDeg_eq])

private def rightMap {E F : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E F) (r : ℤ) (k : ι) :
    (E.pageShortComplex r (k - E.diffDeg r)).X₃ ⟶
      (F.pageShortComplex r (k - F.diffDeg r)).X₃ :=
  f.pageMap r (k - E.diffDeg r + E.diffDeg r + E.diffDeg r) ≫ eqToHom (by
    change F.Page r (k - E.diffDeg r + E.diffDeg r + E.diffDeg r) =
      F.Page r (k - F.diffDeg r + F.diffDeg r + F.diffDeg r)
    rw [f.diffDeg_eq])

private theorem left_middle_comm {E F : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E F) (r : ℤ) (k : ι) :
    leftMap f r k ≫ (F.pageShortComplex r (k - F.diffDeg r)).f =
      (E.pageShortComplex r (k - E.diffDeg r)).f ≫ middleMap f r k := by
  simp only [leftMap, middleMap, pageShortComplex]
  have hleft : k - E.diffDeg r = k - F.diffDeg r := by rw [f.diffDeg_eq]
  rw [Category.assoc,
    ← eqToHom_naturality (fun j => F.d r j) hleft,
    ← Category.assoc, f.pageMap_comm_d r (k - E.diffDeg r)]
  simp [Category.assoc, f.diffDeg_eq]

private theorem middle_right_comm {E F : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E F) (r : ℤ) (k : ι) :
    middleMap f r k ≫ (F.pageShortComplex r (k - F.diffDeg r)).g =
      (E.pageShortComplex r (k - E.diffDeg r)).g ≫ rightMap f r k := by
  simp only [middleMap, rightMap, pageShortComplex]
  have hmiddle : k - E.diffDeg r + E.diffDeg r =
      k - F.diffDeg r + F.diffDeg r := by simp
  rw [Category.assoc,
    ← eqToHom_naturality (fun j => F.d r j) hmiddle,
    ← Category.assoc, f.pageMap_comm_d r (k - E.diffDeg r + E.diffDeg r)]
  simp [Category.assoc, f.diffDeg_eq]

/-- The actual centered complex map, using the same quotient maps on every vertex. -/
private def centeredComplexMap {E F : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E F) (r : ℤ) (k : ι) :
    E.pageShortComplex r (k - E.diffDeg r) ⟶
      F.pageShortComplex r (k - F.diffDeg r) where
  τ₁ := leftMap f r k
  τ₂ := middleMap f r k
  τ₃ := rightMap f r k
  comm₁₂ := left_middle_comm f r k
  comm₂₃ := middle_right_comm f r k

private def centeredHomologyMap {E F : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E F) (r : ℤ) (k : ι) :
    (E.pageShortComplex r (k - E.diffDeg r)).homology ⟶
      (F.pageShortComplex r (k - F.diffDeg r)).homology :=
  ShortComplex.homologyMap (centeredComplexMap f r k)

/-- The homology map is characterized on all actual cycle representatives. -/
private theorem homology_representative_naturality {E F : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E F) (r : ℤ) (k : ι) {A : C}
    (a : A ⟶ (E.pageShortComplex r (k - E.diffDeg r)).X₂)
    (ha : a ≫ (E.pageShortComplex r (k - E.diffDeg r)).g = 0) :
    (E.pageShortComplex r (k - E.diffDeg r)).liftCycles a ha ≫
      (E.pageShortComplex r (k - E.diffDeg r)).homologyπ ≫
      centeredHomologyMap f r k =
    (F.pageShortComplex r (k - F.diffDeg r)).liftCycles
      (a ≫ middleMap f r k)
      (by rw [Category.assoc, middle_right_comm, ← Category.assoc, ha, zero_comp]) ≫
      (F.pageShortComplex r (k - F.diffDeg r)).homologyπ := by
  rw [centeredHomologyMap, ShortComplex.homologyπ_naturality,
    ← Category.assoc, ShortComplex.liftCycles_comp_cyclesMap]
  rfl


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem comp_zero_of_image_le_kernel
    {A B D : C} (a : A ⟶ B) (b : B ⟶ D)
    (h : imageSubobject a ≤ kernelSubobject b) : a ≫ b = 0 := by
  rw [← imageSubobject_arrow_comp a, Category.assoc,
    show (imageSubobject a).arrow =
      Subobject.ofLE _ _ h ≫ (kernelSubobject b).arrow
      from (Subobject.ofLE_arrow h).symm,
    Category.assoc, kernelSubobject_arrow_comp, comp_zero, comp_zero]

/-- The index displayed at the middle vertex of the actual centered complex. -/
private def middleIndex (E : SpectralSequence C ι) (r : ℤ) (k : ι) : ι :=
  k - E.diffDeg r + E.diffDeg r

/-- A genuine next-stage cycle, viewed in the preceding page. -/
private def nextRepresentative (E : SpectralSequence C ι) (r : ℤ) (k : ι) :
    Subobject.underlying.obj ((E.ssData (middleIndex E r k)).Z
      ↑((r - E.r₀).toNat + 1)) ⟶
      (E.pageShortComplex r (k - E.diffDeg r)).X₂ :=
  Subobject.ofLE _ _ ((E.ssData (middleIndex E r k)).Z_anti
    (by exact_mod_cast Nat.le_succ (r - E.r₀).toNat)) ≫
    (E.ssData (middleIndex E r k)).pageπ ↑(r - E.r₀).toNat

private theorem nextRepresentative_cycle (E : SpectralSequence C ι)
    (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    nextRepresentative E r k ≫
      (E.pageShortComplex r (k - E.diffDeg r)).g = 0 := by
  exact comp_zero_of_image_le_kernel _ _ (by
    change imageSubobject (nextRepresentative E r k) ≤
      kernelSubobject (E.d r (middleIndex E r k))
    rw [E.Z_succ r (middleIndex E r k) hr]
    exact le_refl _)

/-- Map a next-cycle to its homology class. -/
private def nextCycleClass (E : SpectralSequence C ι)
    (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    Subobject.underlying.obj ((E.ssData (middleIndex E r k)).Z
      ↑((r - E.r₀).toNat + 1)) ⟶
      (E.pageShortComplex r (k - E.diffDeg r)).homology :=
  (E.pageShortComplex r (k - E.diffDeg r)).liftCycles
    (nextRepresentative E r k) (nextRepresentative_cycle E r k hr) ≫
    (E.pageShortComplex r (k - E.diffDeg r)).homologyπ

private theorem zero_of_image_eq {A A' B D : C}
    (a : A ⟶ B) (a' : A' ⟶ B) (b : B ⟶ D)
    (h : imageSubobject a = imageSubobject a') (hz : a' ≫ b = 0) :
    a ≫ b = 0 := by
  rw [← imageSubobject_arrow_comp a, Category.assoc,
    show (imageSubobject a).arrow =
      Subobject.ofLE _ _ h.le ≫ (imageSubobject a').arrow from
      (Subobject.ofLE_arrow h.le).symm,
    Category.assoc, imageSubobject_arrow_comp_eq_zero hz, comp_zero, comp_zero]

private theorem nextCycleClass_boundary_zero (E : SpectralSequence C ι)
    (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    Subobject.ofLE ((E.ssData (middleIndex E r k)).B ↑((r - E.r₀).toNat + 1))
      ((E.ssData (middleIndex E r k)).Z ↑((r - E.r₀).toNat + 1))
      ((E.ssData (middleIndex E r k)).B_le_Z _) ≫
      nextCycleClass E r k hr = 0 := by
  apply (cancel_mono (E.pageShortComplex r (k - E.diffDeg r)).homologyι).mp
  rw [zero_comp, Category.assoc, nextCycleClass, Category.assoc,
    ShortComplex.homology_π_ι, ShortComplex.liftCycles_i_assoc, nextRepresentative,
    ← Category.assoc, ← Category.assoc, Subobject.ofLE_comp_ofLE]
  exact zero_of_image_eq _ (E.pageShortComplex r (k - E.diffDeg r)).f _
    (E.B_succ r (k - E.diffDeg r) hr).symm
    (E.pageShortComplex r (k - E.diffDeg r)).f_pOpcycles

/-- Explicit canonical successor map on the actual quotient Z_(n+1)/B_(n+1). -/
private def rawSuccessorMap (E : SpectralSequence C ι)
    (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    (E.ssData (middleIndex E r k)).page ↑((r - E.r₀).toNat + 1) ⟶
      (E.pageShortComplex r (k - E.diffDeg r)).homology :=
  cokernel.desc _ (nextCycleClass E r k hr) (nextCycleClass_boundary_zero E r k hr)

/-- The same explicit successor map with the displayed page and grading transports. -/
private def explicitSuccessorMap (E : SpectralSequence C ι)
    (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    E.Page (r + 1) k ⟶ (E.pageShortComplex r (k - E.diffDeg r)).homology :=
  eqToHom (by
    change (E.ssData k).page ↑((r + 1 - E.r₀).toNat) =
      (E.ssData (middleIndex E r k)).page ↑((r - E.r₀).toNat + 1)
    simp only [middleIndex, sub_add_cancel]
    congr 2
    omega) ≫ rawSuccessorMap E r k hr


/-- Restrict the same ambient morphism to the next cycle stage, including both
page-numbering and centered-degree transports. -/
private def nextCycleMap {E F : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E F) (r : ℤ) (k : ι) :
    Subobject.underlying.obj ((E.ssData (middleIndex E r k)).Z
      ↑((r - E.r₀).toNat + 1)) ⟶
    Subobject.underlying.obj ((F.ssData (middleIndex F r k)).Z
      ↑((r - F.r₀).toNat + 1)) :=
  f.toSSDataMorphism.cycleMap (middleIndex E r k) ↑((r - E.r₀).toNat + 1) ≫
    eqToHom (by
      rw [f.r₀_eq]
      exact congrArg (fun j => Subobject.underlying.obj
        ((F.ssData j).Z ↑((r - F.r₀).toNat + 1)))
        ((sub_add_cancel k (E.diffDeg r)).trans (sub_add_cancel k (F.diffDeg r)).symm))

private theorem nextRepresentative_naturality {E F : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E F) (r : ℤ) (k : ι) :
    nextRepresentative E r k ≫ middleMap f r k =
      nextCycleMap f r k ≫ nextRepresentative F r k := by
  obtain ⟨⟨r₀, D, δ, d⟩, hd, hZ, hB⟩ := E
  obtain ⟨⟨r₀', D', δ', d'⟩, hd', hZ', hB'⟩ := F
  have h₀ := f.r₀_eq
  have hδ := f.diffDeg_eq
  dsimp at h₀ hδ
  subst r₀'
  subst δ'
  simp only [nextRepresentative, middleMap, nextCycleMap, middleIndex,
    SpectralSequenceMorphism.pageMap, PreSSMorphism.pageMap,
    SpectralSequenceMorphism.toPreSSMorphism, SSDataMorphism.pageMapAt,
    eqToHom_refl, Category.comp_id]
  rw [Category.assoc, SSDataMorphism.pageπ_pageMap,
    ← Category.assoc, SSDataMorphism.cycleMap_ofLE, Category.assoc]
  exact_mod_cast Nat.le_succ (r - r₀).toNat

private theorem nextCycleClass_naturality {E F : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E F) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    nextCycleClass E r k hr ≫ centeredHomologyMap f r k =
      nextCycleMap f r k ≫
        nextCycleClass F r k (by rw [← f.r₀_eq]; exact hr) := by
  simp only [nextCycleClass, Category.assoc]
  trans (F.pageShortComplex r (k - F.diffDeg r)).liftCycles
      (nextRepresentative E r k ≫ middleMap f r k)
      (by rw [Category.assoc, middle_right_comm, ← Category.assoc,
        nextRepresentative_cycle E r k hr, zero_comp]) ≫
      (F.pageShortComplex r (k - F.diffDeg r)).homologyπ
  · exact homology_representative_naturality f r k _ _
  · calc
      _ = (nextCycleMap f r k ≫
          (F.pageShortComplex r (k - F.diffDeg r)).liftCycles
            (nextRepresentative F r k) (nextRepresentative_cycle F r k
              (by rw [← f.r₀_eq]; exact hr))) ≫
          (F.pageShortComplex r (k - F.diffDeg r)).homologyπ := by
        apply congrArg (fun z => z ≫ (F.pageShortComplex r (k - F.diffDeg r)).homologyπ)
        apply (cancel_mono (F.pageShortComplex r (k - F.diffDeg r)).iCycles).mp
        simp only [Category.assoc, ShortComplex.liftCycles_i]
        exact nextRepresentative_naturality f r k
      _ = _ := Category.assoc _ _ _

private def nextPageMap {E F : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E F) (r : ℤ) (k : ι) :
    (E.ssData (middleIndex E r k)).page ↑((r - E.r₀).toNat + 1) ⟶
      (F.ssData (middleIndex F r k)).page ↑((r - F.r₀).toNat + 1) :=
  f.toSSDataMorphism.pageMap (middleIndex E r k) ↑((r - E.r₀).toNat + 1) ≫
    eqToHom (by
      rw [f.r₀_eq]
      exact congrArg (fun j => (F.ssData j).page ↑((r - F.r₀).toNat + 1))
        ((sub_add_cancel k (E.diffDeg r)).trans (sub_add_cancel k (F.diffDeg r)).symm))

private theorem nextPageMap_π {E F : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E F) (r : ℤ) (k : ι) :
    (E.ssData (middleIndex E r k)).pageπ ↑((r - E.r₀).toNat + 1) ≫
      nextPageMap f r k =
    nextCycleMap f r k ≫
      (F.ssData (middleIndex F r k)).pageπ ↑((r - F.r₀).toNat + 1) := by
  obtain ⟨⟨r₀, D, δ, d⟩, hd, hZ, hB⟩ := E
  obtain ⟨⟨r₀', D', δ', d'⟩, hd', hZ', hB'⟩ := F
  have h₀ := f.r₀_eq
  have hδ := f.diffDeg_eq
  dsimp at h₀ hδ
  subst r₀'
  subst δ'
  simpa only [nextPageMap, nextCycleMap, middleIndex,
    eqToHom_refl, Category.comp_id] using
    f.toSSDataMorphism.pageπ_pageMap (k - δ r + δ r) ↑((r - r₀).toNat + 1)

private theorem rawSuccessorMap_π (E : SpectralSequence C ι)
    (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    (E.ssData (middleIndex E r k)).pageπ ↑((r - E.r₀).toNat + 1) ≫
      rawSuccessorMap E r k hr = nextCycleClass E r k hr :=
  cokernel.π_desc _ _ _

private theorem rawSuccessorMap_naturality {E F : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E F) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    rawSuccessorMap E r k hr ≫ centeredHomologyMap f r k =
      nextPageMap f r k ≫ rawSuccessorMap F r k (by rw [← f.r₀_eq]; exact hr) := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE
    ((E.ssData (middleIndex E r k)).B ↑((r - E.r₀).toNat + 1))
    ((E.ssData (middleIndex E r k)).Z ↑((r - E.r₀).toNat + 1))
    ((E.ssData (middleIndex E r k)).B_le_Z _)))).mp
  change (E.ssData (middleIndex E r k)).pageπ _ ≫ _ =
    (E.ssData (middleIndex E r k)).pageπ _ ≫ _
  rw [← Category.assoc, rawSuccessorMap_π, nextCycleClass_naturality,
    ← Category.assoc, nextPageMap_π, Category.assoc, rawSuccessorMap_π]

private theorem pageMap_transport {D D' : ι → SSData C}
    (f : SSDataMorphism ι D D') (j k : ι) (n m : WithTop ℕ)
    (hj : j = k) (hn : n = m) :
    eqToHom (by rw [hj, hn]) ≫ f.pageMap k m =
      f.pageMap j n ≫ eqToHom (by rw [hj, hn]) := by
  subst k
  subst m
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

set_option maxHeartbeats 400000 in
/-- Actual successor square.  Both horizontal maps are induced from the same
ambient SSData morphism; both vertical maps use actual cycle representatives. -/
private theorem explicitSuccessorMap_naturality {E F : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E F) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    explicitSuccessorMap E r k hr ≫ centeredHomologyMap f r k =
      f.pageMap (r + 1) k ≫
        explicitSuccessorMap F r k (by rw [← f.r₀_eq]; exact hr) := by
  have hn : (r + 1 - E.r₀).toNat = (r - E.r₀).toNat + 1 := by omega
  simp only [explicitSuccessorMap, Category.assoc]
  rw [rawSuccessorMap_naturality]
  simp only [nextPageMap, SpectralSequenceMorphism.pageMap,
    PreSSMorphism.pageMap, SpectralSequenceMorphism.toPreSSMorphism,
    SSDataMorphism.pageMapAt, Category.assoc]
  have htr := pageMap_transport f.toSSDataMorphism k (middleIndex E r k)
    ↑((r + 1 - E.r₀).toNat) ↑((r - E.r₀).toNat + 1)
    (sub_add_cancel k (E.diffDeg r)).symm (by rw [hn])
  rw [← Category.assoc, htr]
  simp only [Category.assoc, eqToHom_trans_assoc]


/-- The representative construction agrees with the fixed canonical successor
isomorphism by the computation formula. -/
private theorem explicitSuccessorMap_eq_pageHomologyIso
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    explicitSuccessorMap E r k hr = (pageHomologyIso E r k hr).hom := by
  let D := E.ssData (middleIndex E r k)
  let n := (r - E.r₀).toNat
  have hp : D.page ↑(n + 1) = E.Page (r + 1) k := by
    change (E.ssData (middleIndex E r k)).page ↑(n + 1) =
      (E.ssData k).page ↑((r + 1 - E.r₀).toNat)
    have hn : (r + 1 - E.r₀).toNat = n + 1 := by dsimp [n]; omega
    simp only [middleIndex, sub_add_cancel, hn]
  haveI : Epi (D.pageπ ↑(n + 1)) := by
    dsimp only [SSData.pageπ]
    infer_instance
  apply (cancel_epi (D.pageπ ↑(n + 1) ≫ eqToHom hp)).mp
  apply (cancel_mono (E.pageShortComplex r (k - E.diffDeg r)).homologyι).mp
  simp only [Category.assoc]
  have hrep := pageHomologyIso_representative E r k hr
  change D.pageπ ↑(n + 1) ≫ eqToHom hp ≫
      (pageHomologyIso E r k hr).hom ≫
      (E.pageShortComplex r (k - E.diffDeg r)).homologyι = _ at hrep
  rw [hrep]
  simp only [explicitSuccessorMap, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, rawSuccessorMap_π]
  simp only [nextCycleClass, Category.assoc, ShortComplex.homology_π_ι,
    ShortComplex.liftCycles_i_assoc, nextRepresentative]
  rfl

private theorem explicitSuccessorMap_isIso
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    IsIso (explicitSuccessorMap E r k hr) := by
  rw [explicitSuccessorMap_eq_pageHomologyIso]
  infer_instance

/-- Every ordinary spectral-sequence morphism respects the fixed canonical
successor isomorphisms, with the actual homology map of its same page maps. -/
private theorem canonicalSuccessor_naturality {E F : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E F) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    (pageHomologyIso E r k hr).hom ≫ centeredHomologyMap f r k =
      f.pageMap (r + 1) k ≫
        (pageHomologyIso F r k (by rw [← f.r₀_eq]; exact hr)).hom := by
  rw [← explicitSuccessorMap_eq_pageHomologyIso,
    ← explicitSuccessorMap_eq_pageHomologyIso]
  exact explicitSuccessorMap_naturality f r k hr

end
end KIP126.Literature.Paper38Successor
