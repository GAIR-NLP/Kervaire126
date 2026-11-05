module

import all KIP126.Literature.BocksteinSuccessorComparison

/-! Canonical successor naturality from differential squares on valid pages. -/

namespace KIP126.Literature.Paper38OriginalSuccessor
open CategoryTheory CategoryTheory.Limits
open KIP126.Core KIP126.Core.SpectralSequence
open KIP126.Literature.Paper38Successor
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- A map of the original SSData with differential squares only on valid pages. -/
private structure FromFirstMorphism (E F : SpectralSequence C ι)
    extends SSDataMorphism ι E.ssData F.ssData where
  r₀_eq : E.r₀ = F.r₀
  diffDeg_eq : E.diffDeg = F.diffDeg
  comm_d : ∀ (r : ℤ), E.r₀ ≤ r → ∀ p : ι,
    let g := toSSDataMorphism
    g.pageMapAt (E := E.toPreSS) (E' := F.toPreSS) r₀_eq r p ≫ F.d r p =
      E.d r p ≫ g.pageMapAt (E := E.toPreSS) (E' := F.toPreSS) r₀_eq r (p+E.diffDeg r) ≫
        eqToHom (by rw [diffDeg_eq])

private def FromFirstMorphism.pageMap {E F : SpectralSequence C ι}
    (f : FromFirstMorphism E F) (r : ℤ) (p : ι) :=
  f.toSSDataMorphism.pageMapAt (E := E.toPreSS) (E' := F.toPreSS) f.r₀_eq r p

private theorem FromFirstMorphism.pageMap_comm_d {E F : SpectralSequence C ι}
    (f : FromFirstMorphism E F) (r : ℤ) (hr : E.r₀ ≤ r) (p : ι) :
    f.pageMap r p ≫ F.d r p = E.d r p ≫ f.pageMap r (p+E.diffDeg r) ≫
      eqToHom (by rw [f.diffDeg_eq]) := f.comm_d r hr p

private def leftMap {E F : SpectralSequence C ι}
    (f : FromFirstMorphism E F) (r : ℤ) (k : ι) :
    (E.pageShortComplex r (k - E.diffDeg r)).X₁ ⟶
      (F.pageShortComplex r (k - F.diffDeg r)).X₁ :=
  f.pageMap r (k - E.diffDeg r) ≫ eqToHom (by
    change F.Page r (k - E.diffDeg r) = F.Page r (k - F.diffDeg r)
    rw [f.diffDeg_eq])

private def middleMap {E F : SpectralSequence C ι}
    (f : FromFirstMorphism E F) (r : ℤ) (k : ι) :
    (E.pageShortComplex r (k - E.diffDeg r)).X₂ ⟶
      (F.pageShortComplex r (k - F.diffDeg r)).X₂ :=
  f.pageMap r (k - E.diffDeg r + E.diffDeg r) ≫ eqToHom (by
    change F.Page r (k - E.diffDeg r + E.diffDeg r) =
      F.Page r (k - F.diffDeg r + F.diffDeg r)
    rw [f.diffDeg_eq])

private def rightMap {E F : SpectralSequence C ι}
    (f : FromFirstMorphism E F) (r : ℤ) (k : ι) :
    (E.pageShortComplex r (k - E.diffDeg r)).X₃ ⟶
      (F.pageShortComplex r (k - F.diffDeg r)).X₃ :=
  f.pageMap r (k - E.diffDeg r + E.diffDeg r + E.diffDeg r) ≫ eqToHom (by
    change F.Page r (k - E.diffDeg r + E.diffDeg r + E.diffDeg r) =
      F.Page r (k - F.diffDeg r + F.diffDeg r + F.diffDeg r)
    rw [f.diffDeg_eq])

private theorem left_middle_comm {E F : SpectralSequence C ι}
    (f : FromFirstMorphism E F) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    leftMap f r k ≫ (F.pageShortComplex r (k - F.diffDeg r)).f =
      (E.pageShortComplex r (k - E.diffDeg r)).f ≫ middleMap f r k := by
  simp only [leftMap, middleMap, pageShortComplex]
  have hleft : k - E.diffDeg r = k - F.diffDeg r := by rw [f.diffDeg_eq]
  rw [Category.assoc,
    ← eqToHom_naturality (fun j => F.d r j) hleft,
    ← Category.assoc, f.pageMap_comm_d r hr (k - E.diffDeg r)]
  simp only [Category.assoc, eqToHom_trans]

private theorem middle_right_comm {E F : SpectralSequence C ι}
    (f : FromFirstMorphism E F) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    middleMap f r k ≫ (F.pageShortComplex r (k - F.diffDeg r)).g =
      (E.pageShortComplex r (k - E.diffDeg r)).g ≫ rightMap f r k := by
  simp only [middleMap, rightMap, pageShortComplex]
  have hmiddle : k - E.diffDeg r + E.diffDeg r =
      k - F.diffDeg r + F.diffDeg r := by simp
  rw [Category.assoc,
    ← eqToHom_naturality (fun j => F.d r j) hmiddle,
    ← Category.assoc, f.pageMap_comm_d r hr (k - E.diffDeg r + E.diffDeg r)]
  simp only [Category.assoc, eqToHom_trans]

/-- The actual centered complex map, using the same quotient maps on every vertex. -/

private def centeredComplexMap {E F : SpectralSequence C ι}
    (f : FromFirstMorphism E F) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    E.pageShortComplex r (k - E.diffDeg r) ⟶
      F.pageShortComplex r (k - F.diffDeg r) where
  τ₁ := leftMap f r k
  τ₂ := middleMap f r k
  τ₃ := rightMap f r k
  comm₁₂ := left_middle_comm f r k hr
  comm₂₃ := middle_right_comm f r k hr

private def centeredHomologyMap {E F : SpectralSequence C ι}
    (f : FromFirstMorphism E F) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    (E.pageShortComplex r (k - E.diffDeg r)).homology ⟶
      (F.pageShortComplex r (k - F.diffDeg r)).homology :=
  ShortComplex.homologyMap (centeredComplexMap f r k hr)

/-- The homology map is characterized on all actual cycle representatives. -/

private theorem homology_representative_naturality {E F : SpectralSequence C ι}
    (f : FromFirstMorphism E F) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) {A : C}
    (a : A ⟶ (E.pageShortComplex r (k - E.diffDeg r)).X₂)
    (ha : a ≫ (E.pageShortComplex r (k - E.diffDeg r)).g = 0) :
    (E.pageShortComplex r (k - E.diffDeg r)).liftCycles a ha ≫
      (E.pageShortComplex r (k - E.diffDeg r)).homologyπ ≫
      centeredHomologyMap f r k hr =
    (F.pageShortComplex r (k - F.diffDeg r)).liftCycles
      (a ≫ middleMap f r k)
      (by rw [Category.assoc, middle_right_comm f r k hr, ← Category.assoc, ha, zero_comp]) ≫
      (F.pageShortComplex r (k - F.diffDeg r)).homologyπ := by
  rw [centeredHomologyMap, ShortComplex.homologyπ_naturality,
    ← Category.assoc, ShortComplex.liftCycles_comp_cyclesMap]
  rfl

private def nextCycleMap {E F : SpectralSequence C ι}
    (f : FromFirstMorphism E F) (r : ℤ) (k : ι) :
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
    (f : FromFirstMorphism E F) (r : ℤ) (k : ι) :
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
    FromFirstMorphism.pageMap, SSDataMorphism.pageMapAt,
    eqToHom_refl, Category.comp_id]
  rw [Category.assoc, SSDataMorphism.pageπ_pageMap,
    ← Category.assoc, SSDataMorphism.cycleMap_ofLE, Category.assoc]
  exact_mod_cast Nat.le_succ (r - r₀).toNat

private theorem nextCycleClass_naturality {E F : SpectralSequence C ι}
    (f : FromFirstMorphism E F) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    nextCycleClass E r k hr ≫ centeredHomologyMap f r k hr =
      nextCycleMap f r k ≫
        nextCycleClass F r k (by rw [← f.r₀_eq]; exact hr) := by
  simp only [nextCycleClass, Category.assoc]
  trans (F.pageShortComplex r (k - F.diffDeg r)).liftCycles
      (nextRepresentative E r k ≫ middleMap f r k)
      (by rw [Category.assoc, middle_right_comm f r k hr, ← Category.assoc,
        nextRepresentative_cycle E r k hr, zero_comp]) ≫
      (F.pageShortComplex r (k - F.diffDeg r)).homologyπ
  · exact homology_representative_naturality f r k hr _ _
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
    (f : FromFirstMorphism E F) (r : ℤ) (k : ι) :
    (E.ssData (middleIndex E r k)).page ↑((r - E.r₀).toNat + 1) ⟶
      (F.ssData (middleIndex F r k)).page ↑((r - F.r₀).toNat + 1) :=
  f.toSSDataMorphism.pageMap (middleIndex E r k) ↑((r - E.r₀).toNat + 1) ≫
    eqToHom (by
      rw [f.r₀_eq]
      exact congrArg (fun j => (F.ssData j).page ↑((r - F.r₀).toNat + 1))
        ((sub_add_cancel k (E.diffDeg r)).trans (sub_add_cancel k (F.diffDeg r)).symm))

private theorem nextPageMap_π {E F : SpectralSequence C ι}
    (f : FromFirstMorphism E F) (r : ℤ) (k : ι) :
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

private theorem rawSuccessorMap_naturality {E F : SpectralSequence C ι}
    (f : FromFirstMorphism E F) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    rawSuccessorMap E r k hr ≫ centeredHomologyMap f r k hr =
      nextPageMap f r k ≫ rawSuccessorMap F r k (by rw [← f.r₀_eq]; exact hr) := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE
    ((E.ssData (middleIndex E r k)).B ↑((r - E.r₀).toNat + 1))
    ((E.ssData (middleIndex E r k)).Z ↑((r - E.r₀).toNat + 1))
    ((E.ssData (middleIndex E r k)).B_le_Z _)))).mp
  change (E.ssData (middleIndex E r k)).pageπ _ ≫ _ =
    (E.ssData (middleIndex E r k)).pageπ _ ≫ _
  rw [← Category.assoc, rawSuccessorMap_π, nextCycleClass_naturality,
    ← Category.assoc, nextPageMap_π, Category.assoc, rawSuccessorMap_π]

private theorem explicitSuccessorMap_naturality {E F : SpectralSequence C ι}
    (f : FromFirstMorphism E F) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    explicitSuccessorMap E r k hr ≫ centeredHomologyMap f r k hr =
      f.pageMap (r + 1) k ≫
        explicitSuccessorMap F r k (by rw [← f.r₀_eq]; exact hr) := by
  have hn : (r + 1 - E.r₀).toNat = (r - E.r₀).toNat + 1 := by omega
  simp only [explicitSuccessorMap, Category.assoc]
  rw [rawSuccessorMap_naturality]
  simp only [nextPageMap, FromFirstMorphism.pageMap,
    SSDataMorphism.pageMapAt, Category.assoc]
  have htr := pageMap_transport f.toSSDataMorphism k (middleIndex E r k)
    ↑((r + 1 - E.r₀).toNat) ↑((r - E.r₀).toNat + 1)
    (sub_add_cancel k (E.diffDeg r)).symm (by rw [hn])
  rw [← Category.assoc, htr]
  simp only [Category.assoc, eqToHom_trans_assoc]


/-- The representative construction agrees with the fixed canonical successor
isomorphism by the computation formula. -/

private theorem canonicalSuccessor_naturality {E F : SpectralSequence C ι}
    (f : FromFirstMorphism E F) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    (pageHomologyIso E r k hr).hom ≫ centeredHomologyMap f r k hr =
      f.pageMap (r + 1) k ≫
        (pageHomologyIso F r k (by rw [← f.r₀_eq]; exact hr)).hom := by
  rw [← explicitSuccessorMap_eq_pageHomologyIso,
    ← explicitSuccessorMap_eq_pageHomologyIso]
  exact explicitSuccessorMap_naturality f r k hr

end
end KIP126.Literature.Paper38OriginalSuccessor
