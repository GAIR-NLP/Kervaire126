module
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.Additive

namespace KIP126.Literature.Standard.E2AugmentedComparison
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ ψ : K ⟶ L)

/-- Local homotopy at every nonnegative degree, constructed from the two actual extension facts. -/
private theorem exists_local_homotopy
    {A : C} (a : A ⟶ K.X 0) (haug : a ≫ φ.f 0 = a ≫ ψ.f 0)
    (hzero : ∀ e : K.X 0 ⟶ L.X 0, a ≫ e = 0 →
      ∃ q : K.X 1 ⟶ L.X 0, K.d 0 1 ≫ q = e)
    (hsucc : ∀ (n : ℕ) (e : K.X ((n:ℤ)+1) ⟶ L.X ((n:ℤ)+1)),
      K.d (n:ℤ) ((n:ℤ)+1) ≫ e = 0 →
      ∃ q : K.X ((n:ℤ)+1+1) ⟶ L.X ((n:ℤ)+1),
        K.d ((n:ℤ)+1) ((n:ℤ)+1+1) ≫ q = e) :
    ∀ n : ℕ, ∃ p : K.X (n:ℤ) ⟶ L.X ((n:ℤ)-1),
      ∃ q : K.X ((n:ℤ)+1) ⟶ L.X (n:ℤ),
        φ.f (n:ℤ) - ψ.f (n:ℤ) =
          p ≫ L.d ((n:ℤ)-1) (n:ℤ) + K.d (n:ℤ) ((n:ℤ)+1) ≫ q := by
  intro n
  induction n with
  | zero =>
      obtain ⟨q,hq⟩ := hzero (φ.f 0 - ψ.f 0) (by rw [Preadditive.comp_sub, haug, sub_self])
      refine ⟨0, q, ?_⟩
      simpa using hq.symm
  | succ n ih =>
      obtain ⟨p,q,hpq⟩ := ih
      let e := φ.f ((n:ℤ)+1) - ψ.f ((n:ℤ)+1) - q ≫ L.d (n:ℤ) ((n:ℤ)+1)
      have he : K.d (n:ℤ) ((n:ℤ)+1) ≫ e = 0 := by
        dsimp only [e]
        rw [Preadditive.comp_sub, Preadditive.comp_sub,
          ← φ.comm, ← ψ.comm, ← Preadditive.sub_comp, hpq,
          Preadditive.add_comp, Category.assoc, L.d_comp_d, comp_zero,
          zero_add, Category.assoc, sub_self]
      obtain ⟨r,hr⟩ := hsucc n e he
      have hn : (n:ℤ)+1-1 = (n:ℤ) := by omega
      rw [Int.natCast_succ, hn]
      refine ⟨q,r,?_⟩
      rw [hr]
      dsimp only [e]
      abel

/-- A local homotopy equation in one degree identifies the original induced homology maps. -/
private theorem homologyMap_eq_of_local_homotopy (s : ℤ)
    [K.HasHomology s] [L.HasHomology s]
    (p : K.X s ⟶ L.X (s-1)) (q : K.X (s+1) ⟶ L.X s)
    (hpq : φ.f s - ψ.f s = p ≫ L.d (s-1) s + K.d s (s+1) ≫ q) :
    HomologicalComplex.homologyMap φ s = HomologicalComplex.homologyMap ψ s := by
  apply sub_eq_zero.mp
  rw [← HomologicalComplex.homologyMap_sub]
  apply (cancel_epi (K.homologyπ s)).mp
  rw [HomologicalComplex.homologyπ_naturality, comp_zero]
  have hc : HomologicalComplex.cyclesMap (φ - ψ) s =
      K.iCycles s ≫ p ≫ L.toCycles (s-1) s := by
    apply (cancel_mono (L.iCycles s)).mp
    rw [HomologicalComplex.cyclesMap_i]
    change K.iCycles s ≫ (φ.f s - ψ.f s) = _
    rw [hpq, Preadditive.comp_add, ← Category.assoc (K.iCycles s) (K.d s (s+1)),
      K.iCycles_d, zero_comp, add_zero]
    simp only [Category.assoc, HomologicalComplex.toCycles_i]
  rw [hc]
  simp only [Category.assoc, HomologicalComplex.toCycles_comp_homologyπ, comp_zero]

/-- An additive functor preserves the local homotopy equation and the equality it induces. -/
private theorem mapped_homologyMap_eq_of_local_homotopy
    {D : Type u'} [Category.{v'} D] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (s : ℤ) [((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).HasHomology s]
    [((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).HasHomology s]
    (p : K.X s ⟶ L.X (s-1)) (q : K.X (s+1) ⟶ L.X s)
    (hpq : φ.f s - ψ.f s = p ≫ L.d (s-1) s + K.d s (s+1) ≫ q) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) s =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) s := by
  apply homologyMap_eq_of_local_homotopy _ _ s (F.map p) (F.map q)
  change F.map (φ.f s) - F.map (ψ.f s) =
    F.map p ≫ F.map (L.d (s-1) s) + F.map (K.d s (s+1)) ≫ F.map q
  rw [← F.map_sub, hpq, F.map_add, F.map_comp, F.map_comp]

/-- Augmentation-compatible cochain maps induce equal homology maps after an additive functor. -/
private theorem mapped_homologyMap_eq_nonnegative
    {A : C} (a : A ⟶ K.X 0) (haug : a ≫ φ.f 0 = a ≫ ψ.f 0)
    (hzero : ∀ e : K.X 0 ⟶ L.X 0, a ≫ e = 0 →
      ∃ q : K.X 1 ⟶ L.X 0, K.d 0 1 ≫ q = e)
    (hsucc : ∀ (n : ℕ) (e : K.X ((n:ℤ)+1) ⟶ L.X ((n:ℤ)+1)),
      K.d (n:ℤ) ((n:ℤ)+1) ≫ e = 0 →
      ∃ q : K.X ((n:ℤ)+1+1) ⟶ L.X ((n:ℤ)+1),
        K.d ((n:ℤ)+1) ((n:ℤ)+1+1) ≫ q = e)
    {D : Type u'} [Category.{v'} D] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (n : ℕ) [((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).HasHomology (n:ℤ)]
    [((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).HasHomology (n:ℤ)] :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) (n:ℤ) =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) (n:ℤ) := by
  obtain ⟨p,q,hpq⟩ := exists_local_homotopy φ ψ a haug hzero hsucc n
  exact mapped_homologyMap_eq_of_local_homotopy φ ψ F (n:ℤ) p q hpq

/-- At a zero source degree the cochain maps agree. -/
private theorem mapped_homologyMap_eq_of_isZero
    {D : Type u'} [Category.{v'} D] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (s : ℤ) [((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).HasHomology s]
    [((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).HasHomology s]
    (hK : IsZero (K.X s)) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) s =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) s := by
  apply mapped_homologyMap_eq_of_local_homotopy φ ψ F s 0 0
  rw [hK.eq_of_src (φ.f s) (ψ.f s), sub_self, zero_comp, comp_zero, zero_add]

/-- The nonnegative comparison extends to all integers when the source is zero in negative degrees. -/
private theorem mapped_homologyMap_eq
    {A : C} (a : A ⟶ K.X 0) (haug : a ≫ φ.f 0 = a ≫ ψ.f 0)
    (hzero : ∀ e : K.X 0 ⟶ L.X 0, a ≫ e = 0 →
      ∃ q : K.X 1 ⟶ L.X 0, K.d 0 1 ≫ q = e)
    (hsucc : ∀ (n : ℕ) (e : K.X ((n:ℤ)+1) ⟶ L.X ((n:ℤ)+1)),
      K.d (n:ℤ) ((n:ℤ)+1) ≫ e = 0 →
      ∃ q : K.X ((n:ℤ)+1+1) ⟶ L.X ((n:ℤ)+1),
        K.d ((n:ℤ)+1) ((n:ℤ)+1+1) ≫ q = e)
    (hnegative : ∀ s : ℤ, s < 0 → IsZero (K.X s))
    {D : Type u'} [Category.{v'} D] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (s : ℤ) [((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).HasHomology s]
    [((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).HasHomology s] :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) s =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) s := by
  by_cases hs : 0 ≤ s
  · lift s to ℕ using hs
    exact mapped_homologyMap_eq_nonnegative φ ψ a haug hzero hsucc F s
  · exact mapped_homologyMap_eq_of_isZero φ ψ F s (hnegative s (lt_of_not_ge hs))


end
end KIP126.Literature.Standard.E2AugmentedComparison
