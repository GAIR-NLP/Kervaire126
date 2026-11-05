module
import all KIP126.ProofTools.GeneralizedLeibniz.Filtration
import all KIP126.ProofTools.StretchingRepresentatives

/-! Source-filtration bounds for the finite crossing comparison in AimPaper
Proposition `prop:cross-f-Er`. The finite E∞ window bounds the source displacement;
at page two it rules out all higher-source essential extensions. -/
@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.AdamsSynthetic.Completed
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem finite_extension_zero_source_not_essential (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (q : ℕ)
    (p : ℤ × ℤ) (u d : ℤ) (hd : 0 ≤ d)
    (y : ((background.family.obj ((SyntheticObject.quotient q (.nu Y)).obj background.nu background.auxiliary)).sequence.ssData
      (u+d,p.1+(u+d),p.2)).eInfty) :
    ¬ TowerEssentialExtension (background.convergentMap
      (.quotient q (extensionSourceObject background X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap background X Y f q)) p u d 0 y := by
  intro he
  have hrel : TowerExtensionEquation (background.convergentMap
      (.quotient q (extensionSourceObject background X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap background X Y f q)) p u d 0 y := he.1
  have hzero : TowerExtensionEquation (background.convergentMap
      (.quotient q (extensionSourceObject background X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap background X Y f q)) p u d 0 0 := by
    apply (tower_extension_iff _ _ _ _ _ _).mpr
    refine ⟨hd,0,0,?_,?_,?_⟩ <;> simp
  exact ((tower_essential_iff_no_zero _ _ _ _ _ _ hrel).mp he) hzero

private theorem finite_crossing_source_bound (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (q : ℕ) (hq : 0 < q)
    (s t u v : ℤ) (huv : u ≤ v)
    (x : ((background.family.obj ((SyntheticObject.quotient q (extensionSourceObject background X Y f)).obj background.nu background.auxiliary)).sequence.ssData
      (u,(t-s)+u,t+normalizedExponent background.classicalTower f)).eInfty)
    (y : ((background.family.obj ((SyntheticObject.quotient q (.nu Y)).obj background.nu background.auxiliary)).sequence.ssData
      (u+(v-u),(t-s)+(u+(v-u)),t+normalizedExponent background.classicalTower f)).eInfty)
    (he : TowerEssentialExtension (background.convergentMap
      (.quotient q (extensionSourceObject background X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap background X Y f q))
      (t-s,t+normalizedExponent background.classicalTower f) u (v-u) x y) : u-s < q := by
  by_contra hqle
  have hz := shifted_quotient_eInfty_zero X q hq (normalizedExponent background.classicalTower f)
    u ((t-s)+u) (t+normalizedExponent background.classicalTower f) (by omega)
  have hsub := ModuleCat.isZero_iff_subsingleton.mp hz
  have hx : x = 0 := @Subsingleton.elim _ hsub _ _
  subst x
  exact finite_extension_zero_source_not_essential X Y f q
    (t-s,t+normalizedExponent background.classicalTower f) u (v-u) (by omega) y he

private theorem page_two_tower_no_crossing (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (s t n : ℤ) :
    TowerNoCrossing (background.convergentMap
      (.quotient 1 (extensionSourceObject background X Y f)) (.quotient 1 (.nu Y))
      (finiteExtensionMap background X Y f 1))
      (t-s,t+normalizedExponent background.classicalTower f) s n := by
  intro u v hsu huv hvs x y he
  have hh := finite_crossing_source_bound X Y f 1 (by omega) s t u v huv x y he
  omega
end
end KIP126.ProofTools.Internal.Leibniz
