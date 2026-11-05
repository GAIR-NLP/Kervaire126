module
public import KIP126.ProofTools.Operations
public import KIP126.ProofTools.Representatives
import all KIP126.Main.Internal.NuThree.ZeroLabels
/-! Normalized exponent-zero labels and representatives for the same fixed maps. -/
@[expose] section
namespace KIP126.Main.Internal.NuThree
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
open KIP126.ProofTools KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald KIP126.Main.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
private theorem classical_page_reaches (X Y : AdamsObject)
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (r : ℤ) (s t : ℤ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (hx : ReachesPage (background.classical.obj (X.obj background.auxiliary)) r (s,t) x) :
    ReachesPage (background.classical.obj (Y.obj background.auxiliary)) r (s,t)
      (background.classical.pageMap f 2 (s,t) x) := by
  obtain ⟨xr,hxr⟩ := hx
  exact ⟨(background.classical.map f).pageMap r (s,t) xr,(background.classical.map f).representsOnPage hxr⟩

private theorem finite_zero_extension_8
    (X Y : AdamsObject) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (he : normalizedExponent background.classicalTower f=0)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (8,134))
    (hx : x∈cycles background X 2 (8,134)) :
    FiniteExtension background X Y f 3 0 8 134 x (background.classical.pageMap f 2 (8,134) x) := by
  let y := background.classical.pageMap f 2 (8,134) x
  have hlower : (normalizedExponent background.classicalTower f:ℤ)≤0 := by omega
  obtain ⟨es,hes⟩ := normalized_zero_source_infinity_8 X Y f he 2 (by decide) x hx
  let et := (background.family.map (finiteExtensionMap background X Y f 2)).eInftyMap
    (8,134,134+normalizedExponent background.classicalTower f) es
  have hm := normalized_zero_map_label_8 X Y f he 2 x
  have ht : HEq (finiteTargetForExtension background X Y f 2 0 8 134 hlower y)
      (finiteTargetLabel background Y 2 8 134 0 y) :=
    zero_exponent_target_label_8 Y 2 _ he y
  have heq := eq_of_heq (hm.trans ht.symm)
  have hmap := family_infinity_representative_map (finiteExtensionMap background X Y f 2)
    (8,134,134+normalizedExponent background.classicalTower f) _ es hes
  have hrep : HasInfinityRepresentative (background.family.obj ((SyntheticObject.quotient 2 (.nu Y)).obj background.nu background.auxiliary)) 2
      (8,134,134+normalizedExponent background.classicalTower f)
      (finiteTargetForExtension background X Y f 2 0 8 134 hlower y) et := heq ▸ hmap
  have hxR : ReachesPage (background.classical.obj (X.obj background.auxiliary)) 3 (8,134) x :=
    (isCycle_iff_reaches background X 3 (by decide) (8,134) x).mp ⟨by decide,hx⟩
  have hyR := classical_page_reaches X Y f 3 8 134 x hxR
  refine ⟨{
    page_ge_two := by decide
    length_lower := hlower
    length_upper := by omega
    source_cycle := hxR
    target_cycle := ?_
    source := es
    target := et
    source_rep := hes
    target_rep := hrep
    equation := ?_ }⟩
  · change ReachesPage (background.classical.obj (Y.obj background.auxiliary))
      ((3:ℤ)-0+normalizedExponent background.classicalTower f) (8,134) y
    rw [he]
    exact hyR
  · exact towerExtensionEquation_zero
      (background.convergentMap (.quotient 2 (extensionSourceObject background X Y f))
        (.quotient 2 (.nu Y)) (finiteExtensionMap background X Y f 2))
      (126,134+normalizedExponent background.classicalTower f) 8 es

private theorem finite_zero_extension_11
    (X Y : AdamsObject) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (he : normalizedExponent background.classicalTower f=0)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (11,136))
    (hx : x∈cycles background X 1 (11,136)) :
    FiniteExtension background X Y f 2 0 11 136 x (background.classical.pageMap f 2 (11,136) x) := by
  let y := background.classical.pageMap f 2 (11,136) x
  have hlower : (normalizedExponent background.classicalTower f:ℤ)≤0 := by omega
  obtain ⟨es,hes⟩ := normalized_zero_source_infinity_11 X Y f he 1 (by decide) x hx
  let et := (background.family.map (finiteExtensionMap background X Y f 1)).eInftyMap
    (11,136,136+normalizedExponent background.classicalTower f) es
  have hm := normalized_zero_map_label_11 X Y f he 1 x
  have ht : HEq (finiteTargetForExtension background X Y f 1 0 11 136 hlower y)
      (finiteTargetLabel background Y 1 11 136 0 y) :=
    zero_exponent_target_label_11 Y 1 _ he y
  have heq := eq_of_heq (hm.trans ht.symm)
  have hmap := family_infinity_representative_map (finiteExtensionMap background X Y f 1)
    (11,136,136+normalizedExponent background.classicalTower f) _ es hes
  have hrep : HasInfinityRepresentative (background.family.obj ((SyntheticObject.quotient 1 (.nu Y)).obj background.nu background.auxiliary)) 2
      (11,136,136+normalizedExponent background.classicalTower f)
      (finiteTargetForExtension background X Y f 1 0 11 136 hlower y) et := heq ▸ hmap
  have hxR : ReachesPage (background.classical.obj (X.obj background.auxiliary)) 2 (11,136) x :=
    (isCycle_iff_reaches background X 2 (by decide) (11,136) x).mp ⟨by decide,hx⟩
  have hyR := classical_page_reaches X Y f 2 11 136 x hxR
  refine ⟨{
    page_ge_two := by decide
    length_lower := hlower
    length_upper := by omega
    source_cycle := hxR
    target_cycle := ?_
    source := es
    target := et
    source_rep := hes
    target_rep := hrep
    equation := ?_ }⟩
  · change ReachesPage (background.classical.obj (Y.obj background.auxiliary))
      ((2:ℤ)-0+normalizedExponent background.classicalTower f) (11,136) y
    rw [he]
    exact hyR
  · exact towerExtensionEquation_zero
      (background.convergentMap (.quotient 1 (extensionSourceObject background X Y f))
        (.quotient 1 (.nu Y)) (finiteExtensionMap background X Y f 1))
      (125,136+normalizedExponent background.classicalTower f) 11 es

end
end KIP126.Main.Internal.NuThree
