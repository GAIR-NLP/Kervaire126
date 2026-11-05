module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import Mathlib.Topology.Homotopy.HomotopyGroup

@[expose] section

namespace KIP126.Topology
open scoped unitInterval
universe u v w
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Composition on genuine based cubical loops by a based continuous map. -/
def continuousGenLoopMap (f : C(X,Y)) (x : X) (y : Y) (h : f x = y) (n : ℕ)
    (p : GenLoop (Fin n) X x) : GenLoop (Fin n) Y y :=
  ⟨f.comp p.val, fun z hz => (congrArg f (p.property z hz)).trans h⟩

/-- The induced map on the actual based cubical homotopy quotient. -/
def continuousHomotopyMap (f : C(X,Y)) (x : X) (y : Y) (h : f x = y) (n : ℕ) :
    HomotopyGroup.Pi n X x → HomotopyGroup.Pi n Y y :=
  Quotient.map (continuousGenLoopMap f x y h n) fun _ _ h => h.comp_continuousMap f

end KIP126.Topology
