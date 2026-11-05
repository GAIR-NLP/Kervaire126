module
public import KIP126.AdamsComputation.Table.Relations
/-! Degree-explicit associativity for the fixed sphere product. -/
@[expose] section
set_option backward.isDefEq.respectTransparency false
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory KIP126.AdamsSynthetic.Completed KIP126.Computation.Standard
noncomputable section

theorem product_heq {p q r : ℤ×ℤ}
    (x : background.classical.sphere.Page 2 p) (y : background.classical.sphere.Page 2 q)
    (h : p+q=r) : HEq (product x y h) (background.sphereAlgebra.product p q x y) := by
  subst r
  rfl

theorem product_assoc_at {p q r pq qr o : ℤ×ℤ}
    (x : background.classical.sphere.Page 2 p) (y : background.classical.sphere.Page 2 q)
    (z : background.classical.sphere.Page 2 r)
    (hpq : p+q=pq) (hqr : q+r=qr) (hl : pq+r=o) (hr : p+qr=o) :
    product (product x y hpq) z hl = product x (product y z hqr) hr := by
  subst pq
  subst qr
  apply eq_of_heq
  exact (product_heq (product x y rfl) z hl).trans
    ((background.sphereAlgebra.assoc p q r x y z).trans
      (product_heq x (product y z rfl) hr).symm)

end
end KIP126.Main.SectionSeven.Internal
