/-symplectic manifolds is the basis of the Hamiltonian formalization of classical mechanics and should
serve as the basis for describing a phase sapce-/
import linear_algebra.bilinear_form

universes u_1 u_2
variables {R : Type u_1} {M : Type u_2} [ring R] [add_comm_monoid M] [module R M] (B : bilin_form R M)

def bilin_form.is_skew_symm := ∀ x y : M, B x y = - B y x

@[protected] lemma is_skew_symm.eq (h : B.is_skew_symm) (x y : M) : B x y = - B y x := h x y 

