import dimensional_analysis.basic
import linear_algebra.dimension
import data.matrix.rank
import data.fin.vec_notation
import set_theory.cardinal.basic

variables {α : Type*} {n : ℕ} [fintype α]


noncomputable def number_of_dimensionless_parameters [decidable_eq α] (M : matrix (fin n) α ℚ) := n - M.rank
open dimension

lemma cardinal.to_nat_eq_iff {c : cardinal} {n : ℕ} (hn : n ≠ 0) : cardinal.to_nat c = n ↔ c = n :=
⟨λ h, (cardinal.cast_to_nat_of_lt_aleph_0 (lt_of_not_ge (hn ∘ h.symm.trans ∘
  cardinal.to_nat_apply_of_aleph_0_le))).symm.trans (congr_arg coe h),
  λ h, (congr_arg cardinal.to_nat h).trans (cardinal.to_nat_cast n)⟩

example : cardinal.to_nat ( 3 : cardinal) = 3 :=
begin
  rw cardinal.to_nat_eq_iff,
  all_goals {finish},
end
example : number_of_dimensionless_parameters (matrix.of (![dimension.length system1, dimension.time system1, dimension.velocity system1])) = 1 :=
begin
  simp [number_of_dimensionless_parameters, matrix.rank],
  rw [finite_dimensional.finrank],
  have h : cardinal.to_nat (module.rank ℚ ((matrix.to_lin' (matrix.of ![length system1, time system1, velocity system1])).range)) = 2,
  { rw [cardinal.to_nat_eq_iff],
    
    },
  
  
  
end
example : matrix.rank !![(1 : ℚ),0;0,1;1,-1] = 2 :=
begin
  simp [matrix.rank],
  rw [finite_dimensional.finrank, cardinal.to_nat_eq_iff, module.rank],
  
  
end