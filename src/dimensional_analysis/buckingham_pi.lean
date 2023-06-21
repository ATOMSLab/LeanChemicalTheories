import dimensional_analysis.basic
import linear_algebra.dimension
import data.matrix.rank
import data.fin.vec_notation
import set_theory.cardinal.basic

variables {α : Type*} {n : ℕ} [fintype α]


noncomputable def number_of_dimensionless_parameters [decidable_eq α] (M : matrix (fin n) α ℚ) := n - M.rank
