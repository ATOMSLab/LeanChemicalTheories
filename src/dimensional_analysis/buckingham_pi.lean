import dimensional_analysis.basic3
import linear_algebra.dimension
import data.matrix.rank
import data.fin.vec_notation



variables {α : Type*} {n : ℕ} [fintype α]


noncomputable def number_of_dimensionless_parameters (M : matrix α (fin n) ℚ) := n - M.rank
open dimension

example : number_of_dimensionless_parameters !![(length system1) system1.length, (time system1) system1.length, velocity system1 system1.length; length system1 system1.time, time system1 system1.time, velocity system1 system1.time] = 1 :=
begin
  simp [dimension.velocity, dimension.length, dimension.time, number_of_dimensionless_parameters],
  iterate 2 { rw pi.single_eq_of_ne, },
  all_goals { try { finish }, },
  norm_num,
end