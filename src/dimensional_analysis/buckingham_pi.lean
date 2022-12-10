import dimensional_analysis.basic3
import linear_algebra.dimension
import data.matrix.rank
import data.fin.vec_notation



variables {α : Type*} {n : ℕ} 


noncomputable def number_of_dimensionless_parameters (M : matrix α (fin n) ℚ) := n - M.rank
open dimension

example : number_of_dimensionless_parameters !![length system1 system1.length, time system1 system1.length, velocity system1 system1.length; length system1 system1.time, time system1 system1.time, velocity system1 system1.time] = 1 :=
begin
  simp [dimension.velocity, number_of_dimensionless_parameters],
  rw [length_at_length_eq_one, length_at_time_eq_zero, time_at_time_eq_one, time_at_length_eq_zero],
  norm_num,
  
end