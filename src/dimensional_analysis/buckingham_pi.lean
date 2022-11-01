import dimensional_analysis.basic2
import data.matrix.rank
import data.fin.vec_notation


noncomputable
def number_of_dimensionless_parameters {m n : ℕ} (M : matrix (fin m) (fin n) ℚ): ℕ := n - matrix.rank M 

example : number_of_dimensionless_parameters !![(1 : ℚ), 0, 1; 0, 1, -1] = 1 :=
begin 
  simp [number_of_dimensionless_parameters],
  have h : (matrix.of ![![(1 : ℚ), 0, 1], ![0, 1, -1]]).rank = 2,
  begin
    rw matrix.rank,
    rw matrix.to_lin',
    

    
  end
end