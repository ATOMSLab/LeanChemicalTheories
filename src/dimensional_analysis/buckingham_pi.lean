import dimensional_analysis.basic2
import data.matrix.rank


noncomputable
def number_of_dimensionless_parameters {m n : ℕ} (M : matrix (fin m) (fin n) ℚ): ℕ := n - matrix.rank M 
