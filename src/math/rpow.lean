import analysis.special_functions.pow

open real


lemma rpow_ne_zero
{x y : ℝ} (hx : 0 < x) (hy : 0 < y)
: x^y ≠ 0 :=
begin
  have hy2 : y ≠ 0 := by linarith,
  apply ne_of_gt,
  rw [← zero_rpow hy2, rpow_lt_rpow_iff],
  iterate 4 {linarith},
end

lemma zero_lt_rpow
{x y : ℝ} (hx : 0 < x) (hy : 0 < y)
: 0 < x^y :=
begin
  have hy2 : y ≠ 0 := by linarith,
  rw [← zero_rpow hy2, rpow_lt_rpow_iff],
  iterate 4 {linarith},
end