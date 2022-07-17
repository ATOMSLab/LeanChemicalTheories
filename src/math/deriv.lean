import analysis.calculus.mean_value
import analysis.special_functions.pow_deriv

--local imports
import math.rpow


open real 

theorem deriv_inv_rpow
{C z: ℝ} (hz : 0 < z)
:
∀ r:ℝ, 1 ≤ r →  deriv (λ x:ℝ, C/x^r) z = -r*C/z^(r+1):=
begin
  intros n hr,
  have h :  (λ x:ℝ, C/x^n) = λ x:ℝ, ((λ x:ℝ, C) x)/((λ x:ℝ, x^n) x) := by simp,
  rw [h, deriv_div],
  simp,
  have h2 : z^(n-1)/(z^n)^2 = 1/z^(n+1),
  { rw [rpow_sub, rpow_one, pow_two],
    field_simp,
    rw [← mul_assoc, div_mul_left, mul_comm z _, ← rpow_add_one],
    linarith,
    apply rpow_ne_zero hz,
    linarith,
    linarith,},
  have h3 : deriv (λ (x : ℝ), x ^ n) z = n*z^(n-1),
  { rw real.deriv_rpow_const, right, exact hr},
  rw [h3, ← mul_assoc, neg_div, mul_div_assoc, pow_two, ← rpow_add hz, ← rpow_sub hz,
  show n-1-(n+n) = -(n+1), by { rw ← sub_sub, simp, ring_nf}],
  have hz1 : 0 ≤ z, by linarith,
  rw [rpow_neg hz1 (n+1), mul_comm C n, neg_div],
  field_simp,
  simp,
  simp,
  apply has_deriv_at.differentiable_at,
  apply real.has_deriv_at_rpow_const (or.inr hr),
  simp,
  rw ← ne.def,
  apply rpow_ne_zero hz,
  linarith,
end

theorem differentiable_at_inv_rpow
{C z: ℝ} (hz : 0 < z)
:
∀ r:ℝ, 1 ≤ r →  differentiable_at ℝ (λ x:ℝ, C/x^r) z :=
begin
  intros n hr,
  have h :  (λ x:ℝ, C/x^n) = λ x:ℝ, ((λ x:ℝ, C) x)/((λ x:ℝ, x^n) x) := by simp,
  apply has_deriv_at.differentiable_at,
  rw h,
  apply has_deriv_at.div,
  apply has_deriv_at_const,
  apply has_deriv_at_rpow_const hr.inr,
  simp,
  rw ← ne.def,
  apply ne_of_gt,
  apply zero_lt_rpow hz,
  linarith,
end

lemma deriv_abs_of_nonneg_rpow
{z : ℝ} (hpos : ∀ x : ℝ, 0 ≤ x)
:
∀ r:ℝ, 1 ≤ r →  (deriv (λ x : ℝ, |x^r|) z) = r * z ^ (r - 1):=
begin
  intros r hr,
  conv {  find (|_^r|) {rw [abs_rpow_of_nonneg (hpos x), abs_of_nonneg (hpos x)],}},
  rw real.deriv_rpow_const,
  exact hr.inr,
end


lemma deriv_inv_abs_rpow
{C z: ℝ} (hz : 0 < z) (hC : 0 < C) (hpos : ∀ x : ℝ, 0 < x)
:
∀ r:ℝ, 1 ≤ r →  deriv (λ x : ℝ , |C|/|x^r|) z = -r*C/z^(r+1):=
begin
  intros r hr,
  simp only [abs_of_pos hC],
  have hnonneg : ∀ x : ℝ, 0 ≤ x := by {intro x, refine le_of_lt (hpos x)},
  conv {  find (|_^r|) {rw [abs_rpow_of_nonneg (hnonneg x), abs_of_nonneg (hnonneg x)],}},
  apply deriv_inv_rpow hz _ hr,
end

theorem differentiable_at_inv_abs_rpow
{C z: ℝ} (hz : 0 < z) (hC : 0 < C) (hpos : ∀ x : ℝ, 0 < x)
:
∀ r:ℝ, 1 ≤ r →  differentiable_at ℝ (λ x:ℝ, |C|/|x^r|) z :=
begin
  intros r hr,
  simp only [abs_of_pos hC],
  have hnonneg : ∀ x : ℝ, 0 ≤ x := by {intro x, refine le_of_lt (hpos x)},
  conv {  find (|_^r|) {rw [abs_rpow_of_nonneg (hnonneg x), abs_of_nonneg (hnonneg x)],}},
  apply differentiable_at_inv_rpow hz r hr,
  
end