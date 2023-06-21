import analysis.calculus.mean_value
import analysis.calculus.deriv.inv
import analysis.special_functions.pow.deriv
import math.rpow


open real 


theorem deriv_within_div_pow
{C x : ℝ}
(hx : x ≠ 0)
(s : set ℝ)
(hu : unique_diff_within_at ℝ s x)
:
∀ n : ℕ, 1 < n →  deriv_within (λ y : ℝ, C/y^n) s x = -n*C/x^(n+1):=
begin
  intros n hn,
  conv {
    find (C) {rw show C = (λ y : ℝ, C) y, by simp},
  },
  rw deriv_within_div (differentiable_within_at_const C) (differentiable_within_at_pow n) (pow_ne_zero n hx) hu,
  field_simp [deriv_within_const x s C hu, deriv_within_pow n hu],
  rw [mul_assoc, mul_assoc, ← pow_add, add_comm n 1, ← add_assoc, nat.sub_add_cancel (le_of_lt hn), pow_two, ← pow_add, ← mul_assoc, mul_comm C _],
end

theorem has_deriv_at_div_pow
{C x : ℝ}
(hx : x ≠ 0)
:
∀ n : ℕ, 1 < n → has_deriv_at (λ y : ℝ, C/y^n) (-n*C/x^(n+1)) x :=
begin
  intros n hn,
  conv {
    find (C) {rw show C = (λ y : ℝ, C) y, by simp},
  },
  rw show -↑n * C / x ^ (n + 1) = (0*x^n-((λ y : ℝ, C) x)*(n*x^(n-1)))/(x^n)^2, by {field_simp, iterate 3 {rw [mul_assoc],}, 
  rw [← pow_add, add_comm n 1, ← add_assoc, nat.sub_add_cancel (le_of_lt hn), pow_two, ← pow_add], ring_exp,  },
  apply has_deriv_at.div (has_deriv_at_const x C) (has_deriv_at_pow n x),
  simp [pow_ne_zero n hx],
end

theorem differentiable_at_div_pow
{C x : ℝ}
(hx : x ≠ 0)
:
∀ n : ℕ, differentiable_at ℝ (λ y : ℝ, C/y^n) x :=
begin
  intro,
  conv {
    find (C) {rw show C = (λ y : ℝ, C) y, by simp},
  },
  apply differentiable_at.div (differentiable_at_const C) (differentiable_at_pow n) (pow_ne_zero n hx),
end

theorem deriv_div_pow 
{C x : ℝ}
(hx : x ≠ 0)
:
∀ n : ℕ, 1 < n →  deriv (λ y : ℝ, C/y^n) x = -n*C/x^(n+1):=
begin
  intros n hn,
  apply has_deriv_at.deriv (has_deriv_at_div_pow hx _ hn),
end

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