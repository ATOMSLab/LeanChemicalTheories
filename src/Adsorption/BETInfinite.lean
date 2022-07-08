import analysis.complex.basic
import data.real.basic
import algebra.ring.basic
import math.infinite_series

open_locale big_operators


theorem BET₁ {x : ℝ} (C : ℝ) (hx1: x < 1) (hx2 : 0 < x) :
  (∑' k : ℕ, ((k + 1 : ℝ)*(x^(k+1))* C))/(1 + ∑' k, x^(k+1)* C) = C*x/((1 - x)*(1 - x + C*x)) :=
begin
  have hxnorm : ∥x∥ < 1, by refine abs_lt.mpr ⟨_, _⟩ ; linarith,
  rw [tsum_mul_right, tsum_mul_right, tsum_coe_mul_geometric_succ hx1 hx2, 
  tsum_geometric_of_lt_1_pow_succ hx1 hx2, pow_two, mul_comm (x/(1-x)) C, ← mul_div_assoc C _ _, one_add_div, 
  mul_comm, ← mul_div_assoc],
  field_simp,
  rw [mul_comm, mul_assoc (1-x) _ _, mul_div_mul_left],
  iterate 2 {linarith},
end

theorem BET_regression
(θ : ℕ → ℝ ){ P A V₀ Vads x y: ℝ}
-- Equations
(h1 : let C := y/x in ∀ k, θ (k+1) = (x ^ (k+1)) * C * θ 0)
(hA : A = ∑' (k : ℕ), θ k)
(hVads : Vads =  V₀ * ∑' (k : ℕ), k * θ k)
-- Constraints
(hx1: x<1)
(hx2 : 0 < x)
(hθ : θ 0 ≠ 0)
(hP : P ≠ 0)
:
  let a := V₀*y/P,
      b := x/P,
      c := y/P,
      q := Vads/A in
  q = a*P/((1-b*P)*(1-b*P+c*P))
:=
begin
simp at h1,
  have hsum2 : summable θ,
  { refine (summable_nat_add_iff 1).mp _,
    simp only [h1, pow_succ', mul_assoc],
    exact (summable_geometric_of_lt_1 hx2.le hx1).mul_right _ },
  have hxnorm : ∥x∥ < 1, by refine abs_lt.mpr ⟨_, _⟩ ; linarith,
  have hsum : summable (λ k : ℕ, ↑k * θ k),
  { refine (summable_nat_add_iff 1).mp _,
    simp only [h1, ← mul_assoc],
    refine summable.mul_right _ (summable.mul_right _ _),
    set u := λ k :ℕ, (k : ℝ) * x ^ k,
    change summable (λ (n : ℕ), u (n+1)),
    refine (summable_nat_add_iff 1).mpr _,
    simpa using summable_pow_mul_geometric_of_norm_lt_1 1 hxnorm },
  intros,
  simp only [a, b, c, q],
  rw [ hVads, hA , tsum_eq_zero_add hsum, tsum_eq_zero_add hsum2],
  have : ∀ k : ℕ, (k + 1 : ℝ) * (x ^ (k + 1) * (y/x) * θ 0) = ((k + 1 : ℝ) * (x ^ (k + 1) * (y/x))) * θ 0,
  by simp [mul_assoc],
  simp only [nat.cast_zero, zero_mul, zero_add, nat.cast_one, one_mul, nat.cast_add, h1, this],
  rw [tsum_mul_right, tsum_mul_right, show ∀ z : ℝ, θ 0 + z * θ 0 = (1+z)*θ 0, by {intro z, rw [add_mul, one_mul] },
      mul_div_assoc, mul_div_mul_right _ _ hθ], 
  conv {find (_*(x^_*(y/x))){rw ← mul_assoc}},
  rw [BET₁ (y/x) hx1 hx2, ← mul_div_assoc],
  have hx3 : x ≠ 0 := by linarith,
  field_simp,
end