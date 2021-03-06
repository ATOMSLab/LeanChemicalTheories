import analysis.complex.basic
import data.real.basic
import algebra.ring.basic
import math.infinite_series

open_locale big_operators

variables (x θ₀ C: ℝ)


def seq : ℕ → ℝ
|(0 : ℕ)            := θ₀
|(nat.succ n) := x^(n+1)*θ₀*C


theorem BET₁ (C : ℝ) (hx1: x < 1) (hx2 : 0 < x) (hθ : θ₀ ≠ 0):
  (∑' k : ℕ, ((k + 1 : ℝ)*(seq x θ₀ C (k+1:ℕ))))/(θ₀ + ∑' k, (seq x θ₀ C (k+1:ℕ))) = C*x/((1 - x)*(1 - x + x*C)) :=
begin
  simp [seq],
  have hxnorm : ∥x∥ < 1, by refine abs_lt.mpr ⟨_, _⟩ ; linarith,
  simp [← mul_assoc],
  rw [tsum_mul_right, tsum_mul_right, tsum_mul_right, tsum_mul_right, tsum_coe_mul_geometric_succ hx1 hx2, 
  tsum_geometric_of_lt_1_pow_succ hx1 hx2, pow_two],
  have h1 : (1-x) ≠ 0 := by linarith,
  field_simp,
  rw [mul_comm, mul_assoc (1-x) _ _, mul_div_mul_left, mul_comm, mul_comm x θ₀, mul_comm C _, mul_assoc θ₀ x C, 
  ← mul_add θ₀ _ _, ← mul_assoc (1-x) _ _,  mul_comm _ θ₀, mul_assoc θ₀ _ _, mul_div_mul_left, mul_comm C x],
  iterate 2 {finish},
end

theorem BET_regression_form
{ P V₀ y: ℝ}
(hx1: x<1)
(hx2 : 0 < x)
(hθ : θ₀ ≠ 0)
(hP : P ≠ 0)
:
  let a := V₀*y/P,
      b := x/P,
      c := y/P,
      C := y/x,
      Vads :=  V₀ * ∑' (k : ℕ), ↑k * (seq x θ₀ C k),
      A :=  ∑' (k : ℕ), (seq x θ₀ C k),
      q := Vads/A in
  q = a*P/((1-b*P)*(1-b*P+c*P))
:=
begin
intros,
  have hsum2 : summable (seq x θ₀ C),
  { refine (summable_nat_add_iff 1).mp _,
    simp only [seq, pow_succ', mul_assoc],
    exact (summable_geometric_of_lt_1 hx2.le hx1).mul_right _ },
  have hxnorm : ∥x∥ < 1, by refine abs_lt.mpr ⟨_, _⟩ ; linarith,
  have hsum : summable (λ k : ℕ, ↑k * (seq x θ₀ C k)),
  { refine (summable_nat_add_iff 1).mp _,
    simp only [seq, ← mul_assoc],
    refine summable.mul_right _ (summable.mul_right _ _),
    set u := λ k :ℕ, (k : ℝ) * x ^ k,
    change summable (λ (n : ℕ), u (n+1)),
    refine (summable_nat_add_iff 1).mpr _,
    simpa using summable_pow_mul_geometric_of_norm_lt_1 1 hxnorm },
  simp only [a, b, c, q, Vads, A],
  rw [tsum_eq_zero_add hsum, tsum_eq_zero_add hsum2],
  simp only [nat.cast_zero, zero_mul, zero_add, nat.cast_one, pow_zero, one_mul, mul_assoc, nat.cast_add, mul_div_assoc],
  rw [show seq x θ₀ C 0 = θ₀, by {simp [seq]}], 
  rw [BET₁ x θ₀ (y/x) hx1 hx2 hθ, ← mul_div_assoc,mul_comm x (y/x)],
  have hx3 : x ≠ 0 := by linarith,
  field_simp,
end