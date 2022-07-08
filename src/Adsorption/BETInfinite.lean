import analysis.complex.basic
import data.real.basic
import algebra.ring.basic
import math.infinite_series

open_locale big_operators


theorem BET₁ {x : ℝ} (C : ℝ) (hx1: x < 1) (hx2 : 0 < x) :
  (∑' k : ℕ, ((k + 1 : ℝ)*(x^(k+1))* C))/(1 + ∑' k, x^(k+1)* C) = C*x/((1 - x)*(1 - x + C*x)) :=
begin
  have hxnorm : ∥x∥ < 1, by refine abs_lt.mpr ⟨_, _⟩ ; linarith,
  rw [tsum_mul_right, tsum_mul_right, tsum_coe_mul_geometric_add_zero hx1 hx2, tsum_geometric_of_lt_1_pow_succ hx1 hx2, pow_two,
  mul_comm (x/(1-x)) C, ← mul_div_assoc C _ _, one_add_div, mul_comm, ← mul_div_assoc, div_div, mul_assoc, ← mul_div_assoc (1-x) _ _, mul_div_cancel_left],
  iterate 2 {linarith},
end

theorem BET
(θ : ℕ → ℝ ){ k1 k2 kads kdes a b C P q A V₀ Vads x y c : ℝ}
--(hsum : summable (λ (b : ℕ), ↑b * θ b)) -- This is automatic
--(hsum2 : summable (λ (b : ℕ), θ b)) -- This is automatic
-- Equations
(h1 : ∀ k, θ (k+1) = (x ^ (k+1)) * C * θ 0)
(hA : A = ∑' (k : ℕ), θ k)
(hVads : Vads =  V₀ * ∑' (k : ℕ), k * θ k)
(hq : q = Vads/A)
-- Definitions
(hC: C = y/x)
(hy: y = k1/k2*P)
(hx: x = kads/kdes*P)
(hc: c = k1/k2)
(ha: a = V₀*c)
(hb: b = kads/kdes)
-- Constraints
(hx1: x<1)
(hx2 : 0 < x)
-- (hV₀ : V₀ ≠ 0)  This assumption was useless
(hθ : θ 0 ≠ 0)
:
q = a*P/((1-b*P)*(1-b*P+c*P))
:=
begin
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
  have hy' : y = C*x, from  (div_eq_iff hx2.ne.symm).mp hC.symm,
  rw [hq, hVads, hA, ha, hb, hc, ← hx, mul_assoc, ←hy, hy', mul_div_assoc, tsum_eq_zero_add hsum, tsum_eq_zero_add hsum2],
  have : ∀ k : ℕ, (k + 1 : ℝ) * (x ^ (k + 1) * C * θ 0) = ((k + 1 : ℝ) * (x ^ (k + 1) * C)) * θ 0,
  by simp [mul_assoc],
  simp only [nat.cast_zero, zero_mul, zero_add, nat.cast_one, one_mul, nat.cast_add, h1, this],
  rw [tsum_mul_right, tsum_mul_right, show ∀ z : ℝ, θ 0 + z * θ 0 = (1+z)*θ 0, by {intro z, rw [add_mul, one_mul] },
      mul_div_mul_right _ _ hθ, BET₁ C hx1 hx2, ← mul_div_assoc],
end

theorem BET_regression
(θ : ℕ → ℝ ){k1 k2 kads kdes a b C P q A V₀ Vads x y c : ℝ}
(hsum : summable (λ (b : ℕ), ↑b * θ b))
(hsum2 : summable (λ (b : ℕ), θ b))
-- Equations
(h1 : ∀ k, θ (k+1) = (x ^ (k+1)) * C * θ 0) -- Equation 14 from Brunauer 1938
(hA : A = ∑' (k : ℕ), θ k) -- Equation 13 from Brunauer 1938
(hVads : Vads =  V₀ * ∑' (k : ℕ), k * θ k)
(hq : q = Vads/A)
-- Definitions
(hC: C = y/x)
(hy: y = (k1/k2)*P)
(hx: x = (kads/kdes)*P)
(hc: c = k1/k2)
(ha: a = V₀*c)
(hb: b = kads/kdes)
-- Constraints
(hx1: x<1)
(hx2 : 0 < x)
(hθ : θ 0 ≠ 0)
:
q = a*P/((1-b*P)*(1-b*P+c*P))
:=
begin
have hx1' : ∥(x : ℝ)∥ < 1,
{ rw [real.norm_eq_abs, abs_lt],
  split, 
  nlinarith,
  exact hx1,}, 
have hx2' : 0 ≤ x,
{ apply le_of_lt,
  exact hx2,
},
conv at h1
{ find (x^_) {rw pow_succ,}},
--Simplfy hA
rw tsum_eq_zero_add at hA,
simp only [h1] at hA {single_pass := tt},
rw [tsum_mul_right, tsum_mul_right, tsum_mul_left , tsum_geometric_of_lt_1 hx2' hx1,mul_comm] at hA,
ring_nf at hA,
rw [mul_assoc, inv_eq_one_div, ← sub_eq_neg_add, mul_comm (1/(1-x)) _, ← mul_div_assoc, mul_one, mul_comm] at hA,
--simplify hVads
rw tsum_eq_zero_add at hVads,
simp only [h1] at hVads {single_pass := tt},
push_cast at hVads,
conv at hVads 
{ find (_*(_*_*_)){rw mul_comm x, rw mul_assoc, rw mul_assoc, rw ← mul_assoc,rw right_distrib, rw one_mul,},},
rw [tsum_mul_right, tsum_add, tsum_geometric_of_lt_1 hx2' hx1, tsum_coe_mul_geometric_of_norm_lt_1 hx1', zero_mul,
zero_add, ← mul_assoc (x / (1 - x) ^ 2 + (1 - x)⁻¹), right_distrib] at hVads,
simp at hVads,
rw inv_eq_one_div at hVads,
iterate 2 {rw mul_comm _ x at hVads},
iterate 2 {rw ← mul_div_assoc x at hVads},
rw [← pow_two, mul_one] at hVads,
have h2 : x^2/(1-x)^2+x/(1-x) = x/(1-x)^2,
{ rw add_comm,
  apply add_eq_of_eq_sub,
  rw div_sub_div_same,
  symmetry,
  apply div_eq_of_eq_mul,
  nlinarith,
  symmetry,
  rw [mul_comm, ← mul_div_assoc, mul_comm, pow_two, ← mul_assoc, mul_div_assoc, div_self],
  linarith,
  linarith,},
rw [h2, mul_comm _ (C*θ 0), ← mul_assoc, ← mul_assoc, mul_comm (V₀*C) _, mul_assoc] at hVads,
--simplify hq
rw [hA, hVads] at hq,
field_simp at hq,
rw [mul_comm ((1-x)^2), mul_assoc, mul_assoc] at hq,
rw [hC, hy, hx, ← hc, ← hb] at hq,
rw [hq, ha],
rw mul_div_mul_left,
rw mul_assoc,
field_simp,
rw [mul_comm (c*P) (b*P), mul_div_mul_left, div_add_one, mul_comm _ ((1 - b * P) ^ 2), pow_two, mul_assoc (1-b*P) (1-b*P) _,
 mul_div_cancel', mul_div_assoc, mul_div_mul_left, add_comm, ← mul_div_assoc],
rw [hb, ← hx, ne_iff_lt_or_gt],
right,
rw gt_iff_lt,
exact hx2,
iterate 2 {rw [hb, ← hx, ne_iff_lt_or_gt],
right,
rw gt_iff_lt,
rw [lt_sub, sub_zero],
exact hx1,},
rw [hb, ← hx, ne_iff_lt_or_gt],
right,
rw gt_iff_lt,
exact hx2,
exact hθ,
convert summable_pow_mul_geometric_of_norm_lt_1 1 hx1',
conv{
  find (↑_^1){rw pow_one,}
},
apply summable_geometric_of_lt_1 hx2' hx1,
exact hsum,
exact hsum2,
end

theorem BET_Brunauer_eq_26
(θ : ℕ → ℝ ){k1 k2 kads kdes a b C P q A V₀ Vads x y c : ℝ}
(hsum : summable (λ (b : ℕ), ↑b * θ b))
(hsum2 : summable (λ (b : ℕ), θ b))
-- Equations
(h1 : ∀ k, θ (k+1) = (x ^ (k+1)) * C * θ 0) -- Equation 14 from Brunauer 1938
(hA : A = ∑' (k : ℕ), θ k) -- Equation 13 from Brunauer 1938
(hVads : Vads =  V₀ * ∑' (k : ℕ), k * θ k)
(hq : q = Vads/A)
-- Definitions
(hC: C = y/x)
(hy: y = (k1/k2)*P)
(hx: x = (kads/kdes)*P)
(hc: c = k1/k2)
(ha: a = V₀*c)
(hb: b = kads/kdes)
-- Constraints
(hx1: x<1)
(hx2 : 0 < x)
(hθ : θ 0 ≠ 0)
:
Vads/(A*V₀) = C*x/((1-x)*(1-x+C*x))
:=
begin
have hBET_regression : q = a*P/((1-b*P)*(1-b*P+c*P)),
{ apply BET_regression θ hsum hsum2 h1 hA hVads hq hC hy hx hc ha hb hx1 hx2 hθ,},
rw hq at hBET_regression,
rw ← hc at hy,
rw ← hb at hx,
rw [div_mul_eq_div_div, hBET_regression, ha, mul_assoc V₀ _ _, ← hy, ← hx, hC],
field_simp,
rw [mul_div_assoc y x x, div_self, mul_comm, mul_div_mul_right, mul_comm y x, mul_div_mul_left, mul_one],
linarith,
linarith,
end

theorem BET_Brunauer_eq_28
(θ : ℕ → ℝ ){k1 k2 kads kdes a b C P q A V₀ Vads x y c P₀: ℝ}
(hsum : summable (λ (b : ℕ), ↑b * θ b))
(hsum2 : summable (λ (b : ℕ), θ b))
-- Equations
(h1 : ∀ k, θ (k+1) = (x ^ (k+1)) * C * θ 0) -- Equation 14 from Brunauer 1938
(hA : A = ∑' (k : ℕ), θ k) -- Equation 13 from Brunauer 1938
(hVads : Vads =  V₀ * ∑' (k : ℕ), k * θ k)
(hq : q = Vads/A)
-- Definitions
(hC: C = y/x)
(hy: y = (k1/k2)*P)
(hx: x = (kads/kdes)*P)
(hc: c = k1/k2)
(ha: a = V₀*c)
(hb: b = kads/kdes)
-- Constraints
(hx1: x<1)
(hx2 : 0 < x)
(hV₀ : V₀ ≠ 0)
(hθ : θ 0 ≠ 0)
:
Vads/(A*V₀) = C*x/((1-x)*(1-x+C*x))
:=
begin
have hBET_Brunauer_eq_26 : Vads/(A*V₀) = C*x/((1-x)*(1-x+C*x)),
{ apply BET_Brunauer_eq_26 θ hsum hsum2 h1 hA hVads hq hC hy hx hc ha hb hx1 hx2 hV₀ hθ,},
set α := (1-x) with h,
have h1 : filter.tendsto (λ α : ℝ, Vads) (nhds_within 0 (set.Ioi 0)) filter.at_top,
{ rw div_eq_of_eq_mul _ at hBET_Brunauer_eq_26,

  }

end