
import analysis.complex.basic
import data.real.basic
import algebra.ring.basic
open_locale big_operators
theorem BET 
(θ : ℕ → ℝ ){ k1 k2 kads kdes a b C P q A V₀ Vads x y c : ℝ}
(hsum : summable (λ (b : ℕ), ↑b * θ b))
(hsum2 : summable (λ (b : ℕ), θ b))
-- Equations
(h1 : ∀ k, θ (k+1) = (x ^ (k+1)) * C * θ 0) 
(hA : A = ∑' (k : ℕ), θ k)
(hVads : Vads =  V₀ * ∑' (k : ℕ), k * θ k)
(hq : q = Vads/A)
-- Definitions
(hC: C = y/(x))
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
rw [mul_assoc, inv_eq_one_div, mul_comm (1/(1-x)) _, ← mul_div_assoc, mul_one, mul_comm] at hA,
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
