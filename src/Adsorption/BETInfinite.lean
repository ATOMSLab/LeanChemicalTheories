import analysis.complex.basic
import data.real.basic
namespace nnreal
open_locale nnreal big_operators

theorem nnreal.tsum_coe_mul_geometric_of_norm_lt_1 {r : ℝ≥0} (hr : r < 1) :
∑' (n : ℕ), (↑n) * r ^ n = r / (1 - r) ^ 2 :=
begin
have hr' : ∥(r : ℝ)∥ < 1,
{ rw [real.norm_eq_abs, abs_lt],
split,
{ refine lt_of_lt_of_le _ r.coe_nonneg, norm_num },
{ exact_mod_cast hr } },
apply nnreal.coe_injective,
convert tsum_coe_mul_geometric_of_norm_lt_1 hr',
{ norm_cast },
{ push_cast,
rw nnreal.coe_sub hr.le,
norm_cast },
end

theorem nnreal.tsum_eq_zero_add {f : ℕ → ℝ≥0} (hf : summable f) :
∑' (b : ℕ), f b = f 0 + ∑' (b : ℕ), f (b + 1) :=
begin
  apply subtype.ext,
  push_cast,
  let g : ℕ → ℝ := λ n, f n,
  have hg : summable g,
  { apply summable.map hf (nnreal.to_real_hom : ℝ≥0 →+ ℝ) continuous_induced_dom },
  exact tsum_eq_zero_add hg,
end

lemma some_name (θ : ℕ → ℝ≥0 )(k1 k2 kads kdes a b C P q A V₀ Vads x y c: ℝ≥0  )
-- Equations
(h1 : ∀ k, θ (k+1) = C * (θ 0 * x ^ (k+1))) (hA : A = ∑' (k : ℕ), θ k)
(hVads : Vads = 0 * θ 0 + ∑' (k : ℕ), C * ( θ 0 * (k * x ^ k)))(hq : q/V₀ = Vads / A)
-- Definitions
(hC: C= y/x)
(hy: y= (k1/k2)*P)
(hx: x=(kads/kdes)*P)
--
(hc: c=k1/k2)
(ha: a=c*V₀)
(hb: b= kads/kdes)
-- Constraints
(hθ: θ 0 ≠ 0)
(hx2: x<1)
(hp: P ≠ 0)
(hx1: x ≠ 0)
(hv: V₀ ≠ 0)
:
q = a*P/((1-b*P)*(1-b*P+c*P))
:=
begin
rw nnreal.tsum_eq_zero_add at hA, 
simp only [h1] at hA {single_pass := tt},
rw tsum_mul_left at hA,
rw tsum_mul_left at hA,
rw ← mul_assoc at hA,
rw mul_comm C (θ 0) at hA,
rw ← mul_one (θ 0) at hA,
rw mul_assoc at hA,
rw mul_assoc at hA,
rw ← mul_add (θ 0) at hA,
rw one_mul at hA,
simp_rw [pow_add, pow_one, tsum_mul_right] at hA,
rw tsum_geometric_nnreal hx2 at hA,
rw inv_eq_one_div at hA,
rw mul_comm (1/(1-x)) x at hA,
rw ← mul_div_assoc x 1(1 - x) at hA,
rw mul_one at hA,
rw zero_mul at hVads,
rw zero_add at hVads,
rw tsum_mul_left at hVads,
rw tsum_mul_left at hVads,
rw ← mul_assoc at hVads,
rw mul_comm C (θ 0) at hVads,
rw mul_assoc at hVads,
rw hA at hq,
rw hVads at hq,
rw mul_div_mul_left at hq,
rw nnreal.tsum_coe_mul_geometric_of_norm_lt_1 at hq,
rw ← mul_div_assoc at hq,
have h1: 1-x ≠ 0,
have h2: 0<1-x,
exact tsub_pos_of_lt hx2,
apply ne_of_gt,
exact h2,
rw ← mul_div_assoc C x(1 - x) at hq,
rw nnreal.add_div' at hq,
rw one_mul at hq,
rw div_div_div_div_eq at hq,
rw sq at hq,
rw mul_assoc (1-x) (1-x) (1-x+C*x) at hq,
rw mul_comm (C*x) (1-x) at hq,
rw mul_div_mul_left at hq,
rw mul_comm C x at hq,
rw hC at hq,
rw mul_div_assoc' at hq,
rw mul_comm x y at hq,
rw mul_div_cancel at hq,
rw hy at hq, 
rw hx at hq,
rw ← hb at hq,
rw ← hc at hq,
rw mul_comm c P at hq,
field_simp[hv] at hq,
rw mul_assoc P c V₀ at hq,
rw ← ha at hq,
rw mul_comm P a at hq,
rw mul_comm b P at hq,
rw mul_comm P b at hq,
rw mul_comm P c at hq,
exact hq,
exact hx1,
exact h1,
exact h1,
exact hx2,
exact hθ,
sorry,
end
