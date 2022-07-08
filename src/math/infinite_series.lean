import data.real.basic
import analysis.complex.basic


open_locale big_operators

theorem tsum_coe_mul_geometric_add_zero
{x : ℝ} (hx1: x<1) (hx2 : 0 < x)
:
∑' k : ℕ, (k + 1 : ℝ)*(x^(k+1)) = x/(1-x)^2
:=
begin
  have hxnorm : ∥x∥ < 1, by refine abs_lt.mpr ⟨_, _⟩ ; linarith,  
  conv{find (_*_){rw [pow_succ, mul_comm x _, ← mul_assoc, right_distrib, one_mul],}},
  rw [tsum_mul_right, tsum_add, tsum_coe_mul_geometric_of_norm_lt_1, tsum_geometric_of_lt_1, inv_eq_one_div, right_distrib,
  show x/(1-x)^2*x = x^2/(1-x)^2, by {field_simp, rw ← pow_two}, mul_comm (1/_) x, ← mul_div_assoc x 1 _, mul_one, show  x^2/(1-x)^2+x/(1-x) = x/(1-x)^2, 
  by {rw [show x^2/(1-x)^2+x/(1-x) = x/(1-x)*(x/(1-x)+1), by {rw left_distrib, simp, rw [← pow_two, div_pow]}, pow_two,
  div_mul_eq_div_div, div_add_one], field_simp, nlinarith}],
  iterate 3 {linarith},
  simpa using summable_pow_mul_geometric_of_norm_lt_1 1 hxnorm,
  simpa using summable_geometric_of_norm_lt_1 hxnorm,
end

namespace nnreal

theorem tsum_eq_zero_add {f : ℕ → nnreal} (hf : summable f) :
∑' (b : ℕ), f b = f 0 + ∑' (b : ℕ), f (b + 1) :=
begin
  apply subtype.ext,
  push_cast,
  let g : ℕ → ℝ := λ n, f n,
  have hg : summable g,
  { apply summable.map hf (nnreal.to_real_hom : nnreal →+ ℝ) continuous_induced_dom },
  exact tsum_eq_zero_add hg,
end

theorem tsum_coe_mul_geometric_of_norm_lt_1 {r : nnreal} (hr : r < 1) :
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

theorem summable_coe_mul_geometric_of_
{r : nnreal} (h1 : r < 1)
:
∑' (n : ℕ), r ^ (n+1) = r / (1 - r)
:=
begin
conv{
  find(r^_){rw pow_succ},
},
rw nnreal.tsum_mul_left,
rw tsum_geometric_nnreal h1,
finish,
end
theorem tsum_mul_geometric_succ
{r : nnreal} (h1 : r < 1)
:
∑' (n : ℕ),(↑n+1)*r^(n+1) = r/(1-r)^2
:=
begin
rw ← tsum_coe_mul_geometric_of_norm_lt_1 h1,
symmetry,
rw tsum_eq_zero_add,
simp,

end

theorem tsum_mul_geometric_succ
{r : nnreal} (hr : r < 1)
:
∑' (n : ℕ),(↑n+1)*r^(n+1) = r/(1-r)^2
:=
begin
have h1: ∑' (n:ℕ), ↑n^1*r^n = r/(1-r)^2,
{ring_nf,
rw tsum_coe_mul_geometric_of_norm_lt_1 hr,},
have hr' : ∥(r : ℝ)∥ < 1,
{ rw [real.norm_eq_abs, abs_lt],
split,
{ refine lt_of_lt_of_le _ r.coe_nonneg, norm_num },
{ exact_mod_cast hr } },
have h2: summable (λ(n:ℕ), ↑n^1*r^n),
{ 
  },



end
