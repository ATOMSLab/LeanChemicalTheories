import analysis.normed_space.basic
import analysis.calculus.local_extr
import group_theory.semidirect_product
import analysis.calculus.lhopital


import math.deriv

universes u 

/-!
# Lennard-Jones potential function
We define the properties of Lennard-Jonnes potential function that describes intermolecular
pair potentials in molecular simulations. The commonly used expression is: <br>
$$
E = 4ε  [(\frac{σ}{r})^{12} - (\frac{σ}{r})^6]
$$
where:
- `E` is the intermolecular potential between the two atoms or molecules
- `ε` is the well depth and a measure of how strongly the two particles attract each other
- `σ` is the distance at which the intermolecular potential between the two particles is zero
- `r` is the distance of separation between both particles

Here we use our own proof of `deriv` defined in `math.deriv` to show that Lennard-Jones potential has its minimum 
at a distance of `r = r_min = 2^1/6 σ`, where the potential energy has the value `-ε`
-/

noncomputable theory

variables (ε minRadius: ℝ)

def LJ (ε minRadius r : ℝ)  :  ℝ := 
  let σ := (1 / 2 ^ (1 / 6:ℝ):ℝ)*minRadius in
  4*ε*(‖ σ/r‖^(12)-‖σ/r‖^(6))

lemma two_pow_one_div_six_pow_six_eq_two
:
(2 ^ (1 / 6:ℝ):ℝ) ^ (6) = (2:ℝ):=
begin
  have h : 0 ≤ (2:ℝ) := by simp,
  rw [← real.rpow_nat_cast, show ↑(6:ℕ) = (6:ℝ), by norm_num, ← real.rpow_mul h (1/6) 6],
  norm_num,
end

lemma two_pow_one_div_six_pow_twelve_eq_four
:
(2 ^ (1 / 6:ℝ):ℝ) ^ (12) = (4:ℝ):=
begin
  have h : 0 ≤ (2:ℝ) := by simp,
  rw [← real.rpow_nat_cast, show ↑(12:ℕ) = (12:ℝ), by norm_num, ← real.rpow_mul h (1/6) 12],
  norm_num,
end

lemma one_lt_six : 1 < 6 := 
begin
  norm_num,
end

lemma one_lt_twelve : 1 < 12 := 
begin
  norm_num,
end


namespace LJ 


theorem minRadius_rpow_div_const_pos : ∀ r y : ℝ, 0 < minRadius → 0 < r → 0 < y → 0 < minRadius ^ y / r:=
begin
  intros r y this that that2, 
  rw [lt_div_iff that, zero_mul],
  apply zero_lt_rpow this that2,
end

theorem const_mul_minRadius_rpow_pos : ∀ r y : ℝ, 0 < minRadius → 0 < r → 0 < y → 0 < r*minRadius^y:=
begin
  intros r y this that that2, 
  rw [zero_lt_mul_left that],
  apply zero_lt_rpow this that2,
end

lemma repulsive_2
(hminRadius : 0 < minRadius)
:
(λ r : ℝ, |minRadius/((2^(1/6:ℝ):ℝ)*r)|^(12))= λ r : ℝ, (|minRadius^(12)/4|)/|r^(12)|:=
begin
  funext,
  rw [← abs_pow, div_pow, mul_pow, two_pow_one_div_six_pow_twelve_eq_four, abs_div, abs_mul, abs_div],
  field_simp,
end

lemma repulsive_3
(hminRadius : 0 < minRadius)
:
(λ r, (|minRadius|/(|(2^(1/6:ℝ):ℝ)|*|r|))^(12))= λ r, (|minRadius^(12)/4|)/|r^(12)|:=
begin
  funext,
  rw [div_pow, mul_pow, ← abs_pow, ← abs_pow, two_pow_one_div_six_pow_twelve_eq_four, abs_div, div_div, ← abs_pow],
end

lemma repulsive_4
(hminRaiuds : 0 < minRadius)
:
(λ (r : ℝ), minRadius ^ 12 / (2 ^ (1 /6:ℝ) * r) ^ 12 ) = λ r, (minRadius^(12)/4)/r^(12):=
begin
  funext,
  rw [mul_pow, two_pow_one_div_six_pow_twelve_eq_four, div_div],
end

lemma attractive_2
(hminRadius : 0 < minRadius)
:
(λ r, |minRadius/((2^(1/6:ℝ):ℝ)*r)|^(6)) =λ r, (|minRadius^(6)/2|)/|r^(6)|:=
begin
  funext,
  rw [← abs_pow, div_pow, mul_pow, two_pow_one_div_six_pow_six_eq_two, abs_div, abs_mul, abs_div],
  field_simp,
end

lemma attractive_3
(hminRadius : 0 < minRadius)
:
(λ r, (|minRadius|/(|(2^(1/6:ℝ):ℝ)|*|r|))^(6)) = λ r, (|minRadius^(6)/2|)/|r^(6)|:=
begin
  funext,
  rw [div_pow, mul_pow, ← abs_pow, ← abs_pow, two_pow_one_div_six_pow_six_eq_two, abs_div, div_div, ← abs_pow],
end
lemma attractive_4
(hminRadius : 0 < minRadius)
:
(λ (r : ℝ), minRadius ^ 6 / (2 ^ (1 /6:ℝ) * r) ^ 6 ) = λ r, (minRadius^(6)/2)/r^(6):=
begin
  funext,
  rw [mul_pow, two_pow_one_div_six_pow_six_eq_two, div_div],
end

theorem deriv_of_LJ
(hminRadius : 0 < minRadius)
:
set.eq_on (deriv ( λ r, LJ ε minRadius r)) (λ r, 4*ε*((-3)*(minRadius^(12))/r^(13)-(-3)*(minRadius^(6))/r^(7))) ({r : ℝ | r = 0})ᶜ :=
begin
  simp_rw [LJ, real.norm_eq_abs, set.eq_on],
  intros x hx,
  simp at hx,
  simp [deriv_const_mul, mul_div_assoc],
  field_simp,
  left,
  rw [deriv_sub, repulsive_4 _ hminRadius, attractive_4 _ hminRadius, deriv_div_pow hx 12, deriv_div_pow hx 6],
  field_simp [sub_mul],
  norm_num,
  ring_exp!,
  iterate 2 {norm_num,},
  rw repulsive_4 _ hminRadius, 
  apply differentiable_at_div_pow hx 12,
  rw attractive_4 _ hminRadius, 
  apply differentiable_at_div_pow hx 6,  
end

theorem has_deriv_at_of_LJ
{r : ℝ}
(hminRadius : 0 < minRadius)
(hr : r ≠ 0)
:
has_deriv_at ( λ r, LJ ε minRadius r) (4*ε*((-3)*(minRadius^(12))/r^(13)-(-3)*(minRadius^(6))/r^(7))) r:=
begin
  simp_rw [LJ, real.norm_eq_abs],
  apply has_deriv_at.const_mul (4*ε),
  rw [mul_comm, mul_div, mul_one],
  apply has_deriv_at.sub,
  simp,
  convert has_deriv_at_div_pow hr _ one_lt_twelve,
  field_simp [two_pow_one_div_six_pow_twelve_eq_four],
  ring_exp,
  simp,
  convert has_deriv_at_div_pow hr _ one_lt_six,
  field_simp [two_pow_one_div_six_pow_six_eq_two],
  ring_exp,
end

theorem has_deriv_at_of_LJ'
{r : ℝ}
:
has_deriv_at (λ (x : ℝ), 2 * x ^ 6 / minRadius ^ 6 - 4 * x ^ 12 / minRadius ^ 12) (6*r^5*(2/minRadius^6) - 12*r^11*(4/minRadius^12)) r:=
begin
  apply has_deriv_at.sub,
  simp [mul_comm (2 : ℝ) _, mul_div_assoc],
  apply has_deriv_at.mul_const,
  rw [show 5 = 6-1, by simp, show (6 : ℝ) = ↑6, by norm_num],
  apply has_deriv_at_pow,
  simp [mul_comm (4 : ℝ) _, mul_div_assoc],
  apply has_deriv_at.mul_const,
  rw [show 11 = 12-1, by simp, show (12 : ℝ) = ↑12, by norm_num],
  apply has_deriv_at_pow,
end

-- theorem deriv_of_LJ'
-- {x : ℝ}
-- (hminRadius : 0 < minRadius)
-- (hx : x ≠ 0)
-- :
-- (deriv_within  (λ r, LJ ε minRadius r)) ({r : ℝ | r = 0})ᶜ x = 4*ε*((-3)*(minRadius^(12))/x^(13)-(-3)*(minRadius^(6))/x^(7)) :=
-- begin
--   have hu : unique_diff_within_at ℝ ({r : ℝ | r = 0})ᶜ x,
--   { rw unique_diff_within_at_iff,
--     split,
--     simp [dense],
--     intro y,
--      },
--   simp [LJ, deriv_within_mul_const],
--   rw deriv_within_const_mul,
--   field_simp [← div_div],
--   rw deriv_within_sub,
-- end
-- theorem deriv2_of_LJ
-- (hminRadius : 0 < minRadius)
-- : 
-- set.eq_on  (deriv^[2] (λ x, LJ ε minRadius x)) (λ x, ε*(156*minRadius^(12:ℝ)/x^(14:ℝ)-84*minRadius^(6:ℝ)/x^(8:ℝ))) ({r : ℝ | r = 0})ᶜ
-- :=
-- begin
--   rw set.eq_on,
--   intros x hx,
--   simp,
--   have h1 : set.eq_on (deriv (λ r, LJ ε minRadius r)) (λ r, 4*ε*((-3)*(minRadius^(12))/r^(13)-(-3)*(minRadius^(6))/r^(7))) ({r : ℝ | r = 0})ᶜ, from deriv_of_LJ _ _ hminRadius,
--   rw set.eq_on at h1,
--   specialize h1 hx,
  
-- end

-- theorem deriv_at_minEnergy
-- (hrpos : ∀ r : ℝ, 0 < r)
-- :
-- deriv (λ r, LJ ε minRadius r) minRadius = 0 :=
-- begin
--   rw deriv_of_LJ ε minRadius hrpos,
--   simp,
--   right,
--   ring_exp,
--   have h3 : minRadius ≠ 0 := by {specialize hrpos minRadius, linarith},
--   field_simp,
--   rw [neg_div, mul_comm _ (3:ℝ), mul_div_assoc, ← rpow_sub (hrpos minRadius), mul_comm _ (3:ℝ), mul_div_assoc, ← rpow_sub (hrpos minRadius)],
--   norm_num,

-- end

-- theorem deriv2_nonneg
-- (hrpos : ∀ r : ℝ, 0 < r)
-- :
--  0 ≤  (deriv^[2] (LJ ε minRadius) minRadius)  :=
-- begin
--   rw deriv2_of_LJ ε minRadius hrpos,
--   field_simp [hrpos ε, mul_div_assoc, ← rpow_sub (hrpos minRadius)],
--   norm_num,
--   apply decidable.mul_le_mul_of_nonneg_right,
--   norm_num,
--   apply real.rpow_nonneg_of_nonneg (le_of_lt (hrpos minRadius)),
-- end

-- def convex_zone (minRadius : ℝ) := set.Ioo (0:ℝ) ((13/7)^(1/6:ℝ)*minRadius)

-- lemma differentiable_at_LJ 
-- (hrpos : ∀ r : ℝ, 0 < r)
-- :
-- ∀ x, differentiable_at ℝ (λ r, LJ ε minRadius r) x:=
-- begin
--   intro,
--   simp [LJ],
--   apply differentiable_at.const_mul _ (4*ε),
--   field_simp,
--   apply differentiable_at.sub,
--   rw repulsive_3 _ hrpos,
--   apply differentiable_at_inv_abs_rpow (hrpos x) (@minRadius_rpow_div_const_pos minRadius 4 12 (hrpos minRadius) zero_lt_four zero_lt_twelve) hrpos,
--   norm_num,
--   rw attractive_3 _ hrpos,
--   apply differentiable_at_inv_abs_rpow (hrpos x) (@minRadius_rpow_div_const_pos minRadius 2 6 (hrpos minRadius) zero_lt_two zero_lt_six) hrpos,
--   norm_num,
-- end

-- lemma differentiable_at_deriv_LJ
-- (hrpos : ∀ r : ℝ, 0 < r)
-- :
-- ∀ x, differentiable_at ℝ (deriv (λ r, LJ ε minRadius r)) x:=
-- begin
--   intro,
--   rw deriv_of_LJ _ _ hrpos,
--   apply differentiable_at.const_mul _ (4*ε),
--   field_simp,
--   apply differentiable_at.sub (differentiable_at_inv_rpow (hrpos x) _ _) (differentiable_at_inv_rpow (hrpos x) _ _),
--   iterate 2 {norm_num,},
-- end

-- lemma continuous_on_convex_zone 
-- (hrpos : ∀ r : ℝ, 0 < r)
-- :
-- continuous_on (LJ ε minRadius) (convex_zone minRadius) :=
-- begin
--   apply @differentiable_on.continuous_on ℝ,
--   apply differentiable.differentiable_on,
--   rw differentiable,
--   exact (differentiable_at_LJ _ _ hrpos),
-- end

-- lemma differentiable_on_convex_zone
-- (hrpos : ∀ r : ℝ, 0 < r)
-- :
-- differentiable_on ℝ (LJ ε minRadius) (interior (convex_zone minRadius)):=
-- begin
--   simp [convex_zone],
--   apply differentiable.differentiable_on,
--   rw differentiable,
--   exact (differentiable_at_LJ _ _ hrpos),  
-- end

-- lemma differentiable_of_deriv_on_convex_zone
-- (hrpos : ∀ r : ℝ, 0 < r)
-- :
-- differentiable_on ℝ (deriv (LJ ε minRadius)) (interior (convex_zone minRadius)):=
-- begin
--   simp [convex_zone],
--   apply differentiable.differentiable_on,
--   rw differentiable, 
--   exact (differentiable_at_deriv_LJ _ _ hrpos),
-- end

-- lemma deriv2_of_convex_zone_nonneg 
-- (hrpos : ∀ r : ℝ, 0 < r)
-- :
-- ∀ x ∈ (convex_zone minRadius), 0 ≤ (deriv^[2] (LJ ε minRadius) x):=
-- begin
--   intros x h,
--   let h1 := deriv2_of_LJ ε minRadius hrpos,
--   rw h1,
--   simp only [convex_zone] at h,
--   cases h with hl hu,
--   field_simp [hrpos ε],
--   rw [show x^(14:ℝ) = x^(6:ℝ)*x^(8:ℝ), by {rw ← real.rpow_add (hrpos x), norm_num}, show minRadius^(12:ℝ) = minRadius^(6:ℝ)*minRadius^(6:ℝ), by {rw ← real.rpow_add (hrpos minRadius), norm_num},
--   mul_div_assoc, mul_div_assoc, mul_div_mul_comm, ← mul_assoc, mul_le_mul_right (hrpos (minRadius^(6:ℝ)/x^(8:ℝ))), ← mul_div_assoc, le_div_iff (hrpos (x^(6:ℝ))),
--   ← le_div_iff' (hrpos (84:ℝ)), mul_comm (156:ℝ) _, mul_div_assoc],
--   norm_num,
--   apply le_of_lt,
--   rw [mul_comm, show (13/7)*minRadius^(6:ℝ) = ((13/7)^(1/6:ℝ)*minRadius)^(6:ℝ), by {rw [mul_rpow, ← rpow_mul], norm_num, norm_num, apply le_of_lt, apply zero_lt_rpow,
--   norm_num, norm_num, linarith [hrpos minRadius],}],
--   apply rpow_lt_rpow _ hu _,
--   linarith [hrpos x],
--   norm_num,
-- end

-- theorem convex_on
-- (hrpos : ∀ r : ℝ, 0 < r)
-- :
-- convex_on ℝ (convex_zone minRadius) (LJ ε minRadius) :=
-- begin
--   apply convex_on_of_deriv2_nonneg (convex_Ioo _ _) (continuous_on_convex_zone _ _ hrpos) (differentiable_on_convex_zone _ _ hrpos) (differentiable_of_deriv_on_convex_zone _ _ hrpos),
--   intros x h,
--   apply deriv2_of_convex_zone_nonneg _ _ hrpos,
--   simp [convex_zone],
--   simp at h,
--   exact h,
-- end

lemma sub_to_div
{f g : ℝ → ℝ}
(hf : ∀ x, f x ≠ 0)
(hg : ∀ x, g x ≠ 0)
: (λ x, f x - g x) = λ x, (1/g x-1/f x)/(1/(f x * g x)):=
begin
  field_simp,
  funext,
  field_simp [hf x, hg x],
  left,
  rw mul_comm,
end

lemma sub_eq_mul_one_sub_div 
{f g : ℝ → ℝ}
(s : set ℝ)
(hf : ∀ x ∈ s, f x ≠ 0)
: set.eq_on (λ x, f x - g x) (λ x, f x * (1 - g x / f x)) s:=
begin
  rw set.eq_on,
  intros x hx,
  funext,
  rw mul_sub,
  field_simp [hf x hx, sub_mul],
  rw mul_comm,
end

lemma fun_sub
{f g : ℝ → ℝ}
:(λ x, f x - g x )= (λ x, f x) - λ x, g x := by {funext, simp}

lemma inv_of_pow_eq_neg_pow 
{x : ℝ}
(n : ℕ)
: (x^n)⁻¹ = x^(-(n:ℤ)) :=
begin
  simp,
end

lemma inv_of_zpow_eq_neg_pow 
{x : ℝ}
(z : ℤ)
: (x^z)⁻¹ = x^(-(z)) :=
begin
  simp,
end
-- lemma lhopital_tendsto_pow_div_pow_zero_at_zero 
-- {n m : ℕ}
-- (hmn : n < m)
-- (hn : (0 : ℝ) < n)
-- : filter.tendsto (λ x : ℝ, x^m/x^n) (nhds_within 0 (set.Ioi 0)) (nhds 0) :=
-- begin
--   have hn' : 0 < n, by {norm_cast at hn, linarith [hn]},
--   have hm' : 0 < m, by exact lt_trans hn' hmn,
--   have hfa : filter.tendsto (λ x : ℝ, x^m) (nhds_within 0 (set.Ioi 0)) (nhds 0),
--   { rw show nhds (0 : ℝ) = nhds (0^m), by {simp, rw zero_pow hm'}, apply filter.tendsto.pow, rw nhds_within, apply filter.tendsto_inf_left, finish,},
--   have hga : filter.tendsto (λ x : ℝ, x^n) (nhds_within 0 (set.Ioi 0)) (nhds 0),
--   { rw show nhds (0 : ℝ) = nhds (0^n), by {simp, rw zero_pow hn'}, apply filter.tendsto.pow, rw nhds_within, apply filter.tendsto_inf_left, finish,},
  
-- end

lemma tendsto_at_zero_pow_seven_div_pow_one
: filter.tendsto (λ x : ℝ, x^7/x) (nhds_within 0 (set.Ioi 0)) (nhds 0):=
begin
  have h1 : (0 : ℝ) < 1, by norm_num,
  have h7 : (0 : ℝ) < 7, by norm_num,
  apply has_deriv_at.lhopital_zero_right_on_Ioo,
  exact zero_lt_two,
  intros x hx,
  apply has_deriv_at_pow,
  intros x hx,
  conv {find (λ x : ℝ, x) {rw ← pow_one x},  },
  apply has_deriv_at_pow,
  intros x hx,
  norm_cast,
  rw ← ne.def,
  apply mul_ne_zero h1.ne',
  apply ne_of_gt (pow_pos hx.1 _),
  rw show nhds (0 : ℝ) = nhds (0^7), by {rw zero_pow, linarith [h7],},
  apply filter.tendsto.pow,
  rw nhds_within,
  apply filter.tendsto_inf_left,
  finish,
  rw show nhds (0 : ℝ) = nhds (0^1), by {rw zero_pow, linarith [h1],},
  conv {find (λ x : ℝ, x) {rw ← pow_one x},  },
  apply filter.tendsto.pow,
  rw nhds_within,
  apply filter.tendsto_inf_left,
  finish,
  norm_num,
  rw show nhds (0 : ℝ) = nhds(7*0), by simp,
  apply filter.tendsto.const_mul,
  rw nhds_within,
  apply filter.tendsto_inf_left,
  rw show nhds (0 : ℝ) = nhds (0^6), by {rw zero_pow, norm_num,},
  apply filter.tendsto.pow,
  finish,
end

lemma tendsto_at_zero_pow_eight_div_pow_two
: filter.tendsto (λ x : ℝ, x^8/x^2) (nhds_within 0 (set.Ioi 0)) (nhds 0):=
begin
  have h2 : (0 : ℝ) < 2, by norm_num,
  have h8 : (0 : ℝ) < 8, by norm_num,
  apply has_deriv_at.lhopital_zero_right_on_Ioo,
  exact zero_lt_two,
  intros x hx,
  apply has_deriv_at_pow,
  intros x hx,
  apply has_deriv_at_pow,
  intros x hx,
  norm_cast,
  rw ← ne.def,
  apply mul_ne_zero h2.ne',
  apply ne_of_gt (pow_pos hx.1 _),
  rw show nhds (0 : ℝ) = nhds (0^8), by {rw zero_pow, linarith [h8],},
  apply filter.tendsto.pow,
  rw nhds_within,
  apply filter.tendsto_inf_left,
  finish,
  rw show nhds (0 : ℝ) = nhds (0^2), by {rw zero_pow, linarith [h2],},
  apply filter.tendsto.pow,
  rw nhds_within,
  apply filter.tendsto_inf_left,
  finish,
  norm_num,
  simp [mul_div_mul_comm],
  norm_num,
  rw show nhds (0 : ℝ) = nhds (4*0), by simp,
  apply filter.tendsto.const_mul,
  apply tendsto_at_zero_pow_seven_div_pow_one,
end


lemma tendsto_at_zero_pow_nine_div_pow_three
: filter.tendsto (λ x : ℝ, x^9/x^3) (nhds_within 0 (set.Ioi 0)) (nhds 0):=
begin
  have h3 : (0 : ℝ) < 3, by norm_num,
  have h9 : (0 : ℝ) < 9, by norm_num,
  apply has_deriv_at.lhopital_zero_right_on_Ioo,
  exact zero_lt_two,
  intros x hx,
  apply has_deriv_at_pow,
  intros x hx,
  apply has_deriv_at_pow,
  intros x hx,
  norm_cast,
  rw ← ne.def,
  apply mul_ne_zero h3.ne',
  apply ne_of_gt (pow_pos hx.1 _),
  rw show nhds (0 : ℝ) = nhds (0^9), by {rw zero_pow, linarith [h9],},
  apply filter.tendsto.pow,
  rw nhds_within,
  apply filter.tendsto_inf_left,
  finish,
  rw show nhds (0 : ℝ) = nhds (0^3), by {rw zero_pow, linarith [h3],},
  apply filter.tendsto.pow,
  rw nhds_within,
  apply filter.tendsto_inf_left,
  finish,
  norm_num,
  simp [mul_div_mul_comm],
  norm_num,
  rw show nhds (0 : ℝ) = nhds (3*0), by simp,
  apply filter.tendsto.const_mul,
  apply tendsto_at_zero_pow_eight_div_pow_two,
end

lemma tendsto_at_zero_pow_ten_div_pow_four
: filter.tendsto (λ x : ℝ, x^10/x^4) (nhds_within 0 (set.Ioi 0)) (nhds 0):=
begin
  have h4 : (0 : ℝ) < 4, by norm_num,
  have h10 : (0 : ℝ) < 10, by norm_num,
  apply has_deriv_at.lhopital_zero_right_on_Ioo,
  exact zero_lt_two,
  intros x hx,
  apply has_deriv_at_pow,
  intros x hx,
  apply has_deriv_at_pow,
  intros x hx,
  norm_cast,
  rw ← ne.def,
  apply mul_ne_zero h4.ne',
  apply ne_of_gt (pow_pos hx.1 _),
  rw show nhds (0 : ℝ) = nhds (0^10), by {rw zero_pow, linarith [h10],},
  apply filter.tendsto.pow,
  rw nhds_within,
  apply filter.tendsto_inf_left,
  finish,
  rw show nhds (0 : ℝ) = nhds (0^4), by {rw zero_pow, linarith [h4],},
  apply filter.tendsto.pow,
  rw nhds_within,
  apply filter.tendsto_inf_left,
  finish,
  norm_num,
  simp [mul_div_mul_comm],
  norm_num,
  rw show nhds (0 : ℝ) = nhds (5/2*0), by simp,
  apply filter.tendsto.const_mul,
  apply tendsto_at_zero_pow_nine_div_pow_three,
end

lemma tendsto_at_zero_pow_eleven_div_pow_five
: filter.tendsto (λ x : ℝ, x^11/x^5) (nhds_within 0 (set.Ioi 0)) (nhds 0):=
begin
  have h5 : (0 : ℝ) < 5, by norm_num,
  have h11 : (0 : ℝ) < 11, by norm_num,
  apply has_deriv_at.lhopital_zero_right_on_Ioo,
  exact zero_lt_two,
  intros x hx,
  apply has_deriv_at_pow,
  intros x hx,
  apply has_deriv_at_pow,
  intros x hx,
  norm_cast,
  rw ← ne.def,
  apply mul_ne_zero h5.ne',
  apply ne_of_gt (pow_pos hx.1 _),
  rw show nhds (0 : ℝ) = nhds (0^11), by {rw zero_pow, linarith [h11],},
  apply filter.tendsto.pow,
  rw nhds_within,
  apply filter.tendsto_inf_left,
  finish,
  rw show nhds (0 : ℝ) = nhds (0^5), by {rw zero_pow, linarith [h5],},
  apply filter.tendsto.pow,
  rw nhds_within,
  apply filter.tendsto_inf_left,
  finish,
  norm_num,
  simp [mul_div_mul_comm],
  rw show nhds (0 : ℝ) = nhds (11/5*0), by simp,
  apply filter.tendsto.const_mul,
  apply tendsto_at_zero_pow_ten_div_pow_four,
end

lemma tendsto_at_zero_pow_twelve_div_pow_six
: filter.tendsto (λ x : ℝ, x^12/x^6) (nhds_within 0 (set.Ioi 0)) (nhds 0) :=
 begin
  have h6 : (0 : ℝ) < 6, by norm_num,
  have h12 : (0 : ℝ) < 12, by norm_num,
  apply has_deriv_at.lhopital_zero_right_on_Ioo,
  exact zero_lt_two,
  intros x hx,
  apply has_deriv_at_pow,
  intros x hx,
  apply has_deriv_at_pow,
  intros x hx,
  norm_cast,
  rw ← ne.def,
  apply mul_ne_zero h6.ne',
  apply ne_of_gt (pow_pos hx.1 _),
  rw show nhds (0 : ℝ) = nhds (0^12), by {rw zero_pow, linarith [h12],},
  apply filter.tendsto.pow,
  rw nhds_within,
  apply filter.tendsto_inf_left,
  finish,
  rw show nhds (0 : ℝ) = nhds (0^6), by {rw zero_pow, linarith [h6],},
  apply filter.tendsto.pow,
  rw nhds_within,
  apply filter.tendsto_inf_left,
  finish,
  norm_num,
  simp [mul_div_mul_comm],
  norm_num,
  rw show nhds (0 : ℝ) = nhds (2*0), by simp,
  apply filter.tendsto.const_mul,
  apply tendsto_at_zero_pow_eleven_div_pow_five,
end
lemma sub_to_div'
(hm :  0 < minRadius)
:set.eq_on (λ (x : ℝ),  minRadius ^ 12 / (2 ^ (6 : ℝ)⁻¹) ^ 12 / x ^ 12 - minRadius ^ 6 / (2 ^ (6 : ℝ)⁻¹) ^ 6 / x ^ 6) 
(λ (x : ℝ),  minRadius ^ 12 / (2 ^ (6 : ℝ)⁻¹) ^ 12 / x ^ 12 * ( 1 - minRadius ^ 6 / (2 ^ (6 : ℝ)⁻¹) ^ 6 / x ^ 6 / (minRadius ^ 12 / (2 ^ (6 : ℝ)⁻¹) ^ 12 / x ^ 12))) 
{r : ℝ | r ≠ 0}
:=
begin
  rw set.eq_on,
  intros x hx,
  simp at hx,
  rw ← ne.def at hx,
  rw [mul_sub, mul_one, ← mul_div_assoc, mul_div_cancel_left],
  field_simp,
  push_neg,
  split,
  exact ne_of_gt hm,
  apply mul_ne_zero _ (pow_ne_zero _ hx),
  apply pow_ne_zero,
  apply rpow_ne_zero (zero_lt_two),
  norm_num,
end
lemma sub_to_div''
(hm : 0 < minRadius)
(hx : ∀ x, x ∈ {r : ℝ | r ≠ 0})
:(λ (x : ℝ),  minRadius ^ 12 / (2 ^ (6 : ℝ)⁻¹) ^ 12 / x ^ 12 - minRadius ^ 6 / (2 ^ (6 : ℝ)⁻¹) ^ 6 / x ^ 6) =
(λ (x : ℝ),  minRadius ^ 12 / (2 ^ (6 : ℝ)⁻¹) ^ 12 / x ^ 12 * ( 1 - minRadius ^ 6 / (2 ^ (6 : ℝ)⁻¹) ^ 6 / x ^ 6 / (minRadius ^ 12 / (2 ^ (6 : ℝ)⁻¹) ^ 12 / x ^ 12))) 
:=
begin
  let H := sub_to_div' _ hm,
  simp [set.eq_on] at H,
  funext,
  exact H (hx x),
end
end LJ
