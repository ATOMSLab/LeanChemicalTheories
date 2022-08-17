import analysis.normed_space.basic
import analysis.calculus.local_extr
import group_theory.semidirect_product


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

def LJ (ε minRadius r: ℝ) : ℝ := 
  let σ := (1 / 2 ^ (1 / 6:ℝ):ℝ)*minRadius in
  4*ε*(∥σ/r∥^(12:ℝ)-∥σ/r∥^(6:ℝ))

open real

lemma zero_lt_six
{α : Type u} [ordered_semiring α] [nontrivial α]
:0 < (6:α):= add_pos zero_lt_three zero_lt_three

lemma zero_lt_twelve
{α : Type u} [ordered_semiring α] [nontrivial α]
:0 < (12:α):= add_pos zero_lt_six zero_lt_six

lemma zero_le_two_pow_one_div_six
:(0:ℝ) ≤ (2:ℝ)^(1/6:ℝ) :=
begin
  rw le_iff_lt_or_eq,
  left,
  apply zero_lt_rpow,
  iterate 2 {simp},
  exact zero_lt_three,
end

lemma zero_lt_two_pow_one_div_six
:(0:ℝ) < (2:ℝ)^(1/6:ℝ) :=
begin
  apply zero_lt_rpow,
  iterate 2 {simp},
  exact zero_lt_three,
end

lemma two_pow_one_div_six_pow_six_eq_two
:
(2 ^ (1 / 6:ℝ):ℝ) ^ (6:ℝ) = (2:ℝ):=
begin
  have h : 0 ≤ (2:ℝ) := by simp,
  rw [ ← real.rpow_mul h (1/6) 6],
  norm_num,
end

lemma two_pow_one_div_six_pow_twelve_eq_four
:
(2 ^ (1 / 6:ℝ):ℝ) ^ (12:ℝ) = (4:ℝ):=
begin
  have h : 0 ≤ (2:ℝ) := by simp,
  rw [ ← real.rpow_mul h (1/6) 12],
  norm_num,
end

namespace LJ 

lemma zero_le_LJ
(hrpos : ∀ r : ℝ, 0 < r)
:
∀ r : ℝ, (0:ℝ) ≤ minRadius / ((2 ^ (1 / 6:ℝ):ℝ) * r):=
begin
  intro,
  simp,
  ring_nf,
  rw zero_le_mul_right,
  simp,
  rw zero_le_mul_left,
  simp,
  refine le_of_lt (hrpos r),
  field_simp,
  simp,
  field_simp,
  exact zero_lt_two_pow_one_div_six,
  refine (hrpos minRadius),
end

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
(hrpos : ∀ r : ℝ, 0 < r)
:
(λ r : ℝ, |minRadius/((2^(1/6:ℝ):ℝ)*r)|^(12:ℝ))= λ r : ℝ,(|minRadius^(12:ℝ)/4|)/|r^(12:ℝ)|:=
begin
  have hcon : ∀ r : ℝ, (0:ℝ) ≤ minRadius / ((2 ^ (1 / 6:ℝ):ℝ) * r) := by exact @zero_le_LJ minRadius hrpos, 
  funext,
  rw [← abs_rpow_of_nonneg (hcon r), div_rpow, mul_rpow, two_pow_one_div_six_pow_twelve_eq_four, abs_div, abs_mul, abs_div],
  field_simp,
  exact zero_le_two_pow_one_div_six,
  refine le_of_lt (hrpos r),
  rw le_iff_lt_or_eq,
  left,
  exact (hrpos minRadius),
  rw zero_le_mul_left,
  refine le_of_lt (hrpos r),
  exact zero_lt_two_pow_one_div_six,
end

lemma repulsive_3
(hrpos : ∀ r : ℝ, 0 < r)
:
(λ r : ℝ, (|minRadius|/(|(2^(1/6:ℝ):ℝ)|*|r|))^(12:ℝ))= λ r : ℝ,(|minRadius^(12:ℝ)/4|)/|r^(12:ℝ)|:=
begin
  have hcon : ∀ r : ℝ, (0:ℝ) ≤ minRadius / ((2 ^ (1 / 6:ℝ):ℝ) * r) := by exact @zero_le_LJ minRadius hrpos, 
  funext,
  rw [div_rpow, ← abs_rpow_of_nonneg, mul_rpow, ← abs_rpow_of_nonneg, ← abs_rpow_of_nonneg, two_pow_one_div_six_pow_twelve_eq_four, abs_div],
  field_simp,
  linarith [hrpos r],  
  exact zero_le_two_pow_one_div_six,
  simp,
  simp,
  linarith [hrpos minRadius], 
  simp,
  simp [← abs_mul],
end

lemma attractive_2
(hrpos : ∀ r : ℝ, 0 < r)
:
(λ r : ℝ, |minRadius/((2^(1/6:ℝ):ℝ)*r)|^(6:ℝ)) = λ r : ℝ,(|minRadius^(6:ℝ)/2|)/|r^(6:ℝ)|:=
begin
  have hcon : ∀ r : ℝ, (0:ℝ) ≤ minRadius / ((2 ^ (1 / 6:ℝ):ℝ) * r) := by exact @zero_le_LJ minRadius hrpos, 
  funext,
  rw [← abs_rpow_of_nonneg (hcon r), div_rpow, mul_rpow, two_pow_one_div_six_pow_six_eq_two, abs_div, abs_mul, abs_div],
  field_simp,
  exact zero_le_two_pow_one_div_six,
  refine le_of_lt (hrpos r),
  rw le_iff_lt_or_eq,
  left,
  exact (hrpos minRadius),
  rw zero_le_mul_left,
  refine le_of_lt (hrpos r),
  exact zero_lt_two_pow_one_div_six,
end

lemma attractive_3
(hrpos : ∀ r : ℝ, 0 < r)
:
(λ r : ℝ, (|minRadius|/(|(2^(1/6:ℝ):ℝ)|*|r|))^(6:ℝ)) = λ r : ℝ,(|minRadius^(6:ℝ)/2|)/|r^(6:ℝ)|:=
begin
  have hcon : ∀ r : ℝ, (0:ℝ) ≤ minRadius / ((2 ^ (1 / 6:ℝ):ℝ) * r) := by exact @zero_le_LJ minRadius hrpos, 
  funext,
  rw [div_rpow, ← abs_rpow_of_nonneg, mul_rpow, ← abs_rpow_of_nonneg, ← abs_rpow_of_nonneg, two_pow_one_div_six_pow_six_eq_two, abs_div],
  field_simp,
  linarith [hrpos r],  
  exact zero_le_two_pow_one_div_six,
  simp,
  simp,
  linarith [hrpos minRadius], 
  simp,
  simp [← abs_mul],
end

theorem deriv_of_LJ
(hrpos : ∀ r : ℝ, 0 < r)
:
(deriv (λ r, LJ ε minRadius r)) = λ r, 4*ε*((-3)*(minRadius^(12:ℝ))/r^(13:ℝ)-(-3)*(minRadius^(6:ℝ))/r^(7:ℝ)) :=
begin
  simp_rw [LJ, real.norm_eq_abs],
  simp [deriv_const_mul, mul_div_assoc],
  funext,
  field_simp,
  left,
  have hx : 0 < x, {  specialize hrpos x, linarith},
  rw [deriv_sub, @repulsive_2 minRadius hrpos, @attractive_2 minRadius hrpos,
  deriv_inv_abs_rpow (hrpos x) (@minRadius_rpow_div_const_pos minRadius 2 6 (hrpos minRadius) zero_lt_two zero_lt_six) hrpos,
  deriv_inv_abs_rpow (hrpos x) (@minRadius_rpow_div_const_pos minRadius 4 12 (hrpos minRadius) zero_lt_four zero_lt_twelve) hrpos],
  norm_num,
  field_simp,
  rw [neg_div, neg_div, show (12:ℝ) = 4*3, by norm_num, mul_assoc, mul_div_mul_left,
  show (6:ℝ) = 2*3, by norm_num, mul_assoc, mul_div_mul_left],
  field_simp,
  iterate 4 {norm_num},
  rw @repulsive_2 minRadius hrpos,
  apply differentiable_at_inv_abs_rpow (hrpos x) (@minRadius_rpow_div_const_pos minRadius 4 12 (hrpos minRadius) zero_lt_four zero_lt_twelve) hrpos,
  norm_num,
  rw @attractice_2 minRadius hrpos,
  apply differentiable_at_inv_abs_rpow (hrpos x) (@minRadius_rpow_div_const_pos minRadius 2 6 (hrpos minRadius) zero_lt_two zero_lt_six) hrpos,
  norm_num,
end

theorem deriv2_of_LJ
(hrpos : ∀ r : ℝ, 0 < r)
: 
(deriv^[2] (LJ ε minRadius)) = λ r, ε*(156*minRadius^(12:ℝ)/r^(14:ℝ)-84*minRadius^(6:ℝ)/r^(8:ℝ))
:=
begin
  simp,
  rw deriv_of_LJ ε minRadius hrpos,
  simp,
  funext,
  rw deriv_sub (differentiable_at_inv_rpow (hrpos x) _ _) (differentiable_at_inv_rpow (hrpos x) _ _),
  rw [deriv_inv_rpow (hrpos x), deriv_inv_rpow (hrpos x)],
  field_simp [← mul_assoc, mul_comm _ ε],
  rw [mul_assoc ε _ _, mul_sub],
  iterate 2 {rw [← mul_div_assoc (4:ℝ) _ _, ← mul_assoc (4:ℝ) _ (minRadius^_)],},
  iterate 5 {norm_num,},
end

theorem deriv_at_minEnergy
(hrpos : ∀ r : ℝ, 0 < r)
:
deriv (λ r, LJ ε minRadius r) minRadius = 0 :=
begin
  rw deriv_of_LJ ε minRadius hrpos,
  simp,
  right,
  ring_exp,
  have h3 : minRadius ≠ 0 := by {specialize hrpos minRadius, linarith},
  field_simp,
  rw [neg_div, mul_comm _ (3:ℝ), mul_div_assoc, ← rpow_sub (hrpos minRadius), mul_comm _ (3:ℝ), mul_div_assoc, ← rpow_sub (hrpos minRadius)],
  norm_num,
end

theorem LJ_deriv_2_pos
(hrpos : ∀ r : ℝ, 0 < r)
:
 0 ≤  (deriv^[2] (LJ ε minRadius) minRadius)  :=
begin
  rw deriv2_of_LJ ε minRadius hrpos,
  field_simp [hrpos ε, mul_div_assoc, ← rpow_sub (hrpos minRadius)],
  norm_num,
  apply decidable.mul_le_mul_of_nonneg_right,
  norm_num,
  apply real.rpow_nonneg_of_nonneg (le_of_lt (hrpos minRadius)),
end

def convex_zone (minRadius : ℝ) := set.Ioo (0:ℝ) ((11/6)^(1/6:ℝ)*minRadius)

lemma differentiable_at_LJ 
(hrpos : ∀ r : ℝ, 0 < r)
:
∀ x, differentiable_at ℝ (λ r, LJ ε minRadius r) x:=
begin
  intro,
  simp [LJ],
  apply differentiable_at.const_mul _ (4*ε),
  field_simp,
  apply differentiable_at.sub,
  rw repulsive_3 _ hrpos,
  apply differentiable_at_inv_abs_rpow (hrpos x) (@minRadius_rpow_div_const_pos minRadius 4 12 (hrpos minRadius) zero_lt_four zero_lt_twelve) hrpos,
  norm_num,
  rw attractive_3 _ hrpos,
  apply differentiable_at_inv_abs_rpow (hrpos x) (@minRadius_rpow_div_const_pos minRadius 2 6 (hrpos minRadius) zero_lt_two zero_lt_six) hrpos,
  norm_num,
end

lemma differentiable_at_deriv_LJ
(hrpos : ∀ r : ℝ, 0 < r)
:
∀ x, differentiable_at ℝ (deriv (λ r, LJ ε minRadius r)) x:=
begin
  intro,
  rw deriv_of_LJ _ _ hrpos,
  apply differentiable_at.const_mul _ (4*ε),
  field_simp,
  apply differentiable_at.sub (differentiable_at_inv_rpow (hrpos x) _ _) (differentiable_at_inv_rpow (hrpos x) _ _),
  iterate 2 {norm_num,},
end

lemma continuous_on_convex_zone 
(hrpos : ∀ r : ℝ, 0 < r)
:
continuous_on (LJ ε minRadius) (convex_zone minRadius) :=
begin
  apply @differentiable_on.continuous_on ℝ,
  apply differentiable.differentiable_on,
  rw differentiable,
  exact (differentiable_at_LJ _ _ hrpos),
end

lemma differentiable_on_convex_zone
(hrpos : ∀ r : ℝ, 0 < r)
:
differentiable_on ℝ (LJ ε minRadius) (interior (convex_zone minRadius)):=
begin
  simp [convex_zone],
  apply differentiable.differentiable_on,
  rw differentiable,
  exact (differentiable_at_LJ _ _ hrpos),  
end

lemma differentiable_of_deriv_on_convex_zone
(hrpos : ∀ r : ℝ, 0 < r)
:
differentiable_on ℝ (deriv (LJ ε minRadius)) (interior (convex_zone minRadius)):=
begin
  simp [convex_zone],
  apply differentiable.differentiable_on,
  rw differentiable, 
  exact (differentiable_at_deriv_LJ _ _ hrpos),
end

lemma deriv2_of_convex_zone_nonneg 
(hrpos : ∀ r : ℝ, 0 < r)
:
:=
begin

end
theorem convex_on
(hrpos : ∀ r : ℝ, 0 < r)
:
convex_on ℝ (convex_zone minRadius) (LJ ε minRadius) :=
begin
  apply convex_on_of_deriv2_nonneg (convex_Ioo _ _) (continuous_on_convex_zone _ _ hrpos) (differentiable_on_convex_zone _ _ hrpos) (differentiable_of_deriv_on_convex_zone _ _ _),
  intros x h,

end
theorem local_min_at_minRadius
(hrpos : ∀ r : ℝ, 0 < r)
:
is_local_min (LJ ε minRadius) minRadius :=
begin
  simp [is_local_min, is_min_filter, LJ],
  
end

end LJ