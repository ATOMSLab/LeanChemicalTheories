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

Here we use our own proof of [derivative] (./deriv.html) to show that Lennard-Jones potential has its minimum 
at a distance of `r = r_min = 2^1/6 σ, where the potential energy has the value `-ε`
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

theorem LJ_repulsive_2
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

theorem LJ_attractice_2
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

theorem LJ_deriv
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
  rw [deriv_sub, @LJ_repulsive_2 minRadius hrpos, @LJ_attractice_2 minRadius hrpos,
  deriv_inv_abs_rpow (hrpos x) (@minRadius_rpow_div_const_pos minRadius 2 6 (hrpos minRadius) zero_lt_two zero_lt_six) hrpos,
  deriv_inv_abs_rpow (hrpos x) (@minRadius_rpow_div_const_pos minRadius 4 12 (hrpos minRadius) zero_lt_four zero_lt_twelve) hrpos],
  norm_num,
  field_simp,
  rw [neg_div, neg_div, show (12:ℝ) = 4*3, by norm_num, mul_assoc, mul_div_mul_left,
  show (6:ℝ) = 2*3, by norm_num, mul_assoc, mul_div_mul_left],
  field_simp,
  iterate 4 {norm_num},
  rw @LJ_repulsive_2 minRadius hrpos,
  apply differentiable_at_inv_abs_rpow (hrpos x) (@minRadius_rpow_div_const_pos minRadius 4 12 (hrpos minRadius) zero_lt_four zero_lt_twelve) hrpos,
  norm_num,
  rw @LJ_attractice_2 minRadius hrpos,
  apply differentiable_at_inv_abs_rpow (hrpos x) (@minRadius_rpow_div_const_pos minRadius 2 6 (hrpos minRadius) zero_lt_two zero_lt_six) hrpos,
  norm_num,
end



theorem LJ_deriv_at_minEnergy
(hrpos : ∀ r : ℝ, 0 < r)
:
deriv (λ r, LJ ε minRadius r) minRadius = 0 :=
begin
  rw LJ_deriv ε minRadius hrpos,
  simp,
  right,
  ring_exp,
  have h3 : minRadius ≠ 0 := by {specialize hrpos minRadius, linarith},
  field_simp,
  rw [neg_div, mul_comm _ (3:ℝ), mul_div_assoc, ← rpow_sub (hrpos minRadius), mul_comm _ (3:ℝ), mul_div_assoc, ← rpow_sub (hrpos minRadius)],
  norm_num,
end


