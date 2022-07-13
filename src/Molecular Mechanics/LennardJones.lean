import analysis.normed_space.basic
import analysis.calculus.local_extr

--Local imports
import math.deriv

/-We define the Lennard Jones potential to take in an ε, the
minimum energy constant, a minRadius, the radius where the function
has a minimum, and r, the radius between the two particles.
We first show that LJ has a local minimum at minRadius. We then
show that LJ is translationally invaraint on a general
vector space, E-/


noncomputable theory
universe u
variables {ε minRadius: ℝ} [(0:ℝ) < minRadius] 

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
(hrpos : ∀ r : ℝ, 0 ≤ r)
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
  exact hrpos r,
  field_simp,
  simp,
  field_simp,
  exact zero_lt_two_pow_one_div_six,
  linarith,
end

theorem minRadius_rpow_div_const_pos : ∀ r y : ℝ, 0 < r → 0 < y → 0 < minRadius ^ y / r:=
begin
  intros r y this that, 
  rw [lt_div_iff this, zero_mul],
  apply zero_lt_rpow _inst_1 that,
end

theorem LJ_deriv_at_minEnergy
(hrpos : ∀ r : ℝ, 0 ≤ r)
:
deriv (λ r, LJ ε minRadius r) minRadius = 0 :=
begin
  simp_rw [LJ, real.norm_eq_abs],
  simp [deriv_const_mul, mul_div_assoc],
  field_simp,
  have hcon : ∀ r : ℝ, (0:ℝ) ≤ minRadius / ((2 ^ (1 / 6:ℝ):ℝ) * r) := by exact @zero_le_LJ minRadius _inst_1 hrpos, 
  have h1 : (λ r : ℝ, |minRadius/((2^(1/6:ℝ):ℝ)*r)|^(12:ℝ))= λ r : ℝ,(|minRadius^(12:ℝ)/4|)/|r^(12:ℝ)|,
  { funext,
    rw [← abs_rpow_of_nonneg (hcon r), div_rpow, mul_rpow, two_pow_one_div_six_pow_twelve_eq_four, abs_div, abs_mul, abs_div],
    field_simp,
    exact zero_le_two_pow_one_div_six,
    exact hrpos r,
    rw le_iff_lt_or_eq,
    left,
    exact _inst_1,
    rw zero_le_mul_left,
    exact hrpos r,
    exact zero_lt_two_pow_one_div_six,},
  have h2 : (λ r : ℝ, |minRadius/((2^(1/6:ℝ):ℝ)*r)|^(6:ℝ)) = λ r : ℝ,(|minRadius^(6:ℝ)/2|)/|r^(6:ℝ)|,
  { funext,
    rw [← abs_rpow_of_nonneg (hcon r), div_rpow, mul_rpow, two_pow_one_div_six_pow_six_eq_two, abs_div, abs_mul, abs_div],
    field_simp,
    exact zero_le_two_pow_one_div_six,
    exact hrpos r,
    rw le_iff_lt_or_eq,
    left,
    exact _inst_1,
    rw zero_le_mul_left,
    exact hrpos r,
    exact zero_lt_two_pow_one_div_six,},
  right,
  rw [deriv_sub, h1, h2, deriv_inv_abs_rpow _inst_1 (@minRadius_rpow_div_const_pos minRadius _inst_1 2 6 zero_lt_two zero_lt_six) hrpos,
   deriv_inv_abs_rpow _inst_1 (@minRadius_rpow_div_const_pos minRadius _inst_1 4 12 zero_lt_four zero_lt_twelve) hrpos],
  ring_exp,
  have h3 : minRadius ≠ 0 := by linarith,
  field_simp,
  rw [neg_div, mul_comm _ (3:ℝ), mul_div_assoc, ← rpow_sub _inst_1, mul_comm _ (3:ℝ), mul_div_assoc, ← rpow_sub _inst_1],
  iterate 2 {norm_num},
  norm_num, 
  rw h1,
  apply differentiable_at_inv_abs_rpow _inst_1 (@minRadius_rpow_div_const_pos minRadius _inst_1 4 12 zero_lt_four zero_lt_twelve) hrpos,
  norm_num,
  rw h2,
  apply differentiable_at_inv_abs_rpow _inst_1 (@minRadius_rpow_div_const_pos minRadius _inst_1 2 6 zero_lt_two zero_lt_six) hrpos,
  norm_num,
end

theorem LJ_deriv
(hrpos : ∀ r : ℝ, 0 ≤ r)
:
(deriv (LJ ε minRadius)) = λ r, (-12)*(minRadius^12/4)/r^(13)-(-6)*(minRadius^6/2)/r^(7) :=
begin
  
end

theorem LJ_deriv_2_pos
(hrpos : ∀ r : ℝ, 0 ≤ r)
:
∀ r, 0 ≤  (deriv^[2] (LJ ε minRadius) r)  :=
begin
  intro,
  simp,
end

theorem LJ_minEnerg
(hrpos : ∀ r : ℝ, 0 ≤ r)
: 
is_local_min (LJ ε minRadius) minRadius :=
begin
  have h1 : deriv (λ r, LJ ε minRadius r) minRadius = 0 := @LJ_deriv_at_minEnergy ε minRadius _inst_1 hrpos,
  have h2 : is_local_extr (LJ ε minRadius) minRadius,
  { },
end
