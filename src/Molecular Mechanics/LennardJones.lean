import analysis.normed_space.basic
import analysis.calculus.local_extr
import analysis.special_functions.pow
import analysis.special_functions.pow_deriv

noncomputable theory

variables {ε : ℝ} {minRadius : nnreal} [(0:ℝ) < minRadius] [nondiscrete_normed_field nnreal] [normed_space nnreal ℝ] 

def LJ (ε : ℝ) (minRadius r : nnreal): ℝ := 
  let σ := (1 / 2 ^ (1 / 6:ℝ):ℝ)*minRadius in
  4*ε*(∥σ/r∥^(12:ℝ)-∥σ/r∥^(6:ℝ))

open real

lemma rpow_ne_zero
{x y : ℝ} (hx : 0 < x) (hy : 0 < y)
: x^y ≠ 0 :=
begin
  have hy2 : y ≠ 0 := by linarith,
  apply ne_of_gt,
  rw [← zero_rpow hy2, rpow_lt_rpow_iff],
  iterate 4 {linarith},
end

lemma zero_lt_rpow
{x y : ℝ} (hx : 0 < x) (hy : 0 < y)
: 0 < x^y :=
begin
  have hy2 : y ≠ 0 := by linarith,
  rw [← zero_rpow hy2, rpow_lt_rpow_iff],
  iterate 4 {linarith},
end

lemma deriv_inv_rpow
{C z: ℝ} (hz : 0 < z)
:
∀ r:ℝ, 1 ≤ r →  deriv (λ x:ℝ, C/x^r) z = -r*C/z^(r+1):=
begin
  intros n hr,
  have h :  (λ x:ℝ, C/x^n) = λ x:ℝ, ((λ x:ℝ, C) x)/((λ x:ℝ, x^n) x) := by simp,
  rw [h, deriv_div],
  simp,
  have h2 : z^(n-1)/(z^n)^2 = 1/z^(n+1),
  { rw [rpow_sub, rpow_one, pow_two],
    field_simp,
    rw [← mul_assoc, div_mul_left, mul_comm z _, ← rpow_add_one],
    linarith,
    apply rpow_ne_zero hz,
    linarith,
    linarith,
    },
  have h3 : deriv (λ (x : ℝ), x ^ n) z = n*z^(n-1),
  { rw real.deriv_rpow_const, right, exact hr},
  rw [h3, ← mul_assoc, neg_div, mul_div_assoc, pow_two, ← rpow_add hz, ← rpow_sub hz,
  show n-1-(n+n) = -(n+1), by { rw ← sub_sub, simp, ring_nf}],
  have hz1 : 0 ≤ z, by linarith,
  rw [rpow_neg hz1 (n+1), mul_comm C n, neg_div],
  field_simp,
  simp,
  simp,
  apply has_deriv_at.differentiable_at,
  apply real.has_deriv_at_rpow_const (or.inr hr),
  simp,
  rw ← ne.def,
  apply rpow_ne_zero hz,
  linarith,
end

theorem LJ_minEnergy
: 
is_local_min (LJ ε minRadius) minRadius :=
begin
  have h1 : deriv (λ r, LJ ε minRadius r) minRadius = 0,
  { simp_rw [LJ, real.norm_eq_abs],
    simp [deriv_const_mul, mul_div_assoc],
    field_simp,
    have hnum1 : (2 ^ (1 / 6:ℝ):ℝ) ^ (6:ℝ) = (2:ℝ),
    { have h : 0 ≤ (2:ℝ) := by simp,
      rw [ ← real.rpow_mul h (1/6) 6],
      norm_num,},
    have hnum2 : ( 2 ^ (1 / 6:ℝ):ℝ) ^ (12:ℝ) = (4:ℝ),
    { have h : 0 ≤ (2:ℝ) := by simp,
      rw [← real.rpow_mul h (1/6) 12],
      norm_num,},
    have h1 : (λ r : nnreal, |↑minRadius/((2^(1/6:ℝ):ℝ)*↑r)|^(12:ℝ))= λ r : nnreal,|↑minRadius^(12:ℝ)/((4:ℝ)*↑r^(12:ℝ))|,
    { funext,
      have h1 : (0:ℝ) ≤ ↑minRadius / ((2 ^ (1 / 6:ℝ):ℝ) * ↑r) ,
      { simp,
        ring_nf,
        rw zero_le_mul_right,
        simp,
        rw zero_le_mul_left,
        exact nnreal.coe_nonneg r,
        apply zero_lt_rpow,
        iterate 2 {simp},
        exact zero_lt_three,
        linarith,},
      rw [← abs_rpow_of_nonneg h1, div_rpow, mul_rpow, hnum2],
      rw le_iff_lt_or_eq,
      left,
      apply zero_lt_rpow,
      iterate 2 {simp},
      exact zero_lt_three,
      exact nnreal.coe_nonneg r,
      rw le_iff_lt_or_eq,
      left,
      exact _inst_1,
      rw zero_le_mul_left,
      exact nnreal.coe_nonneg r,
      apply zero_lt_rpow,
      iterate 2 {simp},
      exact zero_lt_three,},
    have h2 : (λ r : nnreal, |↑minRadius/((2^(1/6:ℝ):ℝ)*↑r)|^(6:ℝ)) = λ r : nnreal,|↑minRadius^(6:ℝ)/((2:ℝ)*↑r^(6:ℝ))|,
    { funext,
      have h1 : (0:ℝ) ≤ ↑minRadius / ((2 ^ (1 / 6:ℝ):ℝ) * ↑r) ,
      { simp,
        ring_nf,
        rw zero_le_mul_right,
        simp,
        rw zero_le_mul_left,
        exact nnreal.coe_nonneg r,
        apply zero_lt_rpow,
        iterate 2 {simp},
        exact zero_lt_three,
        linarith,},
      rw [← abs_rpow_of_nonneg h1, div_rpow, mul_rpow, hnum1],
      rw le_iff_lt_or_eq,
      left,
      apply zero_lt_rpow,
      iterate 2 {simp},
      exact zero_lt_three,
      exact nnreal.coe_nonneg r,
      rw le_iff_lt_or_eq,
      left,
      exact _inst_1,
      rw zero_le_mul_left,
      exact nnreal.coe_nonneg r,
      apply zero_lt_rpow,
      iterate 2 {simp},
      exact zero_lt_three,},
    rw deriv_const_mul,
    apply h1,
    
    },
end
