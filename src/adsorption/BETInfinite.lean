import data.real.basic
import math.infinite_series

open_locale big_operators

/-!
# BET 
This section defines the Brunauer–Emmett–Teller (BET) adsorption theory where we relax the assumption 
of the [Langmuir model](./langmuir_kinetics.html) that restricts adsorption on a single site to be one molecule;
instead, molecules can stack on top of each other in layers.

-/


/-! 
### Definitions
-/
noncomputable theory

constants (C_1 C_L s₀: ℝ) (P₀ : nnreal) (hCL : 0 < C_L) (hC1 : 0 < C_1) (hs₀ : 0 < s₀) (hP₀ : 0 < P₀)

def BET_first_layer_adsoprtion_rate (P : nnreal) := (C_1)*P
local notation `y` := BET_first_layer_adsoprtion_rate

def BET_n_layer_adsorption_rate (P : nnreal):= (C_L)*P
local notation `x` := BET_n_layer_adsorption_rate

def BET_constant := C_1/C_L
local notation `C` := BET_constant


def seq (P: nnreal) : ℕ → ℝ
|(0 : ℕ)            := s₀
|(nat.succ n) := (x P)^(n+1)*s₀*C


/-! 
### Proof
-/
section BET

lemma sequence_math  (P : nnreal) (hx1: (x P) < 1) (hx2 : 0 < (x P)):
  (∑' k : ℕ, ((k + 1 : ℝ)*(seq P (k+1:ℕ))))/(s₀ + ∑' k, (seq P (k+1:ℕ))) = C*(x P)/((1 - (x P))*(1 - (x P) + (x P)*C)):=
begin
  simp [seq],
  have hxnorm : ‖x P‖ < 1, by refine abs_lt.mpr ⟨_, _⟩ ; linarith,
  simp [← mul_assoc],
  rw [tsum_mul_right, tsum_mul_right, tsum_mul_right, tsum_mul_right, tsum_coe_mul_geometric_succ hx1 hx2, 
  tsum_geometric_of_lt_1_pow_succ hx1 hx2, pow_two],
  have h1 : (1-(x P)) ≠ 0 := by linarith,
  field_simp,
  rw [mul_comm, mul_assoc (1-(x P)) _ _, mul_div_mul_left, mul_comm, mul_comm (x P) s₀, mul_comm C _, mul_assoc s₀ (x P) C, 
  ← mul_add s₀ _ _, ← mul_assoc (1-(x P)) _ _,  mul_comm _ s₀, mul_assoc s₀ _ _, mul_div_mul_left, mul_comm C (x P)],
  iterate 2 {linarith [hs₀, h1],},
end

theorem regression_form
{P : nnreal}
{V₀: ℝ}
(hx1: (x P) < 1)
(hx2 : 0 < (x P))
(hθ : 0 < s₀ )
(hP : 0 < P)
:
  let a := V₀*C_1,
      b := C_L,
      c := C_1,
      Vads :=  V₀ * ∑' (k : ℕ), ↑k * (seq P k),
      A :=  ∑' (k : ℕ), (seq P k),
      q := Vads/A in
  q = a*P/((1-b*P)*(1-b*P+c*P))
:=
begin
intros,
  have hsum2 : summable (seq P),
  { refine (summable_nat_add_iff 1).mp _,
    simp only [seq, pow_succ', mul_assoc],
    exact (summable_geometric_of_lt_1 hx2.le hx1).mul_right _ },
  have hxnorm : ‖x P‖ < 1, by refine abs_lt.mpr ⟨_, _⟩ ; linarith,
  have hsum : summable (λ k : ℕ, ↑k * (seq P k)),
  { refine (summable_nat_add_iff 1).mp _,
    simp only [seq, ← mul_assoc],
    refine summable.mul_right _ (summable.mul_right _ _),
    set u := λ k :ℕ, (k : ℝ) * (x P) ^ k,
    change summable (λ (n : ℕ), u (n+1)),
    refine (summable_nat_add_iff 1).mpr _,
    simpa using summable_pow_mul_geometric_of_norm_lt_1 1 hxnorm },
  simp only [a, b, c, q, Vads, A],
  rw [tsum_eq_zero_add hsum, tsum_eq_zero_add hsum2],
  simp only [nat.cast_zero, zero_mul, zero_add, nat.cast_one, pow_zero, one_mul, mul_assoc, nat.cast_add, mul_div_assoc],
  rw [show seq P 0 = s₀, by {simp [seq]}], 
  rw [sequence_math P hx1 hx2, BET_constant, BET_n_layer_adsorption_rate],
  have h1 : C_L ≠ 0 := by {linarith [hCL],},
  field_simp,
  rw [mul_comm (1-C_L*P) C_L, mul_assoc C_L P _, ← mul_add C_L _ _, ← mul_assoc V₀ C_1 _, mul_comm C_L _, ← mul_assoc (V₀*C_1) _ _,
  mul_comm C_L _, ← mul_assoc _ _ C_L, mul_div_mul_right _ _ h1, mul_comm (↑P) C_1, mul_assoc],
end

def brunauer_26 := λ P : nnreal, C*(x P)/((1-(x P))*(1-(x P)+C*(x P))) 

theorem brunauer_26_from_seq
{P : nnreal}
{V₀: ℝ}
(hx1: (x P) < 1)
(hx2 : 0 < (x P))
(hP : 0 < P)
:
  let Vads :=  V₀ * ∑' (k : ℕ), ↑k * (seq P k),
      A :=  ∑' (k : ℕ), (seq P k) in
  Vads/A = V₀*(brunauer_26 P)
:=
begin
  intros,
  simp [brunauer_26],
  have hsum2 : summable (seq P),
  { refine (summable_nat_add_iff 1).mp _,
    simp only [seq, pow_succ', mul_assoc],
    exact (summable_geometric_of_lt_1 hx2.le hx1).mul_right _ },
  have hxnorm : ‖x P‖ < 1, by refine abs_lt.mpr ⟨_, _⟩ ; linarith,
  have hsum : summable (λ k : ℕ, ↑k * (seq P k)),
  { refine (summable_nat_add_iff 1).mp _,
    simp only [seq, ← mul_assoc],
    refine summable.mul_right _ (summable.mul_right _ _),
    set u := λ k :ℕ, (k : ℝ) * (x P) ^ k,
    change summable (λ (n : ℕ), u (n+1)),
    refine (summable_nat_add_iff 1).mpr _,
    simpa using summable_pow_mul_geometric_of_norm_lt_1 1 hxnorm },
  simp only [Vads, A],
  rw [tsum_eq_zero_add hsum, tsum_eq_zero_add hsum2],
  simp only [nat.cast_zero, zero_mul, zero_add, nat.cast_one, pow_zero, one_mul, mul_assoc, nat.cast_add, mul_div_assoc],
  rw [show seq P 0 = s₀, by {simp [seq]}], 
  rw [sequence_math P hx1 hx2],
  field_simp [mul_comm (x P) C],
end

lemma tendsto_at_top_at_inv_CL
: filter.tendsto brunauer_26 (nhds_within (1/C_L.to_nnreal) (set.Ioo 0 (1/C_L.to_nnreal))) filter.at_top:=
begin
  have h1 : filter.tendsto (λ («x» : nnreal), 1 - C_L * ↑«x») (nhds (C_L.to_nnreal)⁻¹) (nhds (0)) := by {rw show (0 : ℝ) = 1 - 1, by norm_num, 
      apply filter.tendsto.sub, apply tendsto_const_nhds,  rw show (1 : ℝ) = C_L*C_L⁻¹, by { symmetry, rw mul_inv_cancel (ne_of_gt hCL),},
      apply filter.tendsto.const_mul, rw show C_L⁻¹ = C_L.to_nnreal⁻¹, by { rw real.coe_to_nnreal _ (le_of_lt hCL),}, norm_cast, finish,},
  have h : 0 < C := by { simp [BET_constant], exact div_pos hC1 hCL,},
  simp only [brunauer_26, BET_n_layer_adsorption_rate, div_eq_inv_mul],
  apply filter.tendsto.at_top_mul h,
  apply filter.tendsto.inv_tendsto_zero,
  simp [nhds_within],
  apply filter.tendsto.inf,
  rw show 0 = 0*C, by simp,
  apply filter.tendsto.mul,
  exact h1,
  rw show nhds C = nhds (0 + C), by simp,
  apply filter.tendsto.add h1,
  rw show nhds C = nhds (C*1), by simp,
  apply filter.tendsto.const_mul,
  rw show 1 = C_L*C_L⁻¹, by {symmetry, rw mul_inv_eq_one₀, linarith[hCL]},
  apply filter.tendsto.const_mul,
  rw show C_L⁻¹ = C_L.to_nnreal⁻¹, by { rw real.coe_to_nnreal _ (le_of_lt hCL),}, 
  norm_cast,
  finish,
  simp,
  intros a ha1 ha2,
  have HC : C_L.to_nnreal < C_1.to_nnreal ∨ C_1.to_nnreal ≤ C_L.to_nnreal := by { apply lt_or_ge,},
  cases HC with HC1 HC2,
  { rw [zero_lt_mul_left, sub_add, ← neg_sub, neg_sub', lt_sub, sub_zero, neg_sub, BET_constant, ← mul_assoc, div_mul, div_self (ne_of_gt hCL), div_one, ← sub_mul, 
    mul_comm, ← div_lt_iff],
    rw show C_L = C_L.to_nnreal, by { rw real.coe_to_nnreal _ (le_of_lt hCL),}, 
    rw show C_1 = C_1.to_nnreal, by { rw real.coe_to_nnreal _ (le_of_lt hC1),}, 
    rw ← nnreal.coe_lt_coe at ha1,
    apply lt_trans _ ha1,
    simp,
    rw [neg_div, neg_lt_zero],
    rw ← nnreal.coe_lt_coe at HC1,
    simpa using HC1,    
    rw ← nnreal.coe_lt_coe at HC1,
    rw show C_L = C_L.to_nnreal, by { rw real.coe_to_nnreal _ (le_of_lt hCL),}, 
    rw show C_1 = C_1.to_nnreal, by { rw real.coe_to_nnreal _ (le_of_lt hC1),}, 
    simpa using HC1,
    rw [lt_sub, mul_comm, ← lt_div_iff hCL],
    rw ← nnreal.coe_lt_coe at ha2,
    rw show C_L = C_L.to_nnreal, by { rw real.coe_to_nnreal _ (le_of_lt hCL),}, 
    simpa using ha2,},
  { rw le_iff_lt_or_eq at HC2,
    cases HC2 with HC2 HC3,
    rw [zero_lt_mul_left, sub_add, lt_sub, sub_zero, BET_constant, ← mul_assoc, div_mul, div_self (ne_of_gt hCL), div_one, ← sub_mul, 
    mul_comm, ← lt_div_iff],
    have H : C_L.to_nnreal⁻¹ <  1/(C_L.to_nnreal-C_1.to_nnreal) := by { rw one_div, apply nnreal.inv_lt_inv, simpa using HC2, rw ← nnreal.coe_lt_coe, rw nnreal.coe_sub (le_of_lt HC2), simpa using hC1,},
    rw ← nnreal.coe_lt_coe at ha2,
    rw ← nnreal.coe_lt_coe at H,
    push_cast at H,
     rw nnreal.coe_sub (le_of_lt HC2) at H,
    rw show C_L = C_L.to_nnreal, by { rw real.coe_to_nnreal _ (le_of_lt hCL),}, 
    rw show C_1 = C_1.to_nnreal, by { rw real.coe_to_nnreal _ (le_of_lt hC1),}, 
    apply lt_trans ha2 H,
    rw show C_L = C_L.to_nnreal, by { rw real.coe_to_nnreal _ (le_of_lt hCL),}, 
    rw show C_1 = C_1.to_nnreal, by { rw real.coe_to_nnreal _ (le_of_lt hC1),},
    rw ← nnreal.coe_lt_coe at HC2,
    simpa using HC2,
    rw [lt_sub, mul_comm, ← lt_div_iff hCL],
    rw show C_L = C_L.to_nnreal, by { rw real.coe_to_nnreal _ (le_of_lt hCL),}, 
    simpa using ha2,
    rw [BET_constant, show C_L = C_L.to_nnreal, by { rw real.coe_to_nnreal _ (le_of_lt hCL),}, show C_1 = C_1.to_nnreal, by { rw real.coe_to_nnreal _ (le_of_lt hC1),}, HC3, div_self, one_mul, sub_add_cancel, mul_one,
    lt_sub, sub_zero, mul_comm, ← lt_div_iff, one_div],
    rw ← nnreal.coe_lt_coe at ha2,
    simpa using ha2,
    simpa using hCL,
    simpa using hCL,},
  simp [nhds_within],
  apply filter.tendsto_inf_left,
  rw show nhds C = nhds (C*1), by simp,
  apply filter.tendsto.const_mul,
  rw show 1 = C_L*C_L⁻¹, by {symmetry, rw mul_inv_eq_one₀, linarith [hCL]},
  apply filter.tendsto.const_mul,
  rw show C_L⁻¹ = C_L.to_nnreal⁻¹, by { rw real.coe_to_nnreal _ (le_of_lt hCL),}, 
  norm_cast,
  finish,
end

theorem brunauer_27
(h1 : P₀ = 1/C_L.to_nnreal)
: filter.tendsto brunauer_26 (nhds_within (P₀) (set.Ioo 0 (P₀))) filter.at_top:=
begin
  simpa [h1] using  tendsto_at_top_at_inv_CL,
end

def brunauer_28 := λ P : nnreal, C*P/((P₀-P)*(1+(C-1)*(P/P₀)))

theorem brunauer_28_from_seq
{P : nnreal}
{V₀: ℝ}
(h27 : P₀ = 1/C_L.to_nnreal)
(hx1: (x P) < 1)
(hx2 : 0 < (x P))
(hP : 0 < P)
: let Vads :=  V₀ * ∑' (k : ℕ), ↑k * (seq P k),
      A :=  ∑' (k : ℕ), (seq P k) in
  Vads/A = V₀*(brunauer_28 P) :=
begin
  have h1 : let Vads :=  V₀ * ∑' (k : ℕ), ↑k * (seq P k),
      A :=  ∑' (k : ℕ), (seq P k) in
  Vads/A = V₀*(brunauer_26 P) := by exact brunauer_26_from_seq hx1 hx2 hP,
  simp at *,
  rw [h1, brunauer_26, brunauer_28, BET_constant],
  field_simp,
  rw [BET_n_layer_adsorption_rate, h27],
  rw [← mul_assoc, mul_comm C_L _, ← mul_assoc, mul_comm _ C_L, mul_div_mul_left _ _ (ne_of_gt hCL), show ↑(C_L.to_nnreal)⁻¹ = C_L⁻¹, by {push_cast, rw real.coe_to_nnreal, linarith [hCL]},
  ← mul_assoc C_L _ _, mul_sub, mul_inv_cancel (ne_of_gt hCL), ← mul_assoc V₀ _ _, mul_comm C_L (↑P), mul_div_assoc C_1 _ _, mul_div_cancel _ (ne_of_gt hCL), sub_mul _ _ (↑P), inv_eq_one_div,
  ← div_mul, div_one, sub_mul _ _ C_L, one_mul, mul_comm (C_1 / C_L * ↑P) C_L, ← mul_assoc C_L _ _, mul_div, mul_comm C_L C_1, mul_div_cancel _ (ne_of_gt hCL), add_sub, add_sub_right_comm],
end
end BET
