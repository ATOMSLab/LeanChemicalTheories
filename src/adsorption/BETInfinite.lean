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
namespace BET
structure system :=
(C_1 C_L s₀ P₀: ℝ)
(hCL : 0 < C_L) 
(hC1 : 0 < C_1) 
(hs₀ : 0 < s₀) 
(hP₀ : 0 < P₀)

def first_layer_adsoprtion_rate (S : BET.system) (P : ℝ):= (S.C_1)*P
local notation `y` := BET.first_layer_adsoprtion_rate

def n_layer_adsorption_rate (S : BET.system) (P : ℝ):= (S.C_L)*P
local notation `x` := BET.n_layer_adsorption_rate

def adsorption_constant (S : BET.system):= S.C_1/S.C_L
local notation `C` := BET.adsorption_constant

def seq (S : BET.system) (P: ℝ) : ℕ → ℝ
|(0 : ℕ)            := S.s₀
|(nat.succ n) := (x S P)^(n+1)*S.s₀*(C S)

def volume_adsorbed (S : BET.system) (V₀ P) := V₀ * ∑' (k : ℕ), ↑k * (seq S P k)
local notation `V` := BET.volume_adsorbed

def catalyst_area (S : BET.system) (P) := ∑' (k : ℕ), (seq S P k)
local notation `A` := BET.catalyst_area

/-! 
### Proof
-/

lemma sequence_math {S : BET.system} {P : ℝ} (hx1: (x S P) < 1) (hx2 : 0 < (x S P)):
  (∑' k : ℕ, ((k + 1 : ℝ)*(seq S P (k+1:ℕ))))/(S.s₀ + ∑' k, (seq S P (k+1:ℕ))) = (C S)*(x S P)/((1 - (x S P))*(1 - (x S P) + (x S P)*(C S))):=
begin
  simp [seq],
  have hxnorm : ‖x S P‖ < 1, by refine abs_lt.mpr ⟨_, _⟩ ; linarith,
  simp [← mul_assoc],
  rw [tsum_mul_right, tsum_mul_right, tsum_mul_right, tsum_mul_right, tsum_coe_mul_geometric_succ hx1 hx2, 
  tsum_geometric_of_lt_1_pow_succ hx1 hx2, pow_two],
  have h1 : (1-(x S P)) ≠ 0 := by linarith,
  field_simp,
  rw [mul_comm, mul_assoc (1-(x S P)) _ _, mul_div_mul_left, mul_comm, mul_comm (x S P) S.s₀, mul_comm (C S) _, mul_assoc S.s₀ (x S P) (C S), 
  ← mul_add S.s₀ _ _, ← mul_assoc (1-(x S P)) _ _,  mul_comm _ S.s₀, mul_assoc S.s₀ _ _, mul_div_mul_left, mul_comm (C S) (x S P)],
  iterate 2 {linarith [S.hs₀, h1],},
end

theorem regression_form
{P V₀: ℝ}
(S : BET.system)
(hx1: (x S P) < 1)
(hx2 : 0 < (x S P))
(hθ : 0 < S.s₀ )
(hP : 0 < P)
:
  let a := V₀*S.C_1,
      b := S.C_L,
      c := S.C_1,
      q := (V S V₀ P)/(A S P) in
  q = a*P/((1-b*P)*(1-b*P+c*P))
:=
begin
intros,
  have hsum2 : summable (seq S P),
  { refine (summable_nat_add_iff 1).mp _,
    simp only [seq, pow_succ', mul_assoc],
    exact (summable_geometric_of_lt_1 hx2.le hx1).mul_right _ },
  have hxnorm : ‖x S P‖ < 1, by refine abs_lt.mpr ⟨_, _⟩ ; linarith,
  have hsum : summable (λ k : ℕ, ↑k * (seq S P k)),
  { refine (summable_nat_add_iff 1).mp _,
    simp only [seq, ← mul_assoc],
    refine summable.mul_right _ (summable.mul_right _ _),
    set u := λ k : ℕ, (k : ℝ) * (x S P) ^ k,
    change summable (λ (n : ℕ), u (n+1)),
    refine (summable_nat_add_iff 1).mpr _,
    simpa using summable_pow_mul_geometric_of_norm_lt_1 1 hxnorm },
  simp only [a, b, c, q, BET.volume_adsorbed, BET.catalyst_area],
  rw [tsum_eq_zero_add hsum, tsum_eq_zero_add hsum2],
  simp only [nat.cast_zero, zero_mul, zero_add, nat.cast_one, pow_zero, one_mul, mul_assoc, nat.cast_add, mul_div_assoc],
  rw [show seq S P 0 = S.s₀, by {simp [seq]}], 
  rw [sequence_math hx1 hx2, BET.adsorption_constant, BET.n_layer_adsorption_rate],
  have h1 : S.C_L ≠ 0 := by {linarith [S.hCL],},
  field_simp,
  rw [mul_comm (1-S.C_L*P) S.C_L, mul_assoc S.C_L P _, ← mul_add S.C_L _ _, ← mul_assoc V₀ S.C_1 _, mul_comm S.C_L _, ← mul_assoc (V₀*S.C_1) _ _,
  mul_comm S.C_L _, ← mul_assoc _ _ S.C_L, mul_div_mul_right _ _ h1, mul_comm (P) S.C_1, mul_assoc],
end

def brunauer_26 (S : BET.system) := λ P, (C S)*(x S P)/((1-(x S P))*(1-(x S P)+(C S)*(x S P))) 

theorem brunauer_26_from_seq
{P V₀: ℝ}
{S : BET.system}
(hx1: (x S P) < 1)
(hx2 : 0 < (x S P))
(hP : 0 < P)
:  (V S V₀ P)/(A S P) = V₀*(brunauer_26 S P)
:=
begin
  intros,
  simp [brunauer_26],
  have hsum2 : summable (seq S P),
  { refine (summable_nat_add_iff 1).mp _,
    simp only [seq, pow_succ', mul_assoc],
    exact (summable_geometric_of_lt_1 hx2.le hx1).mul_right _ },
  have hxnorm : ‖x S P‖ < 1, by refine abs_lt.mpr ⟨_, _⟩ ; linarith,
  have hsum : summable (λ k : ℕ, ↑k * (seq S P k)),
  { refine (summable_nat_add_iff 1).mp _,
    simp only [seq, ← mul_assoc],
    refine summable.mul_right _ (summable.mul_right _ _),
    set u := λ k : ℕ, (k : ℝ) * (x S P) ^ k,
    change summable (λ (n : ℕ), u (n+1)),
    refine (summable_nat_add_iff 1).mpr _,
    simpa using summable_pow_mul_geometric_of_norm_lt_1 1 hxnorm },
  simp only [BET.volume_adsorbed, BET.catalyst_area],
  rw [tsum_eq_zero_add hsum, tsum_eq_zero_add hsum2],
  simp only [nat.cast_zero, zero_mul, zero_add, nat.cast_one, pow_zero, one_mul, mul_assoc, nat.cast_add, mul_div_assoc],
  rw [show seq S P 0 = S.s₀, by {simp [seq]}], 
  rw [sequence_math hx1 hx2],
  field_simp [mul_comm (x S P) (C S)],
end

--filter.tendsto (brunauer_26 S) (nhds_within (1/S.C_L) (set.Ioo 0 (1/S.C_L))) filter.at_top
lemma tendsto_at_top_at_inv_CL (S : BET.system)
: filter.tendsto (brunauer_26 S) (nhds_within (1/S.C_L) (set.Ioo 0 (1/S.C_L))) filter.at_top:=
begin
  have h1 : filter.tendsto (λ («x» : ℝ), 1 - S.C_L * «x») (nhds (S.C_L)⁻¹) (nhds (0)) := by {rw show (0 : ℝ) = 1 - 1, by norm_num, 
      apply filter.tendsto.sub, apply tendsto_const_nhds,  rw show (1 : ℝ) = S.C_L*S.C_L⁻¹, by { symmetry, rw mul_inv_cancel (ne_of_gt S.hCL),},
      apply filter.tendsto.const_mul, finish,},
  have h : 0 < (C S) := by { simp [BET.adsorption_constant], exact div_pos S.hC1 S.hCL,},
  simp only [brunauer_26, BET.n_layer_adsorption_rate, div_eq_inv_mul],
  apply filter.tendsto.at_top_mul h,
  apply filter.tendsto.inv_tendsto_zero,
  simp [nhds_within],
  apply filter.tendsto.inf,
  rw show 0 = 0*(C S), by simp,
  apply filter.tendsto.mul,
  exact h1,
  rw show nhds (C S) = nhds (0 + (C S)), by simp,
  apply filter.tendsto.add h1,
  rw show nhds (C S) = nhds ((C S)*1), by simp,
  apply filter.tendsto.const_mul,
  rw show 1 = S.C_L*S.C_L⁻¹, by {symmetry, rw mul_inv_eq_one₀, linarith[S.hCL]},
  apply filter.tendsto.const_mul,
  finish,
  simp,
  intros a ha1 ha2,
  have HC : S.C_L < S.C_1 ∨ S.C_1 ≤ S.C_L := by { apply lt_or_ge,},
  field_simp at ha2,
  rw lt_div_iff S.hCL at ha2,
  cases HC with HC1 HC2,
  { rw [zero_lt_mul_left, sub_add, ← neg_sub, neg_sub', lt_sub_comm, sub_zero, neg_sub, BET.adsorption_constant, ← mul_assoc, div_mul, div_self (ne_of_gt S.hCL), div_one, ← sub_mul, 
    mul_comm, ← div_lt_iff],
    apply lt_trans _ ha1,
    simp,
    rw [neg_div, neg_lt_zero],
    simpa using HC1,  
    simpa using HC1,
    rw [lt_sub_comm],
    simp,
    linarith [ha2],},
  { rw [BET.adsorption_constant, zero_lt_mul_right, lt_sub_comm],
    simp,
    linarith [ha2],
    rw [← mul_assoc, div_mul_cancel _ (ne_of_gt S.hCL), add_comm],
    apply lt_add_of_sub_left_lt,
    apply lt_sub_left_of_add_lt,
    rw [zero_sub, tactic.ring.add_neg_eq_sub, ← sub_mul],
    apply lt_trans _ ha2,
    rw mul_comm,
    apply mul_lt_mul',
    simp,
    field_simp [S.hC1],
    simp,
    exact HC2,
    exact ha1, },
  simp [nhds_within],
  apply filter.tendsto_inf_left,
  rw show nhds (C S) = nhds ((C S)*1), by simp,
  apply filter.tendsto.const_mul,
  rw show 1 = S.C_L*S.C_L⁻¹, by {symmetry, rw mul_inv_eq_one₀, linarith [S.hCL]},
  apply filter.tendsto.const_mul,
  finish,
end

lemma tendsto_at_bot_at_inv_CL (S : BET.system) (hCL : S.C_1 < S.C_L)
: filter.tendsto (brunauer_26 S) (nhds_within (1/S.C_L) (set.Ioo (1/S.C_L) (1/(S.C_L-S.C_1)))) filter.at_bot:=
begin
  have h1 : filter.tendsto (λ («x» : ℝ), -(1 - S.C_L * «x»)) (nhds (S.C_L)⁻¹) (nhds (0)) := by {simp, rw show (0 : ℝ) = 1 - 1, by norm_num, 
      apply filter.tendsto.sub, rw show (1 : ℝ) = S.C_L*S.C_L⁻¹, by { symmetry, rw mul_inv_cancel (ne_of_gt S.hCL),},
      apply filter.tendsto.const_mul, finish, apply tendsto_const_nhds,},
  have h2 : filter.tendsto (λ («x» : ℝ), 1 - S.C_L * «x») (nhds (S.C_L)⁻¹) (nhds (0)) := by {rw show (0 : ℝ) = 1 - 1, by norm_num, 
      apply filter.tendsto.sub, apply tendsto_const_nhds,  rw show (1 : ℝ) = S.C_L*S.C_L⁻¹, by { symmetry, rw mul_inv_cancel (ne_of_gt S.hCL),},
      apply filter.tendsto.const_mul, finish,},
  have h : 0 < (C S) := by { simp [BET.adsorption_constant], exact div_pos S.hC1 S.hCL,},
  simp only [brunauer_26, BET.n_layer_adsorption_rate, div_eq_inv_mul],
  apply filter.tendsto.at_bot_mul h,
  rw [← filter.tendsto_neg_at_top_iff],
  simp only [neg_inv],
  apply filter.tendsto.inv_tendsto_zero,
  simp [nhds_within],
  apply filter.tendsto.inf,
  rw [show 0 = 0*(C S), by simp],
  simp only [← neg_mul],
  apply filter.tendsto.mul,
  exact h1,
  rw show nhds (C S) = nhds (0 + (C S)), by simp,
  apply filter.tendsto.add,
  exact h2,
  rw show nhds (C S) = nhds ((C S)*1), by simp,
  apply filter.tendsto.const_mul,
  rw show 1 = S.C_L*S.C_L⁻¹, by {symmetry, rw mul_inv_eq_one₀, linarith[S.hCL]},
  apply filter.tendsto.const_mul,
  finish,
  simp,
  intros a ha1 ha2,
  { rw [←neg_neg ((1 - S.C_L * a) * (1 - S.C_L * a + C S * (S.C_L * a))), neg_lt_zero, ← neg_mul,
    BET.adsorption_constant, zero_lt_mul_right],
    field_simp at ha1,
    rw div_lt_iff S.hCL at ha1,
    simp,
    linarith [ha1],
    rw [← mul_assoc, div_mul, div_self (ne_of_gt S.hCL), div_one, sub_add, ← sub_mul],
    simp,
    ring_nf,
    rw [← mul_sub],
    field_simp at ha2,
    rw lt_div_iff at ha2,
    linarith [ha2],
    linarith [hCL],},
  simp [nhds_within],
  apply filter.tendsto_inf_left,
  rw show nhds (C S) = nhds ((C S)*1), by simp,
  apply filter.tendsto.const_mul,
  rw show 1 = S.C_L*S.C_L⁻¹, by {symmetry, rw mul_inv_eq_one₀, linarith [S.hCL]},
  apply filter.tendsto.const_mul,
  finish,
end

lemma tendsto_at_bot_at_inv_CL' (S : BET.system) (hCL : S.C_L ≤ S.C_1)
: filter.tendsto (brunauer_26 S) (nhds_within (1/S.C_L) (set.Ioi (1/S.C_L))) filter.at_bot:=
begin
  have h1 : filter.tendsto (λ («x» : ℝ), -(1 - S.C_L * «x»)) (nhds (S.C_L)⁻¹) (nhds (0)) := by {simp, rw show (0 : ℝ) = 1 - 1, by norm_num, 
      apply filter.tendsto.sub, rw show (1 : ℝ) = S.C_L*S.C_L⁻¹, by { symmetry, rw mul_inv_cancel (ne_of_gt S.hCL),},
      apply filter.tendsto.const_mul, finish, apply tendsto_const_nhds,},
  have h2 : filter.tendsto (λ («x» : ℝ), 1 - S.C_L * «x») (nhds (S.C_L)⁻¹) (nhds (0)) := by {rw show (0 : ℝ) = 1 - 1, by norm_num, 
      apply filter.tendsto.sub, apply tendsto_const_nhds,  rw show (1 : ℝ) = S.C_L*S.C_L⁻¹, by { symmetry, rw mul_inv_cancel (ne_of_gt S.hCL),},
      apply filter.tendsto.const_mul, finish,},
  have h : 0 < (C S) := by { simp [BET.adsorption_constant], exact div_pos S.hC1 S.hCL,},
  simp only [brunauer_26, BET.n_layer_adsorption_rate, div_eq_inv_mul],
  apply filter.tendsto.at_bot_mul h,
  rw [← filter.tendsto_neg_at_top_iff],
  simp only [neg_inv],
  apply filter.tendsto.inv_tendsto_zero,
  simp [nhds_within],
  apply filter.tendsto.inf,
  rw [show 0 = 0*(C S), by simp],
  simp only [← neg_mul],
  apply filter.tendsto.mul,
  exact h1,
  rw show nhds (C S) = nhds (0 + (C S)), by simp,
  apply filter.tendsto.add,
  exact h2,
  rw show nhds (C S) = nhds ((C S)*1), by simp,
  apply filter.tendsto.const_mul,
  rw show 1 = S.C_L*S.C_L⁻¹, by {symmetry, rw mul_inv_eq_one₀, linarith[S.hCL]},
  apply filter.tendsto.const_mul,
  finish,
  simp,
  intros a ha1,
  rw le_iff_lt_or_eq at hCL,
  cases hCL with hCL1 hCL2,
  { rw [←neg_neg ((1 - S.C_L * a) * (1 - S.C_L * a + C S * (S.C_L * a))), neg_lt_zero, ← neg_mul,
    BET.adsorption_constant, zero_lt_mul_right],
    field_simp at ha1,
    rw div_lt_iff S.hCL at ha1,
    simp,
    linarith [ha1],
    rw [← mul_assoc, div_mul, div_self (ne_of_gt S.hCL), div_one, sub_add, ← sub_mul],
    simp,
    ring_nf,
    have h3 : S.C_L < S.C_1 ↔  a*(S.C_L - S.C_1) < 0,
    { have h4 : 0 < a, { apply lt_trans _ ha1, simp, linarith [S.hCL],},
      split,
      intro,
      rw [← mul_zero a, mul_lt_mul_left h4],
      linarith [S.hCL],
      intro,
      exact hCL1,},
    rw [← mul_sub],
    apply lt_trans' _ (h3.mp hCL1),
    finish,},
    { rw [←neg_neg ((1 - S.C_L * a) * (1 - S.C_L * a + C S * (S.C_L * a))), neg_lt_zero, ← neg_mul,
      BET.adsorption_constant, zero_lt_mul_right],
      field_simp at ha1,
      rw div_lt_iff S.hCL at ha1,
      simp,
      linarith [ha1],
      rw [← mul_assoc, div_mul, div_self (ne_of_gt S.hCL), div_one, sub_add, ← sub_mul, hCL2],
      finish,},
  simp [nhds_within],
  apply filter.tendsto_inf_left,
  rw show nhds (C S) = nhds ((C S)*1), by simp,
  apply filter.tendsto.const_mul,
  rw show 1 = S.C_L*S.C_L⁻¹, by {symmetry, rw mul_inv_eq_one₀, linarith [S.hCL]},
  apply filter.tendsto.const_mul,
  finish,
end

def brunauer_28 (S : BET.system) := λ P : ℝ , (C S)*P/((S.P₀-P)*(1+((C S)-1)*(P/S.P₀)))

theorem brunauer_28_from_seq
{P V₀: ℝ}
(S : BET.system)
(h27 : S.P₀ = 1/S.C_L)
(hx1: (x S P) < 1)
(hx2 : 0 < (x S P))
(hP : 0 < P)
: (V S V₀ P)/(A S P) = V₀*(brunauer_28 S P) :=
begin
  have h1 := brunauer_26_from_seq hx1 hx2 hP,
  simp at *,
  rw [h1, brunauer_26, brunauer_28, BET.adsorption_constant],
  field_simp,
  rw [BET.n_layer_adsorption_rate, h27],
  rw [← mul_assoc, mul_comm S.C_L _, ← mul_assoc, mul_comm _ S.C_L, mul_div_mul_left _ _ (ne_of_gt S.hCL),
  ← mul_assoc S.C_L _ _, mul_sub, mul_inv_cancel (ne_of_gt S.hCL), ← mul_assoc V₀ _ _, mul_comm S.C_L P, mul_div_assoc S.C_1 _ _, mul_div_cancel _ (ne_of_gt S.hCL), sub_mul _ _ P, inv_eq_one_div,
  ← div_mul, div_one, sub_mul _ _ S.C_L, one_mul, mul_comm (S.C_1 / S.C_L * P) S.C_L, ← mul_assoc S.C_L _ _, mul_div, mul_comm S.C_L S.C_1, mul_div_cancel _ (ne_of_gt S.hCL), add_sub, add_sub_right_comm],
end
end BET
