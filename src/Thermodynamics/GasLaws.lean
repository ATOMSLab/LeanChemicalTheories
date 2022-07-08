import data.real.nnreal
open_locale nnreal
theorem fun_eq_inverse_fun_to_relation
{c : ℝ≥0}
{f g: ℕ → ℝ≥0}
(hg : ∀ n, (g n) ≠ 0)
(h1 : ∀ n, f n = c/(g n))
:
∀ n m, (f n)*(g n) = (f m)*(g m):=
begin
intros n m, 
have h1' : ∀ n, f n = c/(g n) := h1,
specialize h1 n,
specialize h1' m,
simp_rw [h1, h1'],
field_simp,
iterate 2 {rw [mul_div_assoc, div_self]},
iterate 2 {apply hg},
end
theorem fun_eq_fun_to_relation
{c : ℝ≥0}
{f g: ℕ → ℝ≥0}
(h1 : ∀ n, f n = c*(g n))
:
∀ n m, (f n)*(g m) = (f m)*(g n) :=
begin
intros n m, 
have h1' : ∀ n, f n = c*(g n) := h1,
specialize h1 n,
specialize h1' m,
simp_rw [h1, h1'],
rw [mul_assoc, mul_comm (g n) _, ← mul_assoc],
end

lemma Boyle's_Law
{k : ℝ≥0}
{P V: ℕ → ℝ≥0}
(hV : ∀ n, (V n) ≠ 0)
(h1 : ∀ n, P n = k/(V n)) --n is the state of our system
:
(P 1)*(V 1) = (P 2)*(V 2)
:=
begin
exact fun_eq_inverse_fun_to_relation hV h1 1 2,
end

lemma Charle's_Law 
{k : ℝ≥0}
{T V: ℕ → ℝ≥0}
(h1 : ∀ n, V n = k*(T n))
:
(V 1)*(T 2) = (V 2)*(T 1)
:=
begin
exact fun_eq_fun_to_relation h1 1 2,
end

lemma Avagadro's_Law 
{k : ℝ≥0}
{N V: ℕ → ℝ≥0}
(h1 : ∀ n, V n = k*(N n))
:
(V 1)*(N 2) = (V 2)*(N 1)
:=
begin
exact Charle's_Law h1, -- I think this is funny
end

lemma Gay_Lussac_law
{k : ℝ≥0}
{P T: ℕ → ℝ≥0}
(h1 : ∀ n, P n = k*(T n))
:
(P 1)*(T 2) = (P 2)*(T 1)
:=
begin
exact Charle's_Law h1,
end

lemma ideal_gas_law
{ka kg R: ℝ≥0}
{P V T N: ℕ → ℝ≥0}
(ha : ∀ n, V n = ka*(N n))
(hg : ∀ n, P n = kg*(T n))
(hR : R = ka*kg)
:
∀ n, (P n)*(V n) = R*(N n)*(T n) 
:=
begin
intro n,
rw [hg n, ha n, hR, mul_assoc, mul_comm (T n) _, ← mul_assoc, 
← mul_assoc, mul_comm kg ka],
end
