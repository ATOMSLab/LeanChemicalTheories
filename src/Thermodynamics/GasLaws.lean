import data.real.basic
import data.real.nnreal
open nnreal
universe u_1
local notation `ℝ≥0` := {r : ℝ // 0 ≤ r}
theorem exist_mul_eq_const_to_binary_relation
{C : ℝ≥0}
(h1 : ∃(a b : ℝ≥0), a*b = C)
:
∃ (a1 a2 b1 b2 : ℝ≥0), a1*b1 = a2*b2 
:=
begin
    have h2 : ∃(a b : ℝ≥0), a*b = C,
    exact h1,
    cases h1 with a1 h1,
    cases h1 with b1 h1,
    cases h2 with a2 h2,
    cases h2 with b2 h2,
    rw ← h1 at h2,
    use a1, use a2, use b1, use b2,
    symmetry,
    exact h2,
end
theorem exist_div_eq_const_to_binary_relation
{C : ℝ≥0}
(h1 : ∃(a b : ℝ≥0), a/b = C)
:
∃ (a1 a2 b1 b2 : ℝ≥0), a1/b1 = a2/b2 
:=
begin
    have h2 : ∃(a b : ℝ≥0), a/b = C,
    exact h1,
    cases h1 with a1 h1,
    cases h1 with b1 h1,
    cases h2 with a2 h2,
    cases h2 with b2 h2,
    rw ← h1 at h2,
    use a1, use a2, use b1, use b2,
    symmetry,
    exact h2,
end

lemma Boyle's_Law 
{k : ℝ≥0}
(h1 : ∃(P V : ℝ≥0), P*V = k)
:
∃ (P1 P2 V1 V2 : ℝ≥0), P1*V1 = P2*V2 
:=
begin
    apply exist_mul_eq_const_to_binary_relation,
    exact h1,
    
end

lemma Boyle's_Law_2
{k : ℝ}
{P V: ℕ → ℝ}
(hV : ∀ n, (V n) ≠ 0)
(h1 : ∀ n, P n = k/(V n)) --n is the state of our system
:
(P 1)*(V 1) = (P 2)*(V 2)
:=
begin
have h2 : ∀ n m, (P n)*(V n) = (P m)*(V m),
{ intros n m, 
  have h1' : ∀ n, P n = k/(V n) := h1,
  specialize h1 n,
  specialize h1' m,
  simp_rw [h1, h1'],
  field_simp,
  iterate 2 {rw [mul_div_assoc, div_self]},
  iterate 2 {apply hV},
},
specialize h2 1,
specialize h2 2,
exact h2,
end

lemma Charle's_Law 
{k : ℝ≥0}
(h1 : ∃(V T: ℝ≥0), V/T = k)
:
∃ (V1 V2 T1 T2 : ℝ≥0), V1/T1 = V2/T2 
:=
begin
    apply exist_div_eq_const_to_binary_relation,
    exact h1,
end

lemma Avagadro's_Law 
{k : ℝ≥0}
(h1 : ∃(V n : ℝ≥0), V/n = k)
:
∃ (V1 V2 n1 n2 : ℝ≥0), V1/n1 = V2/n2 
:=
begin
  apply exist_div_eq_const_to_binary_relation,
  exact h1,
end

lemma Gay_Lussac_law
{k : ℝ≥0}
(h1 : ∃(P T :ℝ≥0), P/T = k)
:
∃ (P1 P2 T1 T2 : ℝ≥0), P1/T1 = P2/T2 
:=
begin
  apply exist_div_eq_const_to_binary_relation,
  exact h1,
end

lemma ideal_gas_law
{kb kc ka kg R: ℝ}
{P V T N: ℕ → ℝ}
(hV : ∀ n, (V n) ≠ 0)
(hb : ∀ n, P n = kb/(V n))
(hc : ∀ n, T n = kc*(V n))
(ha : ∀ n, V n = ka*(N n))
(hg : ∀ n, P n = kg*(T n))
:
∀ n, (P n)*(V n) = R*(N n)*(T n) 
:=
begin
intro n,
rw [hb n, hc n, ha n],

end
