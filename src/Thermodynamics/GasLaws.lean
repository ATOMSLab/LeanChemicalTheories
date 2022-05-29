import data.real.basic
import data.real.nnreal
open nnreal
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

theorem Avagadro's_Law 
{k : ℝ≥0}
(h1 : ∃(n V : ℝ≥0), V/n = k)
:
∃ (V1 V2 n1 n2 : ℝ≥0), V1/n1 = V2/n2 
:=
begin
    have h2 :  ∃(n V : ℝ≥0), V/n = k,
    exact h1,
    cases h1 with n1 h1,
    cases h1 with V1 h1,
    cases h2 with n2 h2,
    cases h2 with V2 h2,
    rw ← h1 at h2,
    use V1, use V2, use n1, use n2,
    symmetry,
    exact h2,
end
theorem Ideal_Gas_Law
{R : ℝ≥0}

:

:=
begin

end