import data.real.basic
import data.real.nnreal

-- Variables
lemma Boyle (P1 P2 V1 V2 T1 T2 n1 n2 R : ℝ )

-- Assumptions
(a1: P1*V1=n1*R*T1)  -- Gas 1 is ideal
(a2: P2*V2=n2*R*T2)  -- Gas 2 is ideal
(a3: T1=T2)  -- Temperature is equal
(a4: n1=n2) :  -- Number of moles is equal

--Conjecture
(P1*V1=P2*V2) -- Boyle's Law
:=

begin
    rw a3 at a1,
    rw a4 at a1,
    exact (rfl.congr (eq.symm a2)).mp a1,
    --or  rw ← a2 at a1, 
    --and exact a1,   
end

open nnreal
local notation `ℝ≥0` := {r : ℝ // 0 ≤ r}
theorem Boyle's_Law_2
{k : ℝ≥0}
(h1 : ∃(P V : ℝ≥0), P*V = k)
:
∃ (P1 P2 V1 V2 : ℝ≥0), P1*V1 = P2*V2 
:=
begin
    have h2 : ∃(P V : ℝ≥0), P*V = k,
    exact h1,
    cases h1 with P1 h1,
    cases h1 with V1 h1,
    cases h2 with P2 h2,
    cases h2 with V2 h2,
    rw ← h1 at h2,
    use P1, use P2, use V1, use V2,
    symmetry,
    exact h2,
end
