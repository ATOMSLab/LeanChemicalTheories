import data.real.basic

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

