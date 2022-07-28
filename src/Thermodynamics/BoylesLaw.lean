import data.real.basic
import data.real.nnreal

-- Variables
lemma Boyle (P1 P2 V1 V2 T1 T2 n1 n2 R : ℝ )

-- Assumptions
(a1: P1*V1=n1*R*T1)
(a2: P2*V2=n2*R*T2)
(a3: T1=T2) 
(a4: n1=n2) : 


(P1*V1=P2*V2)
:=

begin
    rw a3 at a1,
    rw a4 at a1,
    exact (rfl.congr (eq.symm a2)).mp a1, 
end

