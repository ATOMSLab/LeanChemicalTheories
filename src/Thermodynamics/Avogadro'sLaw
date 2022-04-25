import data.real.basic

-- Variables
lemma Avogadro (P1 P2 V1 V2 T1 T2 n1 n2 R : ℝ )

-- Assumptions
(a1: P1*V1=n1*R*T1)  -- Gas 1 is ideal
(a2: P2*V2=n2*R*T2)  -- Gas 2 is ideal
(a3: P1=P2)  -- Pressure is constant
(a4: T1=T2)  -- Tempertature is constant


--
(hn2: n2 ≠ 0)
(hP2: P2 ≠ 0)
(hn1: n1 ≠ 0)
 :

--Conjecture
(V1/n1=V2/n2) -- Avogadro's Law
:=

begin
  rw a3 at a1,
  rw a4 at a1,
  rw mul_comm P2 V1 at a1,
  rw mul_comm P2 V2 at a2,
  rw mul_assoc n1 R T2 at a1,
  rw mul_comm n1 (R*T2) at a1,
  rw ← div_eq_div_iff at a1,
  rw mul_assoc n2 R T2 at a2,
  rw mul_comm n2 (R*T2) at a2,
  rw ← div_eq_div_iff at a2,
  rw eq_comm at a2,
  rw a2 at a1,
  exact a1,
  exact hn2,
  exact hP2,
  exact hn1,
  exact hP2,
end
