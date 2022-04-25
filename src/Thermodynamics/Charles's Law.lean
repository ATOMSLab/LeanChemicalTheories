import analysis.complex.basic
namespace nnreal
open_locale nnreal big_operators

-- Variables
lemma Charles (P1 P2 V1 V2 T1 T2 n1 n2 R : ℝ≥0 )

-- Assumptions
(a1: P1*V1=n1*R*T1)  -- Gas 1 is ideal
(a2: P2*V2=n2*R*T2)  -- Gas 2 is ideal
(a3: P1=P2)  -- Pressure is constant
(a4: n1=n2)   -- Number of moles is equal

-- Constraints
(hT2: T2 ≠ 0)
(hP2: P2 ≠ 0)
(hT1: T1 ≠ 0)
 :
--Conjecture
(V1/T1)=(V2/T2)-- Charles's Law
:=

begin
  rw a3 at a1,
  rw a4 at a1,
  rw mul_comm P2 V1 at a1,
  rw mul_comm P2 V2 at a2,
  rw ← div_eq_div_iff at a1,
  rw ← div_eq_div_iff at a2,
  rw eq_comm at a2,
  rw a2 at a1,
  exact a1,
  exact hT2,
  exact hP2,
  exact hT1,
  exact hP2,
end
