import data.real.basic
import data.real.nnreal

/-!
# Boyle's Law
This section defines Boyle's Law which states that absolute pressure of an ideal gas is inversely proportional 
to the volume it occupies at constant temperature in a closed thermodynamic system. <br>
$$
P ∝ \frac{1}{V} 
$$
or
$$
P V  = k
$$

where:
- `P` is pressure
- `V` is volume
- `k` is a constant for a given sample of gas and depends only on the mass of the gas and the temperature 

### Assumption
The model assumes:
- ideal gas law for state 1 and state 2 (`PV = nRT`)
- equal temperature (`T1 = T2`)
- equal number of moles (`n1 = n2`)

#### A better proof for Boyle's law, following from the properties of a thermodynamic system, is shown [here](./basic.html).
-/

-- Variables
lemma Boyle (P1 P2 V1 V2 T1 T2 n1 n2 R : ℝ )
-- Assumptions
(a1: P1*V1=n1*R*T1)
(a2: P2*V2=n2*R*T2)
(a3: T1=T2) 
(a4: n1=n2) 
: 
-- Conjecture
(P1*V1=P2*V2)
:=
begin
    rw a3 at a1,
    rw a4 at a1,
    exact (rfl.congr (eq.symm a2)).mp a1, 
end
