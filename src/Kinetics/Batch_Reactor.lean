import math.anti_deriv
import data.complex.exponential


variables
{k: ℝ}(Cₐ rₐ : ℝ → ℝ)

theorem operating_equation_BR_first_order
(hrₐ :  rₐ  = λ t, -k*Cₐ t)
(hCₐ: (λ t, deriv Cₐ t) = λ t, (rₐ t))
:
Cₐ = λ t, (Cₐ 0)*real.exp (-k*t)
:=
begin
rw hrₐ at hCₐ,
end