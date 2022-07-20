import data.real.basic
/-We define the langmuir single site isotherm as the outcome of a constant function.
Equillibrium is defined by hreaction, where we say that the adsopriton rate is equal
to the desoprtion rate. In hreaction, we define the local definiton of each rate. 
The adsoprtion rate is defined as the product of the adsoprtion rate constant,
the partial pressure and the concentration of empty sites. The desoprtion rate is defined
as the product of the desoprtion rate and the concentration of sites filled with A. We then
define the langmuir isotherm as the equation relating the fraction adsorbed, θ, to the equilibrium
constant and the partial pressure of A-/

theorem Langmuir_single_site
(Pₐ k_ad k_d A S : ℝ)
(hreaction : let r_ad := k_ad*Pₐ*S, r_d := k_d*A in r_ad = r_d) 
(hS : S ≠ 0)
(hk_d : k_d ≠ 0)
: 
let θ := A/(S+A), --local definition of fractional adsorption
    K := k_ad/k_d in --local definition of equillibrium constant
θ = K*Pₐ/(1+K*Pₐ) :=
begin
  simp at hreaction,
  rw [mul_comm k_d A, ← div_eq_div_iff hk_d hS] at hreaction,
  field_simp [hreaction],
end

