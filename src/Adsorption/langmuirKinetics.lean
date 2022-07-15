import data.real.basic

theorem kineticDerivLangmuir
[comm_group ℝ]
(theta k_eq P_A r_ad r_d k_ad k_d A_ad S_0 S : ℝ) --premises
(h1 : r_ad = k_ad*P_A*S) -- Adsorption rate expression
(h2 : r_d = k_d*A_ad) -- Desorption rate expression
(h3 : r_ad = r_d) -- Equilibrium assumption
(h4 : k_eq = k_ad/k_d) -- Definition of adsorption constant
(h5 : S_0 = S + A_ad) -- Site balance
(h6 : theta = A_ad/S_0) -- Definition of fractional coverage
(h7 : S + A_ad ≠ 0) 
(h8 : k_d + k_ad * P_A ≠ 0)
(h9 : k_d ≠ 0)
: 
theta = k_eq*P_A/(1+k_eq*P_A) := -- Langmuir's adsorption law
begin
  rw [h1, h2] at h3,
  rw [h6, h5, h4],
  field_simp,
  iterate 2 {rw mul_add},
  rw [h3, ← right_distrib _ _ A_ad, ← left_distrib, mul_comm],  
end

