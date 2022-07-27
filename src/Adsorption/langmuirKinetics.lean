import data.real.basic

theorem Langmuir_single_site
(Pₐ k_ad k_d A S : ℝ)
(hreaction : let r_ad := k_ad*Pₐ*S, r_d := k_d*A in r_ad = r_d) 
(hS : S ≠ 0)
(hk_d : k_d ≠ 0)
: 
let θ := A/(S+A),
    K := k_ad/k_d in 
θ = K*Pₐ/(1+K*Pₐ) :=
begin
  simp at hreaction,
  rw [mul_comm k_d A, ← div_eq_div_iff hk_d hS] at hreaction,
  field_simp [hreaction],
end

