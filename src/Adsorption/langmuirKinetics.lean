import data.real.basic

theorem Langmuir_single_site
(Pₐ k_ad k_d A S₀ S : ℝ)
(hreaction : let r_ad := k_ad*Pₐ*S, r_d := k_d*A in r_ad = r_d) --definition of equillibrium with local definitions

--three constraints that field_simp auto uses
(hS : S ≠ 0)
(hk_d : k_d ≠ 0)
(hPₐ : Pₐ ≠ 0)
: 
let θ := A/(S+A), --local definition of fractional adsorption
    K := k_ad/k_d in --local definition of equillibrium constant
θ = K*Pₐ/(1+K*Pₐ) :=
begin
  simp at hreaction,
  simp,
  have h : k_ad/k_d*Pₐ = A/S,
  { field_simp [hreaction],
    rw mul_comm,},
  rw h,
  field_simp,  
end

