import data.real.basic


theorem kineticDerivLangmuir
[comm_group ℝ]
(theta k_eq P_A r_ad r_d k_ad k_d A_ad S_0 S: ℝ) --premises
(h1:r_ad = k_ad*P_A*S)
(h2:r_d = k_d*A_ad)
(h3:r_ad = r_d)
(h4:k_eq = A_ad/(P_A*S))
(h5:S_0 = S + A_ad)
(h6:theta = A_ad/S_0)
(h7: P_A > 0)
(h8: 1 + A_ad*S⁻¹ ≠ 0 )
(h9: S + A_ad ≠ 0)
(h10 : S > 0)
: 
theta = k_eq*P_A/(1+k_eq*P_A) :=
begin
rw h6,
rw div_eq_iff,
rw mul_comm,
rw ← mul_div_assoc,
rw eq_div_iff,
rw mul_add,
simp,
rw h4,
rw h5,
ring_nf,
simp,
left,
rw inv_eq_one_div,
rw mul_one_div,
rw mul_comm,
rw eq_div_iff,
rw one_mul,
rw mul_ne_zero_iff,
split,
exact ne_of_gt h7,
exact ne_of_gt h10,
rw h4,
rw mul_comm,
rw ← mul_div_assoc,
{
rw mul_div_mul_left,
rw one_add_div,
apply div_ne_zero,
exact h9,
repeat {exact ne_of_gt h10},
exact ne_of_gt h7,
},
rw h5,
exact h9,
end

