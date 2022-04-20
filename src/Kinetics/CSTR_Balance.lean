import data.real.basic 

open real
axiom steady_state {accumulation : ℝ } : accumulation = 0 -- Steady State axiom
axiom mass_flow { mass_flow volume_flow conc : ℝ } : mass_flow = volume_flow*conc -- Mass Flow axiom
axiom reaction_gen { mass_gen react_con vol stoich : ℝ } : mass_gen = react_con*vol*stoich -- Mass Generated axiom

theorem cstr_balance (m_in m_out m_gen m_acc ra Q va Ca0 Ca V: ℝ) (v : V>0): 
m_acc = m_in - m_out + m_gen → 0 = Q/V * (Ca0 - Ca) + va*ra:=
begin
  intro h, --Use conditional derivation
  have h2 : m_acc = 0 := steady_state, -- have hypothesis mass accumulated is 0
  rw h2 at h, -- apply mass accumulated equals 0
  have h3 : m_in = Q*Ca0 := mass_flow, -- have hypothesis for equation for mass flow
  have h4 : m_out = Q*Ca := mass_flow, -- have hypothesis for equation for mass flow
  rw h3 at h, rw h4 at h, -- apply mass flow hypotheses
  have h5 : m_gen = ra*V*va := reaction_gen, -- have hypothesis for reaction term
  have h6 : m_gen = V*(ra*va) , -- rewrite reaction term for use later
  {
    rw mul_comm at h5,
    rw ← mul_assoc at h5,
    rw mul_comm at h5,
    rw mul_comm va at h5,
    exact h5,
  },
  rw h6 at h, -- apply reaction term 
  rw ← mul_sub at h, -- begin simplifing the main hypothesis
  rw ← one_mul Q at h,
  have v2 : V ≠ 0 := ne_of_gt v, -- need V not equal to 0 for simplification
  rw ← div_self v2 at h,
  rw mul_assoc at h,
  rw div_mul_eq_mul_div_comm at h,
  rw ← mul_add V at h,
  rw zero_eq_mul at h, -- give an or statement that V = 0 or the hypothesis
  cases h with h7 h8, -- split the or statement
  exfalso, -- prove that V = 0 is false
  apply v2 h7,
  symmetry, -- rearrange more to get final answer
  rw mul_div_assoc at h8,
  rw mul_div_comm at h8,
  rw mul_comm at h8,
  rw mul_comm ra at h8,
  exact h8,
end