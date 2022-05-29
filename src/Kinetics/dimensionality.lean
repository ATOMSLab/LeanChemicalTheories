import data.real.basic -- imports theory of real numbers

-- proves the conversion of specific volume to molar volume using molecular weight 
theorem dim_analysis {volume mass numMoles specificVolume molecularWeight molarVolume : ℝ }: specificVolume = volume/mass ∧ molecularWeight = mass/numMoles ∧ molarVolume = volume/numMoles ∧ mass>0 → specificVolume*molecularWeight = molarVolume :=
begin
  intro h, -- introduces conditional derivation
  cases h with h1 h2, -- splits and statements
  cases h2 with h3 h4, -- splits and statements
  cases h4 with h5 h6, -- splits and statements
  rw h1, -- rewrite specificVolume in terms of volume/mass
  rw h3, -- rewrite molecularWeight in terms of mass/numMoles
  rw h5, -- rewrite molarVolume in terms of vol/numMoles
  rw div_mul_div_cancel, -- simplifies the equation by cancelling out the common term (mass)
  exact ne_of_gt h6, 
end
