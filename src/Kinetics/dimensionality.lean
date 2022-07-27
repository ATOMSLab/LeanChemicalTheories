import data.real.basic

theorem dim_analysis {volume mass numMoles specificVolume molecularWeight molarVolume : ℝ }: specificVolume = volume/mass ∧ molecularWeight = mass/numMoles ∧ molarVolume = volume/numMoles ∧ mass>0 → specificVolume*molecularWeight = molarVolume :=
begin
  intro h,
  cases h with h1 h2,
  cases h2 with h3 h4,
  cases h4 with h5 h6,
  rw h1,
  rw h3,
  rw h5, 
  rw div_mul_div_cancel, 
  exact ne_of_gt h6, 
end
