import dimensional_analysis.basic

/-! # Proof of dimensionless numbers
We demonstrate Grashof and Prandtl numbers are dimensionless by expressing the variables in their
fundamental units defined in our [basic] (./basic.html) `dimensionsal_analysis` system.

Here:
- `g` is gravitational acceleration 
- `β` is coefficient of thermal expansion 
- `ν` is kinematic viscosity 
- `T_s` is surfact temperature
- `T_inf` is bulk temperature 
- `α` is thermal diffusivity 

-/

namespace dimension

local notation `L` := dimension.length
local notation `M` := dimension.mass
local notation `N` := dimension.amount_of_substance
local notation `I` := dimension.electric_current
local notation `θ` := dimension.absolute_temperature
local notation `T` := dimension.time
local notation `J` := dimension.luminous_intensity

def acceleration := L/T^2
local notation `g`:= acceleration

def coeff_therm_exp:= θ⁻¹
local notation `β` := coeff_therm_exp

def kinematic_viscosity := L^2/T
local notation `ν`:= kinematic_viscosity

def surface_temp := θ
local notation `T_s` := surface_temp

def bulk_temp := θ
local notation `T_inf`:= bulk_temp

def therm_diffusivity := L^2/T
local notation `α` := therm_diffusivity

def diameter := L
local notation `L` := diameter

theorem dimensionless_grashof: g*β*(T_s-T_inf)*(L^3)/(ν^2)=1 :=
begin
  field_simp [acceleration,coeff_therm_exp,surface_temp,bulk_temp,diameter,kinematic_viscosity,length,absolute_temperature,time],
  norm_num,
end

theorem dimensionless_prandtl: ν/α =1:=
begin
  field_simp [kinematic_viscosity,therm_diffusivity],
end

end dimension
