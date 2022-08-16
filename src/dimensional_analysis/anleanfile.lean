
def volume := L^3
local notation `V` := volume

def density := M/L^3
local notation `ρ` := density

def molecular_weight := M/N
local notation `MW` := molecular_weight

def molar_volume := L^3/N
local notation `MV` := molar_volume

def specific_volume := L^3/M
local notation `SV` := specific_volume

def area := L^2
local notation `A` := area 

def force := M*L/T^2
local notation `F` := force 

def pressure := M/(T^2*L)
local notation `p` := pressure

def acceleration := L/T^2
local notation `g`:= acceleration

def coeff_therm_exp:= θ⁻¹
local notation `β` := coeff_therm_exp

def kinematic_viscosity := L^2/T
local notation `ν`:= kinematic_viscosity

def dynamic_viscosity:= M*L⁻¹*T⁻¹
local notation `μ`:= dynamic_viscosity

def specific_heat:= M*L^2/T^2
local notation `cp`:= specific_heat

def surface_temp := θ
local notation `T_s` := surface_temp

def bulk_temp := θ
local notation `T_inf`:= bulk_temp

def diameter := L
local notation `D` := diameter

def temp_diff := θ
local notation `deltaT` := temp_diff

def therm_diffusivity := L^2/T
local notation `α` := therm_diffusivity


theorem molar_volume_div_molecular_weight_eq_density : MW/MV = ρ :=
begin
  field_simp [molecular_weight, molar_volume, density],
end

theorem volume_div_area_eq_length :V/A = L :=
begin
  field_simp [volume, area, length],
  norm_num,
end

theorem p_eq_force_div_area :F/A = p:=
begin
  field_simp [force, area, pressure,length,mass,time],
  norm_num,
end

theorem dimensionless_grashof: g*β*(T_s-T_inf)*(L^3)/(ν^2)=1 :=
begin
  field_simp [acceleration,coeff_therm_exp,surface_temp,bulk_temp,diameter,kinematic_viscosity,length,absolute_temperature,time],
  norm_num,
end

theorem dimensionless_prandtl: ν/α =1:=
begin
  field_simp [kinematic_viscosity,therm_diffusivity],
end

def Grashof := g*β*(T_s-T_inf)*(L^3)/(ν^2)
local notation `Gr`:= Grashof

def Prandtl := ν/α
local notation `Pr`:= Prandtl

def Rayleigh:= Grashof*Prandtl
local notation `Ra` := Rayleigh

theorem dimensionless_rayleigh: Gr*Pr=1:=
begin
  field_simp [Grashof,Prandtl,acceleration,coeff_therm_exp,surface_temp,bulk_temp,diameter,kinematic_viscosity,length,absolute_temperature,time,therm_diffusivity],
  norm_num,
end