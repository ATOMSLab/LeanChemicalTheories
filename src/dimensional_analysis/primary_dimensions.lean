import algebra.group.defs
import tactic

universe u

class primary_dimensions (dimension : Type u) [comm_group dimension] :=
(length : dimension)
(mass : dimension)
(amount_of_mass : dimension) --aka moles
(absolute_temperature : dimension)


variables {dimension : Type u} [comm_group dimension] (D : primary_dimensions dimension)


local notation `L` := D.length
local notation `M` := D.mass
local notation `N` := D.amount_of_mass


--define advanced dimensions
def volume := L^3
local notation `V` := volume D

def density := M/L^3
local notation `ρ` := density D

def molecular_weight := M/N
local notation `MW` := molecular_weight D

def molar_volume := L^3/N
local notation `MV` := molar_volume D 

def specific_volume := L^3/M
local notation `SV` := specific_volume D



theorem molar_volume_div_molecular_weight_eq_density : MW/MV = ρ :=
begin
  field_simp [molecular_weight, molar_volume, density],
end

theorem specific_volume_eq_inv_of_density : SV = ρ⁻¹ :=
begin
  field_simp [specific_volume, density],
end