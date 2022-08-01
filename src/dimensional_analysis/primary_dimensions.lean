import algebra.group.defs
import tactic

universe u

structure primary_dimensions (dimension : Type u) [comm_group dimension] :=
(length : dimension)
(mass : dimension)
(amount_of_mass : dimension) --aka moles


variables {dimension : Type u} [comm_group dimension] (D : primary_dimensions dimension)


local notation `L` := D.length
local notation `M` := D.mass
local notation `N` := D.amount_of_mass



def volume := L^3
local notation `V` := volume D

def density := M⁻¹*L^3
local notation `ρ` := density D

def molecular_weight := M*N⁻¹
local notation `MW` := molecular_weight D

def molar_volume := L^3*N⁻¹
local notation `MV` := molar_volume D 



theorem molar_volume_div_molecular_weight_eq_density : MV/MW = ρ :=
begin
  field_simp [molecular_weight, molar_volume, density],
end

