import algebra.group.defs
import analysis.inner_product_space.basic
/-!# The Thermodynamic System and Models
We define a thermodynamic system to be over a general field, which we require to be an albelian group 
for multiplication. This class has five properties to describe the system, pressure, volume, temperature, 
amount of substance, and energy. Each property is defined as a function from the natural numbers to our 
field. This function represents the equillibrium states of the system. 

We also define six properties of a thermodynamic system: isobaric, isochoric, isothermal, adiabatic,
closed system, and isolated system. These take in a thermodynamic system and have the type Prop, so
they can be thought of as assertation about the system.

We finally define an ideal gas, which extends the thermodynamic system by providing a model for the systems
properties. So far, the ideal gas only defines the unviersal gas constant and the ideal gas law. Then we show
how the boyles law follows form the ideal gas law and the assumption of isothermal and a closed system


## To Do
  - Consider changing from general field to real numbers. Can run into problem where we have number of atoms as a real a number, but it should be a natural number
  - Add more parameters to the ideal gas model, including ideal models of energy. 
  - Define more for energy: heat capacity as a function of temeperature, the first and second law of thermodynamics
    -/

universe u

class thermo_system (𝕜 : Type u) [comm_group 𝕜] :=

(pressure : ℕ → 𝕜)
(volume : ℕ → 𝕜)
(temperature : ℕ → 𝕜)
(substance_amount : ℕ → 𝕜)
(energy : ℕ → 𝕜)

export thermo_system (pressure volume temperature substance_amount energy)


def isobaric {𝕜 : Type u} [comm_group 𝕜] (M : thermo_system 𝕜) : Prop := ∀ n m : ℕ, @pressure 𝕜 _ _ n = pressure m
def isochoric {𝕜 : Type u} [comm_group 𝕜] (M : thermo_system 𝕜) : Prop := ∀ n m : ℕ, @volume 𝕜 _ _ n = volume m
def isothermal {𝕜 : Type u} [comm_group 𝕜] (M : thermo_system 𝕜) : Prop := ∀ n m : ℕ, @temperature 𝕜 _ _ n = temperature m
def adiabatic {𝕜 : Type u} [comm_group 𝕜] (M : thermo_system 𝕜) : Prop :=  ∀ n m : ℕ, @energy 𝕜 _ _ n = energy m
def closed_system {𝕜 : Type u} [comm_group 𝕜] (M : thermo_system 𝕜) : Prop := ∀ n m : ℕ, @substance_amount 𝕜 _ _ n = substance_amount m
def isolated_system {𝕜 : Type u} [comm_group 𝕜] (M : thermo_system 𝕜) : Prop := adiabatic M ∧ closed_system M


/-! ### System models-/
class ideal_gas (𝕜 : Type u) [comm_group 𝕜]
  extends thermo_system 𝕜 :=
(R : 𝕜)
(ideal_gas_law : ∀ n : ℕ, (pressure n)*(volume n) = (substance_amount n)*R*(temperature n))

def boyles_law {𝕜 : Type u} [comm_group 𝕜] (M : ideal_gas 𝕜) :=  ∃ (k : 𝕜), ∀ n : ℕ, (pressure n) * (volume n)= k

/-! ### Properties about the ideal gas law-/
variables {𝕜 : Type u}[comm_group 𝕜] {M : ideal_gas 𝕜}
theorem ideal_gas_law_relation 
: ∀ n m : ℕ, (@pressure 𝕜 _ M.to_thermo_system n)*(volume n)/((substance_amount n)*(temperature n)) = 
(pressure m)*(volume m)/((substance_amount m)*(temperature m)):=
begin
  intros,
  let h1 := ideal_gas.ideal_gas_law n,
  let h2 := ideal_gas.ideal_gas_law m,
  rw [h1,h2],
  field_simp,
end

theorem boyles_law_relation 
: boyles_law M →  ∀ n m, (@pressure 𝕜 _ _ n)*volume n = pressure m * volume m:=
begin
  intros h n m,
  simp [boyles_law] at h,
  cases h with k h,
  field_simp [h n, h m],
end

theorem boyles_law_relation'
: (∀ n m, (@pressure 𝕜 _ _ n)*volume n = pressure m * volume m) → boyles_law M :=
begin
  intros h,
  simp [boyles_law],
  use (pressure 1 * volume 1),
  intro,
  exact h n 1,
end

theorem boyles_from_ideal_gas {𝕜 : Type u}[comm_group 𝕜] {M : ideal_gas 𝕜} (iso1 : isothermal M.to_thermo_system)
(iso2 : closed_system M.to_thermo_system)
: boyles_law M:=
begin
  simp [boyles_law, isothermal, closed_system] at *,
  let h := @ideal_gas_law_relation 𝕜 _ M,
  apply boyles_law_relation',
  intros,
  specialize h n m,
  simp [iso1 n m, iso2 n m] at h,
  exact h,  
end

