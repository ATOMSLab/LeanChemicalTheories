import algebra.group.defs
import analysis.inner_product_space.basic
/-!

# The Thermodynamic System and Models
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

class thermo_system :=

(pressure : ℕ → ℝ)
(volume : ℕ → ℝ)
(temperature : ℕ → ℝ)
(substance_amount : ℕ → ℝ)
(energy : ℕ → ℝ)

export thermo_system (pressure volume temperature substance_amount energy)


def isobaric (M : thermo_system) : Prop := ∀ n m : ℕ, pressure n = pressure m
def isochoric (M : thermo_system) : Prop := ∀ n m : ℕ, volume n = volume m
def isothermal (M : thermo_system) : Prop := ∀ n m : ℕ, temperature n = temperature m
def adiabatic (M : thermo_system) : Prop :=  ∀ n m : ℕ, energy  n = energy m
def closed_system (M : thermo_system) : Prop := ∀ n m : ℕ, substance_amount  n = substance_amount m
def isolated_system (M : thermo_system) : Prop := adiabatic M ∧ closed_system M

/-!### Gas Laws-/
def boyles_law (M : thermo_system) :=  ∃ (k : ℝ), ∀ n : ℕ, (pressure n) * (volume n)= k
def charles_law (M : thermo_system) :=  ∃ (k : ℝ), ∀ n : ℕ, (volume n) = k * (temperature n)
def avogadros_law (M : thermo_system):=  ∃ (k : ℝ), ∀ n : ℕ, (volume n) = k * (substance_amount n)
variables {M : thermo_system}
theorem boyles_law_relation 

: boyles_law M →  ∀ n m, pressure n*volume n = pressure m * volume m:=
begin
  intros h n m,
  simp [boyles_law] at h,
  cases h with k h,
  field_simp [h n, h m],
end

theorem boyles_law_relation'

: (∀ n m, pressure n * volume n = pressure m * volume m) → boyles_law M :=
begin
  intros h,
  simp [boyles_law],
  use (pressure 1 * volume 1),
  intro,
  exact h n 1,
end

theorem charles_law_relation 
: charles_law M →  ∀ n m, volume n * temperature m = volume m * temperature n:=
begin
  intros h n m,
  simp [charles_law] at h,
  cases h with k h,
  rw [h n, h m],
  ring_exp
end

theorem charles_law_relation'
(hT : temperature 1 ≠ 0)
: (∀ n m, volume n * temperature m = volume m * temperature n) → charles_law M :=
begin
  intros h,
  simp [charles_law],
  use (volume 1 / temperature 1),
  intro,
  field_simp [h n 1],
end

theorem avogadros_law_relation 
: avogadros_law M →  ∀ n m, volume n * substance_amount m = volume m * substance_amount n :=
begin
  intros h n m,
  simp [avogadros_law] at h,
  cases h with k h,
  rw [h n, h m],
  ring_exp,
end

theorem avogadros_law_relation'
(hn : substance_amount 1 ≠ 0)
: (∀ n m, volume n * substance_amount m = volume m * substance_amount n) → avogadros_law M :=
begin
  intros h,
  simp [avogadros_law],
  use (volume 1 / substance_amount 1),
  intro,
  field_simp [h n 1],
end

/-! ### System models-/
class ideal_gas
  extends thermo_system  :=
(R : ℝ)
(ideal_gas_law : ∀ n : ℕ, (pressure n)*(volume n) = (substance_amount n)*R*(temperature n))



/-! ### Properties about the ideal gas law-/

theorem ideal_gas_law_relation 
{M : ideal_gas}
: ∀ n m : ℕ, (@pressure M.to_thermo_system n)*(volume n)*((substance_amount m)*(temperature m)) = 
(pressure m)*(volume m)*((substance_amount n)*(temperature n)):=
begin
  intros,
  let h1 := ideal_gas.ideal_gas_law n,
  let h2 := ideal_gas.ideal_gas_law m,
  rw [h1,h2],
  ring_exp,
end



theorem boyles_from_ideal_gas {M : ideal_gas} (iso1 : isothermal M.to_thermo_system)
(iso2 : closed_system M.to_thermo_system)
(hT : ∀ n, temperature n ≠ 0)
(hn : ∀ n, substance_amount n ≠ 0)
: boyles_law M.to_thermo_system:=
begin
  simp [boyles_law, isothermal, closed_system] at *,
  let h := ideal_gas_law_relation,
  apply boyles_law_relation',
  intros,
  specialize h n m,
  rw [iso1 n m, iso2 n m] at h,
  field_simp [hT m, hn m] at h,
  exact h,
end

theorem charles_from_ideal_gas {M : ideal_gas} (iso1 : isobaric M.to_thermo_system)
(iso2 : closed_system M.to_thermo_system)
(hT : ∀ n, temperature n ≠ 0)
(hn : ∀ n, substance_amount n ≠ 0)
(hP : ∀ n, pressure n ≠ 0)
: charles_law M.to_thermo_system:=
begin
  simp [charles_law, isobaric, closed_system] at *,
  let h := ideal_gas_law_relation,
  apply charles_law_relation' (hT 1),
  intros,
  specialize h n m,
  rw [iso1 n m, iso2 n m] at h,
  field_simp [mul_mul_mul_comm, hP m, hn m] at h,
  exact h, 
end

theorem avogadros_from_ideal_gas {M : ideal_gas} (iso1 : isothermal M.to_thermo_system)
(iso2 : isobaric M.to_thermo_system) 
(hT : ∀ n, temperature n ≠ 0)
(hn : ∀ n, substance_amount n ≠ 0)
(hP : ∀ n, pressure n ≠ 0)
: avogadros_law M.to_thermo_system:=
begin
  simp [avogadros_law, isothermal, isobaric] at *,
  let h := ideal_gas_law_relation,
  apply avogadros_law_relation' (hn 1),
  intros,
  specialize h n m,
  rw [iso1 n m, iso2 n m] at h,
  rw [mul_mul_mul_comm (pressure m), mul_comm (pressure m) _, mul_mul_mul_comm (substance_amount _)] at h,
  rw [mul_mul_mul_comm (pressure m), mul_comm (pressure m) (substance_amount n), mul_mul_mul_comm (substance_amount n)] at h,
  field_simp [hP m, hT m] at h,
  rw [mul_comm, mul_comm _ (volume m)] at h,
  exact h,  
end
