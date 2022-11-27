import data.list.basic
import algebra.group.to_additive
import algebra.group.pi
import data.rat.basic
universe u

/-! 
### Dimension type classes
-/

class has_time (α : Type u) :=
[dec : decidable_eq α]
(time : α)

class has_length (α : Type u) :=
[dec : decidable_eq α]
(length : α)

class has_mass (α : Type u) :=
[dec : decidable_eq α]
(mass : α)

class has_amount_of_substance (α : Type u) :=
[dec : decidable_eq α]
(amount_of_substance : α)

class has_electric_current (α : Type u) :=
[dec : decidable_eq α]
(electric_current : α)

class has_temperature (α : Type u) :=
[dec : decidable_eq α]
(temperature : α)

class has_luminous_intensity (α : Type u) :=
[dec : decidable_eq α]
(luminous_intensity : α)

attribute [instance] has_time.dec
attribute [instance] has_length.dec
attribute [instance] has_mass.dec
attribute [instance] has_amount_of_substance.dec
attribute [instance] has_electric_current.dec
attribute [instance] has_temperature.dec
attribute [instance] has_luminous_intensity.dec


/-! 
### Def of dimensions and the base dimensions
-/

@[derive comm_group]
def dimension (α : Type u) := multiplicative (α → ℚ)
namespace dimension

--I would love to add unicode to make specific globabl notation for dimension derivatives and integrals, 
--but thats more fluff than important

def derivative (α) : dimension α → dimension α → dimension α
| a b := a / b

def intergral (α) : dimension α → dimension α → dimension α
| a b := a * b


def length (α) [has_length α] : dimension α :=
pi.single (has_length.length) 1

def time (α) [has_time α] : dimension α :=
pi.single (has_time.time) 1

def mass (α) [has_mass α] : dimension α :=
pi.single (has_mass.mass) 1

def amount_of_substance (α) [has_amount_of_substance α] : dimension α :=
pi.single (has_amount_of_substance.amount_of_substance) 1

def electric_current (α) [has_electric_current α] : dimension α :=
pi.single (has_electric_current.electric_current) 1

def temperature (α) [has_temperature α] : dimension α :=
pi.single (has_temperature.temperature) 1

def luminous_intensity (α) [has_luminous_intensity α] : dimension α :=
pi.single (has_luminous_intensity.luminous_intensity) 1

def dimensionless (α) : dimension α := pi.single 1 1

/-! 
### Other dimensions
-/
--physics
def velocity (α) [has_length α] [has_time α] : dimension α := length α / time α

def acceleration (α) [has_length α] [has_time α] : dimension α := length α / ((time α) ^ 2)

def force (α) [has_length α] [has_time α] [has_mass α] : dimension α := length α / ((time α) ^ 2) * mass α


/-! 
### examples for personal understanding
-/
inductive system1
| time | length
#print system1
instance : decidable_eq system1 := sorry

instance : has_time system1 := {dec := system1.decidable_eq, time := system1.time}
instance : has_length system1 := {dec := system1.decidable_eq, length := system1.length}



variables (α : Type*) [has_time α] 
--This show that we index our tuple through the specific base dimension rather than the previous way of vector number
example : dimension.time system1 system1.time = 1 :=
begin
  simp [dimension.time],
  apply pi.single_eq_same,
end

example : dimension.time system1 system1.length = 0 :=
begin
  simp [dimension.time],
  apply pi.single_eq_of_ne,
  finish,
end


-- def dimension.add {α : Type u} [decidable_eq (dimension α)]: dimension α → dimension α → option (dimension α)
-- | a b := ite (a = b) (option.some a) option.none

-- variables (α : Type u) [decidable_eq (dimension α)] (a b : dimension α) (h : ↥(dimension.add a b).is_some)
-- #check h
-- instance {α : Type*} [decidable_eq (dimension α)] (h : ↥(dimension.add a b).is_some) : has_add (dimension α) := ⟨λ (a b : (dimension α)), (option.get h)⟩

open dimension 

