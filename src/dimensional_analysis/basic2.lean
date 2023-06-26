import data.real.basic

universe u

class has_time (α : Type u) :=
[dec : decidable_eq α]
(time [] : α)

class has_length (α : Type u) :=
[dec : decidable_eq α]
(length [] : α)

class has_mass (α : Type u) :=
[dec : decidable_eq α]
(mass [] : α)

class has_amount_of_substance (α : Type u) :=
[dec : decidable_eq α]
(amount_of_substance [] : α)

class has_electric_current (α : Type u) :=
[dec : decidable_eq α]
(electric_current [] : α)

class has_temperature (α : Type u) :=
[dec : decidable_eq α]
(temperature [] : α)

class has_luminous_intensity (α : Type u) :=
[dec : decidable_eq α]
(luminous_intensity [] : α)

attribute [instance] has_time.dec
attribute [instance] has_length.dec
attribute [instance] has_mass.dec
attribute [instance] has_amount_of_substance.dec
attribute [instance] has_electric_current.dec
attribute [instance] has_temperature.dec
attribute [instance] has_luminous_intensity.dec
@[reducible] def dimension (α : Type u) := α → multiplicative (ℚ)
@[reducible] def dimension.of {α : Type u} (a : α) [decidable_eq α] : dimension α := pi.single a (multiplicative.of_add 1)

def dimensionless (α) : dimension α := λ a , 0
def length (α) [has_length α] [decidable_eq α] : dimension α := dimension.of $ has_length.length α
def time (α) [has_time α] [decidable_eq α] : dimension α := dimension.of $ has_time.time α
def mass (α) [has_mass α] [decidable_eq α] : dimension α := dimension.of $ has_mass.mass α
#check time _ _
def velocity (α) [has_length α] [has_time α] : dimension α := λ a, additive.of_mul (additive.to_mul (length α a) / additive.to_mul (time α a))

example {α} [has_length α] [decidable_eq α] : (length α) (has_length.length α) = additive.of_mul 1 :=
begin
  simp [length, dimension.of, dimension],
end
example {α} [has_length α] [has_time α] [decidable_eq α] : (velocity α) (has_length.length α) = additive.of_mul 1 :=
begin
  simp [velocity, length, time, dimension.of, dimension],
end
example {α} [has_length α] [has_time α] [decidable_eq α] : (velocity α) (has_time.time α) = additive.of_mul (-1) :=
begin
  simp [velocity, length, time, dimension.of, dimension],
  
end

example {α} [has_length α] [decidable_eq α] : length α + length α = length α := 
begin
  simp,
end
@[nolint unused_arguments]
structure measurement (V) {α : Type*} (dim : α) :=of :: (value : V)
