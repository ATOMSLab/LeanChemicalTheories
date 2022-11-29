import data.list.basic
import algebra.group.to_additive
import algebra.group.pi
import data.rat.basic
import data.fin.vec_notation

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
### Def of dimensions and its properties
-/


def dimension (α : Type u) := α → ℚ

namespace dimension
protected def mul {α} : dimension α → dimension α → dimension α 
| a b := λ (i : α), a i + b i
protected def div {α} : dimension α → dimension α → dimension α 
| a b := λ (i : α), a i - b i 
protected def npow {α} : dimension α → ℕ → dimension α 
| a n := λ (i : α), n • (a i)
protected def zpow {α} : dimension α → ℤ → dimension α 
| a n := λ (i : α), n • (a i)
protected def qpow {α} : dimension α → ℚ → dimension α 
| a n := λ (i : α), n • (a i)
protected def inv {α} : dimension α → dimension α 
| a := λ (i : α), (-1 : ℤ) • (a i)

instance {α} : has_mul (dimension α) := ⟨dimension.mul⟩
instance {α} : has_div (dimension α) := ⟨dimension.div⟩
instance {α} : has_pow (dimension α) ℕ := ⟨dimension.npow⟩
instance {α} : has_pow (dimension α) ℤ := ⟨dimension.zpow⟩
instance {α} : has_pow (dimension α) ℚ := ⟨dimension.qpow⟩ 
instance {α} : has_inv (dimension α) := ⟨dimension.inv⟩


--I would love to add unicode to make specific globabl notation for dimension derivatives and integrals, 
--but thats more fluff than important

protected def derivative {α} : dimension α → dimension α → dimension α
| a b := a / b
protected def intergral {α} : dimension α → dimension α → dimension α
| a b := a * b

@[simp] lemma mul_def {α} (a b : dimension α) : a.mul b = a * b := by refl
@[simp] lemma mul_def' {α} (a b : dimension α) : a * b = λ (i : α), a i + b i := by refl
@[simp] lemma div_def {α} (a b : dimension α) : a.div b = a / b := by refl
@[simp] lemma div_def' {α} (a b : dimension α) : a / b = λ (i : α), a i - b i := by refl
@[simp] lemma qpow_def {α} (a : dimension α) (b : ℚ) : a.qpow b = a^b := by refl
@[simp] lemma qpow_def' {α} (a : dimension α) (b : ℚ) : a ^ b = λ (i : α), b • (a i):= by refl
@[simp] lemma pow_def {α} (a : dimension α) (b : ℕ) : a.npow b = a^b := by refl
@[simp] lemma pow_def' {α} (a : dimension α) (b : ℕ) : a ^ b = λ (i : α), b • (a i) := by refl
@[simp] lemma zpow_def {α} (a : dimension α) (b : ℤ) : a.zpow b = a^b := by refl
@[simp] lemma zpow_def' {α} (a : dimension α) (b : ℤ) : a ^ b = λ (i : α), b • (a i) := by refl
@[simp] lemma inv_def {α} (a : dimension α) : a.inv = a⁻¹ := by refl
@[simp] lemma inv_def' {α} (a : dimension α) : a⁻¹ = λ (i : α), (-1 : ℤ) • (a i) := by refl

protected theorem mul_comm {α} (a b : dimension α) : a * b = b * a := by {simp, funext, rw add_comm}
protected theorem div_mul_comm {α} (a b c : dimension α) : a / c * b  = b / c * a := by {simp, funext, rw sub_add_comm}
protected theorem mul_assoc {α} (a b c : dimension α) : a * b * c = a * (b * c) := by {simp, funext, rw add_assoc}




/-!
### Definition of the base dimensions
-/
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

def dimensionless (α) : dimension α := λ i, 0

instance {α} : has_one (dimension α) := ⟨dimension.dimensionless α⟩

@[simp] lemma one_eq_dimensionless {α} : 1 = dimensionless α := rfl
@[simp] lemma dimensionless_def' {α} : dimensionless α = λ i, 0 := rfl

protected theorem mul_one {α} (a : dimension α ) : a*1 = a := by simp
 
/-! 
### Other dimensions
-/
--physics
def velocity (α) [has_length α] [has_time α] : dimension α := length α / time α

def acceleration (α) [has_length α] [has_time α] : dimension α := length α / ((time α) ^ 2)

def force (α) [has_length α] [has_time α] [has_mass α] : dimension α := length α / ((time α) ^ 2) * mass α

lemma force_eq_mass_mul_accel {α} [has_length α] [has_time α] [has_mass α] : force α = mass α * acceleration α :=
begin
  rw [force, acceleration],
  finish,
end
 
/-! 
### examples for personal understanding
-/
inductive system1
| time | length

instance : decidable_eq system1 
| system1.time system1.time := is_true rfl
| system1.time system1.length := is_false (λ h, system1.no_confusion h)
| system1.length system1.time := is_false (λ h, system1.no_confusion h)
| system1.length system1.length := is_true rfl


instance : has_time system1 := {dec := system1.decidable_eq, time := system1.time}
instance : has_length system1 := {dec := system1.decidable_eq, length := system1.length}


variables (α : Type*) [has_time α] 
--This show that we index our tuple through the specific base dimension rather than the previous way of vector number
example : (dimension.time system1) system1.time = 1 :=
begin
  simp [dimension.time],
  apply pi.single_eq_same,
end

example : (dimension.time system1) system1.length = 0 :=
begin
  simp [dimension.time],
  apply pi.single_eq_of_ne,
  finish,
end

example : (dimension.length system1) * (dimension.length system1) = pi.single (has_length.length) 2 :=
begin
  simp [dimension.length],
  ext1,
  cases x,
  rw [pi.single_eq_of_ne, pi.single_eq_of_ne],
  iterate 3 {finish},
  finish,
end

example : dimension.velocity system1 system1.length = 1 :=
begin
  simp [velocity, length, time],
  
end
-- def dimension.add {α : Type u} [decidable_eq (dimension α)]: dimension α → dimension α → option (dimension α)
-- | a b := ite (a = b) (option.some a) option.none

-- variables (α : Type u) [decidable_eq (dimension α)] (a b : dimension α) (h : ↥(dimension.add a b).is_some)
-- #check h
-- instance {α : Type*} [decidable_eq (dimension α)] (h : ↥(dimension.add a b).is_some) : has_add (dimension α) := ⟨λ (a b : (dimension α)), (option.get h)⟩

open dimension 
