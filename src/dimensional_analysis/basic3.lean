import data.list.basic
import algebra.group.to_additive
import algebra.group.pi
import data.rat.basic
import data.fin.vec_notation
import data.real.basic

universe u

/-! 
### Dimension type classes
-/

class has_time (α : Type u) :=
[dec : decidable_eq α]
(time [] : α)
(h : [time].nodup)

class has_length (α : Type u) :=
[dec : decidable_eq α]
(length [] : α)
(h : [length].nodup)

class has_mass (α : Type u) :=
[dec : decidable_eq α]
(mass [] : α)
(h : [mass].nodup)

class has_amount_of_substance (α : Type u) :=
[dec : decidable_eq α]
(amount_of_substance [] : α)
(h : [amount_of_substance].nodup)

class has_electric_current (α : Type u) :=
[dec : decidable_eq α]
(electric_current [] : α)
(h : [electric_current].nodup)

class has_temperature (α : Type u) :=
[dec : decidable_eq α]
(temperature [] : α)
(h : [temperature].nodup)

class has_luminous_intensity (α : Type u) :=
[dec : decidable_eq α]
(luminous_intensity [] : α)
(h : [luminous_intensity].nodup)

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
def dimensionless (α) : dimension α := λ i, 0

protected def add {α} [decidable_eq (dimension α)]: dimension α → dimension α → dimension α
| a b := ite (a = b) a (dimensionless α)
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

instance {α} [decidable_eq (dimension α)] : has_add (dimension α) := ⟨dimension.add⟩ 
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

@[simp] lemma add_def {α} (a b : dimension α) [decidable_eq (dimension α)] : a.add b = a + b := by refl
@[simp] lemma add_def' {α} (a : dimension α) [decidable_eq (dimension α)] : a.add a = a := by {simp [dimension.add]}
@[simp] lemma add_def'' {α} (a : dimension α) [decidable_eq (dimension α)] : a + a = a := by {rw [← add_def, add_def'],}
        lemma add_def''' {α} (a b : dimension α) [decidable_eq (dimension α)] (h : a ≠ b): a + b = dimensionless α := by {rw [← add_def], simp [dimension.add, h]}
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

/-!
### Definition of the base dimensions
-/
def length (α) [has_length α] : dimension α :=
pi.single (has_length.length α) 1

def time (α) [has_time α] : dimension α :=
pi.single (has_time.time α) 1

def mass (α) [has_mass α] : dimension α :=
pi.single (has_mass.mass α) 1

def amount_of_substance (α) [has_amount_of_substance α] : dimension α :=
pi.single (has_amount_of_substance.amount_of_substance α) 1

def electric_current (α) [has_electric_current α] : dimension α :=
pi.single (has_electric_current.electric_current α) 1

def temperature (α) [has_temperature α] : dimension α :=
pi.single (has_temperature.temperature α) 1

def luminous_intensity (α) [has_luminous_intensity α] : dimension α :=
pi.single (has_luminous_intensity.luminous_intensity α) 1


instance {α} : has_one (dimension α) := ⟨dimension.dimensionless α⟩

protected def numbers_are_dimensionless (α : Type*) [ordered_semiring α] [nontrivial α] {β}: α → dimension β
|a := dimension.dimensionless β 
instance {α} [ordered_semiring α] [nontrivial α] {β}: has_coe α (dimension β):= ⟨dimension.numbers_are_dimensionless α⟩

@[simp] lemma one_eq_dimensionless {α} : 1 = dimensionless α := rfl
@[simp] lemma dimensionless_def' {α} : dimensionless α = λ i, 0 := rfl

protected theorem mul_comm {α} (a b : dimension α) : a * b = b * a := by {simp, funext, rw add_comm}
protected theorem div_mul_comm {α} (a b c : dimension α) : a / c * b  = b / c * a := by {simp, funext, rw sub_add_comm}
protected theorem mul_assoc {α} (a b c : dimension α) : a * b * c = a * (b * c) := by {simp, funext, rw add_assoc}
protected theorem mul_one {α} (a : dimension α) : a*1 = a := by simp
protected theorem one_mul {α} (a : dimension α) : 1*a = a := by simp
protected theorem div_eq_mul_inv {α} (a b : dimension α) : a / b = a * b⁻¹ := by {simp, funext, rw sub_eq_add_neg}
protected theorem mul_left_inv {α} (a : dimension α) : a⁻¹*a = 1 := by {simp}
protected theorem mul_right_inv {α} (a : dimension α) : a*a⁻¹ = 1 := by {simp}
@[simp] protected lemma nat_numbers_are_dimensionless {α} {n : ℕ}: ↑n = (1 : dimension α) := rfl
@[simp] protected lemma int_numbers_are_dimensionless {α} {z : ℤ}: ↑z = (1 : dimension α) := rfl
@[simp] protected lemma rat_numbers_are_dimensionless {α} {q : ℚ}: ↑q = (1 : dimension α) := rfl
@[simp] protected lemma real_numbers_are_dimensionless {α} {r : ℝ}: ↑r = (1 : dimension α) := rfl


instance {α} : comm_group (dimension α) :=
begin
  refine_struct { mul := dimension.mul,
                  div := dimension.div,
                  inv := dimension.inv,
                  mul_assoc := dimension.mul_assoc,
                  one := dimensionless α,
                  npow := @npow_rec (dimension α) dimension.has_one dimension.has_mul,
                  zpow := @zpow_rec (dimension α) dimension.has_one dimension.has_mul dimension.has_inv,
                  one_mul := dimension.one_mul,
                  mul_one := dimension.mul_one,
                  mul_comm := dimension.mul_comm,
                  div_eq_mul_inv := dimension.div_eq_mul_inv,
                  mul_left_inv := dimension.mul_left_inv,}, 
  repeat {rintro ⟨_⟩, },
  iterate 8 {intro, refl,},
end


/-! 
### Other dimensions
-/
--physics
def velocity (α) [has_length α] [has_time α] : dimension α := length α / time α

def acceleration (α) [has_length α] [has_time α] : dimension α := length α / ((time α) ^ 2)

def force (α) [has_length α] [has_time α] [has_mass α] : dimension α := length α / ((time α) ^ 2) * mass α

lemma force_eq_mass_mul_accel {α} [has_length α] [has_time α] [has_mass α] : force α = mass α * acceleration α :=
begin
  simp [force, acceleration],
  funext,
  finish,
end

end dimension
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

lemma system1.time_nodup : [system1.time].nodup := by finish
lemma system1.length_nodup : [system1.length].nodup := by finish
 
instance : has_time system1 := {dec := system1.decidable_eq, time := system1.time, h := system1.time_nodup}
instance : has_length system1 := {dec := system1.decidable_eq, length := system1.length, h := system1.length_nodup}
instance : fintype system1 := ⟨⟨multiset.cons system1.time (multiset.cons system1.length ∅), by simp⟩, λ x, by cases x; simp⟩ 

@[simp] lemma system1_length_to_has_length : system1.length = has_length.length system1:= by refl
@[simp] lemma system1_time_to_has_time : system1.time = has_time.time system1:= by refl
#check has_repr
#eval fintype.trunc_equiv_fin system1
--This show that we index our tuple through the specific base dimension rather than the previous way of vector number
example : (dimension.time system1) system1.time = 1 :=
begin
  simp [dimension.time],
end

example : (dimension.time system1) system1.length = 0 :=
begin
  simp [dimension.time],
  apply pi.single_eq_of_ne,
  finish,
end

example : (dimension.length system1) * (dimension.length system1) = pi.single (has_length.length system1) 2 :=
begin
  simp [dimension.length],
  ext1,
  cases x,
  rw [pi.single_eq_of_ne, pi.single_eq_of_ne],
  iterate 4 {finish},
end

example : ((dimension.length system1) * (dimension.length system1)) system1.length = 2 :=
begin
  simp [dimension.length],
  finish,
end


