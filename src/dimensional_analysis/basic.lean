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
instance {α} : has_one (dimension α) := ⟨dimension.dimensionless α⟩
instance {α} : nonempty (dimension α) := has_one.nonempty

protected noncomputable def add {α} [decidable_eq (dimension α)]: dimension α → dimension α → dimension α := 
classical.epsilon $ λ f, ∀ a b, a = b → f a b = a
protected noncomputable def sub {α} [decidable_eq (dimension α)]: dimension α → dimension α → dimension α := 
classical.epsilon $ λ f, ∀ a b, a = b → f a b = a
protected def mul {α} : dimension α → dimension α → dimension α 
| a b := λ (i : α), a i + b i
protected def div {α} : dimension α → dimension α → dimension α 
| a b := λ (i : α), a i - b i 

protected def qpow {α} : dimension α → ℚ → dimension α 
| a n := λ (i : α), n • (a i)
protected def npow {α} : dimension α → ℕ → dimension α 
| a n := a.qpow ↑n
protected def zpow {α} : dimension α → ℤ → dimension α 
| a n := a.qpow ↑n
protected def inv {α} : dimension α → dimension α 
| a := a.zpow (-1)

noncomputable instance {α} [decidable_eq (dimension α)] : has_add (dimension α) := ⟨dimension.add⟩ 
noncomputable instance {α} [decidable_eq (dimension α)] : has_sub (dimension α) := ⟨dimension.sub⟩ 
instance {α} : has_mul (dimension α) := ⟨dimension.mul⟩ 
instance {α} : has_div (dimension α) := ⟨dimension.div⟩
instance {α} : has_pow (dimension α) ℕ := ⟨dimension.npow⟩
instance {α} : has_pow (dimension α) ℤ := ⟨dimension.zpow⟩
instance {α} : has_pow (dimension α) ℚ := ⟨dimension.qpow⟩ 
instance {α} : has_inv (dimension α) := ⟨dimension.inv⟩


--I would love to add unicode to make specific globabl notation for dimension derivatives and integrals, 
--but thats more fluff than important

protected def derivative {α} : ℕ → dimension α → dimension α → dimension α
| n a b := a / (b ^ n)
protected def integral {α} : dimension α → dimension α → dimension α
| a b := a * b

@[simp] lemma add_def {α} (a b : dimension α) [decidable_eq (dimension α)] : a.add b = a + b := by refl
@[simp] lemma add_def' {α} (a : dimension α) [decidable_eq (dimension α)] : a.add a = a :=
begin
  generalize hb : a = b, symmetry' at hb,
  nth_rewrite 1 hb, revert b a hb, unfold dimension.add,
  apply classical.epsilon_spec (⟨λ a _, a, λ _ _ _, rfl⟩ :
    ∃ (f : dimension α → dimension α → dimension α), ∀ a b, a = b → f a b = a),
end
@[simp] lemma add_def'' {α} (a : dimension α) [decidable_eq (dimension α)] : a + a = a := by {rw [← add_def, add_def'],}
@[simp] lemma sub_def {α} (a b : dimension α) [decidable_eq (dimension α)] : a.sub b = a - b := by refl
@[simp] lemma sub_def' {α} (a : dimension α) [decidable_eq (dimension α)] : a.sub a = a :=
begin
  generalize hb : a = b, symmetry' at hb,
  nth_rewrite 1 hb, revert b a hb, unfold dimension.sub,
  apply classical.epsilon_spec (⟨λ a _, a, λ _ _ _, rfl⟩ :
    ∃ (f : dimension α → dimension α → dimension α), ∀ a b, a = b → f a b = a),
end
@[simp] lemma sub_def'' {α} (a : dimension α) [decidable_eq (dimension α)] : a - a = a := by {rw [← sub_def, sub_def'],}
@[simp] lemma mul_def {α} (a b : dimension α) : a.mul b = a * b := by refl
@[simp] lemma mul_def' {α} (a b : dimension α) : a * b = λ (i : α), a i + b i := by refl
@[simp] lemma div_def {α} (a b : dimension α) : a.div b = a / b := by refl
@[simp] lemma div_def' {α} (a b : dimension α) : a / b = λ (i : α), a i - b i := by refl
@[simp] lemma qpow_def {α} (a : dimension α) (b : ℚ) : a.qpow b = a^b := by refl
@[simp] lemma qpow_def' {α} (a : dimension α) (b : ℚ) : a ^ b = λ (i : α), b • (a i):= by refl
@[simp] lemma pow_def {α} (a : dimension α) (b : ℕ) : a.npow b = a^b := by refl
@[simp] lemma pow_def' {α} (a : dimension α) (b : ℕ) : a ^ b = λ (i : α), b • (a i) := by {simp, refl}
@[simp] lemma zpow_def {α} (a : dimension α) (b : ℤ) : a.zpow b = a^b := by refl
@[simp] lemma zpow_def' {α} (a : dimension α) (b : ℤ) : a ^ b = λ (i : α), b • (a i) := by {simp, refl}
@[simp] lemma inv_def {α} (a : dimension α) : a.inv = a⁻¹ := by refl
@[simp] lemma inv_def' {α} (a : dimension α) : a⁻¹ = λ (i : α), (-1 : ℤ) • (a i) := by {rw [← inv_def, dimension.inv, dimension.zpow, dimension.qpow], simp}

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
noncomputable theorem fun_equiv {α β c} (H : α ≃ β) : (α → c) → (β → c) :=
begin
  intros h h1,
  apply h (H.inv_fun h1),
end

noncomputable def dimension.to_tuple {α} [fintype α] [decidable_eq α] (a : dimension α) : fin (fintype.card α) → ℚ :=
begin
  have h := fintype.trunc_equiv_fin α,
  have h1 : α ≃ fin (fintype.card α) := trunc.out h,
  intro h2,
  apply fun_equiv h1 a h2,
end

/-! 
### Other dimensions
-/
--physics
def velocity (α) [has_length α] [has_time α] : dimension α := length α / time α

def acceleration (α) [has_length α] [has_time α] : dimension α := length α / ((time α) ^ 2)

def force (α) [has_length α] [has_time α] [has_mass α] : dimension α := length α / ((time α) ^ 2) * mass α

theorem accel_eq_vel_div_time {α} [has_length α] [has_time α] : acceleration α = velocity α / time α :=
begin
  field_simp [velocity, acceleration],
  funext,
  ring_nf,
end

theorem force_eq_mass_mul_accel {α} [has_length α] [has_time α] [has_mass α] : force α = mass α * acceleration α :=
begin
  simp [force, acceleration],
  funext,
  ring_nf,
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

lemma system1_length_to_has_length : system1.length = has_length.length system1:= by refl
lemma system1_time_to_has_time : system1.time = has_time.time system1:= by refl

--Working on cardinality to convert dimension as system1 → ℚ to fin n → ℚ for matrix
instance : fintype system1 := ⟨⟨multiset.cons system1.time (multiset.cons system1.length ∅), by simp⟩, λ x, by cases x; simp⟩ 

def system1.equiv_fin : trunc (system1 ≃ fin (fintype.card system1)) := fintype.trunc_equiv_fin system1

noncomputable theorem fun_equiv {α β c} (H : α ≃ β) : (α → c) → (β → c) :=
begin
  intros h h1,
  apply h (H.inv_fun h1),
end

noncomputable def system1.to_tuple : (system1 → ℚ) → fin (fintype.card system1) → ℚ :=
begin
  apply fun_equiv,
  have h := system1.equiv_fin,
  apply trunc.out h,
end

protected def system1.repr : system1 → string
| system1.length := "length"
| system1.time := "time"

instance : has_repr system1 := ⟨system1.repr⟩ 

open dimension
theorem system1.accel_eq_vel_div_time : acceleration system1 = velocity system1 / time system1 := accel_eq_vel_div_time


--This show that we index our tuple through the specific base dimension rather than the previous way of vector number

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


