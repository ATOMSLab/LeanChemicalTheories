import data.real.basic
import data.fin.vec_notation


structure dimension :=
mk ::
(exponent : Π n : ℕ, fin n → rat)


namespace dimension

def dimensionless := dimension.mk (λ (n : ℕ) (x : fin n), (0 : ℚ))

instance : linear_order (Π n : ℕ, fin n → rat) :=
begin  
  refine_struct { le := 

  },
end
def exponent_eq_decidable (a b : dimension) : decidable (a.exponent = b.exponent) :=
begin
  apply eq.decidable,
end


protected def add : dimension → dimension → option dimension
| a b := ite (a.exponent = b.exponent) (option.some a) option.none

protected def sub : dimension → dimension → option dimension
| a b := ite (a.exponent = b.exponent) (option.some a) option.none

protected def mul : dimension → dimension → dimension
| a b := dimension.mk (a.exponent + b.exponent)

protected def div : dimension → dimension → dimension
| a b := dimension.mk (a.exponent - b.exponent)

protected def npow : dimension → ℕ → dimension
| a b := dimension.mk (b•a.exponent)

protected def zpow : dimension → ℤ → dimension
| a b := dimension.mk (b•a.exponent)

protected def qpow : dimension → ℚ → dimension
| a b := dimension.mk (b•a.exponent)

protected def inv : dimension → dimension 
| a := dimension.mk ((-(1 : ℤ))•a.exponent)
protected def deriv : dimension → dimension → dimension := dimension.div

protected def integrate : dimension → dimension → dimension := dimension.mul

protected def numbers_are_dimensionless (α : Type*) [ordered_semiring α] [nontrivial α] : α → dimension
|a := dimension.dimensionless


instance : has_mul dimension := ⟨dimension.mul⟩
instance : has_pow dimension ℚ := ⟨dimension.qpow⟩
instance : has_pow dimension ℕ := ⟨dimension.npow⟩
instance : has_pow dimension ℤ := ⟨dimension.zpow⟩
instance : has_div dimension := ⟨dimension.div⟩
instance : has_one dimension := ⟨dimension.dimensionless⟩
instance : has_inv dimension := ⟨dimension.inv⟩
instance {α} [ordered_semiring α] [nontrivial α] : has_coe α dimension := ⟨dimension.numbers_are_dimensionless α⟩

@[simp] lemma mul_def (a b : dimension) : a.mul b = a*b := by refl

@[simp] lemma qpow_def (a : dimension) (b : ℚ) : a.qpow b = a^b := by refl

@[simp] lemma pow_def (a : dimension) (b : ℕ) : a.npow b = a^b := by refl

@[simp] lemma zpow_def (a : dimension) (b : ℤ) : a.zpow b = a^b := by refl

@[simp] lemma div_def (a b : dimension) : a.div b = a/b := by refl

@[simp] lemma inv_def (a : dimension) : a.inv = a⁻¹ := by refl


@[simp] theorem mul_def' {a b : dimension} : a * b = dimension.mk (a.exponent + b.exponent) :=
begin
  rw ← mul_def,
  simp [dimension.mul],
end

@[simp] theorem pow_def' {a : dimension} {q : ℕ} : a ^ q = dimension.mk (q•a.exponent):=
begin
  rw ← pow_def,
  simp [dimension.npow],
end

@[simp] theorem qpow_def' {a : dimension} {q : ℚ} : a ^ q = dimension.mk (q•a.exponent) :=
begin
  rw ← qpow_def,
  simp [dimension.qpow],
end

@[simp] theorem zpow_def' {a : dimension} {q : ℤ} : a ^ q = dimension.mk (q•a.exponent):=
begin
  rw ← zpow_def,
  simp [dimension.zpow],
end

@[simp] theorem div_def'  {a b : dimension} : a / b = dimension.mk (a.exponent - b.exponent) :=
begin
  rw ← div_def,
  simp [dimension.div],
end

@[simp] theorem inv_def'  {a : dimension} : a⁻¹ = dimension.mk ((-(1:ℤ) )•a.exponent)  := 
begin
  rw ← inv_def,
  simp [dimension.inv],
end

@[simp] theorem one_def : 1 = dimensionless:=
begin
  simp [has_one.one],
end

protected theorem mul_comm (a b : dimension) : a * b = b * a :=
begin
  induction a,
  induction b,
  simp,
  rw add_comm,
end

protected theorem div_mul_comm (a b c : dimension) : a/b*c = c/b*a :=
begin
  induction a,
  induction b,
  induction c,
  simp,
  rw sub_add_comm,
end

protected theorem mul_assoc (a b c : dimension) : a * b * c = a * (b * c) :=
begin
  induction a,
  induction b,
  induction c,
  simp,
  rw add_assoc,
end

protected theorem mul_one (a : dimension) : a*1 = a :=
begin
  induction a,
  simp,
  finish, 
end

protected theorem div_eq_mul_inv (a b : dimension) :a/b = a*b⁻¹ :=
begin
  induction a,
  induction b,
  simp,
  rw sub_eq_add_neg,
end

protected theorem mul_left_inv (a : dimension) : a⁻¹*a = 1 :=
begin
  induction a,
  simp,
  finish,
end

protected theorem mul_right_inv (a : dimension) : a*a⁻¹ = 1:=
begin
  rw [dimension.mul_comm, dimension.mul_left_inv],
end
protected theorem one_mul (a : dimension) : 1*a = a := by {rw dimension.mul_comm, exact dimension.mul_one _,}

@[simp] protected lemma nat_numbers_are_dimensionless {n : ℕ}: ↑n = (1 : dimension) := rfl

@[simp] protected lemma int_numbers_are_dimensionless {z : ℤ}: ↑z = (1 : dimension) := rfl

@[simp] protected lemma rat_numbers_are_dimensionless {q : ℚ}: ↑q = (1 : dimension) := rfl

@[simp] protected lemma real_numbers_are_dimensionless {r : ℝ}: ↑r = (1 : dimension) := rfl


instance : comm_group dimension :=
begin
  refine_struct { mul := dimension.mul,
                  div := dimension.div,
                  inv := dimension.inv,
                  mul_assoc := dimension.mul_assoc,
                  one := (1:dimension),
                  npow := @npow_rec dimension dimension.has_one dimension.has_mul,
                  zpow := @zpow_rec dimension dimension.has_one dimension.has_mul dimension.has_inv,
                  one_mul := dimension.one_mul,
                  mul_one := dimension.mul_one,
                  mul_comm := dimension.mul_comm,
                  div_eq_mul_inv := dimension.div_eq_mul_inv,
                  mul_left_inv := dimension.mul_left_inv,}, 
  repeat {rintro ⟨_⟩, },
  try { refl },
  iterate 2 {rw npow_rec,},
  try { refl },
  iterate 2 {rw [zpow_rec, zpow_rec, npow_rec, npow_rec],},
  rw [zpow_rec, inv_def, show ↑(1:ℕ) = int.of_nat 1, by finish, zpow_rec],
  rw [zpow_rec, inv_def, show ↑(n.succ.succ) = int.of_nat n.succ.succ, by finish, zpow_rec],
end





def length_tuple_constructor  : Π n, fin n → ℚ
| 0 := 0
| (n + 1) := pi.single 0 1
def length := dimension.mk length_tuple_constructor

def mass_tuple_constructor  : Π n, fin n → ℚ
| 0 := 0
| (n + 1) := pi.single 1 1
def mass := dimension.mk length_tuple_constructor

def area := length^2

theorem length_pow_three_div_length_eq_area
:length^3/length = area :=
begin
  field_simp [length, area],
  funext n i,
  induction n with d,
  simp [length_tuple_constructor],
  field_simp [length_tuple_constructor],
  rw [← one_mul (pi.single 0 1 i), ← mul_assoc, ← mul_assoc, ← sub_mul],
  norm_num,
end


end dimension

