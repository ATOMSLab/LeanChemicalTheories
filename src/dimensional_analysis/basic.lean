
import tactic
import data.real.basic

inductive dimension 
| Q : rat → rat → rat → rat → rat → rat → rat → dimension -- L → M → N → I → θ → T → J → dimension


namespace dimension

protected def add : dimension → dimension → dimension
|(Q a b c d e f g) (Q a b c d e f g) := (Q a b c d e f g)

protected def mul : dimension → dimension → dimension 
|(Q a b c d e f g) (Q h i j k l m n) := (Q (a+h) (b+i) (c+j) (d+k) (e+l) (f+m) (g+n))

protected def qpow : dimension → rat → dimension 
|(Q a b c d e f g) (q : ℚ) := (Q (a*q) (b*q) (c*q) (d*q) (e*q) (f*q) (g*q))

protected def pow : dimension → ℕ → dimension 
|(Q a b c d e f g) (q : ℕ) := (Q (a*q) (b*q) (c*q) (d*q) (e*q) (f*q) (g*q))

protected def zpow : dimension → ℤ → dimension 
|(Q a b c d e f g) (q : ℤ) := (Q (a*q) (b*q) (c*q) (d*q) (e*q) (f*q) (g*q))

protected def div : dimension → dimension → dimension 
|(Q a b c d e f g) (Q h i j k l m n) := (Q (a-h) (b-i) (c-j) (d-k) (e-l) (f-m) (g-n))

protected def inv : dimension → dimension 
|(Q a b c d e f g) := (Q (-a) (-b) (-c) (-d) (-e) (-f) (-g))

instance : has_mul dimension := ⟨dimension.mul⟩
instance : has_pow dimension ℚ := ⟨dimension.qpow⟩
instance : has_pow dimension ℕ := ⟨dimension.pow⟩
instance : has_pow dimension ℤ := ⟨dimension.zpow⟩
instance : has_div dimension := ⟨dimension.div⟩
instance : has_one dimension := ⟨Q 0 0 0 0 0 0 0⟩
instance : has_inv dimension := ⟨dimension.inv⟩

def length               : dimension := Q 1 0 0 0 0 0 0
def mass                 : dimension := Q 0 1 0 0 0 0 0 
def time                 : dimension := Q 0 0 1 0 0 0 0 
def electric_current     : dimension := Q 0 0 0 1 0 0 0
def absolute_temperature : dimension := Q 0 0 0 0 1 0 0
def amount_of_substance  : dimension := Q 0 0 0 0 0 1 0
def luminous_intensity   : dimension := Q 0 0 0 0 0 0 1
local notation `L` := length
local notation `M` := mass
local notation `N` := amount_of_substance
local notation `I` := electric_current
local notation `θ` := absolute_temperature
local notation `T` := time
local notation `J` := luminous_intensity


@[simp] lemma mul_def (a b : dimension) : a.mul b = a*b := by refl

@[simp] lemma qpow_def (a : dimension) (b : ℚ) : a.qpow b = a^b := by refl

@[simp] lemma pow_def (a : dimension) (b : ℕ) : a.pow b = a^b := by refl

@[simp] lemma zpow_def (a : dimension) (b : ℤ) : a.zpow b = a^b := by refl

@[simp] lemma div_def (a b : dimension) : a.div b = a/b := by refl

@[simp] lemma inv_def (a : dimension) : a.inv = a⁻¹ := by refl

@[simp] theorem mul_def' {a b c d e f g h i j k l m n : ℚ} : (Q a b c d e f g) * (Q h i j k l m n) 
= (Q (a+h) (b+i) (c+j) (d+k) (e+l) (f+m) (g+n)) :=
begin
  rw ← mul_def,
  simp [dimension.mul],
end

@[simp] theorem pow_def' {a b c d e f g : ℚ} {q : ℕ} : (Q a b c d e f g) ^ q 
= (Q (a*q) (b*q) (c*q) (d*q) (e*q) (f*q) (g*q)) :=
begin
  rw ← pow_def,
  simp [dimension.pow],
end

@[simp] theorem qpow_def' {a b c d e f g : ℚ} {q : ℚ} : (Q a b c d e f g) ^ q
 = (Q (a*q) (b*q) (c*q) (d*q) (e*q) (f*q) (g*q)) :=
begin
  rw ← qpow_def,
  simp [dimension.qpow],
end

@[simp] theorem zpow_def' {a b c d e f g : ℚ} {q : ℤ} : (Q a b c d e f g) ^ q 
= (Q (a*q) (b*q) (c*q) (d*q) (e*q) (f*q) (g*q)) :=
begin
  rw ← zpow_def,
  simp [dimension.zpow],
end

@[simp] theorem div_def'  {a b c d e f g h i j k l m n : ℚ} : (Q a b c d e f g) / (Q h i j k l m n) 
= (Q (a-h) (b-i) (c-j) (d-k) (e-l) (f-m) (g-n)) :=
begin
  rw ← div_def,
  simp [dimension.div],
end

@[simp] theorem inv_def'  {a b c d e f g : ℚ} : (Q a b c d e f g)⁻¹ = (Q (-a) (-b) (-c) (-d) (-e) (-f) (-g)) := 
begin
  rw ← inv_def,
  simp [dimension.inv],
end

@[simp] theorem one_def : 1 = Q 0 0 0 0 0 0 0 :=
begin
  simp [has_one.one],
end

protected theorem mul_comm (a b : dimension) : a * b = b * a :=
begin
  induction a,
  induction b,
  simp,
  iterate 6 {split, exact rat.add_comm _ _,},
  exact rat.add_comm _ _,
end

protected theorem div_mul_comm {a b c : dimension} : a/b*c = c/b*a :=
begin
  induction a,
  induction b,
  induction c,
  simp,
  iterate 6 {split, rw add_comm, rw ← add_sub_assoc, ring,},
  rw add_comm, rw ← add_sub_assoc, ring,
end

protected theorem mul_assoc (a b c : dimension) : a * b * c = a * (b * c) :=
begin
  induction a,
  induction b,
  induction c,
  simp,
  iterate 6 {split, exact add_assoc _ _ _},
  exact add_assoc _ _ _,
end

protected theorem mul_one (a : dimension) : a*1 = a :=
begin
  induction a,
  simp, 
end

protected theorem div_eq_mul_inv (a b : dimension) :a/b = a*b⁻¹ :=
begin
  induction a,
  induction b,
  simp,
  iterate 6 {split, exact sub_eq_add_neg _ _},
  exact sub_eq_add_neg _ _,
end

protected theorem mul_left_inv (a : dimension) : a⁻¹*a = 1 :=
begin
  induction a,
  simp,
end
protected theorem mul_right_inv (a : dimension) : a*a⁻¹ = 1:=
begin
  rw [dimension.mul_comm, dimension.mul_left_inv],
end
protected theorem one_mul (a : dimension) : 1*a = a := by {rw dimension.mul_comm, exact dimension.mul_one _,}

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

def volume := L^3
local notation `V` := volume

def density := M/L^3
local notation `ρ` := density

def molecular_weight := M/N
local notation `MW` := molecular_weight

def molar_volume := L^3/N
local notation `MV` := molar_volume

def specific_volume := L^3/M
local notation `SV` := specific_volume


theorem molar_volume_div_molecular_weight_eq_density : MW/MV = ρ :=
begin
  field_simp [molecular_weight, molar_volume, density],
end

theorem specific_volume_eq_inv_of_density : SV = 1/ρ :=
begin
  field_simp [specific_volume, density],
end


end dimension
