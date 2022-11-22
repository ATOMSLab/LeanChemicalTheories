import data.list.basic
import algebra.group.to_additive
import algebra.group.pi
import data.rat.basic
import data.fin.vec_notation
import data.matrix.rank

-- class si_dimension_system (α : Type*) :=
-- [dec : decidable_eq α]
-- (time [] : α) -- etc
-- (length : α) -- etc
-- (mass [] : α) -- etc
-- (h : [time, length, mass].nodup)

-- attribute [instance] si_dimension_system.dec

-- @[derive comm_group]
-- def dimension (α : Type*) := multiplicative (α → ℚ)

-- def dimension.length (α) [si_dimension_system α] : dimension α :=
-- pi.single (si_dimension_system.length) 1
-- def dimension.time (α) [si_dimension_system α] : dimension α :=
-- pi.single (si_dimension_system.time α) 1
-- def dimension.mass (α) [si_dimension_system α] : dimension α :=
-- pi.single (si_dimension_system.mass α) 1

-- open dimension

-- variables (α : Type*) [si_dimension_system α]

-- example : length α / length α = 1 := div_self' _


-- inductive your_system
-- | T | L | M

-- instance : si_dimension_system your_system := sorry

-- inductive my_system
-- | T | L | M | ZULIP_MESSAGE_COUNT

-- instance : si_dimension_system my_system := sorry


--new

class has_time (α : Type*) :=
[dec : decidable_eq α]
(time : α)

class has_length (α : Type*) :=
[dec : decidable_eq α]
(length : α)


attribute [instance] has_time.dec
attribute [instance] has_length.dec

inductive system1
| time | length
#print system1
instance : decidable_eq system1 := sorry

instance : has_time system1 := {dec := system1.decidable_eq, time := system1.time}
instance : has_length system1 := {dec := system1.decidable_eq, length := system1.length}

@[derive comm_group]
def dimension (α : Type*) := multiplicative (α → ℚ)

def dimension.length (α) [has_length α] : dimension α :=
pi.single (has_length.length) 1
def dimension.time (α) [has_time α] : dimension α :=
pi.single (has_time.time) 1

def dimension.add {α : Type*} [decidable_eq (dimension α)]: dimension α → dimension α → option (dimension α)
| a b := ite (a = b) (option.some a) option.none
variables (α : Type*) [decidable_eq (dimension α)] (a b : dimension α)
#check a.add b
#check Π a b : (dimension α), option.get 
instance (α : Type*) [decidable_eq (dimension α)]: has_add (dimension α) := {add := (Π (a b : (dimension α)), ((@option.get _ (a.add b)) (a.add b).is_some))}
open dimension 

