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

end dimension

