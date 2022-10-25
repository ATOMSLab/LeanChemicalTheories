import data.real.basic
import data.fin.vec_notation


class dimension :=
mk ::
(exponent : Π n : ℕ, fin n → rat)

def dimensionsless := dimension.mk (λ (n : ℕ) (x : fin n), (0 : ℚ))

namespace dimension

instance : linear_order (Π n : ℕ, fin n → rat) :=
begin  
  refine_struct { le := 

  },
end
def exponent_eq_decidable (a b : dimension) : decidable (a.exponent = b.exponent) :=
begin
  apply eq.decidable,
end


protected def add : dimension → dimension → dimension
| a b := ite (a.exponent = b.exponent) a 

protected def mul : dimension → dimension → dimension
| a b := dimension.mk (a.exponent + b.exponent)

protected def div : dimension → dimension → dimension
| a b := dimension.mk (a.exponent - b.exponent)

protected def npow : ℕ → dimension → dimension
| a b := dimension.mk (a•b.exponent)

protected def zpow : ℤ → dimension → dimension
| a b := dimension.mk (a•b.exponent)

protected def qpow : ℚ → dimension → dimension
| a b := dimension.mk (a•b.exponent)

#print axioms dimension.zpow
end dimension

