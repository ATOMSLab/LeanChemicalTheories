import data.real.basic
import analysis.calculus.deriv
import analysis.calculus.mean_value

theorem anti_deriv_nat_pow 
(f f' : ℝ → ℝ) {x y :ℝ}
(hf : ∀ x, has_deriv_at f (f' x) x)
(hf' : ∀ n:ℕ, f' = λ x, x^n)
:
∃(C:ℝ),∀(n:ℕ), f = λ x, (x^(n+1))/↑(n+1) + C
:=
  begin
  have h1: ∀ (n:ℕ) (x y : ℝ), f x - (x^(n+1))/↑(n+1) = f y - (y^(n+1))/↑(n+1),
  { 
    intro n,
    rw ← nat.succ_eq_add_one,
    apply is_const_of_deriv_eq_zero,
    {
      rw differentiable,
      intro x,
      specialize hf x,
      apply has_deriv_at.differentiable_at,
      apply has_deriv_at.sub,
      {
        convert hf,
      },
      apply has_deriv_at.div_const,
      apply has_deriv_at_pow,
    },
    intro x,
    rw deriv_sub,
    rw sub_eq_zero,
    simp,
    rw has_deriv_at.deriv,
    rw hf' at hf,
    specialize hf x,
    rw ← nat.cast_add_one,
    rw mul_div_assoc,
    rw mul_div_left_comm,
    rw div_self,
    rw mul_one,
    exact hf,
    rw nat.cast_ne_zero,
    finish,
    apply has_deriv_at.differentiable_at,
    apply hf,
    apply differentiable_at.div_const,
    apply differentiable_at_pow,
  },
  use f 0,
  intro n,
  ext z,
  specialize h1 n z 0,
  apply eq_add_of_sub_eq',
  simpa using h1,
end
