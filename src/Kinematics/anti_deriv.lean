import data.real.basic
import analysis.calculus.deriv
import analysis.calculus.mean_value

theorem anti_deriv_const 
(f f' : ℝ → ℝ) (k : ℝ)
(hf : ∀ x, has_deriv_at f (f' x) x)
(hf' :  f' = λ x, k)
:
∃(C:ℝ), (f = λ x, (k*x) + C )∧ (C = f 0)
:=
begin
   have h1: ∀(x y : ℝ), f x - (x*k) = f y - (y*k),
   { 
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
      apply has_deriv_at_mul_const,
    },
    intro x,
    rw deriv_sub,
    rw sub_eq_zero,
    simp,
    rw has_deriv_at.deriv,
    rw hf' at hf,
    specialize hf x,
    simp at hf,
    apply hf,
    apply has_deriv_at.differentiable_at,
    specialize hf x,
    apply hf,
    simp,
  },
  use f 0,
  split,
  ext z,
  specialize h1 z 0,
  apply eq_add_of_sub_eq',
  simp at h1,
  rw mul_comm at h1,
  exact h1,
  refl,
end

theorem anti_deriv_nat_pow 
(f f' : ℝ → ℝ)
(hf : ∀ x, has_deriv_at f (f' x) x)
(hf' : ∀ n:ℕ, f' = λ x, x^n)
:
∀(n:ℕ),∃(C:ℝ), (f = λ x, (x^(n+1))/↑(n+1) + C) ∧ (C = f 0)
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
    rw mul_div_comm,
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
  intro n,
  use f 0,
  split,
  ext z,
  specialize h1 n z 0,
  apply eq_add_of_sub_eq',
  simpa using h1,
  refl,
end

theorem anti_deriv_zpow
(f f' : ℝ → ℝ)
(hf : ∀ x, x ≠ 0 ∧ has_deriv_at f (f' x) x)
(hf' : ∀ z:ℤ, f' = λ x, x^z)
:
∃(C:ℝ),∀(z:ℤ), (↑z + (1:ℝ) ≠ 0  → f = λ x, (x^(z+1))/↑(z+1) + C) ∧ (C = f 0)
:=
begin
  have h1: ∀ (z:ℤ), ↑z + (1:ℝ) ≠ 0  → ∀ (x y : ℝ), f x - (x^(z+1))/↑(z+1) = f y - (y^(z+1))/↑(z+1),
  { 
    intro z,
    intro h,
    apply is_const_of_deriv_eq_zero,
    {
      rw differentiable,
      intro x,
      specialize hf x,
      cases hf with hx hf,
      apply has_deriv_at.differentiable_at,
      apply has_deriv_at.sub,
      {
        convert hf,
      },
      apply has_deriv_at.div_const,
      apply has_deriv_at_zpow,
      left,
      exact hx,
    },
    intro x,
    specialize hf x,
    cases hf with hx hf,
    rw deriv_sub,
    rw sub_eq_zero,
    simp,
    rw has_deriv_at.deriv,
    rw hf' at hf,
    rw mul_div_assoc,
    rw mul_div_comm,
    rw div_self,
    rw mul_one,
    exact hf,
    exact h,
    apply has_deriv_at.differentiable_at,
    apply hf,
    apply differentiable_at.div_const,
    rw differentiable_at_zpow,
    left,
    exact hx,
  },
  use f 0,
  intro z,
  split,
  intro h,
  ext v,
  specialize h1 z h v 0,
  apply eq_add_of_sub_eq',
  rw zero_zpow at h1,
  simpa using h1,
  norm_cast at *, 
  refl,
end

lemma anti_deriv_first_order_poly
{k j: ℝ}
(f f' : ℝ → ℝ)
(hf : ∀ x, has_deriv_at f (f' x) x)
(hf' :f' = λ x, j*x + k)
:
∃(C:ℝ), (f = λ x, j*(x^2)/2 + k*x + C)∧ (C = f 0)
:=
begin
  conv{
  find (k*_) {rw ← pow_one x,}
  },
  have h1: ∀ (x y : ℝ), f x - (j*(x^2)/2 + k*x^1)= f y - (j*(y^2)/2 + k*y^1),
  { 
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
      apply has_deriv_at.add,
      apply has_deriv_at.div_const,
      apply has_deriv_at.const_mul,
      apply has_deriv_at_pow,
      apply has_deriv_at.const_mul,
      apply has_deriv_at_pow,
    },
    intro x,
    rw deriv_sub,
    rw sub_eq_zero,
    simp,
    rw has_deriv_at.deriv,
    rw hf' at hf,
    specialize hf x,
    ring_nf,
    rw mul_comm,
    exact hf,
    apply has_deriv_at.differentiable_at,
    apply hf,
    finish,
  },
  use f 0,
  split,
  ext z,
  specialize h1 z 0,
  apply eq_add_of_sub_eq',
  simpa using h1,
  refl,
end
