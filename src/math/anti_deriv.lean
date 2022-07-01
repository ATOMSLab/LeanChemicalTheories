import data.real.basic
import analysis.calculus.deriv
import analysis.calculus.mean_value

lemma fun_split
(f g : ℝ → ℝ)
:
(λ x, (f x) + (g x)) = ((λ x, f x) + (λ x, g x))
:=
begin
ring_nf,
end

theorem antideriv_const 
(f : ℝ → ℝ) (k : ℝ)
(hf : ∀ x, has_deriv_at f k x):
(f = λ x, (k*x) + (f 0) ) :=
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
    specialize hf x,
    apply hf,
    apply has_deriv_at.differentiable_at,
    specialize hf x,
    apply hf,
    simp,
  },
  ext z,
  specialize h1 z 0,
  apply eq_add_of_sub_eq',
  simp at h1,
  rw mul_comm at h1,
  exact h1,
end


theorem antideriv_pow 
(f : ℝ → ℝ)
(hf : ∀ x, ∀ (n : ℕ), has_deriv_at f (x^n) x) :
∀(n:ℕ), (f = λ x, (x^(n+1))/↑(n+1) + (f 0)) :=
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
        specialize hf n,
        exact hf,
      },
      apply has_deriv_at.div_const,
      apply has_deriv_at_pow,
    },
    intro x,
    rw deriv_sub,
    rw sub_eq_zero,
    simp,
    rw has_deriv_at.deriv,
    specialize hf x,
    specialize hf n,
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
    exact n,
    apply differentiable_at.div_const,
    apply differentiable_at_pow,
  },
  intro n,
  ext z,
  specialize h1 n z 0,
  apply eq_add_of_sub_eq',
  simpa using h1,
end

theorem antideriv_zpow
(f : ℝ → ℝ)
(hf : ∀ x, x ≠ 0 ∧ ∀ z:ℤ,has_deriv_at f (x^z) x) :
∀(z:ℤ), (↑z + (1:ℝ) ≠ 0  → f = λ x, (x^(z+1))/↑(z+1) + (f 0)) :=
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
        specialize hf z,
        exact hf,
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
    rw mul_div_assoc,
    rw mul_div_comm,
    rw div_self,
    rw mul_one,
    exact hf z,
    exact h,
    apply has_deriv_at.differentiable_at,
    exact hf z,
    apply differentiable_at.div_const,
    rw differentiable_at_zpow,
    left,
    exact hx,
  },
  intro z,
  intro h,
  ext v,
  specialize h1 z h v 0,
  apply eq_add_of_sub_eq',
  rw zero_zpow at h1,
  simpa using h1,
  norm_cast at *, 
end

lemma antideriv_first_order_poly
{k j: ℝ}
(f : ℝ → ℝ)
(hf : ∀ x, has_deriv_at f (j*x + k) x) :
(f = λ x, j*(x^2)/2 + k*x + (f 0)) :=
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
    specialize hf x,
    ring_nf,
    rw mul_comm,
    exact hf,
    apply has_deriv_at.differentiable_at,
    apply hf,
    finish,
  },
  ext z,
  specialize h1 z 0,
  apply eq_add_of_sub_eq',
  simpa using h1,
end

open set
theorem antideriv_within_at_const
(f : ℝ → ℝ) (k x : ℝ) (s : set ℝ) 
(hf : ∀ (x:ℝ), has_deriv_within_at f k s x)  :
f x =  (k*(x-a)) + (f a) :=
begin

end
