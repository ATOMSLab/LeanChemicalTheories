import math.antideriv

example
{A B C D : ℝ}
(h1 : A + B = C + D)
(h2 : 0 < A)
:
B < C + D
:=
begin
nlinarith,
end

example
{A B C D : ℝ}
(h1 : A + B = C + D)
(h2 : 0 ≤ A)
:
B ≤ C + D
:=
begin
nlinarith,
end

example
{C D : ℝ}
(A B : ℝ → ℝ )
(h1 : A + B = λ x, C + D)
:
∀ x, deriv (A + B) x = 0
:=
begin
intro,
rw [h1, deriv_const],
end

example
(A B : ℝ → ℝ)
(h1 : ∀ x, has_deriv_at (A + B) 0 x)
:
∀ x, A x + B x = A 0 + B 0
:=
begin
have h2 : ∀ x y, A x + B x = A y + B y,
apply is_const_of_deriv_eq_zero,
rw differentiable,
intro,
apply has_deriv_at.differentiable_at,
apply h1,
intro,
rw has_deriv_at.deriv,
apply h1,
intro x,
specialize h2 x,
specialize h2 0,
exact h2,
end

