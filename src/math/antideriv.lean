import analysis.special_functions.exp_deriv
import analysis.calculus.deriv
import analysis.calculus.mean_value

universe u_1

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
    rw mul_div_left_comm,
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
    rw mul_div_left_comm,
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

theorem antideriv_first_order_poly
{k j: ℝ}
(f : ℝ → ℝ)
(hf : ∀ x, has_deriv_at f (j*x + k) x) :
(f = λ x, j*(x^2)/2 + k*x + (f 0)) :=
begin
  conv{
  find (k*_) {rw ← pow_one x,}
  },
  rw fun_split,
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


theorem constant_of_has_deriv_right_zero' {E : Type u_1} [normed_add_comm_group E] [normed_space ℝ E]
  {f : ℝ → E} {a b : ℝ} (hderiv : ∀ (x : ℝ), x ∈ set.Icc a b → has_deriv_at f 0 x) (h : a ≤ b) :
  f b = f a :=
begin
  apply constant_of_has_deriv_right_zero,
  apply has_deriv_at.continuous_on hderiv,
  intros,
  apply has_deriv_at.has_deriv_within_at,
  apply hderiv x (set.mem_Icc_of_Ico H), 
  finish,
end


section vector_function
universes u_2 u_3
variables {E : Type u_2}  {𝕜 : Type u_3} [is_R_or_C 𝕜] [normed_add_comm_group E] 
[normed_space 𝕜 E]

theorem antideriv 
{f F G: 𝕜 → E} (hf : ∀ t, has_deriv_at F (f t) t)
(hg : ∀ t, has_deriv_at G (f t) t)
(hg' : G 0 = 0)
: F = λ t, G t + F(0) :=
begin
have h1: ∀(x y : 𝕜), F x - G x = F y - G y,
   { 
    apply is_const_of_deriv_eq_zero,
    {
      rw differentiable,
      intro x,
      apply has_deriv_at.differentiable_at,
      apply has_deriv_at.sub (hf x),
      apply (hg x),},
    intro x,
    rw [deriv_sub, sub_eq_zero],
    rw has_deriv_at.deriv,
    simp,
    rw has_deriv_at.deriv,
    apply hf,
    apply hg,
    apply has_deriv_at.differentiable_at (hf x),
    apply has_deriv_at.differentiable_at (hg x),
  },
  funext z,
  specialize h1 z 0,
  rw hg' at h1,
  simp at h1,
  apply eq_add_of_sub_eq' h1,  
end
lemma has_deriv_at_linear_no_pow
:
∀ x : 𝕜, has_deriv_at (λ y : 𝕜, y) 1 x
:=
begin
  intro,
  rw [show (λ y : 𝕜, y) = (λ y : 𝕜, y^1), by finish, show 1 = ↑(1:ℕ)*x^(1-1), by finish],
  apply has_deriv_at_pow 1,
end

theorem antideriv_const'
(f : 𝕜 → E) {k : E}
(hf : ∀ x, has_deriv_at f k x):
(f = λ (x : 𝕜), x•k + f 0) :=
begin
  apply antideriv hf,
  simp,
  intro,
  rw show k = (1:𝕜)•k, by simp,
  conv{
    find (_•(1:𝕜)•k) {simp,},
  },
  rw show (λ t, t•k) = λ t, ((λ t : 𝕜, t) t) • k, by {funext, simp},
  apply has_deriv_at.smul_const (has_deriv_at_linear_no_pow t) k,
  simp,
end

theorem antideriv_first_order_poly'
{k j: E}
(f : 𝕜 → E)
(hf : ∀ x:𝕜, has_deriv_at f (x•j+k) x) :
(f = λ x,(x^2/2)•j + x•k + (f 0)) :=
begin
  conv{
  find (_•k) {rw ← pow_one x,}
  },
  have h1: ∀ (x y : 𝕜), f x - ((x^2/2)•j + x^1•k)= f y - ((y^2/2)•j + y^1•k),
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
      apply has_deriv_at.smul_const,
      apply has_deriv_at.div_const,
      apply has_deriv_at_pow,
      apply has_deriv_at.smul_const,
      apply has_deriv_at_pow,
    },
    intro x,
    rw deriv_sub,
    rw sub_eq_zero,
    simp,
    iterate 2 {rw deriv_smul_const},
    simp,
    ring_nf,
    rw has_deriv_at.deriv,
    exact hf x,
    iterate 2 {finish},
    apply has_deriv_at.differentiable_at,
    exact hf x,
    finish,
  },
  ext z,
  specialize h1 z 0,
  apply eq_add_of_sub_eq',
  simpa using h1,

end
end vector_function

/-! ### Analytical ODE solutions-/
open set

lemma image_norm_le_of_norm_deriv_left_le_deriv_boundary' 
{E : Type u_1} [normed_add_comm_group E] [normed_space ℝ E]
{f : ℝ → E} {a b : ℝ} {f' : ℝ → E}
(hf : continuous_on f (Icc a b))
(hf' : ∀ x ∈ Ioc a b, has_deriv_within_at f (f' x) (Iic x) x)
{B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a) (hB : continuous_on B (Icc a b))
(hB' : ∀ x ∈ Ioc a b, has_deriv_within_at B (B' x) (Iic x) x)
(bound : ∀ x ∈ Ioc a b, ∥f' x∥ ≤ B' x) :
∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
image_le_of_liminf_slope_right_le_deriv_boundary (continuous_norm.comp_continuous_on hf) ha hB hB' $
  (λ x hx r hr, (hf' x hx).liminf_right_slope_norm_le (lt_of_le_of_lt (bound x hx) hr))

theorem image_norm_le_of_norm_deriv_left_le_deriv_boundary 
{E : Type u_1} [normed_add_comm_group E] [normed_space ℝ E]
{f : ℝ → E} {a b : ℝ}{f' : ℝ → E}
(hf : continuous_on f (Icc a b))
(hf' : ∀ x ∈ Ioc a b, has_deriv_within_at f (f' x) (Iic x) x)
{B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a) (hB : ∀ x, has_deriv_at B (B' x) x)
(bound : ∀ x ∈ Ioc a b, ∥f' x∥ ≤ B' x) :
∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
image_norm_le_of_norm_deriv_right_le_deriv_boundary' hf hf' ha
  (λ x hx, (hB x).continuous_at.continuous_within_at)
  (λ x hx, (hB x).has_deriv_within_at) bound

theorem norm_image_sub_le_of_norm_deriv_left_le_segment 
{E : Type u_1} [normed_add_comm_group E] [normed_space ℝ E]
{f : ℝ → E} {a b : ℝ} {f' : ℝ → E} {C : ℝ}
(hf : continuous_on f (set.Icc a b))
(hf' : ∀ x ∈ set.Ioc a b, has_deriv_within_at f (f' x) (set.Iic x) x)
(bound : ∀x ∈ set.Ioc a b, ∥f' x∥ ≤ C) :
∀ x ∈ set.Icc a b, ∥f b - f x∥ ≤ C * (b - x) :=
begin
  let g := λ x, f x - f a,
  have hg : continuous_on g (set.Icc a b), from hf.sub continuous_on_const,
  have hg' : ∀ x ∈ set.Ioc a b, has_deriv_within_at g (f' x) (set.Iic x) x,
  { assume x hx,
    simpa using (hf' x hx).sub (has_deriv_within_at_const _ _ _) },
  let B := λ x, C * (x - a),
  have hB : ∀ x, has_deriv_at B C x,
  { assume x,
    simpa using (has_deriv_at_const x C).mul ((has_deriv_at_id x).sub (has_deriv_at_const x a)) },
  convert image_norm_le_of_norm_deriv_right_le_deriv_boundary hg hg' _ hB bound,
  simp only [g, B], rw [sub_self, norm_zero, sub_self, mul_zero]
end
theorem constant_of_has_deriv_left_zero
{E : Type u_1} [normed_add_comm_group E] [normed_space ℝ E] 
{f : ℝ → E} {a b : ℝ} (hcont : continuous_on f (set.Icc a b))
(hderiv : ∀ x ∈ set.Ioc a b, has_deriv_within_at f 0 (set.Iic x) x) :
∀ x ∈ set.Icc a b, f x = f b :=
by simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using
  λ x hx, norm_image_sub_le_of_norm_deriv_left_le_segment
    hcont hderiv (λ y hy, by rw norm_le_zero_iff) x hx
theorem antideriv_self
{k: ℝ}
(f : ℝ → ℝ)
(hf : ∀ x, has_deriv_at f (k*(f x)) x) :
(f = λ x, (f 0)*real.exp(k*x)) :=
begin
  have : ∀ x, has_deriv_at (λ x, real.exp (- k * x) * f x) 0 x,
  { intros x,
    convert (has_deriv_at_mul_const k).neg.exp.mul (hf x),
    { ext x,
      ring_nf },
    { ring_nf } },
  ext x,
  have hx : x ≤ 0 ∨ 0 ≤ x := by exact le_total x 0,
  cases hx with hx hx',
  swap,
  have : real.exp (-k * x) * f x = f 0,
  { convert @constant_of_has_deriv_right_zero _ _ _ _ 0 x _ (λ y hy, (this y).has_deriv_within_at) x _,
    { simp },
    { intros x hx,
      exact (this x).continuous_at.continuous_within_at },
    { rw set.right_mem_Icc,
      exact hx' } },
  convert congr_arg ((*) (real.exp (k * x))) this using 1,
  { rw [← mul_assoc, ← real.exp_add],
    ring_nf,
    simp, },
  { ring, },
  have : real.exp (-k * x) * f x = f 0,
  { convert @constant_of_has_deriv_right_zero' _ _ _ _ x 0 _ (λ y hy, (this y).has_deriv_within_at) x _,
    { simp },
    { intros x hx,
      exact (this x).continuous_at.continuous_within_at },
    { rw set.right_mem_Icc,
      exact hx' } },

end
