import math.antideriv
import analysis.normed_space.basic



variables
{α : ℝ} --α is a real number, for us it will take on the value of the constant acceleration
(x v a : ℝ → ℝ) --Position, velocity, and acceleration are functions which take in a 
--real number (time) and outputs a real number (position, velocity, or acceleration)

theorem velocity_eq_const_accel_mul_time
(hf' : ∀(t : ℝ), has_deriv_at x (v t) t) /- We say that for all t, where t is a real number,
x, our position function, has a derivative and that derivative is the function v, which
is our velocity function. At each t, v t is the evaluation of the velocity function
at t which is the slope of the tangent line, basically saying x(t) = dv(t)/dt-/
(hf'' : ∀(t : ℝ), has_deriv_at v (a t) t)/- We say that for all t, where t is a real number,
v, our velocity function, has a derivative and that derivative is the function a, which
is our acceleration function. At each t, a t is the evaluation of the acceleration function
at t which is the slope of the tangent line, basically saying v(t) = da(t)/dt-/
(accel_const : a = λ (t : ℝ), α) /-we say that a, which is our acceleration function, is equal
to the lamda function which takes in a t and outputs α. This function is a constant function,
because no matter what value of t is put in, it always outputs the same value, α. da/dt = 0,
a(t) = α-/
:
v =  λ t, α*t + v 0 /- we say that our velocity function is a linear function with slope
α and intercept v₀, which is our initial velocity. We say there exists a v₀, which is our
integration constant.-/
:=
begin
  apply antideriv_const,
  rw accel_const at hf'',
  exact hf'',
end

lemma pos_eq_const_accel_mul_time_sqr_add_velocity_mul_time
(hf' : ∀(t : ℝ), has_deriv_at x (v t) t)
(hf'' : ∀(t : ℝ), has_deriv_at v (a t) t)
(accel_const : a = λ (t : ℝ), α)
:
x = (λ t:ℝ, (α*t^2)/2 + (v 0)*t + (x 0)) 
:=
begin
conv{
  find ((v 0)*_) {rw ← pow_one t,}
},
have h1 :v =  λ t:ℝ, α*t + v 0, 
{
  apply velocity_eq_const_accel_mul_time,
  apply hf',
  apply hf'',
  apply accel_const,
},
exact hf',
exact h1,
end

lemma pos_eq_velocity_add_initial_mul_time
(hf' : ∀(t : ℝ), has_deriv_at x (v t) t)
(hf'' : ∀(t : ℝ), has_deriv_at v (a t) t)
(accel_const : a = λ (t : ℝ), α)
:
∀ t, x t =  ((v t) + (v 0))*t/2 + (x 0)
:=
begin
have h1 : v =  λ t:ℝ, α*t + v 0, 
{
  apply velocity_eq_const_accel_mul_time,
  apply hf',
  apply hf'',
  apply accel_const,
},
intro t,
rw h1, 
simp,
ring_nf, 
have h2 :  x = λ (t : ℝ), α * t ^ 2 / 2 + (v 0) * t + x 0,
{
  apply antideriv_first_order_poly, 
  rw h1 at hf',
  exact hf', 
}, 
rw h2, 
ring_nf,
end

lemma velocity_pow_two_eq_velocity_initial_pow_two_add_accel_mul_pos 
(hf' : ∀(t : ℝ), has_deriv_at x (v t) t)
(hf'' : ∀(t : ℝ), has_deriv_at v (a t) t)
(accel_const : a = λ (t : ℝ), α)
:
∀ t,(v t)^2 = (v 0)^2 + 2*(a t)*((x t) - (x 0))
:=
begin
have h1 :v =  λ t:ℝ, α*t + v 0, 
{
  apply velocity_eq_const_accel_mul_time,
  apply hf',
  apply hf'',
  apply accel_const,
},
intro t,
rw h1,
have h2 :x = λ (t : ℝ), α * t ^ 2 / 2 + (v 0) * t + x 0 ,
{
  apply antideriv_first_order_poly,
  rw h1 at hf',
  exact hf',
},
rw h2,
rw accel_const,
ring_nf,
end

def deriv_matrix 
example
: deriv (λ t:ℝ, ![t,t^2,t] )= λ t, ![1,2*t,1]:=
begin
  simp,
end
variables {E : Type*} [normed_group E] [normed_space ℝ E]
/-Using def to define position, velocity, and acceleration-/
noncomputable theory
variables (𝕩 : ℝ → E) (h𝕩 : continuous 𝕩)
def position (f : ℝ → E) (n : with_top ℕ): Prop := cont_diff ℝ n f
def velocity  : ℝ → E := deriv 𝕩
def acceleration : ℝ → E := deriv (velocity 𝕩)


theorem acceleration_eq_deriv2_position
:acceleration 𝕩 = (deriv^[2] 𝕩):=
begin
  simp [acceleration, velocity],
end


local notation `𝕧` := velocity 𝕩
local notation `𝕒` := acceleration 𝕩
lemma two_le_imp_one_le :∀ (α : Type*), 2 ≤ α 
theorem has_deriv_at_velocity
{n : with_top ℕ} (hn : 2 ≤ n)
(hf : position 𝕩 n)
:
∀ t, has_deriv_at 𝕩 (𝕧 t) t:=
begin
  intro t,
  simp [velocity],
  apply differentiable.differentiable_at,
  simp [position] at hf,
  apply cont_diff.differentiable hf hn,
end

theorem cont_diff_velocity 

:
cont_diff:=
theorem velocity_differentiable
{n : with_top ℕ} (hn : 1 ≤ n)
(hf : position 𝕩 n)
:
differentiable ℝ (velocity 𝕩) :=
begin
  simp [position] at hf,
  simp [velocity],
  
end

theorem has_deriv_at_acceleration
{n : with_top ℕ} (hn : 1 ≤ n)
(hf : position 𝕩 n)
:
∀ t, has_deriv_at 𝕧 (𝕒 t) t:=
begin
  intro t,
  simp [acceleration],
  apply differentiable.differentiable_at,
  simp [position] at hf,
  apply cont_diff.differentiable hf hn,
end

#check antideriv_const'
variable 𝔸 : E
theorem const_accel
(accel_const : 𝕒 = λ (t : ℝ), 𝔸)
:
𝕧 =  λ t:ℝ, t•𝔸 + 𝕧 0:=
begin
  apply antideriv_const',
  rw accel_const at hf'',
  exact hf'',
end
