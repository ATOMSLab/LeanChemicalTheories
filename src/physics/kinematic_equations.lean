import math.antideriv
import analysis.inner_product_space.basic
import analysis.calculus.iterated_deriv

/-!
# The equations of motion
We define motion to be over an inner product space, which is a vector space endowed with an operator caleld the inner product. 
We generalize motion to be over a field that is either real or complex, and show that three of the four kinematic equations for 
constant acceleration hold in complex time. The fourth kinematic equation, as of now, can only be derived in real time. 

We also define an extension of the motion class to require that our functions be continously differentiable n times. In the
future, we plan to define another class extension which only requires the equations of motion to be differentiable on a set. These
classes are defined seperatley from the motion class to give flexibility to motion's applicability. We also don't require the equations
to be infinitley differentiable, but this can be achieved by using ⊤ for n.

Finally, at the end we derive the four equations of motion for the case of linear translation along a line. Currently, these derivations
are independent of the motion class, but in the future, they will be unified with motion and shown to be examples of their vector
coutner-part.

## To-Do
 - Show that the fourth kinematic equations hold in complex time with the nescessary assumptions
 - Show that the linear translation equations follow from the vector form-/

noncomputable theory

class motion (𝕜 : Type*) (E : Type*) [is_R_or_C 𝕜]
  extends inner_product_space 𝕜 E:=
{position velocity acceleration : 𝕜 → E}
(hvel : velocity = deriv position)
(hacc : acceleration = deriv velocity)

export motion (position velocity acceleration)

/-Given the definition of motion and the relation between position, velocity, and acceleration, we extend the motion class
to require that our functions be continously differentiable n times (Cⁿ).-/
class motion_cont_diff_everywhere (𝕜 : Type*) (E : Type*) [is_R_or_C 𝕜]
  extends motion 𝕜 E:=
(contdiff : ∀ n : with_top ℕ, ∀ m : ℕ, (↑m < n) ∧ (cont_diff 𝕜 n (deriv^[m] to_motion.position)))

/-When defining the four kinematic equations, we require the field to be real or complex-/
variables {𝕜 : Type*} {E : Type*} [is_R_or_C 𝕜] [M : motion_cont_diff_everywhere 𝕜 E]

local notation `𝕩` := @motion.position 𝕜 E _inst_1 M.to_motion
local notation `𝕧` := @motion.velocity 𝕜 E _inst_1 M.to_motion
local notation `𝕒` := @motion.acceleration 𝕜 E _inst_1 M.to_motion

lemma acceleration_eq_deriv2_position
:𝕒 = (deriv^[2] 𝕩):=
begin
  simp [M.to_motion.hacc, M.to_motion.hvel],
  
end

lemma acceleration_eq_deriv2_position_iff_acceleration_eq_deriv_velocity
:𝕒 = (deriv^[2] 𝕩) ↔ 𝕒 = deriv 𝕧:=
begin
  simp [M.to_motion.hacc, M.to_motion.hvel],
end

lemma deriv2_position_eq_deriv_velocity
:(deriv^[2] 𝕩) = deriv 𝕧:= by simp [M.to_motion.hvel]

lemma velocity_eq_deriv1_position
:𝕧 =(deriv^[1] 𝕩) := by simp [M.to_motion.hvel]


theorem cont_diff_acceleration 
{n : with_top ℕ}
:
cont_diff 𝕜 n 𝕒 :=
begin
  let hconf := M.contdiff,
  specialize hconf n 2,
  cases hconf with hn hconf,
  simp [M.to_motion.hacc],
  rw ← deriv2_position_eq_deriv_velocity,
  exact hconf,
end

theorem cont_diff_velocity 
{n : with_top ℕ}
:
cont_diff 𝕜 n 𝕧:=
begin
  let hconf := M.contdiff,
  specialize hconf n 1,
  cases hconf with hn hconf,
  simp at hconf,
  simp [M.to_motion.hvel],
  exact hconf,
end


theorem cont_diff_position 
{n : with_top ℕ}
:
cont_diff 𝕜 n 𝕩:=
begin
  let hconf := M.contdiff,
  specialize hconf n 0,
  cases hconf with hn hconf,
  simp at hconf,
  exact hconf,
end

theorem acceleration_differentiable
{n : with_top ℕ}
:
differentiable 𝕜 𝕒 :=
begin
  let hconf := M.contdiff,
  specialize hconf n 2,
  rw [acceleration_eq_deriv2_position, ← iterated_deriv_eq_iterate],
  cases hconf with hn hconf,
  rw ← iterated_deriv_eq_iterate at hconf,
  apply cont_diff.differentiable_iterated_deriv 2 cont_diff_position hn,
end


theorem velocity_differentiable
{n : with_top ℕ}
:
differentiable 𝕜 𝕧 :=
begin
  let hconf := M.contdiff,
  rw [velocity_eq_deriv1_position, ← iterated_deriv_eq_iterate],
  specialize hconf n 1,
  cases hconf with hn hconf,
  rw ← iterated_deriv_eq_iterate at hconf,
  apply cont_diff.differentiable_iterated_deriv 1 cont_diff_position hn,
end

theorem position_differentiable
{n : with_top ℕ}
:
differentiable 𝕜 𝕩 :=
begin
  apply cont_diff.differentiable cont_diff_position,
  let hconf := M.contdiff,
  specialize hconf n 0,
  cases hconf with hn hconf,
  norm_cast at hn,
  rw show (1 : with_top ℕ) = 0 + 1, by simp,
  apply with_top.add_one_le_of_lt hn,
end

open inner_product_space
variables {𝔸 : E}
theorem const_accel
(accel_const : 𝕒 = λ (t : 𝕜), 𝔸)
{n : with_top ℕ}
:
𝕧 =  λ t:𝕜, t•𝔸 + 𝕧 0:=
begin
  apply antideriv_const',
  simp [M.to_motion.hacc] at accel_const,
  intro,
  rw ← show deriv M.to_motion.velocity x = 𝔸, by {rw accel_const, funext},
  apply differentiable_at.has_deriv_at (differentiable.differentiable_at velocity_differentiable),
  exact n,
end

theorem const_accel'
(accel_const : 𝕒 = λ (t : 𝕜), 𝔸)
{n : with_top ℕ}
:
𝕩 = (λ t:𝕜, ((t^2/2)•𝔸) + t•(𝕧 0) + (𝕩 0)) :=
begin
  have h1 : 𝕧 =  λ t:𝕜, t•𝔸 + 𝕧 0 := by {apply const_accel accel_const, exact n},
  apply antideriv_first_order_poly',
  intro,
  rw [show x•𝔸 + 𝕧 0 = 𝕧 x, by {rw h1, simp,}, M.to_motion.hvel],
  apply differentiable_at.has_deriv_at (differentiable.differentiable_at position_differentiable),
  exact n,
end

theorem const_accel''
(accel_const : 𝕒 = λ (t : 𝕜), 𝔸)
{n : with_top ℕ}
:
∀ t, 𝕩 t =  (t/2)•((𝕧 t) + (𝕧 0)) + (𝕩 0):=
begin
  rw [show  𝕧 =  λ t:𝕜, t•𝔸 + 𝕧 0, by {apply const_accel accel_const, exact n},
   show 𝕩 = (λ t:𝕜, ((t^2/2)•𝔸) + t•(𝕧 0) + (𝕩 0)), by {apply const_accel' accel_const, exact n}],
   field_simp,
   intro t,
   rw [add_assoc, ← add_smul, show t/2+t/2 = t, by finish, ← smul_assoc, show (t/2)•t = t^2/2, by {rw smul_eq_mul, ring_nf,}],
end

/- theorem const_accel'''
(accel_const : 𝕒 = λ (t : 𝕜), 𝔸)
{n : with_top ℕ}
:
∀ t : 𝕜, inner (𝕧 t) (𝕧 t) = inner(𝕧 (0:𝕜)) (𝕧 (0:𝕜)) + (2:𝕜) * inner ((𝕩 t) - (𝕩 (0:𝕜))) 𝔸
:=
begin
  intro,
  have : semiring 𝕜 := by apply ring.to_semiring,
  rw [@real_inner_self_eq_norm_sq E (inner_product_space.is_R_or_C_to_real 𝕜 E), show  𝕧 =  λ t:𝕜, t•𝔸 + 𝕧 0, by {apply const_accel accel_const, exact n},
      norm_add_pow_two, norm_smul, mul_pow, inner_smul_left, show (𝕩 t) - (𝕩 (0:𝕜)) = ((t^2/2)•𝔸) + t•(𝕧 0), by {rw const_accel' accel_const, simp, exact n,},
      @inner_add_left _ _ _ (inner_product_space.is_R_or_C_to_real 𝕜 E) ((t ^ 2 / 2) • 𝔸) _ 𝔸, real_inner_eq_re_inner 𝕜 ((t ^ 2 / 2) • 𝔸) 𝔸,
      real_inner_eq_re_inner 𝕜 _ 𝔸, inner_smul_left, inner_smul_left],
  simp,
  rw [← real_inner_eq_re_inner 𝕜 𝔸 _, ← real_inner_eq_re_inner 𝕜 𝔸 _, @real_inner_self_eq_norm_sq _ (inner_product_space.is_R_or_C_to_real 𝕜 E) (velocity (0:𝕜)),
      add_comm,@real_inner_self_eq_norm_sq _ (inner_product_space.is_R_or_C_to_real 𝕜 E) 𝔸, mul_add, mul_add],
  field_simp,
  rw [inner_re_symm, ← real_inner_eq_re_inner 𝕜 𝔸 _, mul_add],
  
end -/

theorem real_const_accel'''
[N : motion_cont_diff_everywhere ℝ E]
(accel_const : N.to_motion.acceleration = λ (t : ℝ), 𝔸)
{n : with_top ℕ}
:
∀ t : ℝ, @inner ℝ  E _ (@motion.velocity ℝ E real.is_R_or_C N.to_motion t) (@motion.velocity ℝ E real.is_R_or_C N.to_motion t) = 
@inner ℝ E _ (@motion.velocity ℝ E real.is_R_or_C N.to_motion (0:ℝ)) (@motion.velocity ℝ E real.is_R_or_C N.to_motion (0:ℝ)) + 
2 * @inner ℝ E _ 𝔸 ((@motion.position ℝ E real.is_R_or_C N.to_motion t) - (@motion.position ℝ E real.is_R_or_C N.to_motion (0:ℝ)))
:=
begin
  intro,
  rw [show  (@motion.velocity ℝ E real.is_R_or_C N.to_motion) =  λ t:ℝ, t•𝔸 + (@motion.velocity ℝ E real.is_R_or_C N.to_motion) 0, 
      by {apply const_accel accel_const, exact n}, show (@motion.position ℝ E real.is_R_or_C N.to_motion t) - (@motion.position ℝ E real.is_R_or_C N.to_motion (0:ℝ)) = 
      ((t^2/2)•𝔸) + t•(@motion.velocity ℝ E real.is_R_or_C N.to_motion 0), by {rw const_accel' accel_const, simp, exact n,}],
  field_simp,
  rw [real_inner_add_add_self, inner_add_right, add_comm],
  repeat {rw real_inner_smul_left,},
  repeat {rw real_inner_smul_right,},
  ring_nf,
end

/-! ### Kinematic equations for translation on a real line-/
variables
{α : ℝ} 
(x v a : ℝ → ℝ) 

theorem velocity_eq_const_accel_mul_time
(hf' : ∀(t : ℝ), has_deriv_at x (v t) t)
(hf'' : ∀(t : ℝ), has_deriv_at v (a t) t)
(accel_const : a = λ (t : ℝ), α) 
:
v =  λ t, α*t + v 0 
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
have h1 :v =  λ t:ℝ, α*t + v 0, 
{
  apply velocity_eq_const_accel_mul_time,
  apply hf',
  apply hf'',
  apply accel_const,
},
apply antideriv_first_order_poly,
rw h1 at hf',
simp at hf',
exact hf',
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


