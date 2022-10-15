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

structure motion (𝕜 : Type*) (E : Type*) [is_R_or_C 𝕜] [inner_product_space 𝕜 E]:=
{position velocity acceleration : 𝕜 → E}
(hvel : velocity = deriv position)
(hacc : acceleration = deriv velocity)


/-Given the definition of motion and the relation between position, velocity, and acceleration, we extend the motion class
to require that our functions be continously differentiable n times (Cⁿ).-/
structure motion_cont_diff_everywhere (𝕜 : Type*) (E : Type*) [is_R_or_C 𝕜] [inner_product_space 𝕜 E]
  extends motion 𝕜 E:=
(contdiff : ∀ n : with_top ℕ, ∀ m : ℕ, (↑m < n) → (cont_diff 𝕜 n (deriv^[m] to_motion.position)))

/-When defining the four kinematic equations, we require the field to be real or complex-/
variables {𝕜 : Type*} {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {M : motion_cont_diff_everywhere 𝕜 E}

local notation `𝕩` := M.position
local notation `𝕧` := M.velocity
local notation `𝕒` := M.acceleration

lemma acceleration_eq_deriv2_position
{𝕜 : Type*} {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (M : motion 𝕜 E)
:M.acceleration = (deriv^[2] M.position):=
begin
  simp [M.hacc, M.hvel],
end

lemma acceleration_eq_deriv2_position_iff_acceleration_eq_deriv_velocity
{𝕜 : Type*} {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (M : motion 𝕜 E)
:M.acceleration = (deriv^[2] M.position) ↔ M.acceleration = deriv M.velocity:=
begin
  simp [M.hacc, M.hvel],
end

lemma deriv2_position_eq_deriv_velocity
{𝕜 : Type*} {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] (M : motion 𝕜 E)
:(deriv^[2] M.position) = deriv M.velocity:= by simp [M.hvel]

lemma velocity_eq_deriv1_position
:M.velocity =(deriv^[1] M.position) := by simp [M.hvel]


theorem cont_diff_acceleration 
{n : with_top ℕ}
(hn : 2 < n)
:
cont_diff 𝕜 n 𝕒 :=
begin
  let hconf := M.contdiff,
  specialize hconf n 2 hn,
  simp [M.to_motion.hacc],
  rw ← deriv2_position_eq_deriv_velocity,
  exact hconf,
end

theorem cont_diff_velocity 
{n : with_top ℕ}
(hn : 1 < n)
:
cont_diff 𝕜 n 𝕧:=
begin
  let hconf := M.contdiff,
  specialize hconf n 1 hn,
  simp at hconf,
  simp [M.hvel],
  exact hconf,
end


theorem cont_diff_position 
{n : with_top ℕ}
(hn : 0 < n)
:
cont_diff 𝕜 n 𝕩:=
begin
  let hconf := M.contdiff,
  specialize hconf n 0 hn,
  simp at hconf,
  exact hconf,
end

theorem acceleration_differentiable
{n : with_top ℕ}
(hn : 2 < n)
:
differentiable 𝕜 𝕒 :=
begin
  let hconf := M.contdiff,
  specialize hconf n 2 hn,
  rw [acceleration_eq_deriv2_position, ← iterated_deriv_eq_iterate],
  rw ← iterated_deriv_eq_iterate at hconf,
  apply cont_diff.differentiable_iterated_deriv 2 (cont_diff_position _) hn,
  apply lt_trans _ hn,
  norm_cast,
  linarith,
end


theorem velocity_differentiable
{n : with_top ℕ}
(hn : 1 < n)
:
differentiable 𝕜 𝕧 :=
begin
  let hconf := M.contdiff,
  rw [velocity_eq_deriv1_position, ← iterated_deriv_eq_iterate],
  specialize hconf n 1 hn,
  rw ← iterated_deriv_eq_iterate at hconf,
  apply cont_diff.differentiable_iterated_deriv 1 (cont_diff_position _) hn,
  apply lt_trans _ hn,
  norm_cast,
  linarith,
end

theorem position_differentiable
{n : with_top ℕ}
(hn : 0 < n)
:
differentiable 𝕜 𝕩 :=
begin
  apply cont_diff.differentiable (cont_diff_position hn),
  let hconf := M.contdiff,
  specialize hconf n 0 hn,
  rw show (1 : with_top ℕ) = 0 + 1, by simp,
  apply with_top.add_one_le_of_lt hn,
end

open inner_product_space
variables {𝔸 : E}

theorem const_accel
(accel_const : 𝕒 = λ (t : 𝕜), 𝔸)
{n : with_top ℕ}
(hn : 1 < n)
:
𝕧 =  λ t:𝕜, t•𝔸 + 𝕧 0:=
begin
  apply antideriv_const',
  simp [M.to_motion.hacc] at accel_const,
  intro,
  rw ← show deriv M.to_motion.velocity x = 𝔸, by {rw accel_const, funext},
  apply differentiable_at.has_deriv_at (differentiable.differentiable_at (velocity_differentiable hn)),
end

theorem const_accel'
(accel_const : 𝕒 = λ (t : 𝕜), 𝔸)
{n : with_top ℕ}
(hn : 1 < n)
:
𝕩 = (λ t:𝕜, ((t^2/2)•𝔸) + t•(𝕧 0) + (𝕩 0)) :=
begin
  have h1 : 𝕧 =  λ t:𝕜, t•𝔸 + 𝕧 0 := (const_accel accel_const hn),
  apply antideriv_first_order_poly',
  intro,
  rw [show x•𝔸 + 𝕧 0 = 𝕧 x, by {rw h1, simp,}, M.to_motion.hvel],
  apply differentiable_at.has_deriv_at (differentiable.differentiable_at (position_differentiable _)),
  exact n,
  apply lt_trans _ hn,
  norm_cast,
  linarith,
end

theorem const_accel''
(accel_const : 𝕒 = λ (t : 𝕜), 𝔸)
{n : with_top ℕ}
(hn : 1 < n)
:
∀ t, 𝕩 t =  (t/2)•((𝕧 t) + (𝕧 0)) + (𝕩 0):=
begin
  rw [const_accel accel_const hn, const_accel' accel_const hn],
  field_simp,
  intro t,
  rw [add_assoc, ← add_smul, show t/2+t/2 = t, by finish, ← smul_assoc, show (t/2)•t = t^2/2, by {rw smul_eq_mul, ring_nf,}],
end

lemma inner_add_add_self' {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {x y : E}
:
(@inner 𝕜 _ _ x y) + inner y x = inner (x + y) (x + y) - inner x x - inner y y
:= by rw inner_add_add_self; ring


-- theorem const_accel'''
-- (accel_const : 𝕒 = λ (t : 𝕜), 𝔸)
-- {n : with_top ℕ}
-- (hn : 1 < n)
-- :
-- ∀ t : 𝕜, @inner 𝕜 _ _ (𝕧 t) (𝕧 t) = inner(𝕧 (0:𝕜)) (𝕧 (0:𝕜)) + inner ((𝕩 t) - (𝕩 (0:𝕜))) 𝔸 + inner 𝔸 ((𝕩 t) - (𝕩 (0:𝕜)))
-- :=
-- begin
--   intro,
--   have h1 : @inner 𝕜 _ _ (𝕧 t) (𝕧 t) = ∥t•𝔸∥^2 + t * inner 𝔸 (𝕧 (0 : 𝕜)) + (star_ring_end 𝕜) t * inner (𝕧 0) 𝔸 + ∥(𝕧 0)∥^2,
--   { rw [const_accel accel_const hn, inner_add_add_self, ← inner_self_re_to_K, inner_self_eq_norm_sq, ← inner_self_re_to_K, inner_self_eq_norm_sq],
--     simp [inner_smul_left, inner_smul_right],
--     sorry, },
--   have h2 : @inner 𝕜 _ _ (𝕧 (0:𝕜)) (𝕧 (0:𝕜)) + inner ((𝕩 t) - (𝕩 (0:𝕜))) 𝔸 + inner 𝔸 ((𝕩 t) - (𝕩 (0:𝕜))) = ∥t•𝔸∥^2 + (star_ring_end 𝕜) t * inner (𝕧 (0 : 𝕜)) 𝔸 + t * inner 𝔸 (𝕧 0) + ∥(𝕧 0)∥^2,
--   { rw [const_accel'' accel_const hn t],
--     simp,
--     rw [← inner_self_re_to_K, inner_self_eq_norm_sq, inner_add_left, inner_add_right, ← inner_conj_sym, add_assoc, add_add_add_comm, add_comm ((star_ring_end 𝕜) _),
--     is_R_or_C.add_conj, ← inner_conj_sym (𝔸) ((t / 2) • M.to_motion.velocity 0), is_R_or_C.add_conj],
--     simp [inner_smul_left, inner_smul_right, add_assoc, add_right_cancel_iff, is_R_or_C.div_re],
--     rw [← inner_self_re_to_K, inner_self_eq_norm_sq, show (2 : 𝕜) = 1 + 1, by norm_num, is_R_or_C.norm_sq_add, is_R_or_C.norm_sq_one],
--     simp [norm_smul, mul_pow],
--     norm_num,
--     have h : is_R_or_C.re (t^2) = ∥t∥^2,
--     { },

--      },
--   rw [const_accel accel_const hn, inner_add_add_self, const_accel' accel_const hn],
--   simp,
--   rw [add_assoc (inner (M.to_motion.velocity 0) (M.to_motion.velocity 0)), ← inner_conj_sym 𝔸, is_R_or_C.add_conj,
--   inner_add_left],
--   simp only [inner_smul_left, inner_smul_right, ← mul_assoc, is_R_or_C.mul_conj, is_R_or_C.norm_sq_eq_def'],

--   field_simp,
--   ring_nf!,
-- end 

theorem real_const_accel'''
[inner_product_space ℝ E]
{N : motion_cont_diff_everywhere ℝ E}
(accel_const : N.to_motion.acceleration = λ (t : ℝ), 𝔸)
{n : with_top ℕ}
(hn : 1 < n)
:
∀ t : ℝ, @inner ℝ  E _ (N.velocity t) (N.velocity t) = @inner ℝ E _ (N.velocity (0:ℝ)) (N.velocity (0:ℝ)) +  
2 * @inner ℝ E _ 𝔸 ((N.position t) - (N.position (0:ℝ)))
:=
begin
  intro,
  rw [show  N.velocity  =  λ t:ℝ, t•𝔸 + N.velocity 0, 
      by {apply const_accel accel_const hn}, show (N.position t) - (N.position (0:ℝ)) = 
      ((t^2/2)•𝔸) + t•(N.velocity 0), by {rw const_accel' accel_const hn, simp,}],
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


