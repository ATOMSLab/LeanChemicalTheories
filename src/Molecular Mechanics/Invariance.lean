import analysis.normed.group.basic
import analysis.normed_space.basic

theorem norm_trans_invar 
:
∀ (x y t : ℝ), has_dist.dist x y = has_dist.dist (x+t) (y+t)
:=
begin
repeat {intro},
repeat {rw real.dist_eq},
simp,
end
theorem norm_scale 
:
∀ (x y t: ℝ),  ∥t∥*has_dist.dist x y = has_dist.dist (t•x) (t•y)
:=
begin
repeat {intro},
rw dist_smul,
end
example (x y t : ℝ) :
has_dist.dist x y = has_dist.dist (x+t) (y+t)
:=
begin
rw norm_trans_invar,
end

example
[normed_group ℝ]
:

:=