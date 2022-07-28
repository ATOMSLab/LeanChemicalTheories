import analysis.normed.group.basic
import analysis.normed_space.basic
variables {n: ℕ }
local notation `ℝ^n ` := fin (n) → ℝ

theorem norm_trans_invar 

:
∀ (x y t : ℝ^n), has_dist.dist x y = has_dist.dist (x+t) (y+t)
:=
begin
  simp,
end


lemma LJInvariance_2 (x y t : ℝ^n) (r rt a b E Et: ℝ)
( a1: r = dist x y) 
( a2: rt = dist (x+t) (y+t)  )
( a3: E = a/r^12 - b/r^6 )
( a4: Et = a/rt^12 - b/rt^6 )
:
E = Et
:=
begin
  simp at a2,
  rw a2 at a4,
  rw a1 at a3,
  exact (rfl.congr (eq.symm a4)).mp a3,
end
