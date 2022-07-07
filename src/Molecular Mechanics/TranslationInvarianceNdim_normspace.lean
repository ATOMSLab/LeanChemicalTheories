import analysis.normed.group.basic
import analysis.normed_space.basic
variables {n: ℕ }
local notation `ℝ^n ` := fin (n) → ℝ

theorem norm_trans_invar 

:
∀ (x y t : ℝ^n), has_dist.dist x y = has_dist.dist (x+t) (y+t)
:=
begin
  -- repeat {intro},
  -- repeat {rw real.dist_eq},
  simp,
end


lemma LJInvariance (x y t : ℝ^n) (r rt a b E Et: ℝ)
( a1: r = dist x y)  -- pairwise distance
( a2: rt = dist (x+t) (y+t)  ) --- pairwise distance after translation
( a3: E = a/r^12 - b/r^6 ) -- LJ potential
( a4: Et = a/rt^12 - b/rt^6 ) -- LJ potential after translation t
:
--Conjecture
E = Et
:=
begin

--(uses simp and rw to work direclty on the axioms)
  simp at a2,
  rw a2 at a4,
  rw a1 at a3,
  exact (rfl.congr (eq.symm a4)).mp a3,

--(alternative proof: uses just simp and finish to directly on the axioms provided)
  -- simp at a2,
  -- finish,

--(alternative proof: introduces a hypothesis (r=rt) invokes the previous proof)
  -- have ht: r=rt,
  -- finish using norm_trans_invar n,
  -- rw ht at a3,
  -- exact (rfl.congr (eq.symm a4)).mp a3,  


end
