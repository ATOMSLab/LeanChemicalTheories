import data.real.basic
import analysis.complex.basic


namespace real  --real.sqrt, will return 0 for negative inputs
 


lemma TranslationInvariance1D (a b r rt E t x y : ℝ )

( a1: E = a/r^12 - b/r^6 ) -- LJ potential
( a2: r = sqrt ((x-y)^2) ) -- pairwise distance
( a3: rt = sqrt (((x+t) - (y+t))^2)  ) --- pairwise distance after translation t
:
--Conjecture
r = rt
:=

begin
  simp at a3,
  rw a3,
  exact a2,
end



lemma TranslationInvariance3D (a b r rt E t x1 y1 z1 x2 y2 z2 : ℝ)

--- LJ potential
( a1: E = a/r^12 - b/r^6 )
--- pairwise distance
(a2: r = sqrt ((x1-x2)^2 + (y1-y2)^2 + (z1-z2)^2))
--- pairwise distance after translation t
(a3: rt = sqrt (((x1+t) - (x2+t))^2 + ((y1+t) - (y2+t))^2 + ((z1+t) - (z2+t))^2))
:
--- Conjecture
r = rt
:=

begin
  simp at a3,
  rw a3,
  exact a2,
end


end real


