import data.real.basic
import analysis.complex.basic


namespace real  --real.sqrt, will return 0 for negative inputs
 
lemma LJTranslationInvariance1D (r x y t rt E a b Et : ℝ )

( a1: r = sqrt ((x-y)^2) ) -- pairwise distance
( a2: E = a/r^12 - b/r^6 ) -- LJ potential
( a3: rt = sqrt (((x+t) - (y+t))^2)  ) --- pairwise distance after translation t
( a4: Et = a/rt^12 - b/rt^6 ) -- LJ potential after translation t
:
--Conjecture
E = Et
:=

begin
 simp at a3,
 rw a1 at a2,
 rw a3 at a4,
 rw ← a4 at a2,
 exact a2,
end


lemma LJTranslationInvariance3D (a b r rt E t Et x1 y1 z1 x2 y2 z2 : ℝ)

( a1: r = sqrt ((x1-x2)^2 + (y1-y2)^2 + (z1-z2)^2) ) -- pairwise distance
( a2: E = a/r^12 - b/r^6 ) -- LJ potential
( a3: rt = sqrt (((x1+t) - (x2+t))^2 + ((y1+t) - (y2+t))^2 + ((z1+t) - (z2+t))^2) ) --- pairwise distance after translation t
( a4: Et = a/rt^12 - b/rt^6 ) -- LJ potential after translation t
:
--Conjecture
E = Et
:=

begin
 simp at a3,
 rw a1 at a2,
 rw a3 at a4,
 rw ← a4 at a2,
 exact a2,
end

end real
