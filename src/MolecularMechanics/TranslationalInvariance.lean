import data.real.basic
import analysis.complex.basic


open real  
 
lemma LJTranslationInvariance1D (r x y t rt E a b Et : ℝ )

( a1: r = sqrt ((x-y)^2) ) 
( a2: E = a/r^12 - b/r^6 ) 
( a3: rt = sqrt (((x+t) - (y+t))^2)  )
( a4: Et = a/rt^12 - b/rt^6 )
:

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

( a1: r = sqrt ((x1-x2)^2 + (y1-y2)^2 + (z1-z2)^2) ) 
( a2: E = a/r^12 - b/r^6 ) 
( a3: rt = sqrt (((x1+t) - (x2+t))^2 + ((y1+t) - (y2+t))^2 + ((z1+t) - (z2+t))^2) ) 
( a4: Et = a/rt^12 - b/rt^6 ) 
:
E = Et
:=

begin
 simp at a3,
 rw a1 at a2,
 rw a3 at a4,
 rw ← a4 at a2,
 exact a2,
end


lemma TranslationInvariance (d dt t x y : ℝ )

( a1: d = sqrt ((x-y)^2) )
( a2: dt = sqrt (((x+t) - (y+t))^2)  )
:
d = dt
:=

begin
 simp at a2,
 rw ← a2 at a1,
 exact a1,
end

lemma LJInvariance (a b r rt x y t E Et : ℝ )
( a1: r = sqrt ((x-y)^2) ) 
( a2: rt = sqrt (((x+t) - (y+t))^2)  ) 
( a3: E = a/r^12 - b/r^6 ) 
( a4: Et = a/rt^12 - b/rt^6 )
:

E = Et
:=

begin
  have ht: r=rt,
  finish using TranslationInvariance,
  rw ht at a3,
  exact (rfl.congr (eq.symm a4)).mp a3,  
end


