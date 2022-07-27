/-This is the attempt to formalize a section of special realtivity, by following the formalization in Coq. 
The paper I am following is from: https://dash.harvard.edu/handle/1/38811518 -/

import data.real.basic
import analysis.inner_product_space.pi_L2

noncomputable theory
variables {i : ℕ}
def body := Type
def v4 := ((ℝ × ℝ × ℝ) × ℝ)
def v4x (v : v4) : ℝ := v.fst.fst
def v4y (v : v4) := v.fst.snd.fst
def v4z (v : v4) := v.fst.snd.snd
def v4t (v : v4) := v.snd
def v4_t (v : v4) := (((0:ℝ),(0:ℝ),(0:ℝ)),v.snd)
def v4_s (v : v4) := (v.fst, (0:ℝ))
def v4norm (v : v4) := real.sqrt ((v4x v)^2 + (v4y v)^2 + (v4z v)^2 + (v4t v)^2)

#check v4_t 
#check v4_s

local notation v`x` := v4x v
local notation v`y` := v4y v
local notation v`z` := v4z v
local notation v`t` := v4t v
local notation v`ˢ` := v4_s v
local notation v`ᵗ` := v4_t v

constant IB : body → Prop --indicates a body is an intertial body
constant Ph : body → Prop --indicates a body is a photon
constant W : body → body → v4 → Prop --the notion of observation

def Ob (m : body) := ∃ b v, W m b v --m is an observer if there exists a body and a coordinate such that m observes b at those coordinates

def IOb (m : body) : Prop := IB m ∧ Ob m 

def eveq (b1 b2 : body) (v1 v2 : v4) := ∀ b, W b1 b v1 ↔ W b2 b v2


structure specrel :=
(AxPh : ∀ (m : body), ∃ (c : ℝ), ∀ (X Y : v4), (IOb m) → ((∃ p, Ph p ∧ W m p X ∧ W m p Y) ↔ v4norm ((Yˢ) -ᵥ (Xˢ)) = c*v4norm ((Yᵗ) -ᵥ (Xᵗ))))
(AxEv : ∀ (m k : body), IOb m ∧ IOb k ↔ forall X, exists Y, eveq m k X Y)
(AxSf : ∀ m, IOb m →  (forall v, W m m v ↔ (v x) = 0 ∧ (v y) = 0 ∧ (v z) = 0))
(AxSm1 : ∀ m k, IOb m ∧ IOb k → forall X Y X' Y', (Xᵗ) = (Yᵗ) ∧ (X'ᵗ) = (Y'ᵗ) ∧ eveq m k X X' ∧ eveq m k Y Y' → v4norm ((Xˢ) -ᵥ (Yˢ)) = v4norm ((X'ˢ) -ᵥ (Y'ˢ)))
(AxSm2 : ∀ m, IOb m → ∃ p, Ph p ∧ W m p ((0, 0, 0), 0) ∧ W m p ((1, 0, 0), 1))



theorem ax_ph' (SR : specrel): ∀ m, forall X Y, IOb m → ((∃ p, Ph p ∧ W m p X ∧ W m p Y) ↔ v4norm ((Yˢ) -ᵥ (Xˢ)) = v4norm ((Yᵗ) -ᵥ (Xᵗ))):=
begin
  let AxPh := specrel.AxPh SR,
  intros m X Y h,
  specialize AxPh m,
  cases AxPh with c AxPh,
  specialize AxPh X Y h,
  convert AxPh,
  cases AxPh with AxPh1 AxPh2,
  let AxSm2 := specrel.AxSm2 SR,
  specialize AxSm2 m h,
  
  
end
