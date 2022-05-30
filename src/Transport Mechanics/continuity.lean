--The continuity equation for mass over a control volume
import data.real.basic
import analysis.calculus.fderiv
import analysis.calculus.deriv
import measure_theory.integral.interval_integral
import analysis.calculus.parametric_integral


open measure_theory 
open_locale big_operators 


local notation `ℝ³` := fin 3 → ℝ
local notation `ℝ² ` := fin (2) → ℝ

theorem some_name 
(μ : measure_theory.measure ℝ³ . measure_theory.volume_tac)
(ρ : ℝ → ℝ³ → ℝ ) -- Mass, density
(M : ℝ → ℝ)
(t : ℝ)
(V1 V2: (ℝ³))  -- consider a finite volume V which is defined on ℝ³ FOr Lean we define V as V2 - V1
(V : ℝ³) (hV : V1 ≤ V2)

(F : ℝ³ → ℝ³) -- flux of our fluid
(F' : (ℝ³) → (ℝ³) →L[ℝ] ℝ³) -- a partial derivatvie of our vector
--define how our flux term F relates to density and velocity

--define how mass relates to density
(hM : ∀ (t:ℝ), M t = ∫ (V : ℝ³) in set.Icc V1 V2,(ρ t V)) --Mass of control volume at time t is equal to triple integral 
-- of density at time t over the control volume
--(hM' : ∀ (t:ℝ), fderiv ℝ M t = ∫(V : ℝ³) in set.Icc V1 V2, (fderiv ℝ ρ t) V) --the time derivative version of hM

--stuff for divergence theorem, I think. I copied this over to have in case I needed it or for reference
(s : set (ℝ³)) -- set of ℝ³ whcih are the variables of our function (like our dimensions mass can flow)
(hs : s.countable) -- the set is finite (we don't have infinite dimensions)
(Hc : continuous_on F (set.Icc V1 V2)) --Our function is continous inside the control volume
-- Hd says that f is differentiable on the interior
(Hd : ∀ (x : fin (3) → ℝ), x ∈ set.pi set.univ (λ (i : fin (3)), set.Ioo (V1 i) (V2 i)) \ s → has_fderiv_at F (F' x) x)
-- Hi defines the divergence and says it is integrable on our control volume
(Hi :measure_theory.integrable_on (λ (x : ℝ³), ∑ (i : fin (3)), (F' x) (pi.single i 1) i) (set.Icc V1 V2) μ)

--differential form of the continuity equation
(DiffCont : ∀ (t : ℝ), deriv M t = - ∑ (i : fin (3)), ((∫ (x : fin 2 → ℝ) in set.Icc (V1 ∘ (i.succ_above)) (V2 ∘ (i.succ_above)), F (i.insert_nth (V2 i) x) i) - ∫ (x : fin 2 → ℝ) in set.Icc (V1 ∘ (i.succ_above)) (V2 ∘ (i.succ_above)), F (i.insert_nth (V1 i) x) i))
:
∀ t: ℝ, ∫ (x : ℝ³) in set.Icc V1 V2, deriv (λ t, ρ t V) t + ∑(i : fin 3), (F' x) (pi.single i 1) i = 0
:=
begin
have hM' : ∀ t : ℝ, deriv M t = ∫ (V : ℝ³) in set.Icc V1 V2,(deriv(λ t, ρ t V) t),
{
sorry,
},

intro t1,
rw measure_theory.integral_Icc_eq_integral_Ioc,
rw ← interval_integral.integral_of_le, 
rw interval_integral.integral_add,
rw ← hM',
end
universe u1
theorem eq_integral_to_deriv_eq_integral_of_deriv
{E : Type u1} [nondiscrete_normed_field E] [normed_group E] [complete_space E] [normed_space E ℝ]
(ρ : E → ℝ³ → ℝ )(M : E → ℝ)(V1 V2: (ℝ³)) (hV : V1 ≤ V2)
:
 (M = λ (t : E),∫ (V : ℝ³) in set.Icc V1 V2,( ρ t V)) →  (∀ (t:E), deriv M t = ∫ (V : ℝ³) in set.Icc V1 V2,(deriv(λ t, ρ t (V2-V1)) t))
:=
begin
intro h,
rw h,

rw interval_integral.integral_const,
end
