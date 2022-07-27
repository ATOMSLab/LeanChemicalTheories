--The continuity equation for mass over a control volume
--this uses stuff from the sphere eversion project

import data.real.basic
import analysis.calculus.fderiv
import analysis.calculus.deriv
import measure_theory.integral.interval_integral
import analysis.calculus.parametric_integral
import measure_theory.function.strongly_measurable




open topological_space measure_theory filter metric 
open_locale big_operators topological_space filter interval



local notation `ℝ³` := fin 3 → ℝ
local notation `ℝ² ` := fin (2) → ℝ

theorem some_name 
(μ : measure_theory.measure ℝ³ . measure_theory.volume_tac)
{V1 V2 V : (ℝ³)}{t0 ε: ℝ} [linear_order ℝ³] (ε_pos : 0 < ε) {bound : ℝ³ → ℝ}
(ρ ρ': ℝ → ℝ³ → ℝ )(M : ℝ → ℝ) (hV : V1 ≤ V2) 
(hρ_meas : ∀ᶠ (t : ℝ) in nhds t0, ae_measurable (ρ t) (μ.restrict (set.interval_oc V1 V2)))
(hρ_int : interval_integrable (ρ t0) μ V1 V2)
(hρ'_meas : ae_measurable (ρ' t0) (μ.restrict (set.interval_oc V1 V2)))
(h_bound : ∀ᵐ (V : ℝ³) ∂μ, V ∈ set.interval_oc V1 V2 → ∀ (t : ℝ), t ∈ metric.ball t0 ε → ∥ρ' t V∥ ≤ bound V)
(bound_integrable : interval_integrable bound μ V1 V2)
(h_diff : ∀ᵐ (V : ℝ³) ∂μ, V ∈ set.interval_oc V1 V2 → ∀ (t : ℝ), t ∈ ball t0 ε → has_deriv_at (λ (t : ℝ), (ρ t V)) (ρ' t V) t)

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
have hM' :  deriv M t0 = ∫ (V : ℝ³) in V1..V2,(ρ' t0 V) ∂μ,
{
  
},
intro t1,
rw measure_theory.integral_Icc_eq_integral_Ioc,
rw ← interval_integral.integral_of_le, 
rw interval_integral.integral_add,
rw ← hM',
end
theorem has_deriv_at_deriv_for_all
(f : ℝ → ℝ) (f' : ℝ) (h : ∀ (x : ℝ), has_deriv_at f f' x)
:
∀ (x : ℝ), deriv f x = f'
:=
begin
intro x,
rw has_deriv_at.deriv,
apply h,
end

/-
theorem eq_integral_to_deriv_eq_integral_of_deriv
{μ : measure_theory.measure ℝ³} {V1 V2 : (ℝ³)}{t0 ε: ℝ} [linear_order ℝ³] (ε_pos : 0 < ε) {bound : ℝ³ → ℝ}
(ρ ρ': ℝ → ℝ³ → ℝ )(M : ℝ → ℝ) (hV : V1 ≤ V2) 
(hρ_meas : ∀ᶠ (t : ℝ) in nhds t0, ae_measurable (ρ t) (μ.restrict (set.interval_oc V1 V2)))
(hρ_int : interval_integrable (ρ t0) μ V1 V2)
(hρ'_meas : ae_measurable (ρ' t0) (μ.restrict (set.interval_oc V1 V2)))
(h_bound : ∀ᵐ (V : ℝ³) ∂μ, V ∈ set.interval_oc V1 V2 → ∀ (t : ℝ), t ∈ metric.ball t0 ε → ∥ρ' t V∥ ≤ bound V)
(bound_integrable : interval_integrable bound μ V1 V2)
(h_diff : ∀ᵐ (V : ℝ³) ∂μ, V ∈ set.interval_oc V1 V2 → ∀ (t : ℝ), t ∈ ball t0 ε → has_deriv_at (λ (t : ℝ), (ρ t V)) (ρ' t V) t)
:
(M = λ (t : ℝ),∫ (V : ℝ³) in V1..V2,( ρ t V) ∂μ) →   deriv M t0 = ∫ (V : ℝ³) in V1..V2,(ρ' t0 V) ∂μ
:=
begin
  have h1 : interval_integrable (ρ' t0) μ V1 V2 ∧ has_deriv_at (λ (t : ℝ), ∫ (V : fin 3 → ℝ) in V1..V2, ρ t V ∂μ) (∫ (V : fin 3 → ℝ) in V1..V2, ρ' t0 V ∂μ) t0,
    {
      rw ← ae_restrict_iff at *,
      simp only [interval_integrable_iff, interval_integral.interval_integral_eq_integral_interval_oc, ← ae_restrict_iff measurable_set_interval_oc] at *,
      have := has_deriv_at_integral_of_dominated_loc_of_deriv_le ε_pos hρ_meas hρ_int hρ'_meas h_bound bound_integrable h_diff,
      exact ⟨this.1, this.2.const_smul _⟩,
      have h1 : measurable_set {x : fin 3 → ℝ | ∀ (t : ℝ), t ∈ ball t0 ε → has_deriv_at (λ (t : ℝ), ρ t x) (ρ' t x) t},
      {
        
      },
      rw set_of,
      sorry,
      sorry,
    },
  intro h,
  rw h,
  cases h1 with h2 h3,
  rw has_deriv_at.deriv,
  apply h3,
end
-/

theorem some_name_2
{μ : measure_theory.measure ℝ³} {V1 V2 : (ℝ³)}{ε: ℝ} {bound : ℝ³ → ℝ}{ρ ρ': ℝ → ℝ³ → ℝ }{M : ℝ → ℝ}
[linear_order ℝ³] (ε_pos : 0 < ε) (hV : V1 ≤ V2) 
(hρ_meas :  ∀ᶠ (t : ℝ) in  nhds t0, ae_measurable (ρ t) (μ.restrict (set.interval_oc V1 V2)))
(hρ_int : ∀ (t0 : ℝ), interval_integrable (ρ t0) μ V1 V2)
(hρ'_meas : ∀ (t0 : ℝ), ae_measurable (ρ' t0) (μ.restrict (set.interval_oc V1 V2)))
(h_bound : ∀ (t0: ℝ), (∀ᵐ (V : ℝ³) ∂μ, V ∈ set.interval_oc V1 V2 → ∀ (t : ℝ), t ∈ metric.ball t0 ε → ∥ρ' t V∥ ≤ bound V))
(bound_integrable : interval_integrable bound μ V1 V2)
(h_diff : ∀ᵐ (V : ℝ³) ∂μ, V ∈ set.interval_oc V1 V2 → ∀ (t : ℝ), has_deriv_at (λ (t : ℝ), (ρ t V)) (ρ' t V) t)
:
(M = λ (t : ℝ),∫ (V : ℝ³) in V1..V2,( ρ t V) ∂μ) →   ∀ t, deriv M t = ∫ (V : ℝ³) in V1..V2,(ρ' t V) ∂μ
:=
begin
have h1 : ∀ (t : ℝ), interval_integrable (ρ' t) μ V1 V2 ∧ has_deriv_at (λ (t : ℝ), ∫ (V : fin 3 → ℝ) in V1..V2, ρ t V ∂μ) (∫ (V : fin 3 → ℝ) in V1..V2, ρ' t V ∂μ) t,
{
  intro t0,
  specialize hρ_meas t0,
  specialize hρ_int t0,
  specialize hρ'_meas t0,
  specialize h_bound t0,
  rw ← ae_restrict_iff at *,
  simp only [interval_integrable_iff, interval_integral.interval_integral_eq_integral_interval_oc, ← ae_restrict_iff measurable_set_interval_oc] at *,
  have := has_deriv_at_integral_of_dominated_loc_of_deriv_le ε_pos hρ_meas hρ_int hρ'_meas h_bound bound_integrable h_diff,
  exact ⟨this.1, this.2.const_smul _⟩,

}
end
