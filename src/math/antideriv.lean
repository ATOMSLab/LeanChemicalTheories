import analysis.special_functions.exp_deriv
import analysis.calculus.deriv
import analysis.calculus.mean_value

universe u_1

lemma fun_split
(f g : ℝ → ℝ)
:
(λ x, (f x) + (g x)) = ((λ x, f x) + (λ x, g x))
:=
begin
ring_nf,
end

theorem antideriv_const 
(f : ℝ → ℝ) (k : ℝ)
(hf : ∀ x, has_deriv_at f k x):
(f = λ x, (k*x) + (f 0) ) :=
begin
   have h1: ∀(x y : ℝ), f x - (x*k) = f y - (y*k),
   { 
    apply is_const_of_deriv_eq_zero,
    {
      rw differentiable,
      intro x,
      specialize hf x,
      apply has_deriv_at.differentiable_at,
      apply has_deriv_at.sub,
      {
        convert hf,
      },
      apply has_deriv_at_mul_const,
    },
    intro x,
    rw deriv_sub,
    rw sub_eq_zero,
    simp,
    rw has_deriv_at.deriv,
    specialize hf x,
    apply hf,
    apply has_deriv_at.differentiable_at,
    specialize hf x,
    apply hf,
    simp,
  },
  ext z,
  specialize h1 z 0,
  apply eq_add_of_sub_eq',
  simp at h1,
  rw mul_comm at h1,
  exact h1,
end


theorem antideriv_pow 
(f : ℝ → ℝ)
(hf : ∀ x, ∀ (n : ℕ), has_deriv_at f (x^n) x) :
∀(n:ℕ), (f = λ x, (x^(n+1))/↑(n+1) + (f 0)) :=
begin
  have h1: ∀ (n:ℕ) (x y : ℝ), f x - (x^(n+1))/↑(n+1) = f y - (y^(n+1))/↑(n+1),
  { 
    intro n,
    rw ← nat.succ_eq_add_one,
    apply is_const_of_deriv_eq_zero,
    {
      rw differentiable,
      intro x,
      specialize hf x,
      apply has_deriv_at.differentiable_at,
      apply has_deriv_at.sub,
      {
        specialize hf n,
        exact hf,
      },
      apply has_deriv_at.div_const,
      apply has_deriv_at_pow,
    },
    intro x,
    rw deriv_sub,
    rw sub_eq_zero,
    simp,
    rw has_deriv_at.deriv,
    specialize hf x,
    specialize hf n,
    rw ← nat.cast_add_one,
    rw mul_div_assoc,
    rw mul_div_left_comm,
    rw div_self,
    rw mul_one,
    exact hf,
    rw nat.cast_ne_zero,
    finish,
    apply has_deriv_at.differentiable_at,
    apply hf,
    exact n,
    apply differentiable_at.div_const,
    apply differentiable_at_pow,
  },
  intro n,
  ext z,
  specialize h1 n z 0,
  apply eq_add_of_sub_eq',
  simpa using h1,
end

theorem antideriv_zpow
(f : ℝ → ℝ)
(hf : ∀ x, x ≠ 0 ∧ ∀ z:ℤ,has_deriv_at f (x^z) x) :
∀(z:ℤ), (↑z + (1:ℝ) ≠ 0  → f = λ x, (x^(z+1))/↑(z+1) + (f 0)) :=
begin
  have h1: ∀ (z:ℤ), ↑z + (1:ℝ) ≠ 0  → ∀ (x y : ℝ), f x - (x^(z+1))/↑(z+1) = f y - (y^(z+1))/↑(z+1),
  { 
    intro z,
    intro h,
    apply is_const_of_deriv_eq_zero,
    {
      rw differentiable,
      intro x,
      specialize hf x,
      cases hf with hx hf,
      apply has_deriv_at.differentiable_at,
      apply has_deriv_at.sub,
      {
        specialize hf z,
        exact hf,
      },
      apply has_deriv_at.div_const,
      apply has_deriv_at_zpow,
      left,
      exact hx,
    },
    intro x,
    specialize hf x,
    cases hf with hx hf,
    rw deriv_sub,
    rw sub_eq_zero,
    simp,
    rw has_deriv_at.deriv,
    rw mul_div_assoc,
    rw mul_div_left_comm,
    rw div_self,
    rw mul_one,
    exact hf z,
    exact h,
    apply has_deriv_at.differentiable_at,
    exact hf z,
    apply differentiable_at.div_const,
    rw differentiable_at_zpow,
    left,
    exact hx,
  },
  intro z,
  intro h,
  ext v,
  specialize h1 z h v 0,
  apply eq_add_of_sub_eq',
  rw zero_zpow at h1,
  simpa using h1,
  norm_cast at *, 
end

theorem antideriv_first_order_poly
{k j: ℝ}
(f : ℝ → ℝ)
(hf : ∀ x, has_deriv_at f (j*x + k) x) :
(f = λ x, j*(x^2)/2 + k*x + (f 0)) :=
begin
  conv{
  find (k*_) {rw ← pow_one x,}
  },
  rw fun_split,
  have h1: ∀ (x y : ℝ), f x - (j*(x^2)/2 + k*x^1)= f y - (j*(y^2)/2 + k*y^1),
  { 
    apply is_const_of_deriv_eq_zero,
    {
      rw differentiable,
      intro x,
      specialize hf x,
      apply has_deriv_at.differentiable_at,
      apply has_deriv_at.sub,
      {
        convert hf,
      },
      apply has_deriv_at.add,
      apply has_deriv_at.div_const,
      apply has_deriv_at.const_mul,
      apply has_deriv_at_pow,
      apply has_deriv_at.const_mul,
      apply has_deriv_at_pow,
    },
    intro x,
    rw deriv_sub,
    rw sub_eq_zero,
    simp,
    rw has_deriv_at.deriv,
    specialize hf x,
    ring_nf,
    rw mul_comm,
    exact hf,
    apply has_deriv_at.differentiable_at,
    apply hf,
    finish,
  },
  ext z,
  specialize h1 z 0,
  apply eq_add_of_sub_eq',
  simpa using h1,
end


theorem constant_of_has_deriv_right_zero' {E : Type u_1} [normed_add_comm_group E] [normed_space ℝ E]
  {f : ℝ → E} {a b : ℝ} (hderiv : ∀ (x : ℝ), x ∈ set.Icc a b → has_deriv_at f 0 x) (h : a ≤ b) :
  f b = f a :=
begin
  apply constant_of_has_deriv_right_zero,
  apply has_deriv_at.continuous_on hderiv,
  intros,
  apply has_deriv_at.has_deriv_within_at,
  apply hderiv x (set.mem_Icc_of_Ico H), 
  finish,
end


section vector_function
universes u_2 u_3
variables {E : Type u_2}  {𝕜 : Type u_3} [is_R_or_C 𝕜] [normed_add_comm_group E] 
[normed_space 𝕜 E]

theorem antideriv 
{f F G: 𝕜 → E} (hf : ∀ t, has_deriv_at F (f t) t)
(hg : ∀ t, has_deriv_at G (f t) t)
(hg' : G 0 = 0)
: F = λ t, G t + F(0) :=
begin
have h1: ∀(x y : 𝕜), F x - G x = F y - G y,
   { 
    apply is_const_of_deriv_eq_zero,
    {
      rw differentiable,
      intro x,
      apply has_deriv_at.differentiable_at,
      apply has_deriv_at.sub (hf x),
      apply (hg x),},
    intro x,
    rw [deriv_sub, sub_eq_zero],
    rw has_deriv_at.deriv,
    simp,
    rw has_deriv_at.deriv,
    apply hf,
    apply hg,
    apply has_deriv_at.differentiable_at (hf x),
    apply has_deriv_at.differentiable_at (hg x),
  },
  funext z,
  specialize h1 z 0,
  rw hg' at h1,
  simp at h1,
  apply eq_add_of_sub_eq' h1,  
end
lemma has_deriv_at_linear_no_pow
:
∀ x : 𝕜, has_deriv_at (λ y : 𝕜, y) 1 x
:=
begin
  intro,
  rw [show (λ y : 𝕜, y) = (λ y : 𝕜, y^1), by finish, show 1 = ↑(1:ℕ)*x^(1-1), by finish],
  apply has_deriv_at_pow 1,
end

theorem antideriv_const'
(f : 𝕜 → E) {k : E}
(hf : ∀ x, has_deriv_at f k x):
(f = λ (x : 𝕜), x•k + f 0) :=
begin
  apply antideriv hf,
  simp,
  intro,
  rw show k = (1:𝕜)•k, by simp,
  conv{
    find (_•(1:𝕜)•k) {simp,},
  },
  rw show (λ t, t•k) = λ t, ((λ t : 𝕜, t) t) • k, by {funext, simp},
  apply has_deriv_at.smul_const (has_deriv_at_linear_no_pow t) k,
  simp,
end

theorem antideriv_first_order_poly'
{k j: E}
(f : 𝕜 → E)
(hf : ∀ x:𝕜, has_deriv_at f (x•j+k) x) :
(f = λ x,(x^2/2)•j + x•k + (f 0)) :=
begin
  conv{
  find (_•k) {rw ← pow_one x,}
  },
  have h1: ∀ (x y : 𝕜), f x - ((x^2/2)•j + x^1•k)= f y - ((y^2/2)•j + y^1•k),
  { 
    apply is_const_of_deriv_eq_zero,
    {
      rw differentiable,
      intro x,
      specialize hf x,
      apply has_deriv_at.differentiable_at,
      apply has_deriv_at.sub,
      {
        convert hf,
      },
      apply has_deriv_at.add,
      apply has_deriv_at.smul_const,
      apply has_deriv_at.div_const,
      apply has_deriv_at_pow,
      apply has_deriv_at.smul_const,
      apply has_deriv_at_pow,
    },
    intro x,
    rw deriv_sub,
    rw sub_eq_zero,
    simp,
    iterate 2 {rw deriv_smul_const},
    simp,
    ring_nf,
    rw has_deriv_at.deriv,
    exact hf x,
    iterate 2 {finish},
    apply has_deriv_at.differentiable_at,
    exact hf x,
    finish,
  },
  ext z,
  specialize h1 z 0,
  apply eq_add_of_sub_eq',
  simpa using h1,

end
end vector_function

/-! ### Analytical ODE solutions-/

open set filter
open_locale topological_space

lemma mem_of_le_of_forall_exists_lt {α : Type u_1} [conditionally_complete_linear_order α] [topological_space α] [order_topology α]
{a b : α} {s : set α} (hs : is_closed (s ∩ Icc a b))
  (hb : b ∈ s) (hab : a ≤ b) (hgt : ∀ x ∈ s ∩ Ioc a b, (s ∩ Ico a x).nonempty) :
  a ∈ s :=
begin
  let S := s ∩ Icc a b,
  replace hb : b ∈ S, from ⟨hb, right_mem_Icc.2 hab⟩,
  have Sbd : bdd_below S, from ⟨a, λ z hz, hz.2.1⟩,
  let c := Inf (s ∩ Icc a b),
  have c_mem : c ∈ S, from hs.cInf_mem ⟨_, hb⟩ Sbd,
  have c_le : a ≤ c, from le_cInf ⟨_, hb⟩ (λ x hx, hx.2.1),
  cases eq_or_lt_of_le c_le with hc hc, from hc.symm ▸ c_mem.1,
  exfalso,
  rcases hgt c ⟨c_mem.1, hc, c_mem.2.2⟩ with ⟨x, xs, ax, xc⟩,
  exact not_lt_of_le (cInf_le Sbd ⟨xs, le_trans (cInf_le Sbd hb) (le_of_lt xc), ax⟩) 
end

lemma lmem_of_ge_of_forall_exists_gt {α : Type u_1} [conditionally_complete_linear_order α] [topological_space α] [order_topology α]
{a b : α} {s : set α} (hs : is_closed (s ∩ Icc a b))
  (ha : a ∈ s) (hab : a ≤ b) (hgt : ∀ x ∈ s ∩ Ico a b, (s ∩ Ioc x b).nonempty) :
  b ∈ s :=
begin
  let S := s ∩ Icc a b,
  replace ha : a ∈ S, from ⟨ha, left_mem_Icc.2 hab⟩,
  have Sbd : bdd_above S, from ⟨b, λ z hz, hz.2.2⟩,
  let c := Sup (s ∩ Icc a b),
  have c_mem : c ∈ S, from hs.cSup_mem ⟨_, ha⟩ Sbd,
  have c_le : c ≤ b, from cSup_le ⟨_, ha⟩ (λ x hx, hx.2.2),
  cases eq_or_lt_of_le c_le with hc hc, from hc ▸ c_mem.1,
  exfalso,
  rcases hgt c ⟨c_mem.1, c_mem.2.1, hc⟩ with ⟨x, xs, cx, xb⟩,
  exact not_lt_of_le (le_cSup Sbd ⟨xs, le_trans (le_cSup Sbd ha) (le_of_lt cx), xb⟩) cx
end
lemma Icc_subset_of_forall_exists_lt {α : Type u_1} [conditionally_complete_linear_order α] [topological_space α] [order_topology α]
{a b : α} {s : set α} (hs : is_closed (s ∩ Icc a b))
  (hb : b ∈ s) (hgt : ∀ x ∈ s ∩ Ioc a b, ∀ y ∈ Iio x, (s ∩ Ico x y).nonempty) :
  Icc a b ⊆ s :=
begin
  assume y hy,
  have : is_closed (s ∩ Icc y b),
  { suffices : s ∩ Icc y b = s ∩ Icc a b ∩ Icc y b,
    { rw this, apply is_closed.inter hs is_closed_Icc },
    rw [inter_assoc],
    congr,
    rw inter_comm,
    apply (inter_eq_self_of_subset_left $ Icc_subset_Icc_left hy.1).symm, },
  exact is_closed.mem_of_ge_of_forall_exists_gt this hb hy.2
    (λ x hx, hgt x ⟨hx.1, Ico_subset_Ico_right hy.2 hx.2⟩ y hx.2.2)
end

lemma image_le_of_liminf_slope_left_lt_deriv_boundary' {f f' : ℝ → ℝ} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  -- `hf'` actually says `liminf (f z - f x) / (z - x) ≤ f' x`
  (hf' : ∀ x ∈ Ioc a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r)
  {B B' : ℝ → ℝ} (hb : f b ≤ B b) (hB : continuous_on B (Icc a b))
  (hB' : ∀ x ∈ Ioc a b, has_deriv_within_at B (B' x) (Iic x) x)
  (bound : ∀ x ∈ Ioc a b, f x = B x → f' x < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
begin
  change Icc a b ⊆ {x | f x ≤ B x},
  set s := {x | f x ≤ B x} ∩ Icc a b,
  have A : continuous_on (λ x, (f x, B x)) (Icc a b), from hf.prod hB,
  have : is_closed s,
  { simp only [s, inter_comm],
    exact A.preimage_closed_of_closed is_closed_Icc order_closed_topology.is_closed_le' },
  apply this.Icc_subset_of_forall_exists_gt,
  rintros x ⟨hxB : f x ≤ B x, xab⟩ y hy,
  cases hxB.lt_or_eq with hxB hxB,
  { -- If `f x < B x`, then all we need is continuity of both sides
    refine nonempty_of_mem (inter_mem _ (Ioc_mem_nhds_within_Ioi ⟨le_rfl, hy⟩)),
    have : ∀ᶠ x in 𝓝[Icc a b] x, f x < B x,
      from A x (Ico_subset_Icc_self xab)
        (is_open.mem_nhds (is_open_lt continuous_fst continuous_snd) hxB),
    have : ∀ᶠ x in 𝓝[>] x, f x < B x,
      from nhds_within_le_of_mem (Icc_mem_nhds_within_Ioi xab) this,
    exact this.mono (λ y, le_of_lt) },
  { rcases exists_between (bound x xab hxB) with ⟨r, hfr, hrB⟩,
    specialize hf' x xab r hfr,
    have HB : ∀ᶠ z in 𝓝[>] x, r < slope B x z,
      from (has_deriv_within_at_iff_tendsto_slope' $ lt_irrefl x).1
        (hB' x xab).Ioi_of_Ici (Ioi_mem_nhds hrB),
    obtain ⟨z, hfz, hzB, hz⟩ :
      ∃ z, slope f x z < r ∧ r < slope B x z ∧ z ∈ Ioc x y,
      from (hf'.and_eventually (HB.and (Ioc_mem_nhds_within_Ioi ⟨le_rfl, hy⟩))).exists,
    refine ⟨z, _, hz⟩,
    have := (hfz.trans hzB).le,
    rwa [slope_def_field, slope_def_field, div_le_div_right (sub_pos.2 hz.1), hxB,
      sub_le_sub_iff_right] at this }
end

lemma image_le_of_liminf_slope_left_le_deriv_boundary {f : ℝ → ℝ} {a b : ℝ} (hf : continuous_on f (set.Icc a b)) 
{B B' : ℝ → ℝ} (ha : f b ≤ B b) (hB : continuous_on B (set.Icc a b)) 
(hB' : ∀ (x : ℝ), x ∈ set.Ioc a b → has_deriv_within_at B (B' x) (set.Iic x) x) 
(bound : ∀ (x : ℝ), x ∈ set.Ioc a b → ∀ (r : ℝ), B' x < r → (∃ᶠ (z : ℝ) in nhds_within x (set.Iio x), slope f x z < r)) 
⦃x : ℝ⦄ :
x ∈ set.Icc a b → f x ≤ B x :=
begin
  have Hr : ∀ x ∈ Icc a b, ∀ r > 0, f x ≤ B x + r * (x - b),
  { intros x hx r hr,
    apply image_le_of_liminf_slope_right_lt_deriv_boundary' hf bound,
    { rwa [sub_self, mul_zero, add_zero] },
    { exact hB.add (continuous_on_const.mul
        (continuous_id.continuous_on.sub continuous_on_const)) },
    { assume x hx,
      exact (hB' x hx).add (((has_deriv_within_at_id x (Ici x)).sub_const a).const_mul r) },
    { assume x hx _,
      rw [mul_one],
      exact (lt_add_iff_pos_right _).2 hr },
    exact hx },
  assume x hx,
  have : continuous_within_at (λ r, B x + r * (x - a)) (Ioi 0) 0,
    from continuous_within_at_const.add (continuous_within_at_id.mul continuous_within_at_const),
  convert continuous_within_at_const.closure_le _ this (Hr x hx); simp
end

lemma image_norm_le_of_norm_deriv_left_le_deriv_boundary' 
{E : Type u_1} [normed_add_comm_group E] [normed_space ℝ E]
{f : ℝ → E} {a b : ℝ} {f' : ℝ → E}
(hf : continuous_on f (Icc a b))
(hf' : ∀ x ∈ Ioc a b, has_deriv_within_at f (- f' x) (Iic x) x)
{B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a) (hB : continuous_on B (Icc a b))
(hB' : ∀ x ∈ Ioc a b, has_deriv_within_at B (B' x) (Iic x) x)
(bound : ∀ x ∈ Ioc a b, ∥f' x∥ ≤ B' x) :
∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
image_le_of_liminf_slope_right_le_deriv_boundary (continuous_norm.comp_continuous_on hf) ha hB hB' $
  (λ x hx r hr, (hf' x hx).liminf_right_slope_norm_le (lt_of_le_of_lt (bound x hx) hr))

theorem image_norm_le_of_norm_deriv_left_le_deriv_boundary 
{E : Type u_1} [normed_add_comm_group E] [normed_space ℝ E]
{f : ℝ → E} {a b : ℝ}{f' : ℝ → E}
(hf : continuous_on f (Icc a b))
(hf' : ∀ x ∈ Ioc a b, has_deriv_within_at f (-f' x) (Iic x) x)
{B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a) (hB : ∀ x, has_deriv_at B (B' x) x)
(bound : ∀ x ∈ Ioc a b, ∥f' x∥ ≤ B' x) :
∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
image_norm_le_of_norm_deriv_right_le_deriv_boundary' hf hf' ha
  (λ x hx, (hB x).continuous_at.continuous_within_at)
  (λ x hx, (hB x).has_deriv_within_at) bound

theorem norm_image_sub_le_of_norm_deriv_left_le_segment 
{E : Type u_1} [normed_add_comm_group E] [normed_space ℝ E]
{f : ℝ → E} {a b : ℝ} {f' : ℝ → E} {C : ℝ}
(hf : continuous_on f (set.Icc a b))
(hf' : ∀ x ∈ set.Ioc a b, has_deriv_within_at f (f' x) (set.Iic x) x)
(bound : ∀x ∈ set.Ioc a b, ∥f' x∥ ≤ C) :
∀ x ∈ set.Icc a b, ∥f b - f x∥ ≤ C * (b - x) :=
begin
  let g := λ x, f b - f x,
  have hg : continuous_on g (set.Icc a b),
  { assume x hx,
    simp [g],
    apply continuous_on.sub (continuous_on_const) hf x hx,},
  have hg' : ∀ x ∈ set.Ioc a b, has_deriv_within_at g (- f' x) (set.Iic x) x,
  { assume x hx,
    simp [g, ← zero_sub],
    apply has_deriv_within_at.sub (has_deriv_within_at_const _ _ _) (hf' x hx),},
  let B := λ x, C * (b - x),
  have hB : ∀ x, has_deriv_at B (- C) x,
  { assume x,
    simpa using (has_deriv_at_const x C).mul ((has_deriv_at_const x b).sub (has_deriv_at_id x))
     },
  convert image_norm_le_of_norm_deriv_right_le_deriv_boundary hg hg' _ hB bound,
  simp only [g, B], rw [sub_self, norm_zero, sub_self, mul_zero]
end
theorem constant_of_has_deriv_left_zero
{E : Type u_1} [normed_add_comm_group E] [normed_space ℝ E] 
{f : ℝ → E} {a b : ℝ} (hcont : continuous_on f (set.Icc a b))
(hderiv : ∀ x ∈ set.Ioc a b, has_deriv_within_at f 0 (set.Iic x) x) :
∀ x ∈ set.Icc a b, f x = f b :=
-- by simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using
--   λ x hx, norm_image_sub_le_of_norm_deriv_left_le_segment
--     hcont hderiv (λ y hy, by rw norm_le_zero_iff) x hx
begin
  assume x hx,
  simpa only [← zero_mul, norm_le_zero_iff, sub_eq_zero] using
  norm_image_sub_le_of_norm_deriv_left_le_segment hcont hderiv (λ y hy, by rw norm_le_zero_iff) x hx
end
theorem antideriv_self
{k: ℝ}
(f : ℝ → ℝ)
(hf : ∀ x, has_deriv_at f (k*(f x)) x) :
(f = λ x, (f 0)*real.exp(k*x)) :=
begin
  have : ∀ x, has_deriv_at (λ x, real.exp (- k * x) * f x) 0 x,
  { intros x,
    convert (has_deriv_at_mul_const k).neg.exp.mul (hf x),
    { ext x,
      ring_nf },
    { ring_nf } },
  ext x,
  have hx : x ≤ 0 ∨ 0 ≤ x := by exact le_total x 0,
  cases hx with hx hx',
  swap,
  have : real.exp (-k * x) * f x = f 0,
  { convert @constant_of_has_deriv_right_zero _ _ _ _ 0 x _ (λ y hy, (this y).has_deriv_within_at) x _,
    { simp },
    { intros x hx,
      exact (this x).continuous_at.continuous_within_at },
    { rw set.right_mem_Icc,
      exact hx' } },
  convert congr_arg ((*) (real.exp (k * x))) this using 1,
  { rw [← mul_assoc, ← real.exp_add],
    ring_nf,
    simp, },
  { ring, },
  have : real.exp (-k * x) * f x = f 0,
  { convert @constant_of_has_deriv_right_zero' _ _ _ _ x 0 _ (λ y hy, (this y).has_deriv_within_at) x _,
    { simp },
    { intros x hx,
      exact (this x).continuous_at.continuous_within_at },
    { rw set.right_mem_Icc,
      exact hx' } },

end
