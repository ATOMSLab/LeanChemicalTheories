-- import analysis.inner_product_space.basic
-- import analysis.inner_product_space.pi_L2

-- import geometry.manifold.tangent_bundle
-- open_locale big_operators
-- noncomputable theory

-- constant f : ℝ → euclidean_space ℝ (fin 4)
-- variables {x : ℝ} {i : (fin 4)} {n : ℕ}
-- #check ![1, 2, 3, 4]


-- variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E] 
-- {I : model_with_corners ℝ E E}  {M : Type*} [topological_space M] [charted_space E M] 
-- [smooth_manifold_with_corners I M] {q : M} [inner_product_space ℝ E]


-- variables {n : ℕ} {velocity : } {mass : vector ℝ n}
-- local notation `𝕧` := velocity
-- local notation `v²` := has_inner.inner (𝕧 (fin n)) (𝕧 (fin n))

-- #check velocity 
-- #check 𝕧
-- #check v²

-- def kinetic_energy : ℕ → ℝ:= λ i, 
-- def total_kinetic_energy : ℝ := finsum kinetic_energy
-- def potential_energy := ℝ 

-- local notation `T` := total_kinetic_energy
-- local notation `V` := potential_energy



