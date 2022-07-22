import analysis.normed_space.basic
import geometry.manifold.tangent_bundle
import linear_algebra.dual


--Local imports
import math.deriv

/-We define the Lennard Jones potential to take in an ε, the
minimum energy constant, a minRadius, the radius where the function
has a minimum, and r, the radius between the two particles which is a vector.
We first show that LJ has a local minimum at minRadius. We then
show that LJ is translationally invaraint on a general
vector space, E-/
universes u_1 u_2 u_3 u_4
variables {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] 
[normed_space 𝕜 E] {H : Type u_3}  [topological_space H] (I : model_with_corners 𝕜 E H) 
{M : Type u_4} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (x : M) 

section Symplectic_Vector_Space

structure symplectic_vector_space :=
(ω : E × E → 𝕜)
(alternating : ∀ v : E, function.curry ω v v = 0)
(nondegenerate : ∀ v : E, function.curry ω v 0 = 0)

section end

section Phase_Space

def cotangent_space := module.dual 𝕜 (tangent_space I x)

def cotangent_bundle := bundle.total_space (cotangent_space I : M → Type*)

#check cotangent_space I x
#check cotangent_bundle I
structure phase_space := 
(position : M)
(momentum : cotangent_space I x)







section end 
variable (n:ℕ)
local notation `ℝⁿ` := fin n → ℝ
variables  [group ℝⁿ] [nonempty ℝⁿ] [add_action.is_pretransitive ℝⁿ ℝⁿ]

def position_translation_group_action (PS : fin n → (ℝⁿ × ℝⁿ)): := 



