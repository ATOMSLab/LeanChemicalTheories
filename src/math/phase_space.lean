/-We define Phase space as the cotangent bundle of configuration space-/

import geometry.manifold.tangent_bundle

open_locale big_operators

variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E] 
{I : model_with_corners ℝ E E}  (M : Type*) [topological_space M] [charted_space E M] 
[smooth_manifold_with_corners I M] {x : M}

def configuration_space := M

#check configuration_space 

