/-We define Phase space as the cotangent bundle of configuration space-/

import geometry.manifold.tangent_bundle

open_locale big_operators

/-This defines a smooth manifold. A closed smooth manifold is a smooth manifold that is compact and without a boundary.
To define a manifold without a boundary, we need I.boundaryless. To define the manifold as compact, we need -/
universes u_1 u_2 u_3 
variables {E : Type u_1} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E] 
{I : model_with_corners ℝ E E} {X : Type u_2} [topological_space X] [charted_space E X] 
[smooth_manifold_with_corners I X] 
{ n m b : ℕ }
local notation `Xⁿ` := 
#check [m,n,b]
def configuration_space_ordered [I.boundaryless] [is_compact s]:=

