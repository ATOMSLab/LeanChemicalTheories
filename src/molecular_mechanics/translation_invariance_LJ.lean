import analysis.normed.group.basic
import analysis.normed_space.basic
variables {n: ℕ }
local notation `ℝ^n ` := fin (n) → ℝ

/-!
# Translation invariance of Lennard-Jones potential
This section defines the translation invariance of Lennard-Jonnes potential function that describes the intermolecular
pair potentials in molecular simulations. The commonly used expression is: <br>
$$
E = 4ε [(\frac{σ}{r})^12 - (\frac{σ}{r})^6]
$$
where:
- `E` is the intermolecular potential between the two atoms or molecules
- `ε` is the well depth and a measure of how strongly the two particles attract each other
- `σ` is the distance at which the intermolecular potential between the two particles is zero
- `r` is the distance of separation between both particles

Here we show that if we translate all the coordinates equally - the molecule is not changing conformations and hence the energy
does not change. Using pairwise disntace removes the choice of origin and makes the model translational invariant.

### Assumption
The pairwise distance is given by Euclidean distance or `L^2` norm where `x` and `y`
are the coordinates of the two vectors representing molecular positions.

### To-Do
- Proof rotational invariance of the Lennard-Jones function
- Generalize proof from properties of system using fundamental theorems of invariant theory
-/


lemma LJ_invariance (x y t : ℝ^n) (r rt a b E Et: ℝ)
( a1: r = dist x y) -- Distance
( a2: rt = dist (x+t) (y+t)  ) -- Distance after translation
( a3: E = a/r^12 - b/r^6 ) -- Engery
( a4: Et = a/rt^12 - b/rt^6 ) -- Energy after translation
:
E = Et -- Conjecture
:=
begin
  simp at a2,
  rw a2 at a4,
  rw a1 at a3,
  exact (rfl.congr (eq.symm a4)).mp a3,
end
