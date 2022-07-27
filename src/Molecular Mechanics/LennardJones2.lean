import data.real.basic
import analysis.normed_space.basic


def position := (ℝ × ℝ × ℝ)
def momentum := (ℝ × ℝ × ℝ)
def phase_space_one_particle := (position × momentum)
variables (p : phase_space_one_particle) [normed_group position] [normed_group momentum]

#check has_dist.dist p.fst 0
def translate_coordinates : :=