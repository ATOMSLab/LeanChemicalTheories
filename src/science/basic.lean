import linear_algebra.basis
import data.real.basic



noncomputable theory

structure metrology.measure :=
(relation : ∀ v w : ℝ, ∃! r, v ≠ 0 → w ≠ 0 → v*r = w)

-- variables (E : Type*) [field E] [decidable_eq E]
-- @[derive has_mul, derive decidable_eq, derive has_add, derive has_sub, derive has_one]
-- def science_unit2 (α : Type*):= monoid_algebra E (dimension α)
