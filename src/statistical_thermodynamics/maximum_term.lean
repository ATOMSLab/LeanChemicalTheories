import algebra.big_operators.order
import tactic.ring


open_locale big_operators


theorem finset.mem_le_pos_sum {α : Type*} {β : Type*} [linear_ordered_add_comm_group β] (f : α → β) (s : finset α) (h1 : ∀ x, x ∈ s → 0 < f x) 
:  ∀ y (H : y ∈ s), f y ≤ ∑ x in s, f x :=
begin
  apply finset.single_le_sum,
  intros x h,
  apply le_of_lt (h1 x h),

end
