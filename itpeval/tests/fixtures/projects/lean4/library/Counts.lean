import Init

namespace Counts

/-- The index following the current one. -/
def nextIndex (n : Nat) : Nat := n + 1

theorem next_index_zero : nextIndex 0 = 1 := rfl

end Counts
