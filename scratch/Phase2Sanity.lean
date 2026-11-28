import Mathlib

-- Sanity check for the fork-only scratch compiler (Phase 2).
theorem phase2_sanity (a b : ℕ) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left h 2

#print axioms phase2_sanity
