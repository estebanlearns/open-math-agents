import OMAReductions.R_Green37_green_37_lower_bound_R1_H1_R1
import Mathlib.NumberTheory.Bertrand

-- Step H3 of reduction Green37.green_37_lower_bound.R1.H1.R1
-- Credit: @estebanlearns
-- Proves N-scale monotonicity of Green37.m and Bertrand prime-scale bridging (p ∈ [N/2, N]).

/-!
# Step H3 of Reduction Green37.green_37_lower_bound.R1.H1.R1
-/

lemma ap_cover_range (N k : ℕ) :
    Green37.IsAPCover ((Finset.range (k * N + 1) : Finset ℕ) : Set ℕ) N k := by
  intro d hd
  refine ⟨0, ((Finset.range k).image (fun i => i * d) : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢
    exact Nat.lt_succ_of_le (Nat.mul_le_mul (Nat.le_of_lt hi) hd.2)
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _
        (fun _ _ h => Nat.eq_of_mul_eq_mul_right hd.1 h), Finset.card_range]
  · ext x
    simp

lemma ap_cover_set_nonempty (N k : ℕ) :
    { m : ℕ | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k }.Nonempty :=
  ⟨(Finset.range (k * N + 1)).card, Finset.range (k * N + 1), rfl, ap_cover_range N k⟩

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1_H1_R1.H3 := by
  refine ⟨?_, ?_⟩
  · intro N₁ N₂ k hN
    obtain ⟨A, hcard, hcov₂⟩ := Nat.sInf_mem (ap_cover_set_nonempty N₂ k)
    have hcard' : A.card = Green37.m N₂ k := hcard
    change Green37.m N₁ k ≤ Green37.m N₂ k
    rw [← hcard']
    apply Nat.sInf_le
    refine ⟨A, rfl, ?_⟩
    intro d hd
    exact hcov₂ d ⟨hd.1, le_trans hd.2 hN⟩
  · intro N hN
    have hpos : N / 2 ≠ 0 := by omega
    obtain ⟨p, hp_prime, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 2) hpos
    exact ⟨p, hp_prime, by omega, by omega⟩
