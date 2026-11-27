import OMAReductions.R_Green37_green_37_lower_bound_R1

-- Step H2 of reduction Green37.green_37_lower_bound.R1
-- Credit: @estebanlearns
-- Proves length monotonicity of minimum AP-cover size: k₁ ≤ k₂ → Green37.m N k₁ ≤ Green37.m N k₂.

/-!
# Step H2 of Reduction Green37.green_37_lower_bound.R1
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

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H2 := by
  intro N k₁ k₂ hk
  obtain ⟨A, hcard, hcov₂⟩ := Nat.sInf_mem (ap_cover_set_nonempty N k₂)
  have hcard' : A.card = Green37.m N k₂ := hcard
  change Green37.m N k₁ ≤ Green37.m N k₂
  rw [← hcard']
  apply Nat.sInf_le
  refine ⟨A, rfl, ?_⟩
  intro d hd
  obtain ⟨a, s₂, hs₂A, _, hs₂_eq⟩ := hcov₂ d hd
  refine ⟨a, ((Finset.range k₁).image (fun i : ℕ => a + i • d) : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi₁ : i < k₁ := Finset.mem_range.mp hi
    have hi₂ : (i : ℕ∞) < (k₂ : ℕ∞) := by
      exact_mod_cast lt_of_lt_of_le hi₁ hk
    have hmem₂ : a + i • d ∈ s₂ := by
      rw [hs₂_eq]
      exact ⟨i, hi₂, rfl⟩
    exact hs₂A hmem₂
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _
        (fun x y h => by
          rw [nsmul_eq_mul, nsmul_eq_mul] at h
          exact Nat.eq_of_mul_eq_mul_right hd.1 (add_left_cancel h)),
      Finset.card_range]
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i, by exact_mod_cast Finset.mem_range.mp hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by exact_mod_cast hi), rfl⟩)
