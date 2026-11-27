import FormalConjectures.GreensOpenProblems.«37»

-- Reduction Green37.green_37_lower_bound.R1 of Ben Green's Open Problem 37 — green 37 lower bound
-- Credit: @estebanlearns
-- Reduces the asymptotic sequence/Big-O formulation to:
--   H1: Finitary uniform polynomial AP-cover lower bound at rational exponents 1 - 1/(n+1) (Green-Ruzsa / Katz-Tao core)
--   H2: Positivity and length-monotonicity of the minimum AP-cover size Green37.m N k

/-!
# Reduction Green37.green_37_lower_bound.R1
-/

namespace OMA.R_Green37_green_37_lower_bound_R1

open Filter Finset Real
open scoped Asymptotics

def H1 : Prop :=
  ∀ n : ℕ, ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 1 ≤ N → C * (N : ℝ) ^ (1 - (1 : ℝ) / ((n : ℝ) + 1)) ≤ (Green37.m N K : ℝ)

def H2 : Prop :=
  (∀ N : ℕ, 1 ≤ N → ∀ k : ℕ, 1 ≤ k → 1 ≤ Green37.m N k) ∧
  (∀ N k₁ k₂ : ℕ, k₁ ≤ k₂ → Green37.m N k₁ ≤ Green37.m N k₂)

lemma exists_inv_succ_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  refine ⟨n, ?_⟩
  set D : ℝ := (n : ℝ) + 1
  have hD_pos : 0 < D := by positivity
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  have hnD : 1 / ε < D := by linarith
  have h1 : ε * (1 / ε) < ε * D := mul_lt_mul_of_pos_left hnD hε
  have h2 : ε * (1 / ε) = 1 := by field_simp [hε_ne]
  have hD_inv : 0 < (1 : ℝ) / D := by positivity
  have h3 : 1 * ((1 : ℝ) / D) < (ε * D) * ((1 : ℝ) / D) :=
    mul_lt_mul_of_pos_right (by linarith) hD_inv
  have h4 : (ε * D) * ((1 : ℝ) / D) = ε := by field_simp [hD_ne]
  linarith

lemma inv_le_inv_of_pos_le {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    (1 : ℝ) / B ≤ (1 : ℝ) / A := by
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  have hA_ne : A ≠ 0 := ne_of_gt hA
  have hB_ne : B ≠ 0 := ne_of_gt hB
  have hA_inv : 0 ≤ (1 : ℝ) / A := by positivity
  have hB_inv : 0 ≤ (1 : ℝ) / B := by positivity
  have h1 : ((1 : ℝ) / A) * A ≤ ((1 : ℝ) / A) * B := mul_le_mul_of_nonneg_left hAB hA_inv
  have h2 : ((1 : ℝ) / A) * A = 1 := by field_simp [hA_ne]
  have h3 : 1 * ((1 : ℝ) / B) ≤ (((1 : ℝ) / A) * B) * ((1 : ℝ) / B) :=
    mul_le_mul_of_nonneg_right (by linarith) hB_inv
  have h4 : (((1 : ℝ) / A) * B) * ((1 : ℝ) / B) = (1 : ℝ) / A := by field_simp [hB_ne]
  linarith

theorem main : H1 → H2 → type_of% @Green37.green_37_lower_bound := by
  intro h1 h2
  classical
  let P : ℕ → ℕ → Prop := fun k n =>
    (fun N : ℕ => (N : ℝ) ^ (1 - (1 : ℝ) / ((n : ℝ) + 1))) =O[atTop]
      fun N => (Green37.m N k : ℝ)
  let S : ℕ → Finset ℕ := fun k => (Finset.range k).filter (fun n => P k n)
  let c : ℕ → ℝ := fun k =>
    if hne : (S k).Nonempty then
      (1 : ℝ) / ((((S k).max' hne : ℕ) : ℝ) + 1)
    else
      1
  refine ⟨c, ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := exists_inv_succ_lt hε
    obtain ⟨K₀, _, C₀, hC₀_pos, hC₀_bound⟩ := h1 n₀
    refine ⟨max (K₀ + 1) (n₀ + 1), fun k hk => ?_⟩
    have hkK : K₀ ≤ k := by omega
    have hnk : n₀ < k := by omega
    have hPk : P k n₀ := by
      dsimp only [P]
      rw [Asymptotics.isBigO_iff]
      refine ⟨1 / C₀, eventually_atTop.mpr ⟨1, fun N hN => ?_⟩⟩
      have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) ^ (1 - (1 : ℝ) / ((n₀ : ℝ) + 1)) :=
        Real.rpow_nonneg (Nat.cast_nonneg N) _
      have hm_mono : (Green37.m N K₀ : ℝ) ≤ (Green37.m N k : ℝ) :=
        Nat.cast_le.mpr (h2.2 N K₀ k hkK)
      have h_step : C₀ * (N : ℝ) ^ (1 - (1 : ℝ) / ((n₀ : ℝ) + 1)) ≤ (Green37.m N k : ℝ) :=
        le_trans (hC₀_bound N hN) hm_mono
      have hm_nonneg : (0 : ℝ) ≤ (Green37.m N k : ℝ) := Nat.cast_nonneg _
      rw [Real.norm_of_nonneg hN_nonneg, Real.norm_of_nonneg hm_nonneg]
      have hC₀_ne : C₀ ≠ 0 := ne_of_gt hC₀_pos
      have hC₀_inv_nonneg : 0 ≤ (1 : ℝ) / C₀ := by positivity
      have hmul : ((1 : ℝ) / C₀) * (C₀ * (N : ℝ) ^ (1 - (1 : ℝ) / ((n₀ : ℝ) + 1))) ≤
          ((1 : ℝ) / C₀) * (Green37.m N k : ℝ) :=
        mul_le_mul_of_nonneg_left h_step hC₀_inv_nonneg
      have hcancel : ((1 : ℝ) / C₀) * (C₀ * (N : ℝ) ^ (1 - (1 : ℝ) / ((n₀ : ℝ) + 1))) =
          (N : ℝ) ^ (1 - (1 : ℝ) / ((n₀ : ℝ) + 1)) := by
        field_simp [hC₀_ne]
      linarith
    have hmem : n₀ ∈ S k := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnk, hPk⟩
    have hne : (S k).Nonempty := ⟨n₀, hmem⟩
    have hmax_ge : n₀ ≤ (S k).max' hne := Finset.le_max' (S k) n₀ hmem
    have hc_eq : c k = (1 : ℝ) / ((((S k).max' hne : ℕ) : ℝ) + 1) := dif_pos hne
    have hc_pos : 0 < c k := by
      rw [hc_eq]
      positivity
    have hc_le : c k ≤ (1 : ℝ) / ((n₀ : ℝ) + 1) := by
      rw [hc_eq]
      have hcast : (n₀ : ℝ) + 1 ≤ (((S k).max' hne : ℕ) : ℝ) + 1 := by
        have h0 : (n₀ : ℝ) ≤ (((S k).max' hne : ℕ) : ℝ) := Nat.cast_le.mpr hmax_ge
        linarith
      exact inv_le_inv_of_pos_le (by positivity) hcast
    rw [Real.dist_eq, sub_zero, abs_of_pos hc_pos]
    exact lt_of_le_of_lt hc_le hn₀
  · intro k hk
    by_cases hne : (S k).Nonempty
    · have hc_eq : c k = (1 : ℝ) / ((((S k).max' hne : ℕ) : ℝ) + 1) := dif_pos hne
      have hmax_mem : (S k).max' hne ∈ S k := Finset.max'_mem (S k) hne
      have hPmax : P k ((S k).max' hne) := (Finset.mem_filter.mp hmax_mem).2
      change (fun N : ℕ => (N : ℝ) ^ (1 - c k)) =O[atTop] fun N => (Green37.m N k : ℝ)
      rw [hc_eq]
      exact hPmax
    · have hc_eq : c k = 1 := dif_neg hne
      change (fun N : ℕ => (N : ℝ) ^ (1 - c k)) =O[atTop] fun N => (Green37.m N k : ℝ)
      rw [hc_eq, sub_self, Asymptotics.isBigO_iff]
      refine ⟨1, eventually_atTop.mpr ⟨1, fun N hN => ?_⟩⟩
      have hm_ge : (1 : ℝ) ≤ (Green37.m N k : ℝ) := by exact_mod_cast h2.1 N hN k hk
      have hm_nonneg : (0 : ℝ) ≤ (Green37.m N k : ℝ) := Nat.cast_nonneg _
      rw [Real.rpow_zero, norm_one, Real.norm_of_nonneg hm_nonneg, one_mul]
      exact hm_ge

end OMA.R_Green37_green_37_lower_bound_R1
