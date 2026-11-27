import FormalConjectures.GreensOpenProblems.«37»

-- Reduction Green37.green_37_lower_bound.R1 of Ben Green's Open Problem 37 — green 37 lower bound
-- Credit: @estebanlearns
-- Reduces the asymptotic sequence / Big-O conjecture into three purely finitary, non-redundant statements in ℕ:
--   H1: Pure ℕ polynomial lower bound N^n ≤ m(N, K)^(n + 1) for n ≥ 2 (exponents ≥ 2/3, the open regime)
--   H2: Monotonicity of minimum AP-cover cardinality Green37.m N k in progression length k
--   H3: Exact base-level bounds at k = 1 (positivity) and k = 2 (sharp Rédei-Rényi / Golomb bound 2N ≤ m(N,2)(m(N,2)-1))

/-!
# Reduction Green37.green_37_lower_bound.R1
-/

namespace OMA.R_Green37_green_37_lower_bound_R1

open Filter Finset Real
open scoped Asymptotics

def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ K : ℕ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    N ^ n ≤ Green37.m N K ^ (n + 1)

def H2 : Prop :=
  ∀ N k₁ k₂ : ℕ, k₁ ≤ k₂ → Green37.m N k₁ ≤ Green37.m N k₂

def H3 : Prop :=
  (∀ N : ℕ, 1 ≤ N → 1 ≤ Green37.m N 1) ∧
  (∀ N : ℕ, 2 * N ≤ Green37.m N 2 * (Green37.m N 2 - 1))

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

lemma nat_pow_le_pow {a b : ℕ} (hab : a ≤ b) : ∀ m : ℕ, a ^ m ≤ b ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
    have h1 : a ^ (k + 1) = a ^ k * a := by ring
    have h2 : b ^ (k + 1) = b ^ k * b := by ring
    rw [h1, h2]
    exact Nat.mul_le_mul ih hab

lemma pow_lt_pow_succ_of_lt {x y : ℝ} (hy : 0 ≤ y) (hlt : y < x) :
    ∀ n : ℕ, y ^ (n + 1) < x ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    simp only [Nat.zero_add, pow_one]
    exact hlt
  | succ k ih =>
    have hx_pos : 0 < x := lt_of_le_of_lt hy hlt
    have hyk_nonneg : 0 ≤ y ^ (k + 1) := pow_nonneg hy (k + 1)
    have hstep1 : y ^ (k + 1) * y ≤ y ^ (k + 1) * x :=
      mul_le_mul_of_nonneg_left (le_of_lt hlt) hyk_nonneg
    have hstep2 : y ^ (k + 1) * x < x ^ (k + 1) * x :=
      mul_lt_mul_of_pos_right ih hx_pos
    have hp1 : y ^ (k + 1 + 1) = y ^ (k + 1) * y := by ring
    have hp2 : x ^ (k + 1 + 1) = x ^ (k + 1) * x := by ring
    rw [hp1, hp2]
    exact lt_of_le_of_lt hstep1 hstep2

lemma rpow_le_of_pow_le {N m n : ℕ} (hpow : N ^ n ≤ m ^ (n + 1)) :
    (N : ℝ) ^ (1 - (1 : ℝ) / ((n : ℝ) + 1)) ≤ (m : ℝ) := by
  set x : ℝ := (N : ℝ) ^ (1 - (1 : ℝ) / ((n : ℝ) + 1))
  have hy : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hD_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hD_ne : (n : ℝ) + 1 ≠ 0 := ne_of_gt hD_pos
  have hexp : (1 - (1 : ℝ) / ((n : ℝ) + 1)) * (((n + 1 : ℕ) : ℝ)) = (n : ℝ) := by
    push_cast
    field_simp [hD_ne]
    ring
  have hx_pow : x ^ (n + 1) = (N : ℝ) ^ n := by
    dsimp only [x]
    rw [← Real.rpow_natCast _ (n + 1), ← Real.rpow_mul hN, hexp, Real.rpow_natCast]
  have hcast : (N : ℝ) ^ n ≤ (m : ℝ) ^ (n + 1) := by
    exact_mod_cast hpow
  have hxy_pow : x ^ (n + 1) ≤ (m : ℝ) ^ (n + 1) := by
    rw [hx_pow]
    exact hcast
  by_contra hnot
  have hlt : (m : ℝ) < x := not_le.mp hnot
  have hlt_pow : (m : ℝ) ^ (n + 1) < x ^ (n + 1) := pow_lt_pow_succ_of_lt hy hlt n
  linarith

lemma isBigO_of_pow_bound {k n N₀ : ℕ}
    (hbound : ∀ N : ℕ, N₀ ≤ N → N ^ n ≤ Green37.m N k ^ (n + 1)) :
    (fun N : ℕ => (N : ℝ) ^ (1 - (1 : ℝ) / ((n : ℝ) + 1))) =O[atTop]
      fun N => (Green37.m N k : ℝ) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, eventually_atTop.mpr ⟨N₀, fun N hN => ?_⟩⟩
  have hle : (N : ℝ) ^ (1 - (1 : ℝ) / ((n : ℝ) + 1)) ≤ (Green37.m N k : ℝ) :=
    rpow_le_of_pow_le (hbound N hN)
  have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) ^ (1 - (1 : ℝ) / ((n : ℝ) + 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hm_nonneg : (0 : ℝ) ≤ (Green37.m N k : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_of_nonneg hN_nonneg, Real.norm_of_nonneg hm_nonneg, one_mul]
  exact hle

theorem main : H1 → H2 → H3 → type_of% @Green37.green_37_lower_bound := by
  intro h1 h2 h3
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
    set n₁ : ℕ := max n₀ 2
    have hn₁_ge : 2 ≤ n₁ := le_max_right n₀ 2
    have hn₀_le : n₀ ≤ n₁ := le_max_left n₀ 2
    obtain ⟨K₀, _, N₀, hN₀_bound⟩ := h1 n₁ hn₁_ge
    refine ⟨max (K₀ + 1) (n₁ + 1), fun k hk => ?_⟩
    have hkK : K₀ ≤ k := by omega
    have hnk : n₁ < k := by omega
    have hPk : P k n₁ := by
      refine isBigO_of_pow_bound (N₀ := N₀) (fun N hN => ?_)
      exact le_trans (hN₀_bound N hN) (nat_pow_le_pow (h2 N K₀ k hkK) (n₁ + 1))
    have hmem : n₁ ∈ S k := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnk, hPk⟩
    have hne : (S k).Nonempty := ⟨n₁, hmem⟩
    have hmax_ge : n₀ ≤ (S k).max' hne := le_trans hn₀_le (Finset.le_max' (S k) n₁ hmem)
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
    have hne : (S k).Nonempty := by
      by_cases hk2 : 2 ≤ k
      · refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
        refine isBigO_of_pow_bound (N₀ := 0) (fun N _ => ?_)
        change N ^ 1 ≤ Green37.m N k ^ 2
        rw [pow_one]
        have h1_le : N ≤ 2 * N := by omega
        have h_golomb : 2 * N ≤ Green37.m N 2 * (Green37.m N 2 - 1) := h3.2 N
        have h_sq2 : Green37.m N 2 * (Green37.m N 2 - 1) ≤ Green37.m N 2 * Green37.m N 2 :=
          Nat.mul_le_mul_left (Green37.m N 2) (Nat.sub_le (Green37.m N 2) 1)
        have h_mono : Green37.m N 2 ≤ Green37.m N k := h2 N 2 k hk2
        have h_sqk : Green37.m N 2 * Green37.m N 2 ≤ Green37.m N k ^ 2 := by
          have hpow2 : Green37.m N 2 * Green37.m N 2 = Green37.m N 2 ^ 2 := by ring
          rw [hpow2]
          exact nat_pow_le_pow h_mono 2
        exact le_trans h1_le (le_trans h_golomb (le_trans h_sq2 h_sqk))
      · have hk1 : k = 1 := by omega
        subst hk1
        refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
        refine isBigO_of_pow_bound (N₀ := 1) (fun N hN => ?_)
        have h_pos : 1 ≤ Green37.m N 1 := h3.1 N hN
        simpa using h_pos
    have hc_eq : c k = (1 : ℝ) / ((((S k).max' hne : ℕ) : ℝ) + 1) := dif_pos hne
    have hmax_mem : (S k).max' hne ∈ S k := Finset.max'_mem (S k) hne
    have hPmax : P k ((S k).max' hne) := (Finset.mem_filter.mp hmax_mem).2
    change (fun N : ℕ => (N : ℝ) ^ (1 - c k)) =O[atTop] fun N => (Green37.m N k : ℝ)
    rw [hc_eq]
    exact hPmax

end OMA.R_Green37_green_37_lower_bound_R1
