import OMAReductions.R_Green37_green_37_lower_bound_R1

-- Reduction Green37.green_37_lower_bound.R1.H1.R1 of Step H1 (Green's Open Problem 37)
-- Credit: @estebanlearns
-- Reference: Ben Green & Imre Z. Ruzsa (2019), On the arithmetic Kakeya conjecture of Katz and Tao,
--   Periodica Mathematica Hungarica 78, 135-151 (arXiv:1712.02108).
-- Reduces the unbounded-universe sInf inequality R1.H1 to three pairwise non-redundant statements:
--   H1: Compact-interval, sInf-free, prime-scale Arithmetic Kakeya Core (A ⊆ [0, |A|*p], p prime)
--   H2: Compact-Diameter / Gap-Compression Theorem (optimal AP-covers live in [0, m(N,k)*N])
--   H3: N-scale monotonicity of Green37.m and Bertrand prime-scale bridging (p ∈ [N/2, N])

/-!
# Reduction Green37.green_37_lower_bound.R1.H1.R1
-/

namespace OMA.R_Green37_green_37_lower_bound_R1_H1_R1

def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ K : ℕ, 0 < K ∧ ∃ P₀ : ℕ,
    ∀ p : ℕ, Nat.Prime p → P₀ ≤ p →
      ∀ A : Finset ℕ, (∀ x ∈ A, x ≤ A.card * p) →
        Green37.IsAPCover (A : Set ℕ) p K →
          p ^ n ≤ A.card ^ (n + 1)

def H2 : Prop :=
  ∀ N k : ℕ, 1 ≤ N → 1 ≤ k →
    ∃ A : Finset ℕ, A.card = Green37.m N k ∧
      Green37.IsAPCover (A : Set ℕ) N k ∧
      ∀ x ∈ A, x ≤ Green37.m N k * N

def H3 : Prop :=
  (∀ N₁ N₂ k : ℕ, N₁ ≤ N₂ → Green37.m N₁ k ≤ Green37.m N₂ k) ∧
  (∀ N : ℕ, 2 ≤ N → ∃ p : ℕ, Nat.Prime p ∧ N ≤ 2 * p ∧ p ≤ N)

lemma nat_pow_le_pow {a b : ℕ} (hab : a ≤ b) : ∀ m : ℕ, a ^ m ≤ b ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact Nat.mul_le_mul ih hab

lemma nat_two_pow_pos : ∀ m : ℕ, 0 < 2 ^ m := by
  intro m
  induction m with
  | zero => omega
  | succ k ih =>
    rw [pow_succ]
    omega

lemma nat_le_of_pow_succ_le {a b m : ℕ} (h : a ^ (m + 1) ≤ b ^ (m + 1)) : a ≤ b := by
  by_contra hnot
  have hlt : b < a := by omega
  have hpow_lt : ∀ r : ℕ, b ^ (r + 1) < a ^ (r + 1) := by
    intro r
    induction r with
    | zero => simpa using hlt
    | succ r ih =>
      have ha_pos : 0 < a := by omega
      have h1 : b ^ (r + 1) * b ≤ b ^ (r + 1) * a := Nat.mul_le_mul_left _ (by omega)
      have h2 : b ^ (r + 1) * a < a ^ (r + 1) * a := Nat.mul_lt_mul_of_pos_right ih ha_pos
      rw [pow_succ b (r + 1), pow_succ a (r + 1)]
      exact lt_of_le_of_lt h1 h2
  have hc := hpow_lt m
  omega

theorem main : H1 → H2 → H3 → OMA.R_Green37_green_37_lower_bound_R1.H1 := by
  intro h1 h2 h3 n hn
  have hn1 : 2 ≤ n + 1 := by omega
  obtain ⟨K, hK, P₀, hP₀⟩ := h1 (n + 1) hn1
  set E : ℕ := (n + 1) * (n + 1)
  refine ⟨K, hK, max (2 * P₀) (max (2 ^ E) 2), fun N hN => ?_⟩
  have hN_P₀ : 2 * P₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN_rest : max (2 ^ E) 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN_pow : 2 ^ E ≤ N := le_trans (le_max_left _ _) hN_rest
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN_rest
  obtain ⟨p, hp_prime, hN_le_2p, hp_le_N⟩ := h3.2 N hN2
  have hp2 : 2 ≤ p := hp_prime.two_le
  have hp1 : 1 ≤ p := by omega
  have hp_P₀ : P₀ ≤ p := by omega
  have hK1 : 1 ≤ K := by omega
  obtain ⟨A, hA_card, hA_cov, hA_bdd⟩ := h2 p K hp1 hK1
  have hA_bdd' : ∀ x ∈ A, x ≤ A.card * p := by
    intro x hx
    rw [hA_card]
    exact hA_bdd x hx
  have hp_pow : p ^ (n + 1) ≤ Green37.m p K ^ (n + 2) := by
    have hraw := hP₀ p hp_prime hp_P₀ A hA_bdd' hA_cov
    rwa [hA_card] at hraw
  set M : ℕ := Green37.m N K
  have hm_mono : Green37.m p K ≤ M := h3.1 p N K hp_le_N
  have hp_le_M : p ^ (n + 1) ≤ M ^ (n + 2) :=
    le_trans hp_pow (nat_pow_le_pow hm_mono (n + 2))
  have hexp : n * (n + 2) + 1 = E := by
    dsimp [E]
    ring
  have h_lhs : (N ^ n) ^ (n + 2) * 2 ^ E ≤ N ^ E := by
    have hmul : N ^ (n * (n + 2)) * 2 ^ E ≤ N ^ (n * (n + 2)) * N :=
      Nat.mul_le_mul_left _ hN_pow
    rw [← pow_mul N n (n + 2)]
    rw [← pow_succ N (n * (n + 2)), hexp] at hmul
    exact hmul
  have h_mid : N ^ E ≤ (p ^ (n + 1)) ^ (n + 1) * 2 ^ E := by
    have h1 : N ^ E ≤ (p * 2) ^ E := by
      have hcomm : N ≤ p * 2 := by omega
      exact nat_pow_le_pow hcomm E
    rw [mul_pow p 2 E] at h1
    have hpE : p ^ E = (p ^ (n + 1)) ^ (n + 1) := by
      dsimp [E]
      exact pow_mul p (n + 1) (n + 1)
    rw [hpE] at h1
    exact h1
  have h_rhs : (p ^ (n + 1)) ^ (n + 1) * 2 ^ E ≤ (M ^ (n + 1)) ^ (n + 2) * 2 ^ E := by
    have h2 : (p ^ (n + 1)) ^ (n + 1) ≤ (M ^ (n + 2)) ^ (n + 1) :=
      nat_pow_le_pow hp_le_M (n + 1)
    have hM_comm : (M ^ (n + 2)) ^ (n + 1) = (M ^ (n + 1)) ^ (n + 2) := by
      rw [← pow_mul, Nat.mul_comm (n + 2) (n + 1), pow_mul]
    rw [hM_comm] at h2
    exact Nat.mul_le_mul_right (2 ^ E) h2
  have h_all : (N ^ n) ^ (n + 2) * 2 ^ E ≤ (M ^ (n + 1)) ^ (n + 2) * 2 ^ E :=
    le_trans h_lhs (le_trans h_mid h_rhs)
  have h_cancel : (N ^ n) ^ (n + 2) ≤ (M ^ (n + 1)) ^ (n + 2) :=
    Nat.le_of_mul_le_mul_right h_all (nat_two_pow_pos E)
  exact nat_le_of_pow_succ_le (m := n + 1) h_cancel

end OMA.R_Green37_green_37_lower_bound_R1_H1_R1
