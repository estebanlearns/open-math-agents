import OMAReductions.R_Green37_green_37_lower_bound_R1_H1_R1_H1_R1
import Mathlib.Data.ZMod.Basic

-- Reduction Green37.green_37_lower_bound.R1.H1.R1.H1.R1.H1.R1 of Step R1.H1.R1.H1.R1.H1 (Green's Open Problem 37)
-- Credit: @estebanlearns
-- Reference: Ben Green & Imre Z. Ruzsa, On the arithmetic Kakeya conjecture of Katz and Tao
--   (arXiv:1712.02108), Conjecture 4(n) and Appendix A.
-- Reduces the finite-plane form (Conjecture 4(2), sets in ZMod q × ZMod q) to the
-- one-dimensional form (Conjecture 4(1), sets in ZMod P), with the same progression length K:
--   H1: Conjecture 4(1) of Green-Ruzsa in constant-free form: a set A ⊆ ZMod P containing a
--       K-term progression with every nonzero common difference has P^(m-1) ≤ |A|^m.
--   H2: Unwrap-and-fold: a K-AP Kakeya set S ⊆ ZMod p × ZMod p yields, for a prime P with
--       p^2 ≤ P ≤ 2 p^2, a set A ⊆ ZMod P with |A| ≤ K^2 |S| containing K-APs with a set D of
--       common differences of density P ≤ 4 |D|.
--   H3: Greedy translate-covering amplification in ZMod q (Green-Ruzsa Lemma A.2 / Cor. A.3, n = 1).

/-!
# Reduction Green37.green_37_lower_bound.R1.H1.R1.H1.R1.H1.R1
-/

namespace OMA.R_Green37_green_37_lower_bound_R1_H1_R1_H1_R1_H1_R1

def H1 : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∃ K : ℕ, 0 < K ∧ ∃ Q₀ : ℕ,
    ∀ P : ℕ, Nat.Prime P → Q₀ ≤ P →
      ∀ A : Finset (ZMod P),
        (∀ d : ZMod P, d ≠ 0 → ∃ a : ZMod P, ∀ j : ℕ, j < K → a + j • d ∈ A) →
        P ^ (m - 1) ≤ A.card ^ m

def H2 : Prop :=
  ∀ K p : ℕ, 1 ≤ K → Nat.Prime p →
    ∀ S : Finset (ZMod p × ZMod p),
      (∀ d : ZMod p × ZMod p, d ≠ 0 →
        ∃ a : ZMod p × ZMod p, ∀ j : ℕ, j < K → a + j • d ∈ S) →
      ∃ P : ℕ, Nat.Prime P ∧ p ^ 2 ≤ P ∧ P ≤ 2 * p ^ 2 ∧
        ∃ A D : Finset (ZMod P),
          A.card ≤ K ^ 2 * S.card ∧
          P ≤ 4 * D.card ∧
          ∀ d ∈ D, ∃ a : ZMod P, ∀ j : ℕ, j < K → a + j • d ∈ A

def H3 : Prop :=
  ∀ q K B L : ℕ, Nat.Prime q → 1 ≤ K → 1 ≤ B → q < 2 ^ L →
    ∀ S₀ D : Finset (ZMod q),
      q ≤ B * D.card →
      (∀ d ∈ D, ∃ a : ZMod q, ∀ j : ℕ, j < K → a + j • d ∈ S₀) →
      ∃ S : Finset (ZMod q),
        S.card ≤ K * B * L * S₀.card ∧
        ∀ d : ZMod q, d ≠ 0 → ∃ a : ZMod q, ∀ j : ℕ, j < K → a + j • d ∈ S

lemma nat_pow_le_pow {a b : ℕ} (hab : a ≤ b) : ∀ m : ℕ, a ^ m ≤ b ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact Nat.mul_le_mul ih hab

lemma nat_pos_pow {a : ℕ} (ha : 0 < a) : ∀ m : ℕ, 0 < a ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact Nat.mul_pos ih ha

lemma two_pow_mono {a b : ℕ} (hab : a ≤ b) : 2 ^ a ≤ 2 ^ b := by
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0
    simp
  | succ k ih =>
    by_cases hle : a ≤ k
    · have h1 := ih hle
      rw [pow_succ 2 k]
      exact le_trans h1 (Nat.le_mul_of_pos_right _ (by omega))
    · have heq : a = k + 1 := by omega
      subst heq
      exact le_rfl

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

lemma exists_pow_two_bracket : ∀ X : ℕ, ∃ k : ℕ, 2 ^ k ≤ X + 1 ∧ X + 1 < 2 ^ (k + 1) := by
  intro X
  induction X with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ X ih =>
    obtain ⟨k, hlo, hhi⟩ := ih
    by_cases hlt : X + 2 < 2 ^ (k + 1)
    · exact ⟨k, by omega, hlt⟩
    · have heq : X + 2 = 2 ^ (k + 1) := by omega
      refine ⟨k + 1, by omega, ?_⟩
      rw [pow_succ 2 (k + 1)]
      omega

lemma sq_le_two_pow_add_four : ∀ t : ℕ, (t + 4) ^ 2 ≤ 2 ^ (t + 4) := by
  intro t
  induction t with
  | zero => decide
  | succ t ih =>
    set k : ℕ := t + 4
    have hk4 : 4 ≤ k := by omega
    have h4k : 4 * k ≤ k * k := Nat.mul_le_mul_right k hk4
    have hk_sq : k * k = k ^ 2 := by ring
    have hexp_sq : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    have hstep : (k + 1) ^ 2 ≤ 2 * k ^ 2 := by omega
    have h2 : 2 * k ^ 2 ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by
      rw [pow_succ 2 k]
      ring
    change (k + 1) ^ 2 ≤ 2 ^ (k + 1)
    exact le_trans hstep (le_trans h2 (le_of_eq hp.symm))

lemma sq_le_two_pow {u : ℕ} (hu : 4 ≤ u) : u ^ 2 ≤ 2 ^ u := by
  have heq : (u - 4) + 4 = u := by omega
  have h := sq_le_two_pow_add_four (u - 4)
  rwa [heq] at h

lemma two_mul_pow_le_two_pow : ∀ d : ℕ, ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → 2 * L ^ d ≤ 2 ^ L := by
  intro d
  induction d with
  | zero =>
    refine ⟨1, fun L hL => ?_⟩
    have h1 : 2 ^ 1 ≤ 2 ^ L := two_pow_mono hL
    simpa using h1
  | succ d ih =>
    obtain ⟨M₀, hM₀⟩ := ih
    set B₂ : ℕ := 2 ^ (d + 3)
    have hB₂_pos : 0 < B₂ := nat_pos_pow (by omega) (d + 3)
    refine ⟨2 * max M₀ (B₂ + 6) + 2, fun L hL => ?_⟩
    have hmax1 : M₀ ≤ max M₀ (B₂ + 6) := le_max_left _ _
    have hmax2 : B₂ + 6 ≤ max M₀ (B₂ + 6) := le_max_right _ _
    set m : ℕ := L / 2
    set u : ℕ := m - 1
    have hm_lo : max M₀ (B₂ + 6) + 1 ≤ m := by omega
    have hm_B₂ : B₂ + 7 ≤ m := le_trans (Nat.add_le_add_right hmax2 1) hm_lo
    have hm1_M₀ : M₀ ≤ m + 1 := le_trans hmax1 (by omega)
    have hu4 : 4 ≤ u := by omega
    have hu_B₂ : B₂ ≤ u := by omega
    have hm1_2u : m + 1 ≤ 2 * u := by omega
    have hL_le : L ≤ 2 * (m + 1) := by omega
    have h2m_le : 2 * m ≤ L := by omega
    have h2d2_le_B₂ : 2 ^ (d + 2) ≤ B₂ := by
      dsimp [B₂]
      rw [show d + 3 = (d + 2) + 1 by omega, pow_succ 2 (d + 2)]
      exact Nat.le_mul_of_pos_right _ (by omega)
    have h2d2_le_u : 2 ^ (d + 2) ≤ u := le_trans h2d2_le_B₂ hu_B₂
    have h_factor1 : 2 ^ (d + 1) * (m + 1) ≤ 2 ^ u := by
      have h1 : 2 ^ (d + 1) * (m + 1) ≤ 2 ^ (d + 1) * (2 * u) :=
        Nat.mul_le_mul_left _ hm1_2u
      have h2 : 2 ^ (d + 1) * (2 * u) = 2 ^ (d + 2) * u := by
        rw [show d + 2 = (d + 1) + 1 by omega, pow_succ 2 (d + 1)]
        ring
      have h3 : 2 ^ (d + 2) * u ≤ u * u := Nat.mul_le_mul_right u h2d2_le_u
      have h4 : u * u = u ^ 2 := by ring
      have h5 : u ^ 2 ≤ 2 ^ u := sq_le_two_pow hu4
      exact le_trans h1 (le_trans (le_of_eq h2) (le_trans h3 (le_trans (le_of_eq h4) h5)))
    have h_factor2 : 2 * (m + 1) ^ d ≤ 2 ^ (m + 1) := hM₀ (m + 1) hm1_M₀
    have h_prod : (2 ^ (d + 1) * (m + 1)) * (2 * (m + 1) ^ d) ≤ 2 ^ u * 2 ^ (m + 1) :=
      Nat.mul_le_mul h_factor1 h_factor2
    have h_lhs_id : 2 * (2 * (m + 1)) ^ (d + 1) = (2 ^ (d + 1) * (m + 1)) * (2 * (m + 1) ^ d) := by
      rw [mul_pow, pow_succ (m + 1) d]
      ring
    have h_rhs_id : 2 ^ u * 2 ^ (m + 1) = 2 ^ (2 * m) := by
      rw [← pow_add]
      have hexp : u + (m + 1) = 2 * m := by omega
      rw [hexp]
    have h_L_pow : 2 * L ^ (d + 1) ≤ 2 * (2 * (m + 1)) ^ (d + 1) :=
      Nat.mul_le_mul_left 2 (nat_pow_le_pow hL_le (d + 1))
    have h_2m_L : 2 ^ (2 * m) ≤ 2 ^ L := two_pow_mono h2m_le
    exact le_trans h_L_pow
      (le_trans (le_of_eq h_lhs_id)
        (le_trans h_prod (le_trans (le_of_eq h_rhs_id) h_2m_L)))

theorem main : H1 → H2 → H3 → OMA.R_Green37_green_37_lower_bound_R1_H1_R1_H1_R1.H1 := by
  intro h1 h2 h3 m hm
  obtain ⟨K, hK, Q₀, hQ₀⟩ := h1 (4 * m) (by omega)
  have hK1 : 1 ≤ K := hK
  obtain ⟨L₀, hL₀⟩ := two_mul_pow_le_two_pow (8 * m + 1)
  refine ⟨K, hK, max (max Q₀ ((K * 4 * K ^ 2) ^ (4 * m))) (2 ^ L₀),
    fun q hq_prime hq_ge S hcov => ?_⟩
  have hq_left : max Q₀ ((K * 4 * K ^ 2) ^ (4 * m)) ≤ q := le_trans (le_max_left _ _) hq_ge
  have hqQ₀ : Q₀ ≤ q := le_trans (le_max_left _ _) hq_left
  have hqC : (K * 4 * K ^ 2) ^ (4 * m) ≤ q := le_trans (le_max_right _ _) hq_left
  have hqL₀ : 2 ^ L₀ ≤ q := le_trans (le_max_right _ _) hq_ge
  have hq2 : 2 ≤ q := hq_prime.two_le
  have hq_pos : 0 < q := hq_prime.pos
  have hq_le_q2 : q ≤ q ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_left q hq_pos
  obtain ⟨P, hP_prime, hq2_le_P, hP_le, A, D, hA_card, hD_dense, hD_cov⟩ :=
    h2 K q hK1 hq_prime S hcov
  have hq_le_P : q ≤ P := le_trans hq_le_q2 hq2_le_P
  have hQ₀P : Q₀ ≤ P := le_trans hqQ₀ hq_le_P
  have h4_le_q2 : 4 ≤ q ^ 2 := by
    have hm4 : 2 * 2 ≤ q * q := Nat.mul_le_mul hq2 hq2
    rw [pow_two]
    omega
  have h4P : 4 ≤ P := le_trans h4_le_q2 hq2_le_P
  obtain ⟨k, hk_lo, hk_hi⟩ := exists_pow_two_bracket (P - 1)
  have hP1 : P - 1 + 1 = P := by omega
  rw [hP1] at hk_lo hk_hi
  set L : ℕ := k + 1 with hL_def
  have h2L_le : 2 ^ L ≤ 2 * P := by
    rw [hL_def, pow_succ 2 k, Nat.mul_comm _ 2]
    exact Nat.mul_le_mul_left 2 hk_lo
  have hL₀_le_L : L₀ ≤ L := by
    by_contra hnot
    have hle : L ≤ L₀ := by omega
    have hpow : 2 ^ L ≤ 2 ^ L₀ := two_pow_mono hle
    have hlt : 2 ^ L₀ < 2 ^ L := lt_of_le_of_lt (le_trans hqL₀ hq_le_P) hk_hi
    exact absurd (lt_of_le_of_lt hpow hlt) (lt_irrefl _)
  have hL2 : 2 ≤ L := by
    by_contra hnot
    have hle : L ≤ 1 := by omega
    have hpow : 2 ^ L ≤ 2 ^ 1 := two_pow_mono hle
    have hlt : P < 2 ^ 1 := lt_of_lt_of_le hk_hi hpow
    norm_num at hlt
    omega
  have hL_pow : L ^ (4 * m) ≤ q := by
    have e1 : 2 * L ^ (8 * m + 1) ≤ 2 ^ L := hL₀ L hL₀_le_L
    have e2 : 2 ^ L ≤ 2 * (2 * q ^ 2) := le_trans h2L_le (Nat.mul_le_mul_left 2 hP_le)
    have e3 : L ^ (8 * m + 1) ≤ 2 * q ^ 2 :=
      Nat.le_of_mul_le_mul_left (le_trans e1 e2) (by omega)
    have e4 : 2 * L ^ (8 * m) ≤ L ^ (8 * m + 1) := by
      rw [pow_succ, Nat.mul_comm 2 (L ^ (8 * m))]
      exact Nat.mul_le_mul_left _ hL2
    have e5 : L ^ (8 * m) ≤ q ^ 2 :=
      Nat.le_of_mul_le_mul_left (le_trans e4 e3) (by omega)
    have e6 : (L ^ (4 * m)) ^ 2 ≤ q ^ 2 := by
      rw [← pow_mul]
      have hexp : 4 * m * 2 = 8 * m := by ring
      rw [hexp]
      exact e5
    exact nat_le_of_pow_succ_le (m := 1) e6
  obtain ⟨S', hS'_card, hS'_cov⟩ :=
    h3 P K 4 L hP_prime hK1 (by norm_num) hk_hi A D hD_dense hD_cov
  have h_kak : P ^ (4 * m - 1) ≤ S'.card ^ (4 * m) := hQ₀ P hP_prime hQ₀P S' hS'_cov
  have hS'_le : S'.card ≤ (K * 4 * K ^ 2) * L * S.card := by
    have hmul : K * 4 * L * A.card ≤ K * 4 * L * (K ^ 2 * S.card) :=
      Nat.mul_le_mul_left _ hA_card
    have hid : K * 4 * L * (K ^ 2 * S.card) = (K * 4 * K ^ 2) * L * S.card := by ring
    exact le_trans hS'_card (le_trans hmul (le_of_eq hid))
  have hS'_pow : S'.card ^ (4 * m) ≤ (S.card ^ m) ^ 4 * q ^ 2 := by
    have e1 : S'.card ^ (4 * m) ≤ ((K * 4 * K ^ 2) * L * S.card) ^ (4 * m) :=
      nat_pow_le_pow hS'_le (4 * m)
    have e2 : ((K * 4 * K ^ 2) * L * S.card) ^ (4 * m) =
        ((K * 4 * K ^ 2) ^ (4 * m) * L ^ (4 * m)) * S.card ^ (4 * m) := by
      rw [mul_pow, mul_pow]
    have e3 : (K * 4 * K ^ 2) ^ (4 * m) * L ^ (4 * m) ≤ q * q := Nat.mul_le_mul hqC hL_pow
    have e4 : ((K * 4 * K ^ 2) ^ (4 * m) * L ^ (4 * m)) * S.card ^ (4 * m) ≤
        (q * q) * S.card ^ (4 * m) := Nat.mul_le_mul_right _ e3
    have e5 : (q * q) * S.card ^ (4 * m) = (S.card ^ m) ^ 4 * q ^ 2 := by
      rw [← pow_mul, Nat.mul_comm m 4]
      ring
    rw [e2] at e1
    exact le_trans e1 (le_trans e4 (le_of_eq e5))
  have hP_pow : (q ^ (2 * m - 1)) ^ 4 * q ^ 2 ≤ P ^ (4 * m - 1) := by
    have e1 : (q ^ 2) ^ (4 * m - 1) ≤ P ^ (4 * m - 1) := nat_pow_le_pow hq2_le_P (4 * m - 1)
    have e2 : (q ^ (2 * m - 1)) ^ 4 * q ^ 2 = (q ^ 2) ^ (4 * m - 1) := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      have hexp : (2 * m - 1) * 4 + 2 = 2 * (4 * m - 1) := by omega
      rw [hexp]
    rw [e2]
    exact e1
  have hall : (q ^ (2 * m - 1)) ^ 4 * q ^ 2 ≤ (S.card ^ m) ^ 4 * q ^ 2 :=
    le_trans hP_pow (le_trans h_kak hS'_pow)
  have hq2_pos : 0 < q ^ 2 := nat_pos_pow hq_pos 2
  have hcancel : (q ^ (2 * m - 1)) ^ 4 ≤ (S.card ^ m) ^ 4 :=
    Nat.le_of_mul_le_mul_right hall hq2_pos
  exact nat_le_of_pow_succ_le (m := 3) hcancel

end OMA.R_Green37_green_37_lower_bound_R1_H1_R1_H1_R1_H1_R1
