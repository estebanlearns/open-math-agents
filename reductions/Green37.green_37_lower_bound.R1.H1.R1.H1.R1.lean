import OMAReductions.R_Green37_green_37_lower_bound_R1_H1_R1
import Mathlib.Data.ZMod.Basic

-- Reduction Green37.green_37_lower_bound.R1.H1.R1.H1.R1 of Step R1.H1.R1.H1 (Green's Open Problem 37)
-- Credit: @estebanlearns
-- Reference: Ben Green & Imre Z. Ruzsa (2019), On the arithmetic Kakeya conjecture of Katz and Tao,
--   Periodica Mathematica Hungarica 78, 135-151 (arXiv:1712.02108), Section 3 & Appendix A.
-- Reduces the integer-interval Arithmetic Kakeya Core R1.H1.R1.H1 to Finite-Field Plane Geometry:
--   H1: Conjecture 4(2) of Green-Ruzsa (2019) — Finite-Plane Arithmetic Kakeya in ZMod q × ZMod q
--       (generalizing Dvir's 2009 polynomial-method Kakeya theorem from K = q lines to bounded K)
--   H2: Cut-and-Move + Base-M Digit Folding from ℕ into ZMod q × ZMod q (Green-Ruzsa §3, eqs. 3.1-3.3)
--   H3: Greedy Translate-Covering Amplification in ZMod q × ZMod q (Green-Ruzsa Appendix A, Lemma A.2 & Cor. A.3)

/-!
# Reduction Green37.green_37_lower_bound.R1.H1.R1.H1.R1
-/

namespace OMA.R_Green37_green_37_lower_bound_R1_H1_R1_H1_R1

def H1 : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∃ K : ℕ, 0 < K ∧ ∃ Q₀ : ℕ,
    ∀ q : ℕ, Nat.Prime q → Q₀ ≤ q →
      ∀ S : Finset (ZMod q × ZMod q),
        (∀ d : ZMod q × ZMod q, d ≠ 0 →
          ∃ a : ZMod q × ZMod q, ∀ j : ℕ, j < K → a + j • d ∈ S) →
        q ^ (2 * m - 1) ≤ S.card ^ m

def H2 : Prop :=
  ∀ K N : ℕ, 1 ≤ K → 64 * K ^ 2 ≤ N →
    ∀ A : Finset ℕ, Green37.IsAPCover (A : Set ℕ) N (2 * K) →
      ∃ q : ℕ, Nat.Prime q ∧ N ≤ q ^ 2 ∧ q ^ 2 ≤ 4 * N ∧
        ∃ S₀ D : Finset (ZMod q × ZMod q),
          S₀.card ≤ A.card ∧
          q ^ 2 ≤ 7000 * K ^ 3 * D.card ∧
          ∀ d ∈ D, ∃ a : ZMod q × ZMod q, ∀ j : ℕ, j < K → a + j • d ∈ S₀

def H3 : Prop :=
  ∀ q K B L : ℕ, Nat.Prime q → 1 ≤ K → 1 ≤ B → q ^ 2 < 2 ^ L →
    ∀ S₀ D : Finset (ZMod q × ZMod q),
      q ^ 2 ≤ B * D.card →
      (∀ d ∈ D, ∃ a : ZMod q × ZMod q, ∀ j : ℕ, j < K → a + j • d ∈ S₀) →
      ∃ S : Finset (ZMod q × ZMod q),
        S.card ≤ K * B * L * S₀.card ∧
        ∀ d : ZMod q × ZMod q, d ≠ 0 →
          ∃ a : ZMod q × ZMod q, ∀ j : ℕ, j < K → a + j • d ∈ S

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

theorem main : H1 → H2 → H3 → OMA.R_Green37_green_37_lower_bound_R1_H1_R1.H1 := by
  intro h1 h2 h3 n hn
  set m : ℕ := 2 * n + 2
  have hm : 2 ≤ m := by omega
  obtain ⟨K₁, hK₁, Q₀, hQ₀⟩ := h1 m hm
  have hK₁_1 : 1 ≤ K₁ := by omega
  set B : ℕ := 7000 * K₁ ^ 3
  have hB_pos : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos (by omega) (nat_pos_pow hK₁ 3)
  have hB_1 : 1 ≤ B := by omega
  set C₁ : ℕ := (K₁ * B) ^ m
  obtain ⟨L₀, hL₀⟩ := two_mul_pow_le_two_pow (2 * m)
  set P₀ : ℕ := max (max (64 * K₁ ^ 2) (Q₀ ^ 2)) (max (C₁ ^ 2) (2 ^ L₀))
  refine ⟨2 * K₁, by omega, P₀, fun p hp_prime hpP₀ A _hAbdd hcov => ?_⟩
  have hp_left : max (64 * K₁ ^ 2) (Q₀ ^ 2) ≤ p := le_trans (le_max_left _ _) hpP₀
  have hp_right : max (C₁ ^ 2) (2 ^ L₀) ≤ p := le_trans (le_max_right _ _) hpP₀
  have hp64 : 64 * K₁ ^ 2 ≤ p := le_trans (le_max_left _ _) hp_left
  have hpQ₀ : Q₀ ^ 2 ≤ p := le_trans (le_max_right _ _) hp_left
  have hpC₁ : C₁ ^ 2 ≤ p := le_trans (le_max_left _ _) hp_right
  have hpL₀ : 2 ^ L₀ ≤ p := le_trans (le_max_right _ _) hp_right
  obtain ⟨q, hq_prime, hp_le_q2, _, S₀, D, hS₀_le, hD_dense, hD_cov⟩ :=
    h2 K₁ p hK₁_1 hp64 A hcov
  have hq2 : 2 ≤ q := hq_prime.two_le
  have hq2_pos : 0 < q ^ 2 := nat_pos_pow (by omega) 2
  have hQ₀_le_q : Q₀ ≤ q :=
    nat_le_of_pow_succ_le (m := 1) (le_trans hpQ₀ hp_le_q2)
  have hC₁_le_q : C₁ ≤ q :=
    nat_le_of_pow_succ_le (m := 1) (le_trans hpC₁ hp_le_q2)
  obtain ⟨k, hk_lo, hk_hi⟩ := exists_pow_two_bracket (q ^ 2 - 1)
  have hq2_sub : q ^ 2 - 1 + 1 = q ^ 2 := by omega
  rw [hq2_sub] at hk_lo hk_hi
  set L : ℕ := k + 1
  have h2L_le : 2 ^ L ≤ 2 * q ^ 2 := by
    dsimp [L]
    rw [pow_succ 2 k, Nat.mul_comm _ 2]
    exact Nat.mul_le_mul_left 2 hk_lo
  have hL₀_le_L : L₀ ≤ L := by
    by_contra hnot
    have hle : L ≤ L₀ := by omega
    have hpow : 2 ^ L ≤ 2 ^ L₀ := two_pow_mono hle
    have hlt : 2 ^ L₀ < 2 ^ L := lt_of_le_of_lt (le_trans hpL₀ hp_le_q2) hk_hi
    exact absurd (lt_of_le_of_lt hpow hlt) (lt_irrefl _)
  have hLm_le_q : L ^ m ≤ q := by
    have h1 : 2 * L ^ (2 * m) ≤ 2 ^ L := hL₀ L hL₀_le_L
    have h2 : L ^ (2 * m) ≤ q ^ 2 :=
      Nat.le_of_mul_le_mul_left (le_trans h1 h2L_le) (by omega)
    have h3 : (L ^ m) ^ 2 ≤ q ^ 2 := by
      rw [← pow_mul, Nat.mul_comm m 2]
      exact h2
    exact nat_le_of_pow_succ_le (m := 1) h3
  obtain ⟨S, hS_card, hS_cov⟩ :=
    h3 q K₁ B L hq_prime hK₁_1 hB_1 hk_hi S₀ D hD_dense hD_cov
  have hS_le_A : S.card ≤ (K₁ * B) * L * A.card := by
    have hmul : K₁ * B * L * S₀.card ≤ K₁ * B * L * A.card :=
      Nat.mul_le_mul_left _ hS₀_le
    exact le_trans hS_card hmul
  have hSm_le : S.card ^ m ≤ A.card ^ m * q ^ 2 := by
    have h1 : S.card ^ m ≤ ((K₁ * B) * L * A.card) ^ m := nat_pow_le_pow hS_le_A m
    rw [mul_pow, mul_pow] at h1
    have hcoeff : C₁ * L ^ m ≤ q ^ 2 := by
      have hm1 : C₁ * L ^ m ≤ q * q := Nat.mul_le_mul hC₁_le_q hLm_le_q
      have hq_sq : q * q = q ^ 2 := by ring
      rwa [hq_sq] at hm1
    have h2 : C₁ * L ^ m * A.card ^ m ≤ q ^ 2 * A.card ^ m :=
      Nat.mul_le_mul_right (A.card ^ m) hcoeff
    have hcomm : q ^ 2 * A.card ^ m = A.card ^ m * q ^ 2 := by ring
    rw [hcomm] at h2
    exact le_trans h1 h2
  have h_kakeya : q ^ (2 * m - 1) ≤ S.card ^ m :=
    hQ₀ q hq_prime hQ₀_le_q S hS_cov
  have hq_all : q ^ (4 * n + 1) * q ^ 2 ≤ A.card ^ m * q ^ 2 := by
    have hexp : 2 * m - 1 = (4 * n + 1) + 2 := by
      dsimp [m]
      omega
    rw [hexp, pow_add] at h_kakeya
    exact le_trans h_kakeya hSm_le
  have hq_cancel : q ^ (4 * n + 1) ≤ A.card ^ m :=
    Nat.le_of_mul_le_mul_right hq_all hq2_pos
  have hq_sq_pow : (q ^ 2) ^ (4 * n + 1) ≤ (A.card ^ (n + 1)) ^ 4 := by
    have hsq : (q ^ (4 * n + 1)) ^ 2 ≤ (A.card ^ m) ^ 2 := nat_pow_le_pow hq_cancel 2
    have hlhs : (q ^ (4 * n + 1)) ^ 2 = (q ^ 2) ^ (4 * n + 1) := by
      rw [← pow_mul, Nat.mul_comm (4 * n + 1) 2, pow_mul]
    have hrhs : (A.card ^ m) ^ 2 = (A.card ^ (n + 1)) ^ 4 := by
      dsimp [m]
      rw [← pow_mul, ← pow_mul]
      have hexp2 : (2 * n + 2) * 2 = (n + 1) * 4 := by ring
      rw [hexp2]
    rw [hlhs, hrhs] at hsq
    exact hsq
  have hp_pow_le : (p ^ n) ^ 4 ≤ (q ^ 2) ^ (4 * n + 1) := by
    have hp1 : 1 ≤ p := le_of_lt hp_prime.one_lt
    have h1 : (p ^ n) ^ 4 = p ^ (4 * n) := by
      rw [← pow_mul, Nat.mul_comm n 4]
    have h2 : p ^ (4 * n) ≤ p ^ (4 * n + 1) := by
      rw [pow_succ]
      have hm1 : p ^ (4 * n) * 1 ≤ p ^ (4 * n) * p := Nat.mul_le_mul_left _ hp1
      simpa using hm1
    have h3 : p ^ (4 * n + 1) ≤ (q ^ 2) ^ (4 * n + 1) :=
      nat_pow_le_pow hp_le_q2 (4 * n + 1)
    rw [h1]
    exact le_trans h2 h3
  exact nat_le_of_pow_succ_le (m := 3) (le_trans hp_pow_le hq_sq_pow)

end OMA.R_Green37_green_37_lower_bound_R1_H1_R1_H1_R1
