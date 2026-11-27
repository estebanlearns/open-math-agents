import OMAReductions.R_Green37_green_37_lower_bound_R1_H1_R1_H1_R1
import Mathlib.Data.ZMod.Basic

-- Step H3 of reduction Green37.green_37_lower_bound.R1.H1.R1.H1.R1
-- Credit: @estebanlearns
-- Proves Lemma A.2 & Corollary A.3 of Green & Ruzsa (2019), arXiv:1712.02108:
-- Greedy translate covering D + T = ZMod q × ZMod q and K-term AP amplification.

/-!
# Step H3 of Reduction Green37.green_37_lower_bound.R1.H1.R1.H1.R1
-/

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

lemma pow_sub_step (B : ℕ) (hB : 1 ≤ B) :
    ∀ r : ℕ, (B - 1) ^ (r + 1) + (r + 1) * (B - 1) ^ r ≤ B ^ (r + 1) := by
  intro r
  induction r with
  | zero =>
    simp
    omega
  | succ r ih =>
    have hmul : ((B - 1) ^ (r + 1) + (r + 1) * (B - 1) ^ r) * B ≤ B ^ (r + 1) * B :=
      Nat.mul_le_mul_right B ih
    rw [← pow_succ B (r + 1)] at hmul
    rw [add_mul] at hmul
    have h1 : (B - 1) ^ (r + 2) + (B - 1) ^ (r + 1) = (B - 1) ^ (r + 1) * B := by
      have hB_eq : (B - 1) + 1 = B := by omega
      calc
        (B - 1) ^ (r + 2) + (B - 1) ^ (r + 1)
            = (B - 1) ^ (r + 1) * (B - 1) + (B - 1) ^ (r + 1) * 1 := by
              rw [pow_succ (B - 1) (r + 1), mul_one]
        _ = (B - 1) ^ (r + 1) * ((B - 1) + 1) := by rw [← mul_add]
        _ = (B - 1) ^ (r + 1) * B := by rw [hB_eq]
    have h2 : (r + 1) * (B - 1) ^ (r + 1) ≤ ((r + 1) * (B - 1) ^ r) * B := by
      have hle : ((r + 1) * (B - 1) ^ r) * (B - 1) ≤ ((r + 1) * (B - 1) ^ r) * B :=
        Nat.mul_le_mul_left _ (by omega)
      have hid : ((r + 1) * (B - 1) ^ r) * (B - 1) = (r + 1) * (B - 1) ^ (r + 1) := by
        rw [mul_assoc, ← pow_succ (B - 1) r]
      rwa [hid] at hle
    have hlhs :
        (B - 1) ^ (r + 2) + (r + 2) * (B - 1) ^ (r + 1) =
          ((B - 1) ^ (r + 2) + (B - 1) ^ (r + 1)) + (r + 1) * (B - 1) ^ (r + 1) := by
      ring
    rw [hlhs, h1]
    exact le_trans (Nat.add_le_add_left h2 _) hmul

lemma two_mul_pred_pow_le (B : ℕ) (hB : 1 ≤ B) : 2 * (B - 1) ^ B ≤ B ^ B := by
  by_cases h1 : B = 1
  · subst h1
    simp
  · set r : ℕ := B - 1
    have hr : r + 1 = B := by omega
    have hstep := pow_sub_step B hB r
    rw [hr] at hstep
    have hle : (B - 1) ^ B ≤ B * (B - 1) ^ r := by
      have hpow : (B - 1) ^ B = (B - 1) ^ r * (B - 1) := by
        calc
          (B - 1) ^ B = (B - 1) ^ (r + 1) := by rw [hr]
          _ = (B - 1) ^ r * (B - 1) := pow_succ (B - 1) r
      have hm : (B - 1) ^ r * (B - 1) ≤ (B - 1) ^ r * B :=
        Nat.mul_le_mul_left _ (by omega)
      have hc : (B - 1) ^ r * B = B * (B - 1) ^ r := by ring
      rw [hpow]
      exact le_trans hm (le_of_eq hc)
    have htwo : 2 * (B - 1) ^ B = (B - 1) ^ B + (B - 1) ^ B := by ring
    rw [htwo]
    exact le_trans (Nat.add_le_add_left hle _) hstep

lemma finset_exists_le_of_sum_le {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (f : α → ℕ) (M : ℕ) (hsum : ∑ x ∈ s, f x ≤ M) :
    ∃ x ∈ s, s.card * f x ≤ M := by
  by_contra hno
  have hall : ∀ x ∈ s, M + 1 ≤ s.card * f x := by
    intro x hx
    by_contra hlt
    exact hno ⟨x, hx, by omega⟩
  have h1 : ∑ _x ∈ s, (M + 1) ≤ ∑ x ∈ s, s.card * f x := Finset.sum_le_sum hall
  simp only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at h1
  have hpos : 0 < s.card := Finset.card_pos.mpr hs
  have h2 : s.card * ∑ x ∈ s, f x ≤ s.card * M := Nat.mul_le_mul_left _ hsum
  have h3 : M + 1 ≤ M := Nat.le_of_mul_le_mul_left (le_trans h1 h2) hpos
  omega

lemma greedy_translate_step (q : ℕ) [NeZero q] (D U : Finset (ZMod q × ZMod q)) :
    ∃ t : ZMod q × ZMod q,
      Fintype.card (ZMod q × ZMod q) *
        (U.filter (fun u => ∀ d ∈ D, d + t ≠ u)).card ≤
          U.card * (Fintype.card (ZMod q × ZMod q) - D.card) := by
  classical
  let G := ZMod q × ZMod q
  have hmiss_card : ∀ u : G,
      ((Finset.univ : Finset G).filter (fun t => ∀ d ∈ D, d + t ≠ u)).card =
        Fintype.card G - D.card := by
    intro u
    let hit : Finset G := (Finset.univ : Finset G).filter (fun t => ∃ d ∈ D, d + t = u)
    let miss : Finset G := (Finset.univ : Finset G).filter (fun t => ∀ d ∈ D, d + t ≠ u)
    have hhit_eq : hit = D.image (fun d => u - d) := by
      ext t
      simp only [hit, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨d, hd, hdt⟩
        refine ⟨d, hd, ?_⟩
        rw [← hdt]
        abel
      · rintro ⟨d, hd, rfl⟩
        refine ⟨d, hd, ?_⟩
        abel
    have hinj : Function.Injective (fun d : G => u - d) := by
      intro d₁ d₂ h
      have h' := congr_arg (fun z => u - z) h
      simpa [sub_sub_cancel] using h'
    have hhit_card : hit.card = D.card := by
      rw [hhit_eq, Finset.card_image_of_injective D hinj]
    have hdisj : Disjoint hit miss := by
      rw [Finset.disjoint_left]
      intro t ht_hit ht_miss
      simp only [hit, miss, Finset.mem_filter, Finset.mem_univ, true_and] at ht_hit ht_miss
      obtain ⟨d, hd, hdt⟩ := ht_hit
      exact ht_miss d hd hdt
    have hunion : hit ∪ miss = (Finset.univ : Finset G) := by
      ext t
      simp only [hit, miss, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_true]
      by_cases hex : ∃ d ∈ D, d + t = u
      · exact Or.inl hex
      · right
        intro d hd heq
        exact hex ⟨d, hd, heq⟩
    have hsum_card : hit.card + miss.card = Fintype.card G := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
    rw [hhit_card] at hsum_card
    change miss.card = Fintype.card G - D.card
    rw [← hsum_card, Nat.add_sub_cancel_left]
  have hdouble :
      ∑ t ∈ (Finset.univ : Finset G), (U.filter (fun u => ∀ d ∈ D, d + t ≠ u)).card =
        U.card * (Fintype.card G - D.card) := by
    calc
      ∑ t ∈ (Finset.univ : Finset G), (U.filter (fun u => ∀ d ∈ D, d + t ≠ u)).card
          = ∑ u ∈ U, ((Finset.univ : Finset G).filter (fun t => ∀ d ∈ D, d + t ≠ u)).card := by
            simp only [Finset.card_filter]
            exact Finset.sum_comm
      _ = ∑ _u ∈ U, (Fintype.card G - D.card) := by
            refine Finset.sum_congr rfl (fun u _ => hmiss_card u)
      _ = U.card * (Fintype.card G - D.card) := by
            simp only [Finset.sum_const, smul_eq_mul]
  have huniv_ne : (Finset.univ : Finset G).Nonempty := ⟨(0, 0), Finset.mem_univ _⟩
  obtain ⟨t, _, ht_le⟩ :=
    finset_exists_le_of_sum_le (Finset.univ : Finset G) huniv_ne
      (fun t => (U.filter (fun u => ∀ d ∈ D, d + t ≠ u)).card)
      (U.card * (Fintype.card G - D.card))
      (le_of_eq hdouble)
  rw [Finset.card_univ] at ht_le
  exact ⟨t, ht_le⟩

lemma greedy_translate_iter (q B : ℕ) [NeZero q] (hq : Nat.Prime q) (_hB : 1 ≤ B)
    (D : Finset (ZMod q × ZMod q))
    (hD : q ^ 2 ≤ B * D.card) :
    ∀ n : ℕ, ∃ T : Finset (ZMod q × ZMod q),
      T.card ≤ n ∧
      B ^ n *
        ((Finset.univ : Finset (ZMod q × ZMod q)).filter
          (fun u => ∀ d ∈ D, ∀ t ∈ T, d + t ≠ u)).card ≤
        (B - 1) ^ n * q ^ 2 := by
  classical
  let G := ZMod q × ZMod q
  have hV_eq : Fintype.card G = q ^ 2 := by
    dsimp [G]
    rw [Fintype.card_prod, ZMod.card]
    ring
  have hV_pos : 0 < Fintype.card G := by
    rw [hV_eq]
    exact nat_pos_pow hq.pos 2
  have hD_le_V : D.card ≤ Fintype.card G := Finset.card_le_univ D
  have hB_sub : B * (Fintype.card G - D.card) ≤ (B - 1) * Fintype.card G := by
    rw [Nat.mul_sub_left_distrib, Nat.sub_mul, one_mul]
    have hBD_le : B * D.card ≤ B * Fintype.card G := Nat.mul_le_mul_left B hD_le_V
    have hV_le_BD : Fintype.card G ≤ B * D.card := by rwa [hV_eq]
    omega
  intro n
  induction n with
  | zero =>
    refine ⟨∅, le_rfl, ?_⟩
    simp only [pow_zero, one_mul]
    rw [← hV_eq]
    exact Finset.card_le_univ _
  | succ n ih =>
    obtain ⟨T, hT_card, hT_bound⟩ := ih
    let U : Finset G :=
      (Finset.univ : Finset G).filter (fun u => ∀ d ∈ D, ∀ t ∈ T, d + t ≠ u)
    obtain ⟨t₀, ht₀⟩ := greedy_translate_step q D U
    let T' : Finset G := insert t₀ T
    let U' : Finset G :=
      (Finset.univ : Finset G).filter (fun u => ∀ d ∈ D, ∀ t ∈ T', d + t ≠ u)
    have hT'_card : T'.card ≤ n + 1 :=
      le_trans (Finset.card_insert_le t₀ T) (by omega)
    have hU'_sub : U' ⊆ U.filter (fun u => ∀ d ∈ D, d + t₀ ≠ u) := by
      intro u hu
      simp only [U', T', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hu
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun d hd t ht => hu d hd t (Or.inr ht), fun d hd => hu d hd t₀ (Or.inl rfl)⟩
    have hU'_card : U'.card ≤ (U.filter (fun u => ∀ d ∈ D, d + t₀ ≠ u)).card :=
      Finset.card_le_card hU'_sub
    have hstep_B : B * U'.card ≤ (B - 1) * U.card := by
      have h1 : Fintype.card G * (B * U'.card) ≤ B * (U.card * (Fintype.card G - D.card)) := by
        have hm1 : Fintype.card G * U'.card ≤ U.card * (Fintype.card G - D.card) :=
          le_trans (Nat.mul_le_mul_left _ hU'_card) ht₀
        have hm2 := Nat.mul_le_mul_left B hm1
        have hc : B * (Fintype.card G * U'.card) = Fintype.card G * (B * U'.card) := by ring
        rwa [hc] at hm2
      have h2 : B * (U.card * (Fintype.card G - D.card)) ≤ Fintype.card G * ((B - 1) * U.card) := by
        have hc1 : B * (U.card * (Fintype.card G - D.card)) =
            U.card * (B * (Fintype.card G - D.card)) := by ring
        have hm3 : U.card * (B * (Fintype.card G - D.card)) ≤
            U.card * ((B - 1) * Fintype.card G) := Nat.mul_le_mul_left U.card hB_sub
        have hc2 : U.card * ((B - 1) * Fintype.card G) =
            Fintype.card G * ((B - 1) * U.card) := by ring
        rw [hc1]
        exact le_trans hm3 (le_of_eq hc2)
      exact Nat.le_of_mul_le_mul_left (le_trans h1 h2) hV_pos
    refine ⟨T', hT'_card, ?_⟩
    change B ^ (n + 1) * U'.card ≤ (B - 1) ^ (n + 1) * q ^ 2
    have h3 : B ^ (n + 1) * U'.card ≤ (B - 1) * (B ^ n * U.card) := by
      have hm := Nat.mul_le_mul_left (B ^ n) hstep_B
      have hl : B ^ (n + 1) * U'.card = B ^ n * (B * U'.card) := by
        rw [pow_succ B n]
        ring
      have hr : B ^ n * ((B - 1) * U.card) = (B - 1) * (B ^ n * U.card) := by ring
      rw [hl]
      exact le_trans hm (le_of_eq hr)
    have h4 : (B - 1) * (B ^ n * U.card) ≤ (B - 1) ^ (n + 1) * q ^ 2 := by
      have hm := Nat.mul_le_mul_left (B - 1) hT_bound
      have hr : (B - 1) * ((B - 1) ^ n * q ^ 2) =
          (B - 1) ^ (n + 1) * q ^ 2 := by
        rw [pow_succ (B - 1) n]
        ring
      exact le_trans hm (le_of_eq hr)
    exact le_trans h3 h4

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1_H1_R1_H1_R1.H3 := by
  classical
  intro q K B L hq hK hB hqL S₀ D hD_dense hD_cov
  have : NeZero q := ⟨hq.ne_zero⟩
  let G := ZMod q × ZMod q
  obtain ⟨T, hT_card, hT_rem⟩ := greedy_translate_iter q B hq hB D hD_dense (B * L)
  have hrem_zero :
      ((Finset.univ : Finset G).filter (fun u => ∀ d ∈ D, ∀ t ∈ T, d + t ≠ u)).card = 0 := by
    set rem := ((Finset.univ : Finset G).filter (fun u => ∀ d ∈ D, ∀ t ∈ T, d + t ≠ u)).card
    by_contra hne
    have hrem_pos : 1 ≤ rem := by omega
    have hBL_pos : 0 < B ^ (B * L) := nat_pos_pow (by omega) (B * L)
    have hlt1 : (B - 1) ^ (B * L) * q ^ 2 < B ^ (B * L) := by
      by_cases hpred0 : (B - 1) ^ (B * L) = 0
      · rw [hpred0, zero_mul]
        exact hBL_pos
      · have hpred_pos : 0 < (B - 1) ^ (B * L) := by omega
        have hstep1 : (B - 1) ^ (B * L) * q ^ 2 < (B - 1) ^ (B * L) * 2 ^ L :=
          Nat.mul_lt_mul_of_pos_left hqL hpred_pos
        have hstep2 : (B - 1) ^ (B * L) * 2 ^ L ≤ B ^ (B * L) := by
          have hid1 : (B - 1) ^ (B * L) * 2 ^ L = (2 * (B - 1) ^ B) ^ L := by
            rw [pow_mul (B - 1) B L, ← mul_pow, Nat.mul_comm]
          have hid2 : B ^ (B * L) = (B ^ B) ^ L := pow_mul B B L
          rw [hid1, hid2]
          exact nat_pow_le_pow (two_mul_pred_pow_le B hB) L
        exact lt_of_lt_of_le hstep1 hstep2
    have hge : B ^ (B * L) ≤ B ^ (B * L) * rem := by
      have hm := Nat.mul_le_mul_left (B ^ (B * L)) hrem_pos
      simpa using hm
    exact absurd (lt_of_le_of_lt (le_trans hge hT_rem) hlt1) (lt_irrefl _)
  have hcover_all : ∀ v : G, ∃ d ∈ D, ∃ t ∈ T, d + t = v := by
    intro v
    by_contra hmiss
    have hmem :
        v ∈ (Finset.univ : Finset G).filter (fun u => ∀ d ∈ D, ∀ t ∈ T, d + t ≠ u) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro d hd t ht heq
      exact hmiss ⟨d, hd, t, ht, heq⟩
    have hpos :
        0 < ((Finset.univ : Finset G).filter (fun u => ∀ d ∈ D, ∀ t ∈ T, d + t ≠ u)).card :=
      Finset.card_pos.mpr ⟨v, hmem⟩
    omega
  let S : Finset G :=
    (Finset.range K).biUnion (fun j => T.biUnion (fun t => S₀.image (fun x => x + j • t)))
  refine ⟨S, ?_, ?_⟩
  · have h1 : S.card ≤ ∑ j ∈ Finset.range K, (T.biUnion (fun t => S₀.image (fun x => x + j • t))).card :=
      Finset.card_biUnion_le
    have h2 :
        ∑ j ∈ Finset.range K, (T.biUnion (fun t => S₀.image (fun x => x + j • t))).card ≤
          ∑ _j ∈ Finset.range K, T.card * S₀.card := by
      refine Finset.sum_le_sum (fun j _ => ?_)
      have hb1 :
          (T.biUnion (fun t => S₀.image (fun x => x + j • t))).card ≤
            ∑ t ∈ T, (S₀.image (fun x => x + j • t)).card :=
        Finset.card_biUnion_le
      have hb2 :
          ∑ t ∈ T, (S₀.image (fun x => x + j • t)).card ≤ ∑ _t ∈ T, S₀.card :=
        Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      simp only [Finset.sum_const, smul_eq_mul] at hb2
      exact le_trans hb1 hb2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
    have h3 : K * (T.card * S₀.card) ≤ K * ((B * L) * S₀.card) :=
      Nat.mul_le_mul_left K (Nat.mul_le_mul_right S₀.card hT_card)
    have h4 : K * ((B * L) * S₀.card) = K * B * L * S₀.card := by ring
    exact le_trans h1 (le_trans h2 (le_trans h3 (le_of_eq h4)))
  · intro v _hv
    obtain ⟨d, hd, t, ht, rfl⟩ := hcover_all v
    obtain ⟨a, ha_cov⟩ := hD_cov d hd
    refine ⟨a, fun j hj => ?_⟩
    have hx : a + j • d ∈ S₀ := ha_cov j hj
    have heq : (a + j • d) + j • t = a + j • (d + t) := by
      rw [smul_add, add_assoc]
    exact Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_range.mpr hj,
        Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_image.mpr ⟨a + j • d, hx, heq⟩⟩⟩
