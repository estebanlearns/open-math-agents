import OMAReductions.R_Green37_green_37_lower_bound_R1_H1_R1_H1_R1_H1_R1
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Bertrand

-- Step H2 of reduction Green37.green_37_lower_bound.R1.H1.R1.H1.R1.H1.R1
-- Credit: @estebanlearns
-- Unwrap-and-fold from the finite plane ZMod p × ZMod p into the line ZMod P:
-- a K-AP Kakeya set S ⊆ ZMod p × ZMod p is lifted digit-wise to ℕ (at most K^2 lifts per point),
-- folded by (x, y) ↦ x + p y, and reduced modulo a Bertrand prime p^2 < P ≤ 2 p^2.
-- The p^2 - 1 nonzero directions become distinct common differences in ZMod P.

/-!
# Step H2 of Reduction Green37.green_37_lower_bound.R1.H1.R1.H1.R1.H1.R1
-/

lemma zmod_natCast_inj_lt {q : ℕ} {a b : ℕ}
    (ha : a < q) (hb : b < q) (h : (a : ZMod q) = (b : ZMod q)) : a = b := by
  have half : ∀ u v : ℕ, v ≤ u → u < q → (u : ZMod q) = (v : ZMod q) → u = v := by
    intro u v hvu huq huv
    have hadd : v + (u - v) = u := by omega
    have hcast : ((v + (u - v) : ℕ) : ZMod q) = (u : ZMod q) := congr_arg Nat.cast hadd
    rw [Nat.cast_add, huv] at hcast
    have hc0 : ((u - v : ℕ) : ZMod q) = 0 :=
      add_left_cancel (hcast.trans (add_zero (v : ZMod q)).symm)
    obtain ⟨k, hk⟩ := (CharP.cast_eq_zero_iff (ZMod q) q (u - v)).mp hc0
    by_cases hk0 : k = 0
    · subst hk0
      omega
    · have hqk : q * 1 ≤ q * k := Nat.mul_le_mul_left q (by omega)
      omega
  rcases le_total b a with hba | hab
  · exact half a b hba ha h
  · exact (half b a hab hb h.symm).symm

lemma base_encode_inj {M : ℕ} {p₁ p₂ : ℕ × ℕ}
    (hp₁ : p₁.1 < M) (hp₂ : p₂.1 < M)
    (heq : p₁.1 + M * p₁.2 = p₂.1 + M * p₂.2) : p₁ = p₂ := by
  have hM_pos : 0 < M := by omega
  have hm1 : (p₁.1 + M * p₁.2) % M = p₁.1 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp₁]
  have hm2 : (p₂.1 + M * p₂.2) % M = p₂.1 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp₂]
  have hfst : p₁.1 = p₂.1 := by rw [← hm1, ← hm2, heq]
  have hmul : M * p₁.2 = M * p₂.2 := by omega
  have hsnd : p₁.2 = p₂.2 := Nat.eq_of_mul_eq_mul_left hM_pos hmul
  exact Prod.ext hfst hsnd

lemma enc_lt_sq {p a b : ℕ} (ha : a < p) (hb : b < p) : a + p * b < p ^ 2 := by
  have hb1 : b + 1 ≤ p := hb
  have hm : p * (b + 1) ≤ p * p := Nat.mul_le_mul_left p hb1
  rw [Nat.mul_add, Nat.mul_one] at hm
  rw [pow_two]
  omega

lemma lift_div_lt {p K a j d : ℕ} (hp : 0 < p) (ha : a < p) (hd : d < p) (hj : j < K) :
    (a + j * d) / p < K := by
  rw [Nat.div_lt_iff_lt_mul hp]
  have h1 : j * d ≤ j * p := Nat.mul_le_mul_left j (le_of_lt hd)
  have h2 : (j + 1) * p ≤ K * p := Nat.mul_le_mul_right p hj
  have h3 : (j + 1) * p = j * p + p := by ring
  omega

lemma zmod_lift_val {p : ℕ} [NeZero p] (x d : ZMod p) (j : ℕ) :
    (x + j • d).val = (x.val + j * d.val) % p := by
  have hcast : ((x.val + j * d.val : ℕ) : ZMod p) = x + j • d := by
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, nsmul_eq_mul]
  rw [← hcast, ZMod.val_natCast]

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1_H1_R1_H1_R1_H1_R1.H2 := by
  classical
  intro K p hK hp S hcov
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp_pos : 0 < p := hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  have hp2_ne : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
  obtain ⟨P, hP_prime, hP_gt, hP_le⟩ := Nat.exists_prime_lt_and_le_two_mul (p ^ 2) hp2_ne
  refine ⟨P, hP_prime, le_of_lt hP_gt, hP_le, ?_⟩
  let enc : ZMod p × ZMod p → ℕ := fun x => x.1.val + p * x.2.val
  let lift : (ZMod p × ZMod p) × (ℕ × ℕ) → ZMod P := fun z =>
    ((z.1.1.val + p * z.2.1 + p * (z.1.2.val + p * z.2.2) : ℕ) : ZMod P)
  let A : Finset (ZMod P) := (S ×ˢ (Finset.range K ×ˢ Finset.range K)).image lift
  let D : Finset (ZMod P) :=
    ((Finset.univ : Finset (ZMod p × ZMod p)).erase 0).image (fun x => ((enc x : ℕ) : ZMod P))
  have hA_card : A.card ≤ K ^ 2 * S.card := by
    have h1 : A.card ≤ (S ×ˢ (Finset.range K ×ˢ Finset.range K)).card := Finset.card_image_le
    have h2 : (S ×ˢ (Finset.range K ×ˢ Finset.range K)).card = K ^ 2 * S.card := by
      rw [Finset.card_product, Finset.card_product, Finset.card_range]
      ring
    rw [h2] at h1
    exact h1
  have henc_lt : ∀ x : ZMod p × ZMod p, enc x < P := by
    intro x
    have h1 : enc x < p ^ 2 := enc_lt_sq (ZMod.val_lt x.1) (ZMod.val_lt x.2)
    exact lt_trans h1 hP_gt
  have henc_inj : Set.InjOn (fun x : ZMod p × ZMod p => ((enc x : ℕ) : ZMod P))
      (((Finset.univ : Finset (ZMod p × ZMod p)).erase 0 : Finset (ZMod p × ZMod p)) :
        Set (ZMod p × ZMod p)) := by
    intro x _ y _ hxy
    have heq : enc x = enc y := zmod_natCast_inj_lt (henc_lt x) (henc_lt y) hxy
    have hpair : ((x.1.val, x.2.val) : ℕ × ℕ) = (y.1.val, y.2.val) :=
      base_encode_inj (M := p) (ZMod.val_lt x.1) (ZMod.val_lt y.1) heq
    have h1 : x.1.val = y.1.val := congr_arg Prod.fst hpair
    have h2 : x.2.val = y.2.val := congr_arg Prod.snd hpair
    exact Prod.ext (ZMod.val_injective p h1) (ZMod.val_injective p h2)
  have hD_card : D.card = p * p - 1 := by
    have h1 : D.card = ((Finset.univ : Finset (ZMod p × ZMod p)).erase 0).card :=
      Finset.card_image_of_injOn henc_inj
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_prod, ZMod.card]
  have hD_dense : P ≤ 4 * D.card := by
    rw [hD_card]
    have hpp : 4 ≤ p * p := Nat.mul_le_mul hp2 hp2
    have hsq : p ^ 2 = p * p := pow_two p
    rw [hsq] at hP_le
    omega
  refine ⟨A, D, hA_card, hD_dense, ?_⟩
  intro δ hδ
  obtain ⟨d, hd_mem, rfl⟩ := Finset.mem_image.mp hδ
  have hd0 : d ≠ 0 := Finset.ne_of_mem_erase hd_mem
  obtain ⟨a, ha⟩ := hcov d hd0
  refine ⟨((enc a : ℕ) : ZMod P), fun j hj => ?_⟩
  have hs : a + j • d ∈ S := ha j hj
  set n₁ : ℕ := a.1.val + j * d.1.val with hn₁
  set n₂ : ℕ := a.2.val + j * d.2.val with hn₂
  have hs1 : (a + j • d).1.val = n₁ % p := by
    rw [hn₁, ← zmod_lift_val]
    rfl
  have hs2 : (a + j • d).2.val = n₂ % p := by
    rw [hn₂, ← zmod_lift_val]
    rfl
  have hi₁ : n₁ / p < K := lift_div_lt hp_pos (ZMod.val_lt a.1) (ZMod.val_lt d.1) hj
  have hi₂ : n₂ / p < K := lift_div_lt hp_pos (ZMod.val_lt a.2) (ZMod.val_lt d.2) hj
  have hmem : (a + j • d, (n₁ / p, n₂ / p)) ∈ S ×ˢ (Finset.range K ×ˢ Finset.range K) :=
    Finset.mem_product.mpr
      ⟨hs, Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi₁, Finset.mem_range.mpr hi₂⟩⟩
  have hnat : (a + j • d).1.val + p * (n₁ / p) + p * ((a + j • d).2.val + p * (n₂ / p)) =
      enc a + j * enc d := by
    rw [hs1, hs2, Nat.mod_add_div n₁ p, Nat.mod_add_div n₂ p, hn₁, hn₂]
    simp only [enc]
    ring
  have hlift : lift (a + j • d, (n₁ / p, n₂ / p)) =
      ((enc a : ℕ) : ZMod P) + j • ((enc d : ℕ) : ZMod P) := by
    simp only [lift]
    rw [hnat, Nat.cast_add, Nat.cast_mul, nsmul_eq_mul]
  exact Finset.mem_image.mpr ⟨_, hmem, hlift⟩
