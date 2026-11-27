import OMAReductions.R_Green37_green_37_lower_bound_R1_H1_R1_H1_R1
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Bertrand

-- Step H2 of reduction Green37.green_37_lower_bound.R1.H1.R1.H1.R1
-- Credit: @estebanlearns
-- Proves Section 3 (eqs. 3.1-3.3) of Green & Ruzsa (2019), arXiv:1712.02108:
-- Cut-and-move compression modulo 2KN + base-M digit folding from ℕ into ZMod q × ZMod q.

/-!
# Step H2 of Reduction Green37.green_37_lower_bound.R1.H1.R1.H1.R1
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

lemma finset_exists_ge_of_sum_ge {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (f : α → ℕ) (B : ℕ) (hsum : B ≤ ∑ x ∈ s, f x) :
    ∃ x ∈ s, B ≤ s.card * f x := by
  by_contra hno
  have hall : ∀ x ∈ s, s.card * f x + 1 ≤ B := by
    intro x hx
    by_contra hlt
    exact hno ⟨x, hx, by omega⟩
  have h1 : ∑ x ∈ s, (s.card * f x + 1) ≤ ∑ _x ∈ s, B := Finset.sum_le_sum hall
  rw [Finset.sum_add_distrib] at h1
  simp only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum, mul_one] at h1
  have hpos : 0 < s.card := Finset.card_pos.mpr hs
  have h2 : s.card * B ≤ s.card * ∑ x ∈ s, f x := Nat.mul_le_mul_left _ hsum
  omega

lemma cut_and_shift_cover (K N M : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N)
    (A : Finset ℕ) (hcov : Green37.IsAPCover (A : Set ℕ) N (2 * K)) :
    ∃ A₁ : Finset ℕ,
      A₁.card ≤ A.card ∧
      (∀ y ∈ A₁, M * M ≤ y ∧ y < 2 * K * N + M * M) ∧
      ∀ d : ℕ, 1 ≤ d ∧ d ≤ N → ∃ a ∈ A₁, ∀ j : ℕ, j < K → a + j * d ∈ A₁ := by
  classical
  set W : ℕ := 2 * K * N
  have hW_pos : 0 < W := by
    dsimp [W]
    exact Nat.mul_pos (by omega) hN
  let f : ℕ → ℕ := fun x => x % W + M * M
  let A₁ : Finset ℕ := A.image f
  refine ⟨A₁, Finset.card_image_le, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    have hlt : x % W < W := Nat.mod_lt x hW_pos
    dsimp [f]
    omega
  · intro d hd
    obtain ⟨a, s, hsA, _, hs_eq⟩ := hcov d hd
    have hmem_term : ∀ i : ℕ, i < 2 * K → a + i * d ∈ A := by
      intro i hi
      have hms : a + i • d ∈ s := by
        rw [hs_eq]
        exact ⟨i, by exact_mod_cast hi, rfl⟩
      have hmA : a + i • d ∈ (A : Set ℕ) := hsA hms
      simpa [nsmul_eq_mul] using hmA
    set r₀ : ℕ := a % W
    set q₀ : ℕ := a / W
    have hdiv : W * q₀ + r₀ = a := Nat.div_add_mod a W
    have hr₀_lt : r₀ < W := Nat.mod_lt a hW_pos
    by_cases hlt : r₀ + (K - 1) * d < W
    · set a' : ℕ := r₀ + M * M
      have hall : ∀ j : ℕ, j < K → a' + j * d ∈ A₁ := by
        intro j hj
        have hjd : j * d ≤ (K - 1) * d := Nat.mul_le_mul_right d (by omega)
        have hrj_lt : r₀ + j * d < W := by omega
        have haj_eq : a + j * d = (r₀ + j * d) + W * q₀ := by omega
        have hmod : (a + j * d) % W = r₀ + j * d := by
          rw [haj_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrj_lt]
        have hf_eq : f (a + j * d) = a' + j * d := by
          dsimp [f, a']
          rw [hmod]
          omega
        exact Finset.mem_image.mpr ⟨a + j * d, hmem_term j (by omega), hf_eq⟩
      exact ⟨a', by simpa using hall 0 hK, hall⟩
    · have hKd_ge : W ≤ r₀ + K * d := by
        have hm : (K - 1) * d ≤ K * d := Nat.mul_le_mul_right d (by omega)
        omega
      set r₁ : ℕ := r₀ + K * d - W
      set a' : ℕ := r₁ + M * M
      have hall : ∀ j : ℕ, j < K → a' + j * d ∈ A₁ := by
        intro j hj
        have hKj_lt_W : (K + j) * d < W := by
          have h1 : (K + j) * d ≤ (2 * K - 1) * N :=
            Nat.mul_le_mul (by omega) hd.2
          have h2 : (2 * K - 1) * N + N = W := by
            dsimp [W]
            have hk_eq : 2 * K - 1 + 1 = 2 * K := by omega
            calc
              (2 * K - 1) * N + N = (2 * K - 1 + 1) * N := by ring
              _ = 2 * K * N := by rw [hk_eq]
          omega
        have hr₁j_lt : r₁ + j * d < W := by
          have hid : K * d + j * d = (K + j) * d := by ring
          omega
        have haj_eq : a + (K + j) * d = (r₁ + j * d) + W * (q₀ + 1) := by
          have hid1 : (K + j) * d = K * d + j * d := by ring
          have hid2 : W * (q₀ + 1) = W * q₀ + W := by ring
          omega
        have hmod : (a + (K + j) * d) % W = r₁ + j * d := by
          rw [haj_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr₁j_lt]
        have hf_eq : f (a + (K + j) * d) = a' + j * d := by
          dsimp [f, a']
          rw [hmod]
          omega
        exact Finset.mem_image.mpr ⟨a + (K + j) * d, hmem_term (K + j) (by omega), hf_eq⟩
      exact ⟨a', by simpa using hall 0 hK, hall⟩

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1_H1_R1_H1_R1.H2 := by
  classical
  intro K N hK hN64 A hcov
  have hK2_pos : 1 ≤ K ^ 2 := by
    have hm : 1 * 1 ≤ K * K := Nat.mul_le_mul hK hK
    have hsq : K * K = K ^ 2 := by ring
    rwa [one_mul, hsq] at hm
  have h64_le : 64 ≤ 64 * K ^ 2 := Nat.le_mul_of_pos_right 64 hK2_pos
  have hN1 : 1 ≤ N := by omega
  set M : ℕ := Nat.sqrt N
  have hM_sq_le : M * M ≤ N := Nat.sqrt_le N
  have hN_lt_succ : N < (M + 1) * (M + 1) := Nat.lt_succ_sqrt N
  have h8K_le_M : 8 * K ≤ M := by
    by_contra hlt
    have hle : M + 1 ≤ 8 * K := by omega
    have hsq : (M + 1) * (M + 1) ≤ (8 * K) * (8 * K) := Nat.mul_le_mul hle hle
    have hid : (8 * K) * (8 * K) = 64 * K ^ 2 := by ring
    rw [hid] at hsq
    exact absurd (lt_of_le_of_lt hN64 (lt_of_lt_of_le hN_lt_succ hsq)) (lt_irrefl _)
  have h8_le_M : 8 ≤ M := by omega
  obtain ⟨q, hq_prime, hM_lt_q, hq_le_2M⟩ :=
    Nat.exists_prime_lt_and_le_two_mul M (by omega)
  have hN_le_q2 : N ≤ q ^ 2 := by
    have hMq : M + 1 ≤ q := by omega
    have hsq : (M + 1) * (M + 1) ≤ q * q := Nat.mul_le_mul hMq hMq
    have hq2 : q * q = q ^ 2 := by ring
    rw [hq2] at hsq
    exact le_of_lt (lt_of_lt_of_le hN_lt_succ hsq)
  have hq2_le_4N : q ^ 2 ≤ 4 * N := by
    have hsq : q * q ≤ (2 * M) * (2 * M) := Nat.mul_le_mul hq_le_2M hq_le_2M
    have hid1 : q * q = q ^ 2 := by ring
    have hid2 : (2 * M) * (2 * M) = 4 * (M * M) := by ring
    have h4 : 4 * (M * M) ≤ 4 * N := Nat.mul_le_mul_left 4 hM_sq_le
    rw [hid1, hid2] at hsq
    exact le_trans hsq h4
  obtain ⟨A₁, hA₁_card, hA₁_bdd, hA₁_cov⟩ := cut_and_shift_cover K N M hK hN1 A hcov
  set T_max : ℕ := (2 * K + 1) * N
  have hT_pos : 0 < T_max := Nat.mul_pos (by omega) (by omega)
  have hW_M_le_T : 2 * K * N + M * M ≤ T_max := by
    have hid : T_max = 2 * K * N + N := by
      dsimp [T_max]
      ring
    rw [hid]
    exact Nat.add_le_add_left hM_sq_le (2 * K * N)
  set r : ℕ := M / (2 * K)
  set h : ℕ := M / 2
  have h2Kr_le_M : 2 * K * r ≤ M := by
    have hm := Nat.div_mul_le_self M (2 * K)
    have hc : r * (2 * K) = 2 * K * r := by ring
    rwa [hc] at hm
  have h2h_le_M : 2 * h ≤ M := by
    have hm := Nat.div_mul_le_self M 2
    have hc : h * 2 = 2 * h := by ring
    rwa [hc] at hm
  have hr_pos : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with hr_eq0 | hr_gt0
    · have hrem : M % (2 * K) < 2 * K := Nat.mod_lt M (by omega)
      have hdiv_M : (2 * K) * r + M % (2 * K) = M := Nat.div_add_mod M (2 * K)
      rw [hr_eq0, Nat.mul_zero, zero_add] at hdiv_M
      omega
    · exact hr_gt0
  have hh_pos : 1 ≤ h := by omega
  have hr_lt_M : r < M := by
    have h1 : 2 * r ≤ M := by
      have hm : 1 * (2 * r) ≤ K * (2 * r) := Nat.mul_le_mul_right (2 * r) hK
      have hc : K * (2 * r) = 2 * K * r := by ring
      rw [one_mul, hc] at hm
      exact le_trans hm h2Kr_le_M
    omega
  have hh_lt_M : h < M := by omega
  let Grid : Finset (ℕ × ℕ) := (Finset.range M) ×ˢ (Finset.range M)
  let PosR : Finset ℕ := (Finset.range r).image (fun x => x + 1)
  have hPosR_card : PosR.card = r := by
    dsimp [PosR]
    rw [Finset.card_image_of_injective _ (fun x y hxy => by omega), Finset.card_range]
  let BoxD : Finset (ℕ × ℕ) := PosR ×ˢ PosR
  have hBoxD_card : BoxD.card = r * r := by
    dsimp [BoxD]
    rw [Finset.card_product, hPosR_card]
  let BoxS : Finset (ℕ × ℕ) := (Finset.range h) ×ˢ (Finset.range h)
  have hBoxS_card : BoxS.card = h * h := by
    dsimp [BoxS]
    rw [Finset.card_product, Finset.card_range]
  let B3 : ℕ → Finset (ℕ × ℕ) := fun t =>
    Grid.filter (fun p => t + p.1 + M * p.2 ∈ A₁)
  have hB3_card : ∀ t : ℕ, (B3 t).card ≤ A.card := by
    intro t
    let enc : ℕ × ℕ → ℕ := fun p => t + p.1 + M * p.2
    have hsub : (B3 t).image enc ⊆ A₁ := by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hp).2
    have hinj : Set.InjOn enc ((B3 t : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      intro p₁ hp₁ p₂ hp₂ heq
      have hg₁ : p₁ ∈ Grid := (Finset.mem_filter.mp hp₁).1
      have hg₂ : p₂ ∈ Grid := (Finset.mem_filter.mp hp₂).1
      have hl₁ : p₁.1 < M := Finset.mem_range.mp (Finset.mem_product.mp hg₁).1
      have hl₂ : p₂.1 < M := Finset.mem_range.mp (Finset.mem_product.mp hg₂).1
      have heq' : p₁.1 + M * p₁.2 = p₂.1 + M * p₂.2 := by
        dsimp [enc] at heq
        omega
      exact base_encode_inj hl₁ hl₂ heq'
    have hcard_eq : ((B3 t).image enc).card = (B3 t).card :=
      Finset.card_image_of_injOn hinj
    have hle₁ : (B3 t).card ≤ A₁.card := by
      rw [← hcard_eq]
      exact Finset.card_le_card hsub
    exact le_trans hle₁ hA₁_card
  let Covers : ℕ → ℕ × ℕ → Prop := fun t u =>
    ∃ s ∈ Grid, ∀ j : ℕ, j < K → (s.1 + j * u.1, s.2 + j * u.2) ∈ B3 t
  have h_each_u : ∀ u ∈ BoxD,
      h * h ≤ ((Finset.range T_max).filter (fun t => Covers t u)).card := by
    intro u hu
    obtain ⟨hu1_mem, hu2_mem⟩ := Finset.mem_product.mp hu
    obtain ⟨i₁, hi₁, hu1_eq⟩ := Finset.mem_image.mp hu1_mem
    obtain ⟨i₂, hi₂, hu2_eq⟩ := Finset.mem_image.mp hu2_mem
    have hi₁_lt : i₁ < r := Finset.mem_range.mp hi₁
    have hi₂_lt : i₂ < r := Finset.mem_range.mp hi₂
    have hu1_lo : 1 ≤ u.1 := by omega
    have hu1_hi : u.1 ≤ r := by omega
    have hu2_lo : 1 ≤ u.2 := by omega
    have hu2_hi : u.2 ≤ r := by omega
    set d : ℕ := u.1 + M * u.2
    have hd_range : 1 ≤ d ∧ d ≤ N := by
      refine ⟨by omega, ?_⟩
      have hd1 : u.1 ≤ M - 1 := by omega
      have hd2 : M * u.2 ≤ M * (M - 1) := Nat.mul_le_mul_left M (by omega)
      have hsum1 : d ≤ (M - 1) + M * (M - 1) := Nat.add_le_add hd1 hd2
      have hid : (M - 1) + M * (M - 1) + 1 = M * M := by
        have hM1 : M - 1 + 1 = M := by omega
        calc
          (M - 1) + M * (M - 1) + 1 = (M + 1) * (M - 1) + 1 := by ring
          _ = M * (M - 1) + (M - 1 + 1) := by ring
          _ = M * (M - 1) + M * 1 := by rw [hM1, mul_one]
          _ = M * (M - 1 + 1) := by rw [← mul_add]
          _ = M * M := by rw [hM1]
      have hsum2 : (M - 1) + M * (M - 1) ≤ M * M := by
        rw [← hid]
        omega
      exact le_trans hsum1 (le_trans hsum2 hM_sq_le)
    obtain ⟨x_u, hx_mem, hx_ap⟩ := hA₁_cov d hd_range
    obtain ⟨hx_lo, hx_hi_W⟩ := hA₁_bdd x_u hx_mem
    have hx_hi : x_u < T_max := lt_of_lt_of_le hx_hi_W hW_M_le_T
    let sh : ℕ × ℕ → ℕ := fun s => x_u - (s.1 + M * s.2)
    have hs_lt_MM : ∀ s ∈ BoxS, s.1 + M * s.2 < M * M := by
      intro s hs
      have hs1 : s.1 < h := Finset.mem_range.mp (Finset.mem_product.mp hs).1
      have hs2 : s.2 < h := Finset.mem_range.mp (Finset.mem_product.mp hs).2
      have hs1_M : s.1 < M := lt_trans hs1 hh_lt_M
      have hm2 : M * s.2 ≤ M * (M - 1) := Nat.mul_le_mul_left M (by omega)
      have hid : M + M * (M - 1) = M * M := by
        have hM1 : 1 + (M - 1) = M := by omega
        calc
          M + M * (M - 1) = M * 1 + M * (M - 1) := by ring
          _ = M * (1 + (M - 1)) := by rw [← mul_add]
          _ = M * M := by rw [hM1]
      have hsum : s.1 + M * s.2 < M + M * (M - 1) :=
        Nat.add_lt_add_of_lt_of_le hs1_M hm2
      rwa [hid] at hsum
    have hsub_sh : BoxS.image sh ⊆ (Finset.range T_max).filter (fun t => Covers t u) := by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      have hs1_h : s.1 < h := Finset.mem_range.mp (Finset.mem_product.mp hs).1
      have hs2_h : s.2 < h := Finset.mem_range.mp (Finset.mem_product.mp hs).2
      have hsm_lt : s.1 + M * s.2 < M * M := hs_lt_MM s hs
      have ht_lt : sh s < T_max := lt_of_le_of_lt (Nat.sub_le _ _) hx_hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht_lt, ?_⟩
      have hs_grid : s ∈ Grid :=
        Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
      refine ⟨s, hs_grid, fun j hj => ?_⟩
      have hj1_lt : s.1 + j * u.1 < M := by
        have hm1 : j * u.1 ≤ (K - 1) * r := Nat.mul_le_mul (by omega) hu1_hi
        have hm2 : (K - 1) * r ≤ K * r := Nat.mul_le_mul_right r (by omega)
        have hm3 : 2 * (j * u.1) ≤ 2 * (K * r) :=
          Nat.mul_le_mul_left 2 (le_trans hm1 hm2)
        have hc : 2 * (K * r) = 2 * K * r := by ring
        have hju : 2 * (j * u.1) ≤ M := le_trans hm3 (by rwa [hc])
        omega
      have hj2_lt : s.2 + j * u.2 < M := by
        have hm1 : j * u.2 ≤ (K - 1) * r := Nat.mul_le_mul (by omega) hu2_hi
        have hm2 : (K - 1) * r ≤ K * r := Nat.mul_le_mul_right r (by omega)
        have hm3 : 2 * (j * u.2) ≤ 2 * (K * r) :=
          Nat.mul_le_mul_left 2 (le_trans hm1 hm2)
        have hc : 2 * (K * r) = 2 * K * r := by ring
        have hju : 2 * (j * u.2) ≤ M := le_trans hm3 (by rwa [hc])
        omega
      have hp_grid : (s.1 + j * u.1, s.2 + j * u.2) ∈ Grid :=
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj1_lt, Finset.mem_range.mpr hj2_lt⟩
      refine Finset.mem_filter.mpr ⟨hp_grid, ?_⟩
      have hsum_eq : sh s + (s.1 + j * u.1) + M * (s.2 + j * u.2) = x_u + j * d := by
        have hle_xu : s.1 + M * s.2 ≤ x_u := le_of_lt (lt_of_lt_of_le hsm_lt hx_lo)
        have hbase : sh s + (s.1 + M * s.2) = x_u := Nat.sub_add_cancel hle_xu
        have hexp :
            sh s + (s.1 + j * u.1) + M * (s.2 + j * u.2) =
              (sh s + (s.1 + M * s.2)) + j * (u.1 + M * u.2) := by
          ring
        rw [hexp, hbase]
      rw [hsum_eq]
      exact hx_ap j hj
    have hinj_sh : Set.InjOn sh ((BoxS : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      intro s₁ hs₁ s₂ hs₂ heq
      have hlt₁ : s₁.1 + M * s₁.2 < M * M := hs_lt_MM s₁ hs₁
      have hlt₂ : s₂.1 + M * s₂.2 < M * M := hs_lt_MM s₂ hs₂
      have hle₁ : s₁.1 + M * s₁.2 ≤ x_u := le_of_lt (lt_of_lt_of_le hlt₁ hx_lo)
      have hle₂ : s₂.1 + M * s₂.2 ≤ x_u := le_of_lt (lt_of_lt_of_le hlt₂ hx_lo)
      have henc_eq : s₁.1 + M * s₁.2 = s₂.1 + M * s₂.2 := by
        dsimp [sh] at heq
        omega
      have hs₁_M : s₁.1 < M := by
        have := Finset.mem_range.mp (Finset.mem_product.mp hs₁).1
        omega
      have hs₂_M : s₂.1 < M := by
        have := Finset.mem_range.mp (Finset.mem_product.mp hs₂).1
        omega
      exact base_encode_inj hs₁_M hs₂_M henc_eq
    have hcard_sh : (BoxS.image sh).card = h * h := by
      rw [Finset.card_image_of_injOn hinj_sh, hBoxS_card]
    rw [← hcard_sh]
    exact Finset.card_le_card hsub_sh
  have hsum_total :
      (r * r) * (h * h) ≤
        ∑ t ∈ Finset.range T_max, (BoxD.filter (fun u => Covers t u)).card := by
    have h1 :
        ∑ _u ∈ BoxD, (h * h) ≤
          ∑ u ∈ BoxD, ((Finset.range T_max).filter (fun t => Covers t u)).card :=
      Finset.sum_le_sum h_each_u
    simp only [Finset.sum_const, smul_eq_mul, hBoxD_card] at h1
    have hswap :
        ∑ u ∈ BoxD, ((Finset.range T_max).filter (fun t => Covers t u)).card =
          ∑ t ∈ Finset.range T_max, (BoxD.filter (fun u => Covers t u)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rwa [hswap] at h1
  obtain ⟨t₀, _, ht₀_ge⟩ :=
    finset_exists_ge_of_sum_ge (Finset.range T_max)
      ⟨0, Finset.mem_range.mpr hT_pos⟩
      (fun t => (BoxD.filter (fun u => Covers t u)).card)
      ((r * r) * (h * h))
      hsum_total
  rw [Finset.card_range] at ht₀_ge
  let D₀ : Finset (ℕ × ℕ) := BoxD.filter (fun u => Covers t₀ u)
  have hD₀_ge : (r * r) * (h * h) ≤ T_max * D₀.card := ht₀_ge
  have hM_le_4Kr : M ≤ 4 * K * r := by
    have hdiv_M : (2 * K) * r + M % (2 * K) = M := Nat.div_add_mod M (2 * K)
    have hrem : M % (2 * K) < 2 * K := Nat.mod_lt M (by omega)
    have h2K_le : 2 * K ≤ (2 * K) * r := by
      have hm := Nat.mul_le_mul_left (2 * K) hr_pos
      simpa using hm
    have h4 : 4 * K * r = (2 * K) * r + (2 * K) * r := by ring
    omega
  have hM_le_3h : M ≤ 3 * h := by
    have hdiv_2 : 2 * h + M % 2 = M := Nat.div_add_mod M 2
    have hrem2 : M % 2 < 2 := Nat.mod_lt M (by omega)
    omega
  have hq2_dense : q ^ 2 ≤ 7000 * K ^ 3 * D₀.card := by
    have hM2_r : M * M ≤ 16 * K ^ 2 * (r * r) := by
      have hm := Nat.mul_le_mul hM_le_4Kr hM_le_4Kr
      have hrhs : (4 * K * r) * (4 * K * r) = 16 * K ^ 2 * (r * r) := by ring
      rwa [hrhs] at hm
    have hM2_h : M * M ≤ 9 * (h * h) := by
      have hm := Nat.mul_le_mul hM_le_3h hM_le_3h
      have hrhs : (3 * h) * (3 * h) = 9 * (h * h) := by ring
      rwa [hrhs] at hm
    have hM4 : (M * M) * (M * M) ≤ 144 * K ^ 2 * ((r * r) * (h * h)) := by
      have hm := Nat.mul_le_mul hM2_r hM2_h
      have hrhs : (16 * K ^ 2 * (r * r)) * (9 * (h * h)) =
          144 * K ^ 2 * ((r * r) * (h * h)) := by ring
      rwa [hrhs] at hm
    have hN_le_4M2 : N ≤ 4 * (M * M) := by
      have hm1 : M + 1 ≤ 2 * M := by omega
      have hsq : (M + 1) * (M + 1) ≤ (2 * M) * (2 * M) := Nat.mul_le_mul hm1 hm1
      have hid : (2 * M) * (2 * M) = 4 * (M * M) := by ring
      rw [hid] at hsq
      exact le_of_lt (lt_of_lt_of_le hN_lt_succ hsq)
    have hT_le : T_max ≤ 12 * K * (M * M) := by
      have hm1 : 2 * K + 1 ≤ 3 * K := by omega
      have hm2 : (2 * K + 1) * N ≤ (3 * K) * (4 * (M * M)) := Nat.mul_le_mul hm1 hN_le_4M2
      have hid : (3 * K) * (4 * (M * M)) = 12 * K * (M * M) := by ring
      exact le_trans hm2 (le_of_eq hid)
    have hM4_D : (M * M) * (M * M) ≤ (M * M) * (1728 * K ^ 3 * D₀.card) := by
      have h1 : 144 * K ^ 2 * ((r * r) * (h * h)) ≤ 144 * K ^ 2 * (T_max * D₀.card) :=
        Nat.mul_le_mul_left _ hD₀_ge
      have h2 : T_max * D₀.card ≤ (12 * K * (M * M)) * D₀.card :=
        Nat.mul_le_mul_right D₀.card hT_le
      have h3 : 144 * K ^ 2 * (T_max * D₀.card) ≤
          144 * K ^ 2 * ((12 * K * (M * M)) * D₀.card) :=
        Nat.mul_le_mul_left _ h2
      have hid : 144 * K ^ 2 * ((12 * K * (M * M)) * D₀.card) =
          (M * M) * (1728 * K ^ 3 * D₀.card) := by ring
      exact le_trans hM4 (le_trans h1 (le_trans h3 (le_of_eq hid)))
    have hMM_pos : 0 < M * M := Nat.mul_pos (by omega) (by omega)
    have hM2_D : M * M ≤ 1728 * K ^ 3 * D₀.card :=
      Nat.le_of_mul_le_mul_left hM4_D hMM_pos
    have hq_M2 : q ^ 2 ≤ 4 * (M * M) := by
      have hsq : q * q ≤ (2 * M) * (2 * M) := Nat.mul_le_mul hq_le_2M hq_le_2M
      have hid1 : q * q = q ^ 2 := by ring
      have hid2 : (2 * M) * (2 * M) = 4 * (M * M) := by ring
      rwa [hid1, hid2] at hsq
    have h4 : 4 * (M * M) ≤ 4 * (1728 * K ^ 3 * D₀.card) :=
      Nat.mul_le_mul_left 4 hM2_D
    have h7000 : 4 * (1728 * K ^ 3 * D₀.card) ≤ 7000 * K ^ 3 * D₀.card := by
      have hid : 4 * (1728 * K ^ 3 * D₀.card) = 6912 * (K ^ 3 * D₀.card) := by ring
      have hid2 : 7000 * K ^ 3 * D₀.card = 7000 * (K ^ 3 * D₀.card) := by ring
      rw [hid, hid2]
      exact Nat.mul_le_mul_right _ (by omega)
    exact le_trans hq_M2 (le_trans h4 h7000)
  let π : ℕ × ℕ → ZMod q × ZMod q := fun p => ((p.1 : ZMod q), (p.2 : ZMod q))
  let S₀ : Finset (ZMod q × ZMod q) := (B3 t₀).image π
  let D : Finset (ZMod q × ZMod q) := D₀.image π
  have hS₀_card : S₀.card ≤ A.card := le_trans Finset.card_image_le (hB3_card t₀)
  have hinj_D₀ : Set.InjOn π ((D₀ : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro u₁ hu₁ u₂ hu₂ heq
    have hb₁ : u₁ ∈ BoxD := (Finset.mem_filter.mp hu₁).1
    have hb₂ : u₂ ∈ BoxD := (Finset.mem_filter.mp hu₂).1
    obtain ⟨i₁, hi₁, hu₁_1⟩ := Finset.mem_image.mp (Finset.mem_product.mp hb₁).1
    obtain ⟨j₁, hj₁, hu₁_2⟩ := Finset.mem_image.mp (Finset.mem_product.mp hb₁).2
    obtain ⟨i₂, hi₂, hu₂_1⟩ := Finset.mem_image.mp (Finset.mem_product.mp hb₂).1
    obtain ⟨j₂, hj₂, hu₂_2⟩ := Finset.mem_image.mp (Finset.mem_product.mp hb₂).2
    have hi₁_r : i₁ < r := Finset.mem_range.mp hi₁
    have hj₁_r : j₁ < r := Finset.mem_range.mp hj₁
    have hi₂_r : i₂ < r := Finset.mem_range.mp hi₂
    have hj₂_r : j₂ < r := Finset.mem_range.mp hj₂
    have hu₁_1q : u₁.1 < q := by omega
    have hu₁_2q : u₁.2 < q := by omega
    have hu₂_1q : u₂.1 < q := by omega
    have hu₂_2q : u₂.2 < q := by omega
    have h1 : (u₁.1 : ZMod q) = (u₂.1 : ZMod q) := congr_arg Prod.fst heq
    have h2 : (u₁.2 : ZMod q) = (u₂.2 : ZMod q) := congr_arg Prod.snd heq
    exact Prod.ext (zmod_natCast_inj_lt hu₁_1q hu₂_1q h1) (zmod_natCast_inj_lt hu₁_2q hu₂_2q h2)
  have hD_card : D.card = D₀.card := Finset.card_image_of_injOn hinj_D₀
  refine ⟨q, hq_prime, hN_le_q2, hq2_le_4N, S₀, D, hS₀_card, ?_, ?_⟩
  · rwa [hD_card]
  · intro d hd
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨_, s, _, hs_cov⟩ := Finset.mem_filter.mp hu
    refine ⟨π s, fun j hj => ?_⟩
    have hmem_B3 : (s.1 + j * u.1, s.2 + j * u.2) ∈ B3 t₀ := hs_cov j hj
    have hπ_eq : π (s.1 + j * u.1, s.2 + j * u.2) = π s + j • π u := by
      ext <;> simp [π, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul]
    exact Finset.mem_image.mpr ⟨(s.1 + j * u.1, s.2 + j * u.2), hmem_B3, hπ_eq⟩
