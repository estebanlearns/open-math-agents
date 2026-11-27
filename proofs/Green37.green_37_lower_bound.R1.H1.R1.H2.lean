import OMAReductions.R_Green37_green_37_lower_bound_R1_H1_R1

-- Step H2 of reduction Green37.green_37_lower_bound.R1.H1.R1
-- Credit: @estebanlearns
-- Proves the Compact-Diameter / Gap-Compression Theorem: every minimum AP-cover cardinality
-- Green37.m N k (for N, k ≥ 1) is achieved by a subset A ⊆ [0, Green37.m N k * N].

/-!
# Step H2 of Reduction Green37.green_37_lower_bound.R1.H1.R1
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

lemma exists_empty_window (A : Finset ℕ) (N B : ℕ)
    (hmem_top : B + 1 ∈ A) (hgt : A.card * N < B + 1) :
    ∃ j : ℕ, j < A.card ∧ ∀ x ∈ A, ¬ (j * N + 1 ≤ x ∧ x ≤ (j + 1) * N) := by
  classical
  by_contra hno
  push_neg at hno
  let g : ℕ → ℕ := fun j =>
    if hj : j < A.card then Classical.choose (hno j hj) else 0
  have hg_spec : ∀ j : ℕ, j < A.card →
      g j ∈ A ∧ j * N + 1 ≤ g j ∧ g j ≤ (j + 1) * N := by
    intro j hj
    have hdef : g j = Classical.choose (hno j hj) := dif_pos hj
    rw [hdef]
    exact Classical.choose_spec (hno j hj)
  have hsub : (Finset.range A.card).image g ⊆ A.erase (B + 1) := by
    intro y hy
    obtain ⟨j, hj_mem, rfl⟩ := Finset.mem_image.mp hy
    have hj : j < A.card := Finset.mem_range.mp hj_mem
    obtain ⟨hgA, _, hgle⟩ := hg_spec j hj
    have hjN : (j + 1) * N ≤ A.card * N := Nat.mul_le_mul_right N (by omega)
    have hne : g j ≠ B + 1 := by omega
    exact Finset.mem_erase.mpr ⟨hne, hgA⟩
  have hinj : Set.InjOn g ((Finset.range A.card : Finset ℕ) : Set ℕ) := by
    intro j₁ hj₁ j₂ hj₂ heq
    have h1 : j₁ < A.card := Finset.mem_range.mp hj₁
    have h2 : j₂ < A.card := Finset.mem_range.mp hj₂
    obtain ⟨_, hlo₁, hhi₁⟩ := hg_spec j₁ h1
    obtain ⟨_, hlo₂, hhi₂⟩ := hg_spec j₂ h2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt_j
    · have hmul : (j₁ + 1) * N ≤ j₂ * N := Nat.mul_le_mul_right N (by omega)
      omega
    · have hmul : (j₂ + 1) * N ≤ j₁ * N := Nat.mul_le_mul_right N (by omega)
      omega
  have hcard_im : ((Finset.range A.card).image g).card = A.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hcard_le : ((Finset.range A.card).image g).card ≤ (A.erase (B + 1)).card :=
    Finset.card_le_card hsub
  have herase : (A.erase (B + 1)).card + 1 = A.card :=
    Finset.card_erase_add_one hmem_top
  omega

lemma compress_step_cover (A : Finset ℕ) (N k t : ℕ) (hk : 1 ≤ k)
    (hgap : ∀ x ∈ A, ¬ (t + 1 ≤ x ∧ x ≤ t + N))
    (hcov : Green37.IsAPCover (A : Set ℕ) N k) :
    Green37.IsAPCover ((A.image (fun x => if x ≤ t then x else x - 1) : Finset ℕ) : Set ℕ) N k := by
  classical
  set f : ℕ → ℕ := fun x => if x ≤ t then x else x - 1
  intro d hd
  obtain ⟨a, s, hsA, _, hs_eq⟩ := hcov d hd
  have hmem_term : ∀ i : ℕ, i < k → a + i * d ∈ A := by
    intro i hi
    have hms : a + i • d ∈ s := by
      rw [hs_eq]
      exact ⟨i, by exact_mod_cast hi, rfl⟩
    have hmA : a + i • d ∈ (A : Set ℕ) := hsA hms
    simpa [nsmul_eq_mul] using hmA
  by_cases ha : a ≤ t
  · have hstay : ∀ i : ℕ, i < k → a + i * d ≤ t := by
      intro i
      induction i with
      | zero =>
        intro _
        simpa using ha
      | succ i ih =>
        intro hi1
        have hi_le : a + i * d ≤ t := ih (by omega)
        have hmA : a + (i + 1) * d ∈ A := hmem_term (i + 1) hi1
        have hng := hgap (a + (i + 1) * d) hmA
        have hstep : a + (i + 1) * d = a + i * d + d := by ring
        omega
    refine ⟨a, ((Finset.range k).image (fun i : ℕ => a + i • d) : Set ℕ), ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨i, hi_mem, rfl⟩ := Finset.mem_image.mp hy
      have hi : i < k := Finset.mem_range.mp hi_mem
      have hmA : a + i * d ∈ A := hmem_term i hi
      have hle_t : a + i * d ≤ t := hstay i hi
      have hf_eq : f (a + i * d) = a + i * d := if_pos hle_t
      have hm_im : a + i * d ∈ A.image f := Finset.mem_image.mpr ⟨a + i * d, hmA, hf_eq⟩
      simpa [nsmul_eq_mul] using hm_im
    · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
        Finset.card_image_of_injective _
          (fun x y h => by
            rw [nsmul_eq_mul, nsmul_eq_mul] at h
            exact Nat.eq_of_mul_eq_mul_right hd.1 (add_left_cancel h)),
        Finset.card_range]
    · ext y
      constructor
      · intro hy
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
        exact ⟨i, by exact_mod_cast Finset.mem_range.mp hi, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact Finset.mem_coe.mpr
          (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by exact_mod_cast hi), rfl⟩)
  · have haA : a ∈ A := by simpa using hmem_term 0 hk
    have ha_ng := hgap a haA
    have ha_pos : 1 ≤ a := by omega
    refine ⟨a - 1, ((Finset.range k).image (fun i : ℕ => (a - 1) + i • d) : Set ℕ), ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨i, hi_mem, rfl⟩ := Finset.mem_image.mp hy
      have hi : i < k := Finset.mem_range.mp hi_mem
      have hmA : a + i * d ∈ A := hmem_term i hi
      have hnle : ¬ (a + i * d ≤ t) := by omega
      have hf_eq : f (a + i * d) = (a - 1) + i * d := by
        dsimp [f]
        rw [if_neg hnle]
        omega
      have hm_im : (a - 1) + i * d ∈ A.image f :=
        Finset.mem_image.mpr ⟨a + i * d, hmA, hf_eq⟩
      simpa [nsmul_eq_mul] using hm_im
    · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
        Finset.card_image_of_injective _
          (fun x y h => by
            rw [nsmul_eq_mul, nsmul_eq_mul] at h
            exact Nat.eq_of_mul_eq_mul_right hd.1 (add_left_cancel h)),
        Finset.card_range]
    · ext y
      constructor
      · intro hy
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
        exact ⟨i, by exact_mod_cast Finset.mem_range.mp hi, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact Finset.mem_coe.mpr
          (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by exact_mod_cast hi), rfl⟩)

lemma compress_cover_le (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) :
    ∀ B : ℕ, ∀ A : Finset ℕ,
      (∀ x ∈ A, x ≤ B) →
      Green37.IsAPCover (A : Set ℕ) N k →
      ∃ A' : Finset ℕ, A'.card ≤ A.card ∧
        Green37.IsAPCover (A' : Set ℕ) N k ∧
        ∀ x ∈ A', x ≤ A'.card * N := by
  classical
  intro B
  induction B with
  | zero =>
    intro A hB hcov
    exact ⟨A, le_rfl, hcov, fun x hx => le_trans (hB x hx) (Nat.zero_le _)⟩
  | succ B ih =>
    intro A hB hcov
    by_cases hle : B + 1 ≤ A.card * N
    · exact ⟨A, le_rfl, hcov, fun x hx => le_trans (hB x hx) hle⟩
    · by_cases hmem : B + 1 ∈ A
      · have hgt : A.card * N < B + 1 := by omega
        obtain ⟨j, hj, hgap_j⟩ := exists_empty_window A N B hmem hgt
        set t : ℕ := j * N
        have htN : (j + 1) * N = t + N := by
          dsimp [t]
          ring
        have hgap : ∀ x ∈ A, ¬ (t + 1 ≤ x ∧ x ≤ t + N) := by
          intro x hx
          rw [← htN]
          exact hgap_j x hx
        let f : ℕ → ℕ := fun x => if x ≤ t then x else x - 1
        let A₁ : Finset ℕ := A.image f
        have hA₁_card : A₁.card ≤ A.card := Finset.card_image_le
        have hjN_le : t + N ≤ A.card * N := by
          rw [← htN]
          exact Nat.mul_le_mul_right N (by omega)
        have hA₁_B : ∀ y ∈ A₁, y ≤ B := by
          intro y hy
          obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.mp hy
          have hxB : x ≤ B + 1 := hB x hxA
          dsimp [f]
          split_ifs with hxt
          · omega
          · omega
        have hA₁_cov : Green37.IsAPCover (A₁ : Set ℕ) N k :=
          compress_step_cover A N k t hk hgap hcov
        obtain ⟨A', hA'_card, hA'_cov, hA'_bdd⟩ := ih A₁ hA₁_B hA₁_cov
        exact ⟨A', le_trans hA'_card hA₁_card, hA'_cov, hA'_bdd⟩
      · have hB_strict : ∀ x ∈ A, x ≤ B := by
          intro x hx
          have hxle : x ≤ B + 1 := hB x hx
          have hxne : x ≠ B + 1 := fun heq => hmem (heq ▸ hx)
          omega
        exact ih A hB_strict hcov

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1_H1_R1.H2 := by
  intro N k hN hk
  obtain ⟨A₀, hcard₀, hcov₀⟩ := Nat.sInf_mem (ap_cover_set_nonempty N k)
  have hcard₀' : A₀.card = Green37.m N k := hcard₀
  obtain ⟨A', hcard_le, hcov', hbdd'⟩ :=
    compress_cover_le N k hN hk (A₀.sup id) A₀
      (fun x hx => Finset.le_sup (f := id) hx) hcov₀
  have hle_card : Green37.m N k ≤ A'.card := Nat.sInf_le ⟨A', rfl, hcov'⟩
  have heq_card : A'.card = Green37.m N k :=
    le_antisymm (le_trans hcard_le (le_of_eq hcard₀')) hle_card
  refine ⟨A', heq_card, hcov', ?_⟩
  intro x hx
  rw [← heq_card]
  exact hbdd' x hx
