import OMAReductions.R_Green37_green_37_lower_bound_R1

-- Step H3 of reduction Green37.green_37_lower_bound.R1
-- Credit: @estebanlearns
-- Proves k = 1 positivity (1 ≤ m(N, 1) for N ≥ 1) and the sharp Rédei-Rényi / Golomb
-- difference-basis bound at k = 2: 2 * N ≤ m(N, 2) * (m(N, 2) - 1) (tight at N = 1, 3, 6).

/-!
# Step H3 of Reduction Green37.green_37_lower_bound.R1
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

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H3 := by
  refine ⟨?_, ?_⟩
  · intro N hN
    obtain ⟨A, hcard, hcov⟩ := Nat.sInf_mem (ap_cover_set_nonempty N 1)
    have hcard' : A.card = Green37.m N 1 := hcard
    change 1 ≤ Green37.m N 1
    rw [← hcard']
    obtain ⟨a, s, hsA, _, hs_eq⟩ := hcov 1 ⟨le_rfl, hN⟩
    have ha_mem_s : a + (0 : ℕ) • (1 : ℕ) ∈ s := by
      rw [hs_eq]
      exact ⟨0, by exact_mod_cast (by omega : 0 < 1), rfl⟩
    have ha_mem_A : a + (0 : ℕ) • (1 : ℕ) ∈ A := hsA ha_mem_s
    exact Finset.one_le_card.mpr ⟨a + (0 : ℕ) • (1 : ℕ), ha_mem_A⟩
  · intro N
    obtain ⟨A, hcard, hcov⟩ := Nat.sInf_mem (ap_cover_set_nonempty N 2)
    have hcard' : A.card = Green37.m N 2 := hcard
    change 2 * N ≤ Green37.m N 2 * (Green37.m N 2 - 1)
    rw [← hcard']
    let P₁ : Finset (ℕ × ℕ) := (A ×ˢ A).filter (fun p => p.1 < p.2)
    let P₂ : Finset (ℕ × ℕ) := (A ×ˢ A).filter (fun p => p.2 < p.1)
    let D : Finset (ℕ × ℕ) := A.image (fun x => (x, x))
    let I : Finset ℕ := (Finset.range N).image (fun i => i + 1)
    have hI_card : I.card = N := by
      rw [Finset.card_image_of_injective _ (fun x y h => by omega), Finset.card_range]
    have hsub : I ⊆ P₁.image (fun p => p.2 - p.1) := by
      intro d hd
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
      rw [Finset.mem_range] at hi
      obtain ⟨a, s, hsA, _, hs_eq⟩ := hcov (i + 1) ⟨by omega, by omega⟩
      have h0 : a + (0 : ℕ) • (i + 1) ∈ s := by
        rw [hs_eq]
        exact ⟨0, by exact_mod_cast (by omega : 0 < 2), rfl⟩
      have h1 : a + (1 : ℕ) • (i + 1) ∈ s := by
        rw [hs_eq]
        exact ⟨1, by exact_mod_cast (by omega : 1 < 2), rfl⟩
      have haA : a ∈ A := by
        have h0A : a + (0 : ℕ) • (i + 1) ∈ (A : Set ℕ) := hsA h0
        simpa using h0A
      have hadA : a + (i + 1) ∈ A := by
        have h1A : a + (1 : ℕ) • (i + 1) ∈ (A : Set ℕ) := hsA h1
        simpa using h1A
      have hp_mem : (a, a + (i + 1)) ∈ P₁ := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haA, hadA⟩, ?_⟩
        omega
      refine Finset.mem_image.mpr ⟨(a, a + (i + 1)), hp_mem, ?_⟩
      omega
    have hN_le : N ≤ P₁.card := by
      have hc1 : I.card ≤ (P₁.image (fun p => p.2 - p.1)).card := Finset.card_le_card hsub
      have hc2 : (P₁.image (fun p => p.2 - p.1)).card ≤ P₁.card := Finset.card_image_le
      omega
    have hP₂_eq : P₂ = P₁.image Prod.swap := by
      ext ⟨x, y⟩
      simp only [P₁, P₂, Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.exists]
      constructor
      · rintro ⟨⟨hx, hy⟩, hyx⟩
        exact ⟨y, x, ⟨⟨hy, hx⟩, hyx⟩, rfl⟩
      · rintro ⟨a, b, ⟨⟨ha, hb⟩, hab⟩, hswap⟩
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hswap
        exact ⟨⟨hb, ha⟩, hab⟩
    have hP₂_card : P₂.card = P₁.card := by
      rw [hP₂_eq, Finset.card_image_of_injective _ Prod.swap_injective]
    have hD_card : D.card = A.card :=
      Finset.card_image_of_injective _ (fun x y h => (Prod.ext_iff.mp h).1)
    have hdisj12 : Disjoint P₁ P₂ := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 : p.1 < p.2 := (Finset.mem_filter.mp hp1).2
      have h2 : p.2 < p.1 := (Finset.mem_filter.mp hp2).2
      omega
    have hdisjD : Disjoint (P₁ ∪ P₂) D := by
      rw [Finset.disjoint_left]
      intro p hp12 hpD
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hpD
      rcases Finset.mem_union.mp hp12 with hp1 | hp2
      · have h1 : x < x := (Finset.mem_filter.mp hp1).2
        omega
      · have h2 : x < x := (Finset.mem_filter.mp hp2).2
        omega
    have hsub_prod : (P₁ ∪ P₂) ∪ D ⊆ A ×ˢ A := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp12 | hpD
      · rcases Finset.mem_union.mp hp12 with hp1 | hp2
        · exact (Finset.mem_filter.mp hp1).1
        · exact (Finset.mem_filter.mp hp2).1
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hpD
        exact Finset.mem_product.mpr ⟨hx, hx⟩
    have hcard_sum : P₁.card + P₁.card + A.card ≤ A.card * A.card := by
      have hle : ((P₁ ∪ P₂) ∪ D).card ≤ (A ×ˢ A).card := Finset.card_le_card hsub_prod
      rw [Finset.card_union_of_disjoint hdisjD, Finset.card_union_of_disjoint hdisj12,
        hP₂_card, hD_card, Finset.card_product] at hle
      exact hle
    rcases hM : A.card with _ | m
    · rw [hM] at hcard_sum
      omega
    · rw [hM] at hcard_sum
      have hsub1 : m + 1 - 1 = m := by omega
      have hmul : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
      rw [hsub1]
      omega
