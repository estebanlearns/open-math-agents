import FormalConjecturesUtil

/-!
# Fase 2 (Green 37, Katz–Tao route): base lemmas

* `sq_card_le_card_mul_energy`: Cauchy–Schwarz over the fibres of a map `f : s → t`.
* `exists_card_eq_m_cover`: a cover of size exactly `Green37.m N k`.
* `cover_terms`: a uniform choice of starting points `x d` of the progressions of a cover.
* `card_Icc_one`: `#[1, N] = N`.
-/

/- Pinned definitions of `FormalConjectures/GreensOpenProblems/37.lean`.

Verbatim copy (formal-conjectures @ 9097e2f). The scratch CI cache holds only the prebuilt libraries
`FormalConjecturesUtil` and `FormalConjecturesForMathlib` (the problem file itself is not built there), so
this block stands in for `import FormalConjectures.GreensOpenProblems.«37»`. With the real import, delete
this block and the import line above; nothing else changes. -/

namespace Green37

/-- `A` contains an arithmetic progression of length `k` and common difference `d` for every `d ∈ {1, …, N}`. -/
def IsAPCover (A : Set ℕ) (N k : ℕ) : Prop := ∀ d, 1 ≤ d ∧ d ≤ N → Set.ContainsAP A k d

/-- The minimum size of a subset of `ℕ` that contains, for each `d = 1, …, N`,
an arithmetic progression of length `k` with common difference `d`. -/
noncomputable def m (N k : ℕ) : ℕ :=
  sInf { m | ∃ A : Finset ℕ, A.card = m ∧ IsAPCover (A : Set ℕ) N k }

end Green37

namespace G37P2

/-- Cauchy–Schwarz on the fibres of `f`: `#s ^ 2 ≤ #t * #{(x, y) ∈ s × s | f x = f y}`. -/
lemma sq_card_le_card_mul_energy {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → β) (hf : ∀ x ∈ s, f x ∈ t) :
    s.card ^ 2 ≤ t.card * ((s ×ˢ s).filter (fun p => f p.1 = f p.2)).card := by
  have h1 : s.card = ∑ b ∈ t, (s.filter (fun x => f x = b)).card :=
    Finset.card_eq_sum_card_fiberwise hf
  have hmaps : ∀ p ∈ (s ×ˢ s).filter (fun p => f p.1 = f p.2), f p.1 ∈ t := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    exact hf p.1 hp.1.1
  have h2a : ((s ×ˢ s).filter (fun p => f p.1 = f p.2)).card
      = ∑ b ∈ t, (((s ×ˢ s).filter (fun p => f p.1 = f p.2)).filter
          (fun p => f p.1 = b)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ b ∈ t,
      (((s ×ˢ s).filter (fun p => f p.1 = f p.2)).filter (fun p => f p.1 = b)).card
        = (s.filter (fun x => f x = b)).card ^ 2 := by
    intro b _
    have hset : ((s ×ˢ s).filter (fun p => f p.1 = f p.2)).filter (fun p => f p.1 = b)
        = (s.filter (fun x => f x = b)) ×ˢ (s.filter (fun x => f x = b)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨⟨hp1, hp2⟩, h12⟩, hb⟩
        exact ⟨⟨hp1, hb⟩, hp2, h12.symm.trans hb⟩
      · rintro ⟨⟨hp1, hb1⟩, hp2, hb2⟩
        exact ⟨⟨⟨hp1, hp2⟩, hb1.trans hb2.symm⟩, hb1⟩
    rw [hset, Finset.card_product, sq]
  have h2 : ((s ×ˢ s).filter (fun p => f p.1 = f p.2)).card
      = ∑ b ∈ t, (s.filter (fun x => f x = b)).card ^ 2 :=
    h2a.trans (Finset.sum_congr rfl hfib)
  have hcs : (∑ b ∈ t, (s.filter (fun x => f x = b)).card) ^ 2
      ≤ t.card * ∑ b ∈ t, (s.filter (fun x => f x = b)).card ^ 2 :=
    sq_sum_le_card_mul_sum_sq (s := t) (f := fun b => (s.filter (fun x => f x = b)).card)
  rw [h1, h2]
  exact hcs

/-- The interval `[0, kN]` is an `(N, k)`-cover. -/
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

/-- A cover whose size is exactly `Green37.m N k`. -/
lemma exists_card_eq_m_cover (N k : ℕ) :
    ∃ A : Finset ℕ, A.card = Green37.m N k ∧ Green37.IsAPCover (A : Set ℕ) N k := by
  obtain ⟨A, hcard, hcov⟩ := Nat.sInf_mem (ap_cover_set_nonempty N k)
  exact ⟨A, hcard, hcov⟩

/-- Starting points `x d` of the progressions of a cover, chosen uniformly in `d`. -/
lemma cover_terms {A : Finset ℕ} {N k : ℕ} (h : Green37.IsAPCover (A : Set ℕ) N k) :
    ∃ x : ℕ → ℕ, ∀ d, 1 ≤ d ∧ d ≤ N → ∀ i, i < k → x d + i * d ∈ A := by
  have key : ∀ d, 1 ≤ d ∧ d ≤ N → ∃ a : ℕ, ∀ i, i < k → a + i * d ∈ A := by
    intro d hd
    obtain ⟨a, s, hsA, _, hs_eq⟩ := h d hd
    refine ⟨a, ?_⟩
    intro i hi
    have hms : a + i • d ∈ s := by
      rw [hs_eq]
      exact ⟨i, by exact_mod_cast hi, rfl⟩
    have hmA : a + i • d ∈ (A : Set ℕ) := hsA hms
    simpa [nsmul_eq_mul] using hmA
  choose! x hx using key
  exact ⟨x, hx⟩

/-- `#[1, N] = N`. -/
lemma card_Icc_one (N : ℕ) : (Finset.Icc 1 N).card = N := by
  have h := Nat.card_Icc 1 N
  omega

end G37P2

#print axioms G37P2.sq_card_le_card_mul_energy
#print axioms G37P2.exists_card_eq_m_cover
#print axioms G37P2.cover_terms
#print axioms G37P2.card_Icc_one
