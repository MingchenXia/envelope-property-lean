/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.Hartogs
import EnvelopeProperty.Local.ExhaustionDef

/-!
# The hull criterion

FHX Lemma 5.19 (`lem:hull-criterion`). Let `u` be upper semicontinuous, of logarithmic growth and
not identically `-∞`, put `ũ = u ∘ p + log|w|` on `Ỹ = Y × 𝔸¹` and let `ρ̃` be nonnegative,
finite and upper semicontinuous on `Ỹ^an` (e.g. a strict exhaustion). If `ũ + c ρ̃` satisfies the
hull inequality for every rational `c > 0`, then `u` is regularizable.

For compact `K ⊆ {ũ + cρ̃ < 0}` the maximum of the upper semicontinuous function `ũ + cρ̃` on `K`
is negative, so `K̂ ⊆ {ũ + cρ̃ < 0}`: these open sets are Runge. They increase to `{ũ < 0}` as
`c ↓ 0`, so `{ũ < 0}` is Runge and the Hartogs lemma applies.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

universe u v

open Berk Polynomial

/-- The sum of two upper semicontinuous `EReal`-valued functions that never take the value `⊤`
is upper semicontinuous. -/
theorem upperSemicontinuous_add_of_ne_top {X : Type*} [TopologicalSpace X] {f g : X → EReal}
    (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g) (hft : ∀ x, f x ≠ ⊤)
    (hgt : ∀ x, g x ≠ ⊤) : UpperSemicontinuous fun x => f x + g x :=
  hf.add' hg fun x => EReal.continuousAt_add (Or.inl (hft x)) (Or.inr (hgt x))

/-- On a nonempty compact set, an upper semicontinuous function bounded above by a negative
constant pointwise has a negative supremum. -/
theorem iSup_lt_of_isCompact_of_forall_lt {X : Type*} [TopologicalSpace X] {f : X → EReal}
    (hf : UpperSemicontinuous f) {K : Set X} (hK : IsCompact K) {c : EReal}
    (hc : ∀ x ∈ K, f x < c) : (⨆ x ∈ K, f x) < c ∨ K = ∅ := by
  rcases K.eq_empty_or_nonempty with h | hne
  · exact Or.inr h
  · left
    obtain ⟨a, ha, hmax⟩ := (hf.upperSemicontinuousOn K).exists_isMaxOn hne hK
    exact lt_of_le_of_lt (iSup₂_le fun x hx => hmax hx) (hc a ha)

variable {k : Type u} [Field k] [IsAlgClosed k] [Countable k] [WuRegularization.{u, v} k]
  {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
  [IsIntegrallyClosed A]

/-- **Hull criterion** (FHX Lemma 5.19). -/
theorem IsRegularizable.of_hullIneq_add_smul (u : Berk k A → EReal)
    (husc : UpperSemicontinuous u) (hlog : HasLogGrowth u) (hne : ∃ x, u x ≠ ⊥)
    (ρ : Berk k A[X] → EReal) (hρ0 : ∀ z, 0 ≤ ρ z) (hρtop : ∀ z, ρ z ≠ ⊤)
    (hρusc : ∀ c : ℚ, 0 < c → UpperSemicontinuous fun z => ((c : ℝ) : EReal) * ρ z)
    (h : ∀ c : ℚ, 0 < c → SatisfiesHullIneq fun z : Berk k A[X] =>
      u (proj z) + logAbs (X : A[X]) z + ((c : ℝ) : EReal) * ρ z) :
    IsRegularizable u := by
  -- `u` never takes the value `⊤`
  obtain ⟨g, C, hgC⟩ := hlog
  have hutop : ∀ x, u x ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top (EReal.add_ne_top (g.eval_ne_top x) (EReal.coe_ne_top C)) (hgC x)
  set ũ : Berk k A[X] → EReal := fun z => u (proj z) + logAbs (X : A[X]) z with hũ
  have hũusc : UpperSemicontinuous ũ :=
    upperSemicontinuous_add_of_ne_top (husc.comp continuous_proj)
      (continuous_logAbs _).upperSemicontinuous (fun z => hutop _) (fun z => logAbs_ne_top _ _)
  have hũtop : ∀ z, ũ z ≠ ⊤ := fun z => EReal.add_ne_top (hutop _) (logAbs_ne_top _ _)
  -- the functions `ũ + c ρ`
  set D : ℕ → Set (Berk k A[X]) := fun n =>
    {z | ũ z + (((1 / (n + 1 : ℚ) : ℚ) : ℝ) : EReal) * ρ z < 0} with hD
  have hcpos : ∀ n : ℕ, (0 : ℚ) < 1 / (n + 1 : ℚ) := fun n => by positivity
  have hcρtop : ∀ (c : ℚ), 0 < c → ∀ z, ((c : ℝ) : EReal) * ρ z ≠ ⊤ := by
    intro c hc z
    have hρbot : ρ z ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) (hρ0 z)
    lift ρ z to ℝ using ⟨hρtop z, hρbot⟩ with r
    rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  have hsumusc : ∀ n : ℕ, UpperSemicontinuous fun z =>
      ũ z + (((1 / (n + 1 : ℚ) : ℚ) : ℝ) : EReal) * ρ z := fun n =>
    upperSemicontinuous_add_of_ne_top hũusc (hρusc _ (hcpos n)) hũtop (hcρtop _ (hcpos n))
  have hDopen : ∀ n, IsOpen (D n) := fun n => (hsumusc n).isOpen_preimage 0
  have hDrunge : ∀ n, IsRunge (D n) := by
    intro n K hKD hK y hy
    rcases iSup_lt_of_isCompact_of_forall_lt (hsumusc n) hK (fun x hx => hKD hx) with hlt | hemp
    · exact lt_of_le_of_lt (h _ (hcpos n) K hK y hy) hlt
    · rw [hemp, hull_empty] at hy; exact absurd hy (Set.notMem_empty y)
  have hDmono : Monotone D := by
    intro m n hmn z hz
    simp only [hD, Set.mem_ofPred_eq] at hz ⊢
    refine lt_of_le_of_lt (add_le_add le_rfl ?_) hz
    exact mul_le_mul_of_nonneg_right (by
      have : (1 / (n + 1 : ℚ)) ≤ 1 / (m + 1 : ℚ) := by
        gcongr
      exact_mod_cast this) (hρ0 z)
  have hunion : (⋃ n, D n) = {z | ũ z < 0} := by
    ext z
    simp only [Set.mem_iUnion, hD, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      refine lt_of_le_of_lt ?_ hn
      have : (0 : EReal) ≤ (((1 / (n + 1 : ℚ) : ℚ) : ℝ) : EReal) * ρ z :=
        mul_nonneg (by exact_mod_cast (hcpos n).le) (hρ0 z)
      simpa using add_le_add (le_refl (ũ z)) this
    · intro hz
      -- choose `n` with `ρ z / (n+1) < -ũ z`
      have hρbot : ρ z ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) (hρ0 z)
      lift ρ z to ℝ using ⟨hρtop z, hρbot⟩ with r hr
      by_cases hũbot : ũ z = ⊥
      · exact ⟨0, by rw [hũbot, EReal.bot_add]; exact EReal.bot_lt_zero⟩
      · lift ũ z to ℝ using ⟨hũtop z, hũbot⟩ with a ha
        have ha0 : a < 0 := by exact_mod_cast hz
        obtain ⟨n, hn⟩ := exists_nat_gt (r / (-a))
        refine ⟨n, ?_⟩
        rw [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_zero, EReal.coe_lt_coe_iff]
        have hr0 : 0 ≤ r := by exact_mod_cast hr ▸ hρ0 z
        have hn1 : (0 : ℝ) < n + 1 := by positivity
        have : r / (n + 1) < -a := by
          rw [div_lt_iff₀ hn1]
          have := (div_lt_iff₀ (by linarith : (0:ℝ) < -a)).1 hn
          nlinarith
        push_cast
        have : 1 / ((n : ℝ) + 1) * r = r / (n + 1) := by ring
        linarith
  have hrunge : IsRunge {z : Berk k A[X] | ũ z < 0} :=
    hunion ▸ isRunge_iUnion_of_monotone hDopen hDrunge hDmono
  exact IsRegularizable.of_isRunge_hartogs u husc ⟨g, C, hgC⟩ hne hrunge

end EnvelopeProperty
