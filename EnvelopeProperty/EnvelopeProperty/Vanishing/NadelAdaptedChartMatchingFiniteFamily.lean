import EnvelopeProperty.Vanishing.NadelKummerCoverTowerCore

/-! # Actual finite simultaneous-root algebras and whole extensionality

Every ring and map is the existing native successive AdjoinRoot construction.
The finite family retains all original root generators, even for unit or
repeated coefficients. No component or root value is selected.
-/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching

open NadelFiniteDualityTower
namespace VaryingFamily

variable {R : Type u} [CommRing R] {q : ℕ} (N : Fin q → ℕ) (c : Fin q → R)

/-- Extend original finite coefficient labels for the native tower;
values after the final stage are never adjoined. -/
def coefficient (i : ℕ) : R := if hi : i < q then c ⟨i, hi⟩ else 0

/-- Extend the SAME original positive degrees to the native Nat-indexed tower. -/
def degree (i : ℕ) : ℕ := if hi : i < q then N ⟨i, hi⟩ - 1 else 0

/-- The native tower degree is exactly the SAME original root degree. -/
theorem degree_eq (hpositive : ∀ i, 0 < N i) (i : Fin q) :
    degree N i + 1 = N i := by
  simp only [degree, dif_pos i.isLt]
  exact Nat.sub_add_cancel (hpositive i)

/-- The WHOLE actual simultaneous-root algebra, as native successive monic quotients. -/
abbrev Ring : Type u := independentRootRing (degree N) (coefficient c) q

/-- The SAME actual original coefficient homomorphism. -/
abbrev structureMap : R →+* Ring N c := independentRootStructure (degree N) (coefficient c) q

/-- Every original finite-family root in the actual final stage. -/
def root (i : Fin q) : Ring N c :=
  NadelKummerCover.Tower.rootInStage (degree N) (coefficient c) (Nat.succ_le_of_lt i.isLt)

/-- Every original root has the SAME original positive-degree equation. -/
theorem root_pow (hpositive : ∀ i, 0 < N i) (i : Fin q) : root N c i ^ N i = structureMap N c (c i) := by
  have hp := NadelKummerCover.Tower.rootInStage_pow (degree N) (coefficient c)
    (Nat.succ_le_of_lt i.isLt)
  simpa only [root, coefficient, dif_pos i.isLt, degree_eq N hpositive i] using hp


variable (hpositive : ∀ i, 0 < N i) {S : Type u} [CommRing S] (f : R →+* S) (y : Fin q → S)
    (hy : ∀ i, y i ^ N i = f (c i))

include hy hpositive in
private theorem extended_relation (i : ℕ) :
    coefficient y i ^ (degree N i + 1) = f (coefficient c i) := by
  by_cases hi : i < q
  · simpa only [coefficient, dif_pos hi, ← degree_eq N hpositive ⟨i, hi⟩] using hy ⟨i, hi⟩
  · simp only [coefficient, dif_neg hi, zero_pow (Nat.succ_ne_zero (degree N i)), map_zero]

/-- The genuine universal evaluation of the entire original finite root family. -/
def evaluate : Ring N c →+* S :=
  NadelKummerCover.Tower.evaluation (degree N) (coefficient c) f (coefficient y)
    (extended_relation N c hpositive f y hy) q

/-- The WHOLE original coefficient map is retained by this actual evaluation. -/
theorem evaluate_structure : (evaluate N c hpositive f y hy).comp (structureMap N c) = f :=
  NadelKummerCover.Tower.evaluation_structure _ _ _ _ _ _

/-- Every original root has its specified actual universal evaluation value. -/
theorem evaluate_root (i : Fin q) : evaluate N c hpositive f y hy (root N c i) = y i := by
  simpa only [evaluate, root, coefficient, dif_pos i.isLt] using
    NadelKummerCover.Tower.evaluation_rootInStage (degree N) (coefficient c)
      f (coefficient y) (extended_relation N c hpositive f y hy) (Nat.succ_le_of_lt i.isLt)

/-- Equality on the original coefficients and EVERY original root proves
equality on the WHOLE simultaneous-root algebra, including every component. -/
theorem hom_ext (p₁ p₂ : Ring N c →+* S)
    (hc : p₁.comp (structureMap N c) = p₂.comp (structureMap N c))
    (hr : ∀ i, p₁ (root N c i) = p₂ (root N c i)) : p₁ = p₂ := by
  have H : ∀ (k : ℕ) (hk : k ≤ q),
      p₁.comp (NadelKummerCover.Tower.transition (degree N) (coefficient c) hk) =
        p₂.comp (NadelKummerCover.Tower.transition (degree N) (coefficient c) hk) := by
    intro k
    induction k with
    | zero =>
        intro hk
        have ht := NadelKummerCover.Tower.transition_structure (degree N) (coefficient c) hk
        change NadelKummerCover.Tower.transition (degree N) (coefficient c) hk = structureMap N c at ht
        rw [ht]
        exact hc
    | succ k ih =>
        intro hk
        have hk' : k ≤ q := Nat.le_trans (Nat.le_succ_of_le (Nat.le_refl k)) hk
        apply AdjoinRoot.ringHom_ext
        · change (p₁.comp (NadelKummerCover.Tower.transition (degree N) (coefficient c) hk)).comp
              (independentRootStep (degree N) (coefficient c) k) =
            (p₂.comp (NadelKummerCover.Tower.transition (degree N) (coefficient c) hk)).comp
              (independentRootStep (degree N) (coefficient c) k)
          rw [RingHom.comp_assoc, NadelKummerCover.Tower.transition_comp_step,
            RingHom.comp_assoc, NadelKummerCover.Tower.transition_comp_step, ih hk']
        · exact hr ⟨k, Nat.lt_of_succ_le hk⟩
  have h := H q (Nat.le_refl q)
  simpa only [NadelKummerCover.Tower.transition_self, RingHom.comp_id] using h

end VaryingFamily
end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching
