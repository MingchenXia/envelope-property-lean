import EnvelopeProperty.ERealAntitoneLimits

/-! # Actual antitone directed extended-real limits -/

open Filter Topology
noncomputable section
namespace EnvelopeProperty

/-- A decreasing net on a nonempty directed preorder converges to its actual infimum. -/
theorem iInf_eq_of_tendsto_of_antitone_directed {J : Type*} [Preorder J]
    [IsDirected J (· ≤ ·)] [Nonempty J] {a : J → EReal} {l : EReal}
    (ha : Antitone a) (h : Tendsto a atTop (𝓝 l)) : (⨅ j, a j) = l :=
  tendsto_nhds_unique (tendsto_atTop_iInf ha) h

/-- Genuine finite upper bounds exclude the exceptional pairs of extended-real addition. -/
theorem iInf_add_of_antitone_directed {J : Type*} [Preorder J]
    [IsDirected J (· ≤ ·)] [Nonempty J] {a b : J → EReal}
    (ha : Antitone a) (hb : Antitone b) (j₀ : J)
    (ha₀ : a j₀ ≠ ⊤) (hb₀ : b j₀ ≠ ⊤) :
    (⨅ j, a j + b j) = (⨅ j, a j) + ⨅ j, b j := by
  have h₁ : (⨅ j, a j) ≠ ⊤ := ne_top_of_le_ne_top ha₀ (iInf_le _ j₀)
  have h₂ : (⨅ j, b j) ≠ ⊤ := ne_top_of_le_ne_top hb₀ (iInf_le _ j₀)
  refine iInf_eq_of_tendsto_of_antitone_directed
    (fun _ _ hij => add_le_add (ha hij) (hb hij)) ?_
  exact (EReal.continuousAt_add (p := ((⨅ j, a j), (⨅ j, b j)))
    (Or.inl h₁) (Or.inr h₂)).tendsto.comp
      ((tendsto_atTop_iInf ha).prodMk_nhds (tendsto_atTop_iInf hb))

end EnvelopeProperty
