import EnvelopeProperty.Local.FiniteFlatNorm

/-! # Finite weighted sums commute with genuine decreasing directed-net infima -/

open Filter Topology
noncomputable section

namespace EnvelopeProperty

variable {J : Type*} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]

/-- Actual addition commutes with genuine decreasing directed nets that never reach top. -/
theorem iInf_add_of_antitone_net {a b : J → EReal} (ha : Antitone a) (hb : Antitone b)
    (hat : ∀ j, a j ≠ ⊤) (hbt : ∀ j, b j ≠ ⊤) :
    ⨅ j, (a j+b j) = (⨅ j, a j)+(⨅ j, b j) := by
  let j0 : J := Classical.arbitrary J
  have h1 : (⨅ j, a j) ≠ ⊤ := ne_top_of_le_ne_top (hat j0) (iInf_le _ j0)
  have h2 : (⨅ j, b j) ≠ ⊤ := ne_top_of_le_ne_top (hbt j0) (iInf_le _ j0)
  have hsum : Antitone (fun j => a j+b j) := fun i j hij => add_le_add (ha hij) (hb hij)
  apply tendsto_nhds_unique (tendsto_atTop_iInf hsum)
  exact (EReal.continuousAt_add (p := ((⨅ j, a j),(⨅ j, b j))) (Or.inl h1) (Or.inr h2)).tendsto.comp
    ((tendsto_atTop_iInf ha).prodMk_nhds (tendsto_atTop_iInf hb))

/-- Real nonnegative scalar multiplication commutes with actual directed decreasing infima. -/
theorem iInf_coe_mul_of_antitone_net {a : J → EReal} (ha : Antitone a) {c : ℝ} (hc : 0 ≤ c) :
    ⨅ j, (c : EReal)*a j = (c : EReal)*(⨅ j, a j) := by
  rcases hc.eq_or_lt with hc0 | hcpos
  · rw [← hc0]
    simp only [EReal.coe_zero,zero_mul,iInf_const]
  · have hanti : Antitone (fun j => (c : EReal)*a j) := fun i j hij =>
      mul_le_mul_of_nonneg_left (ha hij) (by exact_mod_cast hcpos.le)
    apply tendsto_nhds_unique (tendsto_atTop_iInf hanti)
    have hc' : (c : EReal) ≠ 0 := by exact_mod_cast hcpos.ne'
    have hcont : ContinuousAt (fun p : EReal×EReal => p.1*p.2) ((c : EReal),⨅ j, a j) :=
      EReal.continuousAt_mul (Or.inl hc') (Or.inl hc') (Or.inl (EReal.coe_ne_bot c))
        (Or.inl (EReal.coe_ne_top c))
    exact hcont.tendsto.comp (tendsto_const_nhds.prodMk_nhds (tendsto_atTop_iInf ha))

/-- The actual finite weighted sum is continuous under genuine directed decreasing limits;
bottom, zero weights and empty finite sums are all included. -/
theorem iInf_finsetSum_coe_mul_of_antitone_net {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (a : ι → J → EReal) (ha : ∀ i ∈ s, Antitone (a i))
    (hat : ∀ i ∈ s, ∀ j, a i j ≠ ⊤) :
    ⨅ j, ∑ i ∈ s, (c i : EReal)*a i j = ∑ i ∈ s, (c i : EReal)*(⨅ j, a i j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,iInf_const]
  | insert i s hi ih =>
      have hc' : ∀ k ∈ s, 0 ≤ c k := fun k hk => hc k (Finset.mem_insert_of_mem hk)
      have ha' : ∀ k ∈ s, Antitone (a k) := fun k hk => ha k (Finset.mem_insert_of_mem hk)
      have hat' : ∀ k ∈ s, ∀ j, a k j ≠ ⊤ := fun k hk => hat k (Finset.mem_insert_of_mem hk)
      have hhead : i ∈ insert i s := Finset.mem_insert_self _ _
      have hanti1 : Antitone (fun j => (c i : EReal)*a i j) := fun j k hjk =>
        mul_le_mul_of_nonneg_left (ha i hhead hjk) (by exact_mod_cast hc i hhead)
      have hanti2 : Antitone (fun j => ∑ k ∈ s, (c k : EReal)*a k j) := fun j k hjk =>
        Finset.sum_le_sum fun l hl =>
          mul_le_mul_of_nonneg_left (ha' l hl hjk) (by exact_mod_cast hc' l hl)
      simp only [Finset.sum_insert hi]
      rw [iInf_add_of_antitone_net hanti1 hanti2
        (fun j => ereal_coe_mul_ne_top (hc i hhead) (hat i hhead j))
        (fun j => ereal_finsetSum_ne_top _ _ fun k hk => ereal_coe_mul_ne_top (hc' k hk) (hat' k hk j)),
        iInf_coe_mul_of_antitone_net (ha i hhead) (hc i hhead),ih hc' ha' hat']

end EnvelopeProperty
