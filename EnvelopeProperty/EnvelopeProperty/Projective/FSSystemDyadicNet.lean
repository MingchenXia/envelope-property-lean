import EnvelopeProperty.Projective.FSSystemRegularization

/-! # Genuine dyadic finite Fubini--Study nets without countability -/

open scoped Topology Classical
open Filter Topology
noncomputable section
universe u
namespace EnvelopeProperty.FSSystem

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
  {r : ℕ} {F : FSSystem K r} {θ : Fin r → ℚ} {u : K → EReal}

/-- Every original global psh function has a genuine decreasing finite FS net
in dyadic classes. The increasing, cofinal dyadic index is constructed from
actual class convergence; no second-countability or sequence premise occurs. -/
theorem IsPSH.exists_isFinFS_net_dyadic
    (h : F.IsPSH (fun c => (θ c : ℝ)) u) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (n : ι → ℕ) (f : ι → K → EReal), Monotone n ∧ Tendsto n atTop atTop ∧
      (∀ i, F.IsFinFS (θ + fun _ => ((2 : ℚ) ^ n i)⁻¹) (f i)) ∧
      (∀ x, Antitone fun i => f i x) ∧ ∀ x, u x = ⨅ i, f i x := by
  obtain ⟨ι, hι, hd, hn, a, f, hf, _, ha, hanti, hinf⟩ := h.exists_isFinFS_net_gt
  let : Preorder ι := hι
  let : IsDirected ι (· ≤ ·) := hd
  let : Nonempty ι := hn
  have hev (n : ℕ) : ∀ᶠ i in atTop, a i ≤ θ + fun _ => ((2 : ℚ) ^ n)⁻¹ := by
    show ∀ᶠ i in atTop, ∀ c, a i c ≤ (θ + fun _ => ((2 : ℚ) ^ n)⁻¹ : Fin r → ℚ) c
    refine eventually_all.2 fun c => ?_
    have hlt : (θ c : ℝ) < ((θ c + ((2 : ℚ) ^ n)⁻¹ : ℚ) : ℝ) := by
      push_cast
      have hpos : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
      linarith
    filter_upwards [(tendsto_pi_nhds.1 ha c).eventually (gt_mem_nhds hlt)] with i hi
    simp only [Pi.add_apply]
    exact_mod_cast hi.le
  let D := {p : ℕ × ι // a p.2 ≤ θ + fun _ => ((2 : ℚ) ^ p.1)⁻¹}
  have hex (n : ℕ) (i : ι) : ∃ p : D, p.1.1 = n ∧ i ≤ p.1.2 := by
    obtain ⟨j, hj⟩ := (eventually_atTop.1 (hev n))
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    exact ⟨⟨(n, k), hj k hjk⟩, rfl, hik⟩
  have : Nonempty D := by
    obtain ⟨p, _, _⟩ := hex 0 (Classical.arbitrary ι)
    exact ⟨p⟩
  have : IsDirected D (· ≤ ·) := ⟨by
    intro p q
    obtain ⟨i, hpi, hqi⟩ := exists_ge_ge p.1.2 q.1.2
    obtain ⟨s, hsn, his⟩ := hex (Max.max p.1.1 q.1.1) i
    refine ⟨s, ?_, ?_⟩
    · exact ⟨hsn ▸ le_max_left _ _, hpi.trans his⟩
    · exact ⟨hsn ▸ le_max_right _ _, hqi.trans his⟩⟩
  have hnmono : Monotone (fun p : D => p.1.1) := fun _ _ hpq => hpq.1
  have hntop : Tendsto (fun p : D => p.1.1) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    obtain ⟨p, hpn, _⟩ := hex n (Classical.arbitrary ι)
    filter_upwards [eventually_ge_atTop p] with q hpq
    exact hpn ▸ hpq.1
  refine ⟨D, inferInstance, inferInstance, inferInstance, (fun p => p.1.1),
    (fun p => f p.1.2), hnmono, hntop, (fun p => (hf p.1.2).mono p.2),
    (fun x _ _ hpq => hanti x hpq.2), ?_⟩
  intro x
  rw [hinf x]
  apply le_antisymm
  · exact le_iInf fun p => iInf_le _ p.1.2
  · apply le_iInf
    intro i
    obtain ⟨p, _, hip⟩ := hex 0 i
    exact (iInf_le (fun p : D => f p.1.2 x) p).trans (hanti x hip)

end EnvelopeProperty.FSSystem
