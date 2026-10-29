/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.FSSystem

/-!
# Regularization of psh functions of a Fubini–Study system

For a Fubini–Study system `F` of rank `r` on a compact space `K` (`EnvelopeProperty.FSSystem`,
blueprint `def:pg-fs-system`), this file proves the regularization theorems of the blueprint
chapter `projective-general.tex`, modelled on Boucksom–Jonsson, *Global pluripotential theory over
a trivially valued field* (BJ22), pshample and countreg, in the form used by
Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX), Lemma 5.10(1)
(`lem:compactification`): approximation by **finite rational** Fubini–Study functions, in a
**fixed class**.

## Regularization (`thm:pg-regularization`)

* `FSSystem.IsPSH.exists_isFinFS_net_gt` (part (1)): every `u ∈ PSH(θ)` is the limit of a
  decreasing net `f_α ∈ 𝓗_fin(a_α)` with `a_α ∈ ℚ^r`, `a_α > θ` coordinatewise and `a_α → θ`.
  From the finite net `g_β ∈ 𝓗_fin(b_β)` of `thm:pg-psh2`(2), on the product with `ℕ` choose
  rational `a_{β,N}` with coordinates in `(max(b_{β,c}, θ_c), max(b_{β,c}, θ_c) + 1/(N+1))` and use
  (FS2).
* `FSSystem.IsPSH.exists_isFinFS_net_of_pos` (part (2)): if `θ ∈ ℚ^r` has positive coordinates,
  `u` is the limit of a decreasing net in `𝓗_fin(θ)`. After normalizing `u' = u - M ≤ 0`, for
  `σ ∈ ℚ ∩ (0, 1)` the classes `b_β` of a finite net of `u'` eventually satisfy `σ b_β ≤ θ`
  coordinatewise (here the positivity of all coordinates of `θ` is used), so `σ u'` is a
  decreasing limit in `𝓗_fin(θ)` (FS4, FS2); as `σ ↑ 1` the functions `σ u'` decrease to `u'`,
  and the diagonal lemma `IsDecrNetLimit.of_antitone_of_finite_rat` for the single family
  `𝓗_fin(θ)` gives a decreasing net in `𝓗_fin(θ)` with limit `u'`; add `M` back (FS3).

The blueprint writes `σ = τ⁻¹` with `τ ∈ ℚ_{>1}` and uses the net of part (1); we use the net of
`thm:pg-psh2`(2) directly, which is all the argument needs.

## Countable regularization (`cor:pg-countable-regularization`)

For second countable `K` (e.g. `K = X^an` for countable `k`):

* `FSSystem.IsPSH.exists_isFinFS_seq_gt` and `FSSystem.IsPSH.exists_isFinFS_seq_of_pos`: the nets
  of parts (1) and (2) can be replaced by sequences (`EnvelopeProperty.exists_monotone_iInf_eq`,
  `lem:bj-lindelof`);
* `FSSystem.IsPSH.exists_isFinFS_seq_dyadic` (part (2)): if `θ ∈ ℚ^r`, there is a decreasing
  sequence `f_k ∈ 𝓗_fin(θ + 2^{-k} 𝟙)` with limit `u`.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

namespace FSSystem

universe u

variable {K : Type u} [TopologicalSpace K] {r : ℕ} {F : FSSystem K r} {θ : Fin r → ℝ}
  {u : K → EReal}

/-! ### Regularization (`thm:pg-regularization`) -/

/-- **Regularization** (`thm:pg-regularization`(1); BJ22 pshample): every `u ∈ PSH(θ)` is
the pointwise limit (= infimum) of a decreasing net `f_α ∈ 𝓗_fin(a_α)` of finite rational
Fubini–Study functions whose classes `a_α ∈ ℚ^r` satisfy `a_α > θ` coordinatewise and
`a_α → θ`. -/
theorem IsPSH.exists_isFinFS_net_gt [CompactSpace K] (h : F.IsPSH θ u) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (a : ι → Fin r → ℚ) (f : ι → K → EReal), (∀ i, F.IsFinFS (a i) (f i)) ∧
        (∀ i c, θ c < a i c) ∧ Tendsto (fun i c => (a i c : ℝ)) atTop (𝓝 θ) ∧
          (∀ x, Antitone fun i => f i x) ∧ ∀ x, u x = ⨅ i, f i x := by
  obtain ⟨ι, _, _, _, b, g, hg, hb, hanti, hu⟩ := h.exists_isFinFS_net
  have hδ : ∀ N : ℕ, (0 : ℝ) < 1 / ((N : ℝ) + 1) := fun N => by positivity
  choose q hq using fun (β : ι) (N : ℕ) (c : Fin r) =>
    exists_rat_btwn (lt_add_of_pos_right (Max.max (b β c : ℝ) (θ c)) (hδ N))
  have hdown : Tendsto (fun p : ι × ULift.{u} ℕ => p.2.down) atTop atTop :=
    (tendsto_atTop_atTop.2 fun n => ⟨ULift.up n, fun m hm => hm⟩).comp
      ProjBerk.tendsto_prod_snd_atTop
  have : IsDirected (ι × ULift.{u} ℕ) (· ≤ ·) := isDirected_prod
  refine ⟨ι × ULift.{u} ℕ, inferInstance, inferInstance, inferInstance,
    fun p c => q p.1 p.2.down c, fun p => g p.1, fun p => (hg p.1).mono fun c => ?_,
    fun p c => (le_max_right _ _).trans_lt (hq p.1 p.2.down c).1, ?_,
    fun x p p' hpp' => hanti x (Prod.le_def.1 hpp').1, fun x => ?_⟩
  · have := (le_max_left (b p.1 c : ℝ) (θ c)).trans_lt (hq p.1 p.2.down c).1
    exact_mod_cast this.le
  · refine tendsto_pi_nhds.2 fun c => tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ?_ (fun p => ((le_max_right _ _).trans_lt (hq p.1 p.2.down c).1).le)
      (fun p => (hq p.1 p.2.down c).2.le)
    have h1 := ((tendsto_pi_nhds.1 hb c).comp ProjBerk.tendsto_prod_fst_atTop).max
      (tendsto_const_nhds : Tendsto (fun _ : ι × ULift.{u} ℕ => θ c) atTop (𝓝 (θ c)))
    have h2 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hdown
    have := h1.add h2
    rw [max_self, add_zero] at this
    exact this
  · rw [hu x, iInf_prod]
    exact iInf_congr fun β => iInf_const.symm

/-- **Regularization in a fixed class** (`thm:pg-regularization`(2); BJ22 pshample,
FHX `lem:compactification`(1)): if `θ ∈ ℚ^r` has positive coordinates, every `u ∈ PSH(θ)` is the
pointwise limit (= infimum) of a decreasing net in `𝓗_fin(θ)`. -/
theorem IsPSH.exists_isFinFS_net_of_pos [CompactSpace K] {θ : Fin r → ℚ} (hθ : ∀ c, 0 < θ c)
    (h : F.IsPSH (fun c => (θ c : ℝ)) u) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (f : ι → K → EReal), (∀ i, F.IsFinFS θ (f i)) ∧ (∀ x, Antitone fun i => f i x) ∧
        ∀ x, u x = ⨅ i, f i x := by
  -- the single family `𝓗_fin(θ)`, over a point
  set G : Unit → Set (K → EReal) := fun _ => {f | F.IsFinFS θ f} with hG
  set ρ : Unit → ℝ := fun _ => 0 with hρ
  have hGcont : ∀ s, ∀ f ∈ G s, Continuous f := fun _ f hf => IsFinFS.continuous hf
  have hGfin : ∀ s, ∀ f ∈ G s, ∀ x, f x ≠ ⊥ ∧ f x ≠ ⊤ := fun _ f hf x =>
    ⟨IsFinFS.ne_bot hf x, IsFinFS.ne_top hf x⟩
  have hGadd : ∀ s, ∀ f ∈ G s, ∀ c : ℚ, 0 < c → (fun x => f x + ((c : ℝ) : EReal)) ∈ G s :=
    fun _ f hf c _ => IsFinFS.add_const hf c
  -- normalize `u' = u - M ≤ 0`
  obtain ⟨M, hM⟩ := exists_rat_gt (u F.triv).toReal
  set u' : K → EReal := fun x => u x + ((-(M : ℝ) : ℝ) : EReal) with hu'_def
  have h' : F.IsPSH (fun c => (θ c : ℝ)) u' := h.add_const _
  have hu'0 : ∀ x, u' x ≤ 0 := fun x => by
    have h₁ : u x ≤ ((M : ℝ) : EReal) :=
      (h.le_toReal_apply_triv x).trans (EReal.coe_le_coe_iff.2 hM.le)
    have := add_le_add_left h₁ ((-(M : ℝ) : ℝ) : EReal)
    rwa [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at this
  -- the scaling factors `σₘ = (m + 1) / (m + 2) ↑ 1`
  set σ : ℕ → ℚ := fun m => (m + 1) / (m + 2) with hσ_def
  have hσpos : ∀ m, (0 : ℚ) < σ m := fun m => by simp only [hσ_def]; positivity
  have hσpos' : ∀ m, (0 : ℝ) < σ m := fun m => by exact_mod_cast hσpos m
  have hσlt : ∀ m, (σ m : ℝ) < 1 := fun m => by
    simp only [hσ_def]; push_cast
    rw [div_lt_one (by positivity)]; linarith
  have hσmono : Monotone fun m => (σ m : ℝ) := monotone_nat_of_le_succ fun m => by
    simp only [hσ_def]; push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hσlim : Tendsto (fun m => (σ m : ℝ)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun m : ℕ => (1 : ℝ) - 1 / ((m : ℝ) + 2)) atTop (𝓝 (1 - 0)) := by
      refine tendsto_const_nhds.sub ?_
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h2 := this.comp (tendsto_add_atTop_nat 1)
      refine h2.congr fun m => ?_
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      ring_nf
    rw [sub_zero] at h1
    refine h1.congr fun m => ?_
    simp only [hσ_def]; push_cast
    field_simp
    ring
  -- Step 1: `σₘ u'` is a decreasing limit of a net in `𝓗_fin(θ)`
  have hstep : ∀ m, IsDecrNetLimit.{u} G ρ 0 fun x => ((σ m : ℝ) : EReal) * u' x := by
    intro m
    obtain ⟨ι, _, _, _, b, g, hg, hb, hanti, hu⟩ := h'.exists_isFinFS_net
    -- eventually `σₘ b_β ≤ θ`, since `θ_c < θ_c / σₘ` for every coordinate
    have hev : ∀ᶠ β in atTop, ∀ c, σ m * b β c ≤ θ c := by
      refine eventually_all.2 fun c => ?_
      have hθc : (θ c : ℝ) < θ c / σ m := by
        rw [lt_div_iff₀ (hσpos' m)]
        have h₁ : (0 : ℝ) < θ c := by exact_mod_cast hθ c
        have h₂ := hσlt m
        nlinarith
      filter_upwards [(tendsto_pi_nhds.1 hb c).eventually (gt_mem_nhds hθc)] with β hβ
      have hβ' : (b β c : ℝ) < θ c / σ m := hβ
      rw [lt_div_iff₀ (hσpos' m)] at hβ'
      have : ((σ m * b β c : ℚ) : ℝ) ≤ θ c := by push_cast; linarith
      exact_mod_cast this
    obtain ⟨β₀, hβ₀⟩ := eventually_atTop.1 hev
    have := isDirected_subtype_le β₀
    have : Nonempty {β // β₀ ≤ β} := ⟨⟨β₀, le_rfl⟩⟩
    refine ⟨{β // β₀ ≤ β}, inferInstance, inferInstance, inferInstance, fun _ => (),
      fun β x => ((σ m : ℝ) : EReal) * g β x, fun β => ?_, tendsto_const_nhds,
      fun x β β' hββ' => ProjBerk.ereal_coe_mul_monotone (hσpos' m).le (hanti x hββ'),
      fun x => ?_⟩
    · exact ((hg β).smul (hσpos m)).mono fun c => hβ₀ β β.2 c
    · show ((σ m : ℝ) : EReal) * u' x = ⨅ β : {β // β₀ ≤ β}, ((σ m : ℝ) : EReal) * g β x
      rw [hu x, ereal_coe_mul_iInf (hσpos' m)]
      exact (iInf_subtype_le_eq_iInf_of_antitone (f := fun β => ((σ m : ℝ) : EReal) * g β x)
        (fun β β' hββ' => ProjBerk.ereal_coe_mul_monotone (hσpos' m).le (hanti x hββ'))
        β₀).symm
  -- Step 2: `σₘ u'` decreases to `u'`, because `u' ≤ 0`
  have hanti' : ∀ x, Antitone fun m => ((σ m : ℝ) : EReal) * u' x := fun x m m' hmm' =>
    ProjBerk.ereal_coe_mul_le_of_nonpos (hσpos' m) (hσmono hmm') (hu'0 x)
  have hlim : ∀ x, u' x = ⨅ m, ((σ m : ℝ) : EReal) * u' x := fun x => by
    have := ProjBerk.tendsto_coe_mul_ereal hσlim one_pos hσpos' (h'.ne_top x)
    rw [EReal.coe_one, one_mul] at this
    exact tendsto_nhds_unique this (tendsto_atTop_iInf (hanti' x))
  -- Step 3: the diagonal lemma for the single family `𝓗_fin(θ)`
  have hu' : IsDecrNetLimit.{u} G ρ 0 u' :=
    IsDecrNetLimit.of_antitone_of_finite_rat hGcont hGfin hGadd (I := ULift.{u} ℕ)
      (τ := fun _ => (0 : ℝ)) tendsto_const_nhds
      (g := fun m x => ((σ m.down : ℝ) : EReal) * u' x) (fun m => hstep m.down)
      (fun x m m' hmm' => hanti' x hmm') fun x =>
        (hlim x).trans (Equiv.ulift.iInf_comp (g := fun m => ((σ m : ℝ) : EReal) * u' x)).symm
  -- Step 4: add the constant `M` back
  obtain ⟨ι, _, _, _, s, f, hf, -, hanti, hinf⟩ := hu'
  refine ⟨ι, inferInstance, inferInstance, inferInstance, fun i x => f i x + ((M : ℝ) : EReal),
    fun i => IsFinFS.add_const (show F.IsFinFS θ (f i) from hf i) M,
    fun x i j hij => add_le_add_left (hanti x hij) _, fun x => ?_⟩
  rw [← ereal_iInf_add_coe, ← hinf x]
  exact (ProjBerk.ereal_add_neg_add_coe (u x) (M : ℝ)).symm

/-! ### Countable regularization (`cor:pg-countable-regularization`) -/

/-- **Countable regularization** (`cor:pg-countable-regularization`(1) with
`thm:pg-regularization`(1)): if `K` is second countable, every `u ∈ PSH(θ)` is the pointwise
limit (= infimum) of a decreasing **sequence** `f_m ∈ 𝓗_fin(a_m)` with `a_m ∈ ℚ^r`, `a_m > θ`
coordinatewise and `a_m → θ`. -/
theorem IsPSH.exists_isFinFS_seq_gt [CompactSpace K] [SecondCountableTopology K]
    (h : F.IsPSH θ u) :
    ∃ (a : ℕ → Fin r → ℚ) (f : ℕ → K → EReal), (∀ m, F.IsFinFS (a m) (f m)) ∧
      (∀ m c, θ c < a m c) ∧ Tendsto (fun m c => (a m c : ℝ)) atTop (𝓝 θ) ∧
        (∀ x, Antitone fun m => f m x) ∧ ∀ x, u x = ⨅ m, f m x := by
  obtain ⟨ι, _, _, _, a, f, hf, hθa, ha, hanti, hinf⟩ := h.exists_isFinFS_net_gt
  have hj : ∀ m : ℕ, ∃ j : ι, ∀ i ≥ j, ∀ c, (a i c : ℝ) < θ c + 1 / ((m : ℝ) + 1) := fun m =>
    eventually_atTop.1 (eventually_all.2 fun c => (tendsto_pi_nhds.1 ha c).eventually
      (gt_mem_nhds (lt_add_of_pos_right _ (by positivity))))
  choose j hj using hj
  obtain ⟨i, hmono, hji, hiInf⟩ := exists_monotone_iInf_eq
    (fun i => (hf i).continuous.upperSemicontinuous) hanti j
  refine ⟨fun m => a (i m), fun m => f (i m), fun m => hf (i m), fun m => hθa (i m), ?_,
    fun x m m' hmm' => hanti x (hmono hmm'), fun x => by rw [hiInf x, hinf x]⟩
  refine tendsto_pi_nhds.2 fun c => tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds ?_ (fun m => (hθa (i m) c).le) fun m => (hj m (i m) (hji m) c).le
  simpa only [add_zero] using
    tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- **Countable regularization in a fixed class** (`cor:pg-countable-regularization`(1) with
`thm:pg-regularization`(2)): if `K` is second countable and `θ ∈ ℚ^r` has positive coordinates,
every `u ∈ PSH(θ)` is the pointwise limit (= infimum) of a decreasing sequence in `𝓗_fin(θ)`. -/
theorem IsPSH.exists_isFinFS_seq_of_pos [CompactSpace K] [SecondCountableTopology K]
    {θ : Fin r → ℚ} (hθ : ∀ c, 0 < θ c) (h : F.IsPSH (fun c => (θ c : ℝ)) u) :
    ∃ f : ℕ → K → EReal, (∀ m, F.IsFinFS θ (f m)) ∧ (∀ x, Antitone fun m => f m x) ∧
      ∀ x, u x = ⨅ m, f m x := by
  obtain ⟨ι, _, _, _, f, hf, hanti, hinf⟩ := h.exists_isFinFS_net_of_pos hθ
  obtain ⟨i, hmono, -, hiInf⟩ := exists_monotone_iInf_eq
    (fun i => (hf i).continuous.upperSemicontinuous) hanti fun _ => Classical.arbitrary ι
  exact ⟨fun m => f (i m), fun m => hf (i m), fun x m m' hmm' => hanti x (hmono hmm'),
    fun x => by rw [hiInf x, hinf x]⟩

/-- **Dyadic countable regularization** (`cor:pg-countable-regularization`(2)): if `K` is second
countable and `θ ∈ ℚ^r`, every `u ∈ PSH(θ)` is the pointwise limit (= infimum) of a decreasing
sequence `f_k ∈ 𝓗_fin(θ + 2^{-k} 𝟙)`. -/
theorem IsPSH.exists_isFinFS_seq_dyadic [CompactSpace K] [SecondCountableTopology K]
    {θ : Fin r → ℚ} (h : F.IsPSH (fun c => (θ c : ℝ)) u) :
    ∃ f : ℕ → K → EReal, (∀ k, F.IsFinFS (θ + fun _ => ((2 : ℚ) ^ k)⁻¹) (f k)) ∧
      (∀ x, Antitone fun k => f k x) ∧ ∀ x, u x = ⨅ k, f k x := by
  obtain ⟨a, f, hf, -, ha, hanti, hinf⟩ := h.exists_isFinFS_seq_gt
  have hev : ∀ k : ℕ, ∀ᶠ m in atTop, a m ≤ θ + fun _ => ((2 : ℚ) ^ k)⁻¹ := fun k => by
    show ∀ᶠ m in atTop, ∀ c, a m c ≤ (θ + fun _ => ((2 : ℚ) ^ k)⁻¹ : Fin r → ℚ) c
    refine eventually_all.2 fun c => ?_
    have hlt : (θ c : ℝ) < ((θ c + ((2 : ℚ) ^ k)⁻¹ : ℚ) : ℝ) := by
      push_cast
      have : (0 : ℝ) < ((2 : ℝ) ^ k)⁻¹ := by positivity
      linarith
    filter_upwards [(tendsto_pi_nhds.1 ha c).eventually (gt_mem_nhds hlt)] with m hm
    simp only [Pi.add_apply]
    exact_mod_cast hm.le
  obtain ⟨φ, hφ, hφa⟩ := extraction_forall_of_eventually hev
  refine ⟨fun k => f (φ k), fun k => (hf (φ k)).mono (hφa k),
    fun x k k' hkk' => hanti x (hφ.monotone hkk'), fun x => ?_⟩
  rw [hinf x]
  exact le_antisymm (le_iInf fun k => iInf_le _ _)
    (le_iInf fun m => (iInf_le _ m).trans (hanti x (hφ.id_le m)))

end FSSystem

end EnvelopeProperty
