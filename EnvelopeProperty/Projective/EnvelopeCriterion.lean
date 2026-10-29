/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.PLDensity

/-!
# Criteria for the envelope property on `(ℙⁿ)^an`, and Fubini–Study envelopes

This file proves, on the model `ProjBerk k n` of `(ℙⁿ)^an` (`EnvelopeProperty.Projective.Basic`):

* Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field* (BJ22),
  Lemma 5.9 (envppty; blueprint `lem:bj-envppty`): if `θ` is a limit of classes `θⱼ ≥ θ`
  with the envelope property, then `θ` has the envelope property
  (`ProjBerk.HasEnvelopeProperty.of_tendsto`, `ProjBerk.hasEnvelopeProperty_of_forall_rat_gt`).
* Boucksom–Jonsson, *Addendum to "Global pluripotential theory over a trivially valued field"*
  (arXiv:2206.07183v2), Lemma 1.3 (contenv; blueprint `prop:bj-envelope-criterion`, also
  FHX `prop:ample-envelopes`): for `θ ≥ 0`, `θ` has the envelope property iff the psh envelope
  `P_θ(φ)` is `θ`-psh for every rational PL function `φ`
  (`ProjBerk.hasEnvelopeProperty_iff_forall_isRatPL`). The direction (i) ⇒ (ii) holds for all
  usc obstacles bounded above that dominate some `θ`-psh function
  (`ProjBerk.HasEnvelopeProperty.isPSH_envelope`, the addendum's Corollary 1.4(i)); the direction
  (iii) ⇒ (i) is `ProjBerk.hasEnvelopeProperty_of_forall_isRatPL`: for a bounded-above family
  in `PSH(θ)` with `h = (sup)^⋆`, the envelopes `P_θ(ψ)` of the PL functions `ψ > h` form a
  decreasing net of `θ`-psh functions with limit `h` (`lem:bj-usc-pl`,
  `ProjBerk.exists_antitone_isRatPL_net`), and PSH2 applies.
* The addendum's Lemma 1.5 (FSenv) for the ample classes `a ∈ ℚ_{>0}` (blueprint
  `lem:bj-fs-envelope`, also BJ22 envlsc): for a lsc obstacle `φ > -∞`,
  `P_a(φ) = sup {ψ ∈ H_ℚ(a) : ψ ≤ φ}` (`ProjBerk.envelope_eq_iSup_finiteRatFS`,
  `ProjBerk.envelope_coe_eq_iSup_finiteRatFS`).

## Deviations from the blueprint

* `lem:bj-fs-envelope` is proved from the fixed-class regularization
  `ProjBerk.IsPSH.exists_finiteRatFS_net_of_rat` (`thm:bj-regularization`(2)) instead of part (1)
  followed by the rescaling `(a/a_α) τ_α - ε - δ_α`: a `τ ∈ PSH(a)` with `τ ≤ φ` is the limit of a
  decreasing net `τ_α ∈ H_ℚ(a)`, Dini's argument (for the lsc function `φ + ε`,
  `EnvelopeProperty.exists_forall_lt_of_antitone_of_lowerSemicontinuous`) gives `τ_α < φ + ε` for
  some `α`, and `τ_α - ε ∈ H_ℚ(a)` is a competitor. As a consequence the boundedness of `φ` is not
  needed, and `φ` may take the value `+∞`.
* `lem:bj-envppty` is stated for sequences of classes (`θ ∈ ℝ` is metrizable, so this is no loss);
  the hypothesis `θ ≥ 0` is not needed.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

/-! ### Dini's argument for lsc majorants -/

section Topological

/-- `{x | f x < g x}` is open for `f` upper semicontinuous and `g` lower semicontinuous. -/
theorem isOpen_setOf_lt_of_upperSemicontinuous_of_lowerSemicontinuous {X γ : Type*}
    [TopologicalSpace X] [LinearOrder γ] [DenselyOrdered γ] {f g : X → γ}
    (hf : UpperSemicontinuous f) (hg : LowerSemicontinuous g) : IsOpen {x | f x < g x} := by
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  obtain ⟨y, hy₁, hy₂⟩ := exists_between (show f x < g x from hx)
  filter_upwards [hf x y hy₁, hg x y hy₂] with x' h₁ h₂
  exact h₁.trans h₂

/-- **Dini's argument** with a lsc majorant: on a compact space, if a decreasing net of usc
functions `fᵢ` satisfies `∀ x, ∃ i, fᵢ(x) < g(x)` for a lsc `g`, then `fᵢ < g` everywhere for
some `i`. -/
theorem exists_forall_lt_of_antitone_of_lowerSemicontinuous {K : Type*} [TopologicalSpace K]
    [CompactSpace K] {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] {γ : Type*}
    [LinearOrder γ] [DenselyOrdered γ] {f : ι → K → γ} (hf : ∀ i, UpperSemicontinuous (f i))
    (hanti : ∀ x, Antitone fun i => f i x) {g : K → γ} (hg : LowerSemicontinuous g)
    (h : ∀ x, ∃ i, f i x < g x) : ∃ i, ∀ x, f i x < g x := by
  obtain ⟨i, hi⟩ := isCompact_univ.elim_directed_cover (fun i => {x | f i x < g x})
    (fun i => isOpen_setOf_lt_of_upperSemicontinuous_of_lowerSemicontinuous (hf i) hg)
    (fun x _ => mem_iUnion.2 (h x)) fun i i' => by
      obtain ⟨i'', h₁, h₂⟩ := directed_of (· ≤ ·) i i'
      exact ⟨i'', fun x hx => lt_of_le_of_lt (hanti x h₁) hx,
        fun x hx => lt_of_le_of_lt (hanti x h₂) hx⟩
  exact ⟨i, fun x => hi (mem_univ x)⟩

end Topological

namespace ProjBerk

universe u

variable {k : Type u} [Field k] {n : ℕ} {θ : ℝ}

/-- `x ≤ y` in `EReal` as soon as `x ≤ y + ε` for all real `ε > 0`. -/
theorem ereal_le_of_forall_pos_le_add {x y : EReal} (h : ∀ ε : ℝ, 0 < ε → x ≤ y + (ε : EReal)) :
    x ≤ y := by
  induction y using EReal.rec with
  | bot => simpa using h 1 one_pos
  | top => exact le_top
  | coe r =>
    induction x using EReal.rec with
    | bot => exact bot_le
    | top =>
      have := h 1 one_pos
      rw [← EReal.coe_add, top_le_iff] at this
      exact absurd this (EReal.coe_ne_top _)
    | coe s =>
      refine EReal.coe_le_coe_iff.2 (le_of_forall_pos_le_add fun ε hε => ?_)
      have := h ε hε
      rwa [← EReal.coe_add, EReal.coe_le_coe_iff] at this

/-! ### Approximation of classes (`lem:bj-envppty`) -/

/-- **Approximation of classes** (BJ22 envppty, `lem:bj-envppty`): if `θ` is the limit of a
sequence of classes `θⱼ ≥ θ` having the envelope property, then `θ` has the envelope property.
For a bounded-above family in `PSH(θ) ⊆ PSH(θⱼ)`, the usc regularization of its supremum is
`θⱼ`-psh for every `j`, hence `θ`-psh by PSH2 applied to the constant sequence. -/
theorem HasEnvelopeProperty.of_tendsto {θs : ℕ → ℝ} (hθs : Tendsto θs atTop (𝓝 θ))
    (hle : ∀ j, θ ≤ θs j) (h : ∀ j, HasEnvelopeProperty k n (θs j)) :
    HasEnvelopeProperty k n θ := by
  intro S hSne hS hbdd
  have hU : ∀ j, IsPSH (θs j) (uscReg fun v => ⨆ u ∈ S, u v) := fun j =>
    h j S hSne (fun u hu => (hS u hu).mono_class (hle j)) hbdd
  obtain ⟨u, hu⟩ := hSne
  obtain ⟨v, hv⟩ := (hS u hu).exists_ne_bot
  exact isPSH_of_antitone_seq hθs hU (fun _ _ _ _ => le_rfl) (fun _ => iInf_const.symm)
    ⟨v, ne_bot_of_le_ne_bot hv
      ((le_iSup₂ (f := fun (w : ProjBerk k n → EReal) (_ : w ∈ S) => w v) u hu).trans
        (le_uscReg (fun v => ⨆ u ∈ S, u v) v))⟩

/-- `lem:bj-envppty` with rational classes: if every rational `a > θ` has the envelope property,
so does `θ` (take rationals `aⱼ ↓ θ`). -/
theorem hasEnvelopeProperty_of_forall_rat_gt
    (h : ∀ a : ℚ, θ < a → HasEnvelopeProperty k n (a : ℝ)) : HasEnvelopeProperty k n θ := by
  obtain ⟨q, -, hqθ, hq⟩ := Real.exists_seq_rat_strictAnti_tendsto θ
  exact HasEnvelopeProperty.of_tendsto hq (fun j => (hqθ j).le) fun j => h _ (hqθ j)

/-! ### The envelope criterion (`prop:bj-envelope-criterion`) -/

/-- **Envelopes of usc obstacles** (BJ addendum envusc(i), the direction (i) ⇒ (ii) of
contenv): under the envelope property, `P_θ(φ)` is `θ`-psh for every usc `φ` that is
bounded above and dominates some `θ`-psh function. Indeed `P_θ(φ)^⋆` is `θ`-psh and `≤ φ` (as `φ`
is usc), hence a competitor in the definition of `P_θ(φ)`. -/
theorem HasEnvelopeProperty.isPSH_envelope (h : HasEnvelopeProperty k n θ)
    {φ : ProjBerk k n → EReal} (hφ : UpperSemicontinuous φ) (hbdd : ∃ C : ℝ, ∀ v, φ v ≤ C)
    (hne : ∃ τ, IsPSH θ τ ∧ τ ≤ φ) : IsPSH θ (envelope θ φ) := by
  have hU := h.isPSH_uscReg_envelope hne hbdd
  have heq : uscReg (envelope θ φ) = envelope θ φ :=
    le_antisymm (le_envelope hU (uscReg_le_of_le hφ (envelope_le θ φ))) fun v => le_uscReg _ v
  rwa [heq] at hU

/-- The direction (i) ⇒ (ii) of `prop:bj-envelope-criterion` for continuous obstacles: under the
envelope property for `θ ≥ 0`, `P_θ(φ)` is `θ`-psh for every continuous `φ : (ℙⁿ)^an → ℝ`; the
constant `min φ` is a competitor and `max φ` a bound. -/
theorem HasEnvelopeProperty.isPSH_envelope_of_continuous (h : HasEnvelopeProperty k n θ)
    (hθ : 0 ≤ θ) {φ : ProjBerk k n → ℝ} (hφ : Continuous φ) :
    IsPSH θ (envelope θ fun v => (φ v : EReal)) := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_continuous hφ
  refine h.isPSH_envelope (continuous_coe_real_ereal.comp hφ).upperSemicontinuous
    ⟨C, fun v => EReal.coe_le_coe_iff.2 ((le_abs_self _).trans (hC v))⟩
    ⟨fun _ => ((-C : ℝ) : EReal), isPSH_const hθ (-C), fun v => EReal.coe_le_coe_iff.2 ?_⟩
  exact neg_le_of_abs_le (hC v)

/-- The direction (iii) ⇒ (i) of the BJ addendum contenv (`prop:bj-envelope-criterion`):
if `P_θ(φ)` is `θ`-psh for every rational PL function `φ`, then `θ` has the envelope property.
For a nonempty bounded-above family `S ⊆ PSH(θ)` and `h = (sup S)^⋆`, every PL function `ψ > h`
satisfies `h ≤ P_θ(ψ) ≤ ψ` (as `P_θ(ψ)` is usc), so by `lem:bj-usc-pl` the `P_θ(ψ)` form a
decreasing net of `θ`-psh functions with limit `h`, and PSH2 applies. -/
theorem hasEnvelopeProperty_of_forall_isRatPL
    (hPL : ∀ φ : ProjBerk k n → ℝ, IsRatPL φ → IsPSH θ (envelope θ fun v => (φ v : EReal))) :
    HasEnvelopeProperty k n θ := by
  intro S hSne hS hbdd
  obtain ⟨C, hC⟩ := hbdd
  have hle : ∀ u ∈ S, ∀ v, u v ≤ uscReg (fun v => ⨆ u ∈ S, u v) v := fun u hu v =>
    (le_iSup₂ (f := fun (w : ProjBerk k n → EReal) (_ : w ∈ S) => w v) u hu).trans
      (le_uscReg (fun v => ⨆ u ∈ S, u v) v)
  set h := uscReg fun v => ⨆ u ∈ S, u v with h_def
  have hhC : ∀ v, h v ≤ C := uscReg_le_of_le (f := fun v => ⨆ u ∈ S, u v)
    (g := fun _ => (C : EReal)) continuous_const.upperSemicontinuous
    (fun v => iSup₂_le fun u hu => hC u hu v)
  have htop : ∀ v, h v ≠ ⊤ := fun v => ne_top_of_le_ne_top (EReal.coe_ne_top C) (hhC v)
  obtain ⟨ι, _, _, _, ψ, hψ, hgt, hanti, hinf⟩ :=
    exists_antitone_isRatPL_net (upperSemicontinuous_uscReg _) htop
  -- `h ≤ P_θ(ψᵢ)` since `P_θ(ψᵢ)` is usc and dominates every member of `S`
  have hkey : ∀ i v, h v ≤ envelope θ (fun w => (ψ i w : EReal)) v := fun i =>
    uscReg_le_of_le (hPL _ (hψ i)).upperSemicontinuous fun v => iSup₂_le fun u hu =>
      le_envelope (hS u hu) (fun w => (hle u hu w).trans (hgt i w).le) v
  refine isPSH_of_antitone (θ := fun _ => θ) tendsto_const_nhds (fun i => hPL _ (hψ i))
    (fun v i j hij => envelope_mono (fun w => EReal.coe_le_coe_iff.2 (hanti w hij)) v)
    (fun v => le_antisymm (le_iInf fun i => hkey i v) ?_) ?_
  · exact (iInf_mono fun i => envelope_le θ _ v).trans_eq (hinf v).symm
  · obtain ⟨u, hu⟩ := hSne
    obtain ⟨v, hv⟩ := (hS u hu).exists_ne_bot
    exact ⟨v, ne_bot_of_le_ne_bot hv (hle u hu v)⟩

/-- **The envelope criterion** (BJ addendum contenv, FHX `prop:ample-envelopes`,
`prop:bj-envelope-criterion`): for `θ ≥ 0`, `θ` has the envelope property iff the psh envelope
`P_θ(φ)` is `θ`-psh for every rational PL function `φ`. -/
theorem hasEnvelopeProperty_iff_forall_isRatPL (hθ : 0 ≤ θ) :
    HasEnvelopeProperty k n θ ↔
      ∀ φ : ProjBerk k n → ℝ, IsRatPL φ → IsPSH θ (envelope θ fun v => (φ v : EReal)) :=
  ⟨fun h _ hφ => h.isPSH_envelope_of_continuous hθ hφ.continuous,
    hasEnvelopeProperty_of_forall_isRatPL⟩

/-! ### Fubini–Study envelopes (`lem:bj-fs-envelope`) -/

/-- **Fubini–Study envelopes** (BJ addendum FSenv for the ample class `a ∈ ℚ_{>0}`,
`lem:bj-fs-envelope`): for a lsc obstacle `φ : (ℙⁿ)^an → (-∞, +∞]`,
`P_a(φ) = sup {ψ ∈ H_ℚ(a) : ψ ≤ φ}` pointwise. Given `τ ∈ PSH(a)` with `τ ≤ φ` and `ε > 0`
rational, a member `τ_α < φ + ε` of a decreasing net `τ_α ∈ H_ℚ(a)` with limit `τ` (fixed-class
regularization and Dini's argument) gives the competitor `τ_α - ε ∈ H_ℚ(a)`. -/
theorem envelope_eq_iSup_finiteRatFS {a : ℚ} (ha : 0 < a) {φ : ProjBerk k n → EReal}
    (hφ : LowerSemicontinuous φ) (hφbot : ∀ v, φ v ≠ ⊥) (v : ProjBerk k n) :
    envelope (a : ℝ) φ v = ⨆ (ψ : ProjBerk k n → EReal) (_ : IsFiniteRatFS a ψ ∧ ψ ≤ φ), ψ v := by
  refine le_antisymm (iSup₂_le fun τ hτ => ?_)
    (iSup₂_le fun ψ hψ => le_envelope hψ.1.isFS.isPSH hψ.2 v)
  obtain ⟨ι, _, _, _, ψ, hψ, hanti, -, hinf⟩ := hτ.1.exists_finiteRatFS_net_of_rat ha
  refine ereal_le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨q, hq₀, hqε⟩ := exists_rat_btwn hε
  have hφq : LowerSemicontinuous fun w => φ w + ((q : ℝ) : EReal) :=
    (continuous_ereal_add_coe _).comp_lowerSemicontinuous hφ fun _ _ hxy =>
      add_le_add_left hxy _
  obtain ⟨i, hi⟩ := exists_forall_lt_of_antitone_of_lowerSemicontinuous
    (fun i => (hψ i).isFS.continuous.upperSemicontinuous) hanti hφq fun w => by
      have hτw : τ w < φ w + ((q : ℝ) : EReal) := by
        by_cases htop : φ w = ⊤
        · rw [htop, EReal.top_add_coe]
          exact hτ.1.lt_top w
        · exact (hτ.2 w).trans_lt (ereal_lt_add_coe (hφbot w) htop hq₀)
      rw [hinf w] at hτw
      exact iInf_lt_iff.1 hτw
  -- the competitor `ψᵢ - q ∈ H_ℚ(a)`
  have hf : IsFiniteRatFS a fun w => ψ i w + ((-(q : ℝ) : ℝ) : EReal) := by
    simpa only [Rat.cast_neg] using (hψ i).add_const (-q)
  have hfφ : (fun w => ψ i w + ((-(q : ℝ) : ℝ) : EReal)) ≤ φ := fun w => by
    have := add_le_add_left (hi w).le ((-(q : ℝ) : ℝ) : EReal)
    rwa [ereal_add_coe_add_neg] at this
  calc τ v ≤ ψ i v := by rw [hinf v]; exact iInf_le _ i
    _ = ψ i v + ((-(q : ℝ) : ℝ) : EReal) + ((q : ℝ) : EReal) := (ereal_add_neg_add_coe _ _).symm
    _ ≤ (⨆ (ψ : ProjBerk k n → EReal) (_ : IsFiniteRatFS a ψ ∧ ψ ≤ φ), ψ v) + ((q : ℝ) : EReal) :=
        add_le_add_left (le_iSup₂_of_le
          (f := fun (ψ : ProjBerk k n → EReal) (_ : IsFiniteRatFS a ψ ∧ ψ ≤ φ) => ψ v) _
          ⟨hf, hfφ⟩ le_rfl) _
    _ ≤ (⨆ (ψ : ProjBerk k n → EReal) (_ : IsFiniteRatFS a ψ ∧ ψ ≤ φ), ψ v) + (ε : EReal) :=
        add_le_add_right (EReal.coe_le_coe_iff.2 hqε.le) _

/-- **Fubini–Study envelopes** (`lem:bj-fs-envelope`) for a real-valued lsc obstacle `φ`:
`P_a(φ) = sup {ψ ∈ H_ℚ(a) : ψ ≤ φ}` pointwise, for `a ∈ ℚ_{>0}`. -/
theorem envelope_coe_eq_iSup_finiteRatFS {a : ℚ} (ha : 0 < a) {φ : ProjBerk k n → ℝ}
    (hφ : LowerSemicontinuous φ) (v : ProjBerk k n) :
    envelope (a : ℝ) (fun w => (φ w : EReal)) v =
      ⨆ (ψ : ProjBerk k n → EReal) (_ : IsFiniteRatFS a ψ ∧ ψ ≤ fun w => (φ w : EReal)), ψ v :=
  envelope_eq_iSup_finiteRatFS ha
    (continuous_coe_real_ereal.comp_lowerSemicontinuous hφ EReal.coe_strictMono.monotone)
    (fun _ => EReal.coe_ne_bot _) v

end ProjBerk

end EnvelopeProperty
