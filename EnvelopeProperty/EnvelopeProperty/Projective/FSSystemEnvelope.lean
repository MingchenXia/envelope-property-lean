/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.FSSystemRegularization
import EnvelopeProperty.Projective.EnvelopeCriterion

/-!
# Envelopes and the envelope property in Fubini–Study systems

For a Fubini–Study system `F` of rank `r` on a space `(K, ⋆)` (`EnvelopeProperty.FSSystem`,
blueprint `def:pg-fs-system`) this file develops the part of the theory of psh envelopes that is
used, through the blueprint chapter `smooth-general.tex` (`subsec:sg-envelopes`), in the proof of
Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX), Theorem 3.1
(`thm:smooth-EP`) for smooth projective varieties. The definitions are those of FHX §2.3
(`subsec:prelim-envelopes`) and of Boucksom–Jonsson, *Global pluripotential theory over a
trivially valued field* (BJ22), §5.2 (`sec:envprop`); the arguments are the ones of the `ℙⁿ`
templates `EnvelopeProperty.Projective.PSHBasic` and
`EnvelopeProperty.Projective.EnvelopeCriterion`, transported to an abstract Fubini–Study system.

## Main definitions (`def:sg-ep`)

* `FSSystem.envelope F θ φ`: the **psh envelope** `P_θ(φ) = sup {τ ∈ PSH(θ) : τ ≤ φ}`, a
  pointwise supremum without usc regularization (`⊥` where there is no competitor).
* `FSSystem.HasEnvelopeProperty F θ`: for every nonempty family in `PSH(θ)` that is uniformly
  bounded above, the usc regularization `(sup)^⋆` of its pointwise supremum is `θ`-psh.

PL functions, the envelope criterion and the reduction theorem are in
`EnvelopeProperty.Projective.FSSystemPL`.

## Main results

* `lem:sg-env-basic`: `FSSystem.envelope_mono`, `FSSystem.envelope_le`,
  `FSSystem.iInf_le_envelope` (`inf φ ≤ P_θ(φ)` for `θ ≥ 0`), `FSSystem.envelope_add_const`
  (`P_θ(φ + c) = P_θ(φ) + c`) and `FSSystem.envelope_smul` (`P_{tθ}(tφ) = t P_θ(φ)` for real
  `t > 0`).
* `lem:sg-envppty` (BJ22 `lem:envppty`): `FSSystem.HasEnvelopeProperty.of_tendsto` (if `θ` is the
  limit of classes `θⱼ ≥ θ` with the envelope property, so is `θ`) and its rational form
  `FSSystem.hasEnvelopeProperty_of_forall_rat_gt`.
* `FSSystem.hasEnvelopeProperty_of_not_nonneg`: classes `θ ≱ 0` have the envelope property
  vacuously (`prop:pg-maxprin`).
* `FSSystem.HasEnvelopeProperty.isPSH_envelope` (BJ addendum `cor:envusc`(i)): under the envelope
  property, the envelope of a usc obstacle that is bounded above and dominates a `θ`-psh function
  is `θ`-psh; `FSSystem.HasEnvelopeProperty.isPSH_envelope_of_continuous` for continuous
  obstacles on compact `K`.
* `lem:sg-fs-envelope` (BJ addendum `lem:FSenv`, BJ22 `lem:envlsc`):
  `FSSystem.envelope_eq_iSup_isFinFS` and `FSSystem.envelope_coe_eq_iSup_isFinFS`: for
  `a ∈ ℚ^r` with positive coordinates and a lsc obstacle `φ > -∞`,
  `P_a(φ) = sup {ψ ∈ 𝓗_fin(a) : ψ ≤ φ}`.

## Deviations from the blueprint

* `lem:sg-fs-envelope` is proved, as its `ℙⁿ` template `ProjBerk.envelope_eq_iSup_finiteRatFS`,
  from the fixed-class regularization `FSSystem.IsPSH.exists_isFinFS_net_of_pos`
  (`thm:pg-regularization`(2)) and Dini's argument
  (`EnvelopeProperty.exists_forall_lt_of_antitone_of_lowerSemicontinuous`), instead of part (1)
  of `thm:pg-regularization` followed by the rescaling `s_α τ_α - ε - δ_α`. As a consequence the
  boundedness of `φ` is not needed (only lower semicontinuity and `φ > -∞`), and `φ` may take the
  value `+∞`.
* `lem:sg-envppty` is stated for sequences of classes (`ℝ^r` is metrizable, so this is no loss);
  the hypothesis `θ ≥ 0` is not needed.
* `lem:sg-env-basic`: monotonicity, `P_θ(φ) ≤ φ` and the translation rule hold for every `θ` and
  every `φ : K → [-∞, +∞]`; `inf φ ≤ P_θ(φ)` holds for every `φ` once `θ ≥ 0` (the boundedness
  of `φ` is not needed); the scaling rule uses compactness of `K` (through
  `FSSystem.IsPSH.smul`).
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

namespace FSSystem

universe u

variable {K : Type u} [TopologicalSpace K] {r : ℕ} (F : FSSystem K r)

/-! ### Envelopes and the envelope property (`def:sg-ep`) -/

/-- The **psh envelope** `P_θ(φ)(x) = sup {τ(x) : τ ∈ PSH(θ), τ ≤ φ}` of an obstacle
`φ : K → [-∞, +∞]` in a Fubini–Study system (`def:sg-ep`, FHX §2.3 `subsec:prelim-envelopes`):
a pointwise supremum without usc regularization, equal to `⊥` if there is no competitor. -/
def envelope (θ : Fin r → ℝ) (φ : K → EReal) (x : K) : EReal :=
  ⨆ (τ : K → EReal) (_ : F.IsPSH θ τ ∧ τ ≤ φ), τ x

/-- The **envelope property** of a class `θ ∈ ℝ^r` (`def:sg-ep`; BJ22 §5.2, `sec:envprop`): for
every nonempty family `S ⊆ PSH(θ)` uniformly bounded above, the usc regularization
`(sup S)^⋆` of its pointwise supremum is `θ`-psh. -/
def HasEnvelopeProperty (θ : Fin r → ℝ) : Prop :=
  ∀ S : Set (K → EReal), S.Nonempty → (∀ u ∈ S, F.IsPSH θ u) →
    (∃ C : ℝ, ∀ u ∈ S, ∀ x, u x ≤ C) → F.IsPSH θ (uscReg fun x => ⨆ u ∈ S, u x)

variable {F} {θ : Fin r → ℝ} {φ ψ : K → EReal}

/-! ### Basic properties of envelopes (`lem:sg-env-basic`) -/

variable (F) in
/-- `P_θ(φ) ≤ φ` (`lem:sg-env-basic`). -/
theorem envelope_le (θ : Fin r → ℝ) (φ : K → EReal) : F.envelope θ φ ≤ φ := fun x =>
  iSup₂_le fun _ hτ => hτ.2 x

/-- Every `θ`-psh competitor `τ ≤ φ` lies below `P_θ(φ)`. -/
theorem le_envelope {τ : K → EReal} (hτ : F.IsPSH θ τ) (hτφ : τ ≤ φ) : τ ≤ F.envelope θ φ :=
  fun x => le_iSup₂_of_le (f := fun (τ : K → EReal) (_ : F.IsPSH θ τ ∧ τ ≤ φ) => τ x) τ
    ⟨hτ, hτφ⟩ le_rfl

/-- The envelope is increasing in the obstacle (`lem:sg-env-basic`). -/
theorem envelope_mono (h : φ ≤ ψ) : F.envelope θ φ ≤ F.envelope θ ψ := fun x =>
  iSup₂_le fun _ hτ => le_envelope hτ.1 (hτ.2.trans h) x

/-- The envelope of a `θ`-psh function is the function itself. -/
theorem envelope_eq_self (hφ : F.IsPSH θ φ) : F.envelope θ φ = φ :=
  le_antisymm (envelope_le F θ φ) (le_envelope hφ le_rfl)

/-- A real constant below the obstacle lies below the envelope, for `θ ≥ 0`: constants are
`θ`-psh (`thm:pg-psh-basic`(2)). -/
theorem const_le_envelope (hθ : 0 ≤ θ) {c : ℝ} (hc : ∀ x, (c : EReal) ≤ φ x) (x : K) :
    (c : EReal) ≤ F.envelope θ φ x :=
  le_envelope (isPSH_const hθ c) hc x

variable (F) in
/-- **`inf φ ≤ P_θ(φ)`** for `θ ≥ 0` (`lem:sg-env-basic`): every real constant `c < inf φ` is a
competitor. -/
theorem iInf_le_envelope (hθ : 0 ≤ θ) (φ : K → EReal) (x : K) : ⨅ y, φ y ≤ F.envelope θ φ x :=
  EReal.ge_of_forall_gt_iff_ge.1 fun _ hz =>
    const_le_envelope hθ (fun y => hz.le.trans (iInf_le φ y)) x

variable (F) in
/-- **Envelopes and constants** (`lem:sg-env-basic`, FHX §2.3): `P_θ(φ + c) = P_θ(φ) + c` for
`c ∈ ℝ`, since `u ↦ u + c` is a bijection of `PSH(θ)` (`thm:pg-psh-basic`(2)). -/
theorem envelope_add_const (θ : Fin r → ℝ) (φ : K → EReal) (c : ℝ) :
    F.envelope θ (fun x => φ x + (c : EReal)) = fun x => F.envelope θ φ x + (c : EReal) := by
  funext x
  refine le_antisymm (iSup₂_le fun τ hτ => ?_) ?_
  · have h₁ : F.IsPSH θ fun w => τ w + ((-c : ℝ) : EReal) := hτ.1.add_const (-c)
    have h₂ : (fun w => τ w + ((-c : ℝ) : EReal)) ≤ φ := fun w => by
      have := add_le_add_left (hτ.2 w) ((-c : ℝ) : EReal)
      rwa [ProjBerk.ereal_add_coe_add_neg] at this
    have := add_le_add_left (le_envelope h₁ h₂ x) (c : EReal)
    rwa [ProjBerk.ereal_add_neg_add_coe] at this
  · have key : F.envelope θ φ x ≤
        F.envelope θ (fun x => φ x + (c : EReal)) x + ((-c : ℝ) : EReal) := by
      refine iSup₂_le fun τ hτ => ?_
      have h₁ : F.IsPSH θ fun w => τ w + (c : EReal) := hτ.1.add_const c
      have h₂ : (fun w => τ w + (c : EReal)) ≤ fun w => φ w + (c : EReal) := fun w =>
        add_le_add_left (hτ.2 w) _
      have := add_le_add_left (le_envelope h₁ h₂ x) ((-c : ℝ) : EReal)
      rwa [ProjBerk.ereal_add_coe_add_neg] at this
    have := add_le_add_left key (c : EReal)
    rwa [ProjBerk.ereal_add_neg_add_coe] at this

variable (F) in
/-- **Envelopes and scaling of the class** (`lem:sg-env-basic`, FHX §2.3, §3):
`P_{tθ}(t φ) = t P_θ(φ)` for real `t > 0`, since `u ↦ t u` is a bijection
`PSH(θ) → PSH(t θ)` (`thm:pg-psh-basic`(1)). -/
theorem envelope_smul [CompactSpace K] (θ : Fin r → ℝ) (φ : K → EReal) {t : ℝ} (ht : 0 < t) :
    F.envelope (t • θ) (fun x => (t : EReal) * φ x) = fun x => (t : EReal) * F.envelope θ φ x := by
  funext x
  have hinv : (0 : ℝ) ≤ t⁻¹ := (inv_pos.2 ht).le
  refine le_antisymm (iSup₂_le fun τ hτ => ?_) ?_
  · have h₁ : F.IsPSH θ fun w => ((t⁻¹ : ℝ) : EReal) * τ w := by
      have h' := hτ.1.smul (inv_pos.2 ht)
      rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h'
    have h₂ : (fun w => ((t⁻¹ : ℝ) : EReal) * τ w) ≤ φ := fun w => by
      have := ProjBerk.ereal_coe_mul_monotone hinv (hτ.2 w)
      dsimp only at this ⊢
      rwa [ProjBerk.ereal_inv_mul_mul ht.ne'] at this
    have := ProjBerk.ereal_coe_mul_monotone ht.le (le_envelope h₁ h₂ x)
    dsimp only at this
    rwa [ProjBerk.ereal_coe_mul_inv_mul ht.ne'] at this
  · have key : F.envelope θ φ x ≤
        ((t⁻¹ : ℝ) : EReal) * F.envelope (t • θ) (fun x => (t : EReal) * φ x) x := by
      refine iSup₂_le fun τ hτ => ?_
      have h₁ : F.IsPSH (t • θ) fun w => (t : EReal) * τ w := hτ.1.smul ht
      have h₂ : (fun w => (t : EReal) * τ w) ≤ fun w => (t : EReal) * φ w := fun w =>
        ProjBerk.ereal_coe_mul_monotone ht.le (hτ.2 w)
      have := ProjBerk.ereal_coe_mul_monotone hinv (le_envelope h₁ h₂ x)
      dsimp only at this
      rwa [ProjBerk.ereal_inv_mul_mul ht.ne'] at this
    have := ProjBerk.ereal_coe_mul_monotone ht.le key
    dsimp only at this
    rwa [ProjBerk.ereal_coe_mul_inv_mul ht.ne'] at this

/-! ### The envelope property -/

/-- The envelope property for indexed families (in any universe). -/
theorem HasEnvelopeProperty.isPSH_uscReg_iSup (h : F.HasEnvelopeProperty θ) {ι : Sort*}
    [Nonempty ι] {u : ι → K → EReal} (hu : ∀ i, F.IsPSH θ (u i))
    (hbdd : ∃ C : ℝ, ∀ i x, u i x ≤ C) : F.IsPSH θ (uscReg fun x => ⨆ i, u i x) := by
  obtain ⟨C, hC⟩ := hbdd
  have e : (fun x => ⨆ i, u i x) = fun x => ⨆ w ∈ range u, w x := by
    funext x
    exact (iSup_range (g := fun w : K → EReal => w x) (f := u)).symm
  rw [e]
  refine h (range u) (range_nonempty u) ?_ ⟨C, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hu i
  · rintro _ ⟨i, rfl⟩ x
    exact hC i x

/-- Under the envelope property, the usc regularization of the envelope `P_θ(φ)` is `θ`-psh, as
soon as `φ` is bounded above and dominates some `θ`-psh function. -/
theorem HasEnvelopeProperty.isPSH_uscReg_envelope (h : F.HasEnvelopeProperty θ)
    (hne : ∃ τ, F.IsPSH θ τ ∧ τ ≤ φ) (hbdd : ∃ C : ℝ, ∀ x, φ x ≤ C) :
    F.IsPSH θ (uscReg (F.envelope θ φ)) := by
  obtain ⟨C, hC⟩ := hbdd
  exact h {τ | F.IsPSH θ τ ∧ τ ≤ φ} hne (fun _ hτ => hτ.1)
    ⟨C, fun _ hτ x => (hτ.2 x).trans (hC x)⟩

/-- **Envelopes of usc obstacles** (BJ addendum `cor:envusc`(i)): under the envelope property,
`P_θ(φ)` is `θ`-psh for every usc obstacle `φ` that is bounded above and dominates some `θ`-psh
function: `P_θ(φ)^⋆` is `θ`-psh and `≤ φ`, hence a competitor. -/
theorem HasEnvelopeProperty.isPSH_envelope (h : F.HasEnvelopeProperty θ)
    (hφ : UpperSemicontinuous φ) (hbdd : ∃ C : ℝ, ∀ x, φ x ≤ C)
    (hne : ∃ τ, F.IsPSH θ τ ∧ τ ≤ φ) : F.IsPSH θ (F.envelope θ φ) := by
  have hU := h.isPSH_uscReg_envelope hne hbdd
  have heq : uscReg (F.envelope θ φ) = F.envelope θ φ :=
    le_antisymm (le_envelope hU (uscReg_le_of_le hφ (envelope_le F θ φ))) fun x =>
      le_uscReg _ x
  rwa [heq] at hU

/-- Continuous real functions on a compact space are bounded. -/
theorem exists_abs_le_of_continuous [CompactSpace K] {f : K → ℝ} (hf : Continuous f) :
    ∃ C, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun x => by simpa only [Real.norm_eq_abs] using hC x (mem_univ x)⟩

/-- Under the envelope property of `θ ≥ 0` on a compact `K`, `P_θ(φ)` is `θ`-psh for every
continuous `φ : K → ℝ`: the constant `min φ` is a competitor and `max φ` a bound. -/
theorem HasEnvelopeProperty.isPSH_envelope_of_continuous [CompactSpace K]
    (h : F.HasEnvelopeProperty θ) (hθ : 0 ≤ θ) {φ : K → ℝ} (hφ : Continuous φ) :
    F.IsPSH θ (F.envelope θ fun x => (φ x : EReal)) := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_continuous hφ
  refine h.isPSH_envelope (continuous_coe_real_ereal.comp hφ).upperSemicontinuous
    ⟨C, fun x => EReal.coe_le_coe_iff.2 ((le_abs_self _).trans (hC x))⟩
    ⟨fun _ => ((-C : ℝ) : EReal), isPSH_const hθ (-C), fun x => EReal.coe_le_coe_iff.2 ?_⟩
  exact neg_le_of_abs_le (hC x)

/-- If `θ ≱ 0`, then `PSH(θ) = ∅` (`prop:pg-maxprin`), so `θ` has the envelope property
vacuously. -/
theorem hasEnvelopeProperty_of_not_nonneg (hθ : ¬0 ≤ θ) : F.HasEnvelopeProperty θ :=
  fun _ ⟨u, hu⟩ hS _ => absurd (hS u hu).nonneg hθ

/-! ### Approximation of classes (`lem:sg-envppty`) -/

/-- **Approximation of classes** (`lem:sg-envppty`; BJ22 `lem:envppty`): if `θ` is the limit of a
sequence of classes `θⱼ ≥ θ` (coordinatewise) having the envelope property, then `θ` has the
envelope property. For a bounded-above family in `PSH(θ) ⊆ PSH(θⱼ)` (`thm:pg-psh-basic`(3)), the
usc regularization `u` of its supremum is `θⱼ`-psh for every `j`, hence `θ`-psh by PSH2
(`thm:pg-psh2`(3)) applied to the constant sequence `u`. -/
theorem HasEnvelopeProperty.of_tendsto [CompactSpace K] {θs : ℕ → Fin r → ℝ}
    (hθs : Tendsto θs atTop (𝓝 θ)) (hle : ∀ j, θ ≤ θs j)
    (h : ∀ j, F.HasEnvelopeProperty (θs j)) : F.HasEnvelopeProperty θ := by
  intro S hSne hS hbdd
  have hU : ∀ j, F.IsPSH (θs j) (uscReg fun x => ⨆ u ∈ S, u x) := fun j =>
    h j S hSne (fun u hu => (hS u hu).mono_class (hle j)) hbdd
  obtain ⟨u, hu⟩ := hSne
  obtain ⟨x, hx⟩ := (hS u hu).exists_ne_bot
  exact isPSH_of_antitone_seq hθs hU (fun _ _ _ _ => le_rfl) (fun _ => iInf_const.symm)
    ⟨x, ne_bot_of_le_ne_bot hx
      ((le_iSup₂ (f := fun (w : K → EReal) (_ : w ∈ S) => w x) u hu).trans
        (le_uscReg (fun x => ⨆ u ∈ S, u x) x))⟩

/-- `lem:sg-envppty` with rational classes: if every `a ∈ ℚ^r` with `a > θ` coordinatewise has
the envelope property, so does `θ` (take rational vectors `aⱼ ↓ θ`). -/
theorem hasEnvelopeProperty_of_forall_rat_gt [CompactSpace K]
    (h : ∀ a : Fin r → ℚ, (∀ c, θ c < a c) → F.HasEnvelopeProperty fun c => (a c : ℝ)) :
    F.HasEnvelopeProperty θ := by
  obtain ⟨a, hθa, ha⟩ := exists_seq_rat_vec_gt_tendsto θ
  exact HasEnvelopeProperty.of_tendsto ha (fun j c => (hθa j c).le) fun j => h _ (hθa j)

/-! ### Fubini–Study envelopes (`lem:sg-fs-envelope`) -/

/-- **Fubini–Study envelopes** (`lem:sg-fs-envelope`; BJ addendum `lem:FSenv`, BJ22
`lem:envlsc`): for `a ∈ ℚ^r` with positive coordinates and a lsc obstacle
`φ : K → (-∞, +∞]` on a compact `K`, `P_a(φ) = sup {ψ ∈ 𝓗_fin(a) : ψ ≤ φ}` pointwise. Given
`τ ∈ PSH(a)` with `τ ≤ φ` and a rational `q > 0`, a member `τ_α < φ + q` of a decreasing net
`τ_α ∈ 𝓗_fin(a)` with limit `τ` (fixed-class regularization `thm:pg-regularization`(2) and Dini's
argument) gives the competitor `τ_α - q ∈ 𝓗_fin(a)` (FS3). -/
theorem envelope_eq_iSup_isFinFS [CompactSpace K] {a : Fin r → ℚ} (ha : ∀ c, 0 < a c)
    (hφ : LowerSemicontinuous φ) (hφbot : ∀ x, φ x ≠ ⊥) (x : K) :
    F.envelope (fun c => (a c : ℝ)) φ x =
      ⨆ (ψ : K → EReal) (_ : F.IsFinFS a ψ ∧ ψ ≤ φ), ψ x := by
  refine le_antisymm (iSup₂_le fun τ hτ => ?_)
    (iSup₂_le fun ψ hψ => le_envelope hψ.1.isPSH hψ.2 x)
  obtain ⟨ι, _, _, _, ψ, hψ, hanti, hinf⟩ := hτ.1.exists_isFinFS_net_of_pos ha
  refine ProjBerk.ereal_le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨q, hq₀, hqε⟩ := exists_rat_btwn hε
  have hφq : LowerSemicontinuous fun w => φ w + ((q : ℝ) : EReal) :=
    (ProjBerk.continuous_ereal_add_coe _).comp_lowerSemicontinuous hφ fun _ _ hxy =>
      add_le_add_left hxy _
  obtain ⟨i, hi⟩ := exists_forall_lt_of_antitone_of_lowerSemicontinuous
    (fun i => (hψ i).continuous.upperSemicontinuous) hanti hφq fun w => by
      have hτw : τ w < φ w + ((q : ℝ) : EReal) := by
        by_cases htop : φ w = ⊤
        · rw [htop, EReal.top_add_coe]
          exact lt_top_iff_ne_top.2 (hτ.1.ne_top w)
        · exact (hτ.2 w).trans_lt (ProjBerk.ereal_lt_add_coe (hφbot w) htop hq₀)
      rw [hinf w] at hτw
      exact iInf_lt_iff.1 hτw
  -- the competitor `ψᵢ - q ∈ 𝓗_fin(a)`
  have hf : F.IsFinFS a fun w => ψ i w + ((-(q : ℝ) : ℝ) : EReal) := by
    simpa only [Rat.cast_neg] using (hψ i).add_const (-q)
  have hfφ : (fun w => ψ i w + ((-(q : ℝ) : ℝ) : EReal)) ≤ φ := fun w => by
    have := add_le_add_left (hi w).le ((-(q : ℝ) : ℝ) : EReal)
    rwa [ProjBerk.ereal_add_coe_add_neg] at this
  calc τ x ≤ ψ i x := by rw [hinf x]; exact iInf_le _ i
    _ = ψ i x + ((-(q : ℝ) : ℝ) : EReal) + ((q : ℝ) : EReal) :=
        (ProjBerk.ereal_add_neg_add_coe _ _).symm
    _ ≤ (⨆ (ψ : K → EReal) (_ : F.IsFinFS a ψ ∧ ψ ≤ φ), ψ x) + ((q : ℝ) : EReal) :=
        add_le_add_left (le_iSup₂_of_le
          (f := fun (ψ : K → EReal) (_ : F.IsFinFS a ψ ∧ ψ ≤ φ) => ψ x) _
          ⟨hf, hfφ⟩ le_rfl) _
    _ ≤ (⨆ (ψ : K → EReal) (_ : F.IsFinFS a ψ ∧ ψ ≤ φ), ψ x) + (ε : EReal) :=
        add_le_add_right (EReal.coe_le_coe_iff.2 hqε.le) _

/-- **Fubini–Study envelopes** (`lem:sg-fs-envelope`) for a real-valued lsc obstacle `φ`:
`P_a(φ) = sup {ψ ∈ 𝓗_fin(a) : ψ ≤ φ}` pointwise, for `a ∈ ℚ^r` with positive coordinates. -/
theorem envelope_coe_eq_iSup_isFinFS [CompactSpace K] {a : Fin r → ℚ} (ha : ∀ c, 0 < a c)
    {φ : K → ℝ} (hφ : LowerSemicontinuous φ) (x : K) :
    F.envelope (fun c => (a c : ℝ)) (fun w => (φ w : EReal)) x =
      ⨆ (ψ : K → EReal) (_ : F.IsFinFS a ψ ∧ ψ ≤ fun w => (φ w : EReal)), ψ x :=
  envelope_eq_iSup_isFinFS ha
    (continuous_coe_real_ereal.comp_lowerSemicontinuous hφ EReal.coe_strictMono.monotone)
    (fun _ => EReal.coe_ne_bot _) x

end FSSystem

end EnvelopeProperty
