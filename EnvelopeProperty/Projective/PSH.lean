/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.FS

/-!
# `θ`-psh functions on `(ℙⁿ)^an`, envelopes and the envelope property

For `X = ℙⁿ` over the trivially valued field `k` and `n ≥ 1`, `N¹(X)_ℝ = ℝ` and
`Pic(X)_ℚ = ℚ`. For `n = 0` both geometric groups vanish. The definitions below retain
all `n : ℕ`; at `n = 0` their scalar parameters are formal model parameters and do not
identify the geometric numerical or Picard groups with `ℝ` or `ℚ`. This file
transcribes, on the model `ProjBerk k n` of `(ℙⁿ)^an` (`EnvelopeProperty.Projective.Basic`):

* Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field* (BJ22),
  Definition 4.1 (`defi:psh`): a **`θ`-psh function** is a generically finite, usc function
  `u : X^an → [-∞, ∞)` that is the pointwise limit of a decreasing net `φᵢ ∈ 𝓗^gf_ℝ(Lᵢ)` with
  `Lᵢ ∈ Pic(X)_ℚ` and `c₁(Lᵢ) → θ`. For `ℙⁿ` with `n ≥ 1`, `Lᵢ = O(aᵢ)` with
  `aᵢ ∈ ℚ`, `c₁(Lᵢ) = aᵢ`, and the
  FS classes are `ProjBerk.IsFS` (`EnvelopeProperty.Projective.FS`). Since `ℙⁿ` is irreducible,
  generically finite means `u ≢ -∞`.
* The usc regularization `f^⋆(x) = limsup_{y → x} f(y)`, the smallest usc function `≥ f`
  (BJ22, conventions in the introduction; Mathlib has no such notion, so we define
  `EnvelopeProperty.uscReg`).
* Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX), §2.3
  (`subsec:prelim-envelopes`): the **psh envelope** `P_θ(φ) = sup {τ ∈ PSH(θ) : τ ≤ φ}`, without
  usc regularization.
* BJ22 §5.2 (envprop): `θ` has the **envelope property** if for every (nonempty) family in
  `PSH(θ)` that is uniformly bounded above, the usc regularization of its pointwise supremum is
  `θ`-psh.

## Design choices

* The decreasing net is indexed by a type `ι : Type u` in the universe of `k` with
  `[Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]`; "pointwise limit of a decreasing net" is
  recorded as `u = ⨅ᵢ φᵢ` for an antitone net, which is equivalent (`ProjBerk.isPSH_of_tendsto`
  takes the limit form as input).
* The usc condition is kept, verbatim from BJ22, although it is automatic for an infimum of
  continuous functions (`ProjBerk.isPSH_of_iInf` constructs psh functions without it).
* A family in the envelope property is a set `S` of functions (`ProjBerk.HasEnvelopeProperty`);
  `ProjBerk.HasEnvelopeProperty.isPSH_uscReg_iSup` restates it for indexed families in any
  universe.

## Main results

* `EnvelopeProperty.le_uscReg`, `EnvelopeProperty.upperSemicontinuous_uscReg`,
  `EnvelopeProperty.uscReg_le_of_le`: `f^⋆` is the smallest usc majorant of `f`.
* `ProjBerk.IsFS.isPSH` (PSH1): FS functions of class `a` are `a`-psh.
* `ProjBerk.isPSH_const`: constants are `θ`-psh for every `θ ≥ 0`.
* `ProjBerk.IsPSH.lt_top`: `θ`-psh functions take values `< +∞`; `ProjBerk.IsPSH.nonneg`:
  `PSH(θ) ≠ ∅` forces `θ ≥ 0`.
* `ProjBerk.envelope_le`, `ProjBerk.le_envelope`, `ProjBerk.envelope_mono`.
* `ProjBerk.HasEnvelopeProperty.isPSH_uscReg_envelope`: under the envelope property, `P_θ(φ)^⋆`
  is `θ`-psh as soon as `φ` is bounded above and dominates some `θ`-psh function.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

/-! ### The usc regularization -/

section uscReg

variable {X : Type*} [TopologicalSpace X] {γ : Type*} [CompleteLinearOrder γ]

/-- The **usc regularization** `f^⋆(x) = limsup_{y → x} f(y)` (the limit superior includes
`y = x`); it is the smallest usc function `≥ f` (BJ22, conventions). -/
def uscReg (f : X → γ) (x : X) : γ :=
  limsup f (𝓝 x)

theorem uscReg_eq_iInf_iSup (f : X → γ) (x : X) : uscReg f x = ⨅ U ∈ 𝓝 x, ⨆ y ∈ U, f y :=
  limsup_eq_iInf_iSup

theorem le_uscReg (f : X → γ) (x : X) : f x ≤ uscReg f x := by
  rw [uscReg_eq_iInf_iSup]
  exact le_iInf₂ fun U hU => le_iSup₂_of_le (f := fun y (_ : y ∈ U) => f y) x
    (mem_of_mem_nhds hU) le_rfl

theorem uscReg_mono {f g : X → γ} (h : f ≤ g) : uscReg f ≤ uscReg g := fun x => by
  simp only [uscReg_eq_iInf_iSup]
  exact iInf₂_mono fun U _ => iSup₂_mono fun y _ => h y

theorem upperSemicontinuous_uscReg (f : X → γ) : UpperSemicontinuous (uscReg f) := by
  intro x y hy
  rw [uscReg_eq_iInf_iSup] at hy
  obtain ⟨U, hU, hUy⟩ : ∃ U ∈ 𝓝 x, ⨆ z ∈ U, f z < y := by
    simpa only [iInf_lt_iff, exists_prop] using hy
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.1 hU
  filter_upwards [hV.mem_nhds hxV] with x' hx'
  rw [uscReg_eq_iInf_iSup]
  refine lt_of_le_of_lt (iInf₂_le V (hV.mem_nhds hx')) (lt_of_le_of_lt ?_ hUy)
  exact iSup₂_mono' fun z hz => ⟨z, hVU hz, le_rfl⟩

/-- `f^⋆ ≤ g` for every usc function `g ≥ f`. -/
theorem uscReg_le_of_le {f g : X → γ} (hg : UpperSemicontinuous g) (h : f ≤ g) :
    uscReg f ≤ g := fun x =>
  (uscReg_mono h x).trans (upperSemicontinuous_iff_limsup_le.1 hg x)

theorem uscReg_eq_self {f : X → γ} (hf : UpperSemicontinuous f) : uscReg f = f :=
  le_antisymm (uscReg_le_of_le hf le_rfl) (le_uscReg f)

end uscReg

namespace ProjBerk

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-! ### `θ`-psh functions -/

/-- **`θ`-psh functions** on the model of `(ℙⁿ)^an`, with scalar parameter `θ : ℝ`
(BJ22 Definition 4.1, `defi:psh`, after identifying `N¹(ℙⁿ)_ℝ = ℝ` for `n ≥ 1`): `u`
is generically finite (`u ≢ -∞`), usc, and the pointwise limit (= infimum) of a decreasing net
`φᵢ ∈ 𝓗^gf_ℝ(O(aᵢ))` of Fubini–Study functions whose scalar classes `aᵢ ∈ ℚ` converge to `θ`.
For `n = 0`, this is a scalar-parametrized model predicate; the geometric class groups vanish. -/
def IsPSH (θ : ℝ) (u : ProjBerk k n → EReal) : Prop :=
  (∃ v, u v ≠ ⊥) ∧ UpperSemicontinuous u ∧
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (a : ι → ℚ) (φ : ι → ProjBerk k n → EReal),
      (∀ i, IsFS (a i) (φ i)) ∧ Tendsto (fun i => (a i : ℝ)) atTop (𝓝 θ) ∧
        (∀ v, Antitone fun i => φ i v) ∧ ∀ v, u v = ⨅ i, φ i v

variable {θ : ℝ} {u : ProjBerk k n → EReal}

theorem IsPSH.exists_ne_bot (h : IsPSH θ u) : ∃ v, u v ≠ ⊥ := h.1

theorem IsPSH.upperSemicontinuous (h : IsPSH θ u) : UpperSemicontinuous u := h.2.1

/-- Constructing a `θ`-psh function from a decreasing net of FS functions: upper semicontinuity
is automatic for an infimum of continuous functions. -/
theorem isPSH_of_iInf (hfin : ∃ v, u v ≠ ⊥) {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] (a : ι → ℚ) (φ : ι → ProjBerk k n → EReal) (hφ : ∀ i, IsFS (a i) (φ i))
    (ha : Tendsto (fun i => (a i : ℝ)) atTop (𝓝 θ)) (hanti : ∀ v, Antitone fun i => φ i v)
    (hu : ∀ v, u v = ⨅ i, φ i v) : IsPSH θ u := by
  refine ⟨hfin, ?_, ι, inferInstance, inferInstance, inferInstance, a, φ, hφ, ha, hanti, hu⟩
  rw [show u = fun v => ⨅ i, φ i v from funext hu]
  exact upperSemicontinuous_iInf fun i => (hφ i).continuous.upperSemicontinuous

/-- The definition in its limit form: a generically finite pointwise limit of a decreasing net of
FS functions with classes converging to `θ` is `θ`-psh. -/
theorem isPSH_of_tendsto (hfin : ∃ v, u v ≠ ⊥) {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] (a : ι → ℚ) (φ : ι → ProjBerk k n → EReal) (hφ : ∀ i, IsFS (a i) (φ i))
    (ha : Tendsto (fun i => (a i : ℝ)) atTop (𝓝 θ)) (hanti : ∀ v, Antitone fun i => φ i v)
    (hu : ∀ v, Tendsto (fun i => φ i v) atTop (𝓝 (u v))) : IsPSH θ u :=
  isPSH_of_iInf hfin a φ hφ ha hanti fun v =>
    tendsto_nhds_unique (hu v) (tendsto_atTop_iInf (hanti v))

/-- **PSH1**: an FS function of class `a` is `a`-psh (constant net). -/
theorem IsFS.isPSH {a : ℚ} {φ : ProjBerk k n → EReal} (h : IsFS a φ) : IsPSH (a : ℝ) φ :=
  isPSH_of_iInf ⟨triv, h.triv_ne_bot⟩ (ι := PUnit.{u + 1}) (fun _ => a) (fun _ => φ)
    (fun _ => h) tendsto_const_nhds (fun _ _ _ _ => le_rfl) fun _ => (iInf_const).symm

theorem IsRatFS.isPSH {a : ℚ} {φ : ProjBerk k n → EReal} (h : IsRatFS a φ) : IsPSH (a : ℝ) φ :=
  h.isFS.isPSH

/-- Constants are `θ`-psh for every `θ ≥ 0`: they are FS functions of every rational class
`aᵢ ≥ 0`, and we take rationals `aᵢ ↓ θ`. -/
theorem isPSH_const (hθ : 0 ≤ θ) (c : ℝ) : IsPSH (k := k) (n := n) θ fun _ => (c : EReal) := by
  obtain ⟨q, -, hqθ, hq⟩ := Real.exists_seq_rat_strictAnti_tendsto θ
  have hq0 : ∀ i, 0 ≤ q i := fun i => by exact_mod_cast (hθ.trans (hqθ i).le)
  have hdown : Tendsto (ULift.down : ULift.{u} ℕ → ℕ) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨ULift.up b, fun a ha => ha⟩
  exact isPSH_of_iInf ⟨triv, EReal.coe_ne_bot c⟩ (ι := ULift.{u} ℕ) (fun i => q i.down)
    (fun _ _ => (c : EReal)) (fun i => isFS_const (hq0 i.down) c) (hq.comp hdown)
    (fun _ _ _ _ => le_rfl) fun _ => iInf_const.symm

/-- `θ`-psh functions take values `< +∞`. -/
theorem IsPSH.lt_top (h : IsPSH θ u) (v : ProjBerk k n) : u v < ⊤ := by
  obtain ⟨-, -, ι, _, _, _, a, φ, hφ, -, -, hu⟩ := h
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  rw [hu v]
  exact lt_of_le_of_lt (iInf_le _ i) (lt_top_iff_ne_top.2 ((hφ i).ne_top v))

theorem IsPSH.ne_top (h : IsPSH θ u) (v : ProjBerk k n) : u v ≠ ⊤ :=
  (h.lt_top v).ne

/-- `PSH(θ) ≠ ∅` forces `θ ≥ 0` (`θ` is pseudoeffective, BJ22 `equ:pshpsef`): the classes `aᵢ ≥ 0`
of the approximating FS functions converge to `θ`. -/
theorem IsPSH.nonneg (h : IsPSH θ u) : 0 ≤ θ := by
  obtain ⟨-, -, ι, _, _, _, a, φ, hφ, ha, -, -⟩ := h
  exact ge_of_tendsto ha (Eventually.of_forall fun i => by exact_mod_cast (hφ i).nonneg)

/-! ### Envelopes -/

/-- The **psh envelope** `P_θ(φ)(v) = sup {τ(v) : τ ∈ PSH(θ), τ ≤ φ}` (FHX §2.3), the pointwise
supremum without usc regularization. -/
def envelope (θ : ℝ) (φ : ProjBerk k n → EReal) (v : ProjBerk k n) : EReal :=
  ⨆ (τ : ProjBerk k n → EReal) (_ : IsPSH θ τ ∧ τ ≤ φ), τ v

theorem envelope_le (θ : ℝ) (φ : ProjBerk k n → EReal) : envelope θ φ ≤ φ := fun v =>
  iSup₂_le fun _ hτ => hτ.2 v

theorem le_envelope {φ τ : ProjBerk k n → EReal} (hτ : IsPSH θ τ) (hτφ : τ ≤ φ) :
    τ ≤ envelope θ φ := fun v =>
  le_iSup₂_of_le (f := fun (τ : ProjBerk k n → EReal) (_ : IsPSH θ τ ∧ τ ≤ φ) => τ v) τ
    ⟨hτ, hτφ⟩ le_rfl

/-- The envelope is increasing in `φ`. -/
theorem envelope_mono {φ ψ : ProjBerk k n → EReal} (h : φ ≤ ψ) : envelope θ φ ≤ envelope θ ψ :=
  fun v => iSup₂_le fun _ hτ => le_envelope hτ.1 (hτ.2.trans h) v

/-! ### The envelope property -/

/-- The **envelope property** of `θ ∈ N¹(ℙⁿ)_ℝ = ℝ` (BJ22 §5.2, envprop): for every nonempty
family `S ⊆ PSH(θ)` uniformly bounded above, the usc regularization `(sup S)^⋆` of its pointwise
supremum is `θ`-psh. -/
def HasEnvelopeProperty (k : Type u) [Field k] (n : ℕ) (θ : ℝ) : Prop :=
  ∀ S : Set (ProjBerk k n → EReal), S.Nonempty → (∀ u ∈ S, IsPSH θ u) →
    (∃ C : ℝ, ∀ u ∈ S, ∀ v, u v ≤ C) → IsPSH θ (uscReg fun v => ⨆ u ∈ S, u v)

/-- The envelope property for indexed families. -/
theorem HasEnvelopeProperty.isPSH_uscReg_iSup (h : HasEnvelopeProperty k n θ) {ι : Sort*}
    [Nonempty ι] {u : ι → ProjBerk k n → EReal} (hu : ∀ i, IsPSH θ (u i))
    (hbdd : ∃ C : ℝ, ∀ i v, u i v ≤ C) : IsPSH θ (uscReg fun v => ⨆ i, u i v) := by
  obtain ⟨C, hC⟩ := hbdd
  have e : (fun v => ⨆ i, u i v) = fun v => ⨆ w ∈ range u, w v := by
    funext v
    exact (iSup_range (g := fun w : ProjBerk k n → EReal => w v) (f := u)).symm
  rw [e]
  refine h (range u) (range_nonempty u) ?_ ⟨C, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hu i
  · rintro _ ⟨i, rfl⟩ v
    exact hC i v

/-- Under the envelope property, the usc regularization of the envelope `P_θ(φ)` is `θ`-psh, as
soon as `φ` is bounded above and dominates some `θ`-psh function. -/
theorem HasEnvelopeProperty.isPSH_uscReg_envelope (h : HasEnvelopeProperty k n θ)
    {φ : ProjBerk k n → EReal} (hne : ∃ τ, IsPSH θ τ ∧ τ ≤ φ) (hbdd : ∃ C : ℝ, ∀ v, φ v ≤ C) :
    IsPSH θ (uscReg (envelope θ φ)) := by
  obtain ⟨C, hC⟩ := hbdd
  exact h {τ | IsPSH θ τ ∧ τ ≤ φ} hne (fun _ hτ => hτ.1)
    ⟨C, fun _ hτ v => (hτ.2 v).trans (hC v)⟩

end ProjBerk

end EnvelopeProperty
