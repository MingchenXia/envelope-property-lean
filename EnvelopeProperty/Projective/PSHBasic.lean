/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.PSH2
import EnvelopeProperty.Projective.Order

/-!
# Basic properties of `θ`-psh functions on `(ℙⁿ)^an`

This file proves, on the model `ProjBerk k n` of `(ℙⁿ)^an`, Boucksom–Jonsson, *Global
pluripotential theory over a trivially valued field* (BJ22), Theorem 4.7 (PSH) (i),(ii) and
Lemma 4.9 (twopsh), i.e. Fang–Han–Xia, *The envelope property for unibranch projective
varieties* (FHX), `prop:BJ-package`(5), together with the translation rules for psh envelopes of
FHX §2.3 (`subsec:prelim-envelopes`) used in the reduction of FHX §3.

For `ℙⁿ`, `N¹(ℙⁿ)_ℝ = ℝ`, `Pic(ℙⁿ)_ℚ = ℚ` (the class `a` standing for `O(a)`), and "`L' - L`
ample" for rational classes means `a' > a`. The "ample difference" step of BJ22 (twopsh) is
`ProjBerk.IsFS.mono_class`: an FS function for `O(a)` is one for `O(a')` when `a ≤ a'`, by
adding the FS function `0 = max_i log|xᵢ^{m(a'-a)}|` of class `a' - a` (i.e. multiplying the
sections by the forms `xᵢ^{m(a'-a)}`); so two nets of classes converging to `θ` can be replaced by
the common classes `max(aᵢ, a'ⱼ)`.

## Main results

* `ProjBerk.IsPSH.add_const` (additive action of `ℝ`), `ProjBerk.IsPSH.add`
  (`PSH(θ) + PSH(θ') ⊆ PSH(θ + θ')`), `ProjBerk.IsPSH.mono_class` (`PSH(θ) ⊆ PSH(η)` for
  `θ ≤ η`), `ProjBerk.IsPSH.smul_rat`, `ProjBerk.IsPSH.smul`
  (`t PSH(θ) ⊆ PSH(t θ)` for real `t > 0`: rational `t` first, then PSH2 along rationals
  `tₘ ↑ t` after normalizing `u ≤ 0`), `ProjBerk.isPSH_smul_iff` and `ProjBerk.setOf_isPSH_mul`
  (`PSH(t θ) = t PSH(θ)`);
* `ProjBerk.IsPSH.convex_comb` (convexity), `ProjBerk.IsPSH.exists_common_net` (twopsh),
  `ProjBerk.IsPSH.max`, `ProjBerk.isPSH_finset_sup'` (finite maxima),
  `ProjBerk.isPSH_of_uniform_limit` (uniform limits), `ProjBerk.IsPSH.scaleFun` (the scaling
  action `(t · u)(v) = t u(t⁻¹ v)`);
* `ProjBerk.envelope_add_const` (`P_θ(φ + c) = P_θ(φ) + c`) and `ProjBerk.envelope_mul`
  (`P_{tθ}(t φ) = t P_θ(φ)` for `t > 0`).
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

namespace ProjBerk

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-! ### Auxiliary facts on `EReal` -/

theorem ereal_add_coe_add_neg (x : EReal) (c : ℝ) : x + (c : EReal) + ((-c : ℝ) : EReal) = x := by
  rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]

theorem ereal_add_neg_add_coe (x : EReal) (c : ℝ) : x + ((-c : ℝ) : EReal) + (c : EReal) = x := by
  rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]

theorem ereal_inv_mul_mul {t : ℝ} (ht : t ≠ 0) (x : EReal) :
    ((t⁻¹ : ℝ) : EReal) * ((t : EReal) * x) = x := by
  rw [ereal_coe_mul_coe_mul, inv_mul_cancel₀ ht, EReal.coe_one, one_mul]

theorem ereal_add_coe_ne_bot {x : EReal} (hx : x ≠ ⊥) (c : ℝ) : x + (c : EReal) ≠ ⊥ := by
  rw [Ne, EReal.add_eq_bot_iff, not_or]
  exact ⟨hx, EReal.coe_ne_bot c⟩

/-- `b x ≤ a x` for `0 < a ≤ b` and `x ≤ 0`. -/
theorem ereal_coe_mul_le_of_nonpos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {x : EReal} (hx : x ≤ 0) :
    (b : EReal) * x ≤ (a : EReal) * x := by
  induction x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos (ha.trans_le hab)]; exact bot_le
  | coe r =>
    rw [← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    have : r ≤ 0 := by exact_mod_cast hx
    nlinarith
  | top => exact absurd hx (by simp)

/-- `tₘ x → t x` for real `tₘ → t > 0`, `tₘ > 0` and `x ∈ [-∞, ∞)`. -/
theorem tendsto_coe_mul_ereal {ι : Type*} {l : Filter ι} {f : ι → ℝ} {t : ℝ}
    (hf : Tendsto f l (𝓝 t)) (ht : 0 < t) (hf0 : ∀ i, 0 < f i) {x : EReal} (hx : x ≠ ⊤) :
    Tendsto (fun i => (f i : EReal) * x) l (𝓝 ((t : EReal) * x)) := by
  induction x using EReal.rec with
  | bot =>
    simp only [EReal.coe_mul_bot_of_pos (hf0 _), EReal.coe_mul_bot_of_pos ht]
    exact tendsto_const_nhds
  | coe r =>
    simp only [← EReal.coe_mul]
    exact EReal.tendsto_coe.2 (hf.mul_const r)
  | top => exact absurd rfl hx

/-! ### Inclusions of FS classes ("ample difference") -/

/-- **Inclusion of FS classes** (the "ample difference" step of BJ22 twopsh on `ℙⁿ`): an
FS function for `O(a)` is an FS function for `O(b)` for every `b ≥ a`, by adding the FS function
`0 = max_i log|xᵢ^{m(b-a)}|` of class `b - a`. -/
theorem IsFS.mono_class {a b : ℚ} {φ : ProjBerk k n → EReal} (h : IsFS a φ) (hab : a ≤ b) :
    IsFS b φ := by
  have h' := h.add (isFS_const (k := k) (n := n) (sub_nonneg.2 hab) 0)
  rw [add_sub_cancel] at h'
  simpa only [EReal.coe_zero, add_zero] using h'

/-! ### Approximating nets -/

variable {θ θ' : ℝ} {u u' : ProjBerk k n → EReal}

/-- A `θ`-psh function is the limit of a decreasing net of FS functions with classes converging
to `θ`, in the limit form. -/
theorem IsPSH.exists_tendsto (h : IsPSH θ u) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (a : ι → ℚ)
      (φ : ι → ProjBerk k n → EReal), (∀ i, IsFS (a i) (φ i)) ∧
        Tendsto (fun i => (a i : ℝ)) atTop (𝓝 θ) ∧ (∀ v, Antitone fun i => φ i v) ∧
          ∀ v, Tendsto (fun i => φ i v) atTop (𝓝 (u v)) := by
  obtain ⟨-, -, ι, _, _, _, a, φ, hφ, ha, hanti, hu⟩ := h
  exact ⟨ι, inferInstance, inferInstance, inferInstance, a, φ, hφ, ha, hanti, fun v => by
    rw [hu v]; exact tendsto_atTop_iInf (hanti v)⟩

theorem tendsto_prod_fst_atTop {α β : Type*} [Preorder α] [Preorder β] :
    Tendsto (Prod.fst : α × β → α) atTop atTop := by
  rw [← prod_atTop_atTop_eq]; exact tendsto_fst

theorem tendsto_prod_snd_atTop {α β : Type*} [Preorder α] [Preorder β] :
    Tendsto (Prod.snd : α × β → β) atTop atTop := by
  rw [← prod_atTop_atTop_eq]; exact tendsto_snd

/-! ### The additive action of `ℝ` and sums -/

/-- **Adding a real constant** preserves `θ`-psh functions (BJ22 PSH(ii)). -/
theorem IsPSH.add_const (h : IsPSH θ u) (c : ℝ) : IsPSH θ fun v => u v + (c : EReal) := by
  have hfin := h.apply_triv_ne_bot
  obtain ⟨ι, _, _, _, a, φ, hφ, ha, hanti, hlim⟩ := h.exists_tendsto
  exact isPSH_of_tendsto ⟨triv, ereal_add_coe_ne_bot hfin c⟩ a (fun i v => φ i v + (c : EReal))
    (fun i => (hφ i).add_const c) ha (fun v _ _ hij => add_le_add_left (hanti v hij) _)
    fun v => ((continuous_ereal_add_coe c).tendsto _).comp (hlim v)

/-- **Sums** (BJ22 PSH(i)): `PSH(θ) + PSH(θ') ⊆ PSH(θ + θ')`, using the product net. -/
theorem IsPSH.add (h : IsPSH θ u) (h' : IsPSH θ' u') : IsPSH (θ + θ') fun v => u v + u' v := by
  have hfin := h.apply_triv_ne_bot
  have hfin' := h'.apply_triv_ne_bot
  have htop := h.ne_top
  have htop' := h'.ne_top
  obtain ⟨ι, _, _, _, a, φ, hφ, ha, hanti, hlim⟩ := h.exists_tendsto
  obtain ⟨ι', _, _, _, a', φ', hφ', ha', hanti', hlim'⟩ := h'.exists_tendsto
  have : IsDirected (ι × ι') (· ≤ ·) := isDirected_prod
  refine isPSH_of_tendsto (ι := ι × ι') ⟨triv, ?_⟩ (fun p => a p.1 + a' p.2)
    (fun p v => φ p.1 v + φ' p.2 v) (fun p => (hφ p.1).add (hφ' p.2)) ?_
    (fun v p q hpq => add_le_add (hanti v (Prod.le_def.1 hpq).1) (hanti' v (Prod.le_def.1 hpq).2))
      fun v =>
      tendsto_ereal_add ((hlim v).comp tendsto_prod_fst_atTop)
        ((hlim' v).comp tendsto_prod_snd_atTop) (htop v) (htop' v)
  · rw [Ne, EReal.add_eq_bot_iff, not_or]
    exact ⟨hfin, hfin'⟩
  · simp only [Rat.cast_add]
    exact (ha.comp tendsto_prod_fst_atTop).add (ha'.comp tendsto_prod_snd_atTop)

/-- **Monotonicity in the class** (FHX `prop:BJ-package`(5)): `PSH(θ) ⊆ PSH(η)` when `η - θ` is
nef, i.e. `θ ≤ η` on `ℙⁿ`, by adding the zero function of the nef class `η - θ`. -/
theorem IsPSH.mono_class (h : IsPSH θ u) {η : ℝ} (hθη : θ ≤ η) : IsPSH η u := by
  have h' := h.add (isPSH_const (k := k) (n := n) (sub_nonneg.2 hθη) 0)
  rw [add_sub_cancel] at h'
  simpa only [EReal.coe_zero, add_zero] using h'

/-! ### Scalar multiples -/

/-- Positive rational multiples: `c PSH(θ) ⊆ PSH(c θ)` for `c ∈ ℚ_{>0}`. -/
theorem IsPSH.smul_rat (h : IsPSH θ u) {c : ℚ} (hc : 0 < c) :
    IsPSH ((c : ℝ) * θ) fun v => ((c : ℝ) : EReal) * u v := by
  have hfin := h.apply_triv_ne_bot
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  obtain ⟨ι, _, _, _, a, φ, hφ, ha, hanti, hlim⟩ := h.exists_tendsto
  refine isPSH_of_tendsto ⟨triv, ereal_coe_mul_ne_bot hc'.le hfin⟩ (fun i => c * a i)
    (fun i v => ((c : ℝ) : EReal) * φ i v) (fun i => (hφ i).smul hc) ?_
    (fun v _ _ hij => ereal_coe_mul_monotone hc'.le (hanti v hij))
    fun v => tendsto_ereal_coe_mul (hlim v) c
  simp only [Rat.cast_mul]
  exact tendsto_const_nhds.mul ha

/-- **Positive real multiples** (BJ22 PSH(i)): `t PSH(θ) ⊆ PSH(t θ)` for `t > 0`. After
replacing `u` with `u - sup u ≤ 0`, take rationals `tₘ ↑ t`: then `tₘ u ∈ PSH(tₘ θ)` decreases
to `t u`, and PSH2 applies. -/
theorem IsPSH.smul (h : IsPSH θ u) {t : ℝ} (ht : 0 < t) :
    IsPSH (t * θ) fun v => (t : EReal) * u v := by
  set c := (u triv).toReal with hc_def
  set u₀ : ProjBerk k n → EReal := fun v => u v + ((-c : ℝ) : EReal) with hu₀_def
  have h₀ : IsPSH θ u₀ := h.add_const (-c)
  have hu₀ : ∀ v, u₀ v ≤ 0 := fun v => by
    have := add_le_add_left (h.le_toReal_apply_triv v) ((-c : ℝ) : EReal)
    rwa [← hc_def, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at this
  -- rationals increasing to `t`
  obtain ⟨q, hqmono, -, hq⟩ := Real.exists_seq_rat_strictMono_tendsto t
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hq.eventually (lt_mem_nhds ht))
  set q' : ℕ → ℚ := fun m => q (m + N) with hq'_def
  have hq'pos : ∀ m, (0 : ℝ) < q' m := fun m => hN _ (Nat.le_add_left N m)
  have hq'pos' : ∀ m, (0 : ℚ) < q' m := fun m => by exact_mod_cast hq'pos m
  have hq'lim : Tendsto (fun m => (q' m : ℝ)) atTop (𝓝 t) := hq.comp (tendsto_add_atTop_nat N)
  have hq'mono : Monotone fun m => (q' m : ℝ) := fun m m' h => by
    show (q (m + N) : ℝ) ≤ q (m' + N)
    exact_mod_cast hqmono.monotone (Nat.add_le_add_right h N)
  -- PSH2 for `t u₀`
  have htu₀ : IsPSH (t * θ) fun v => (t : EReal) * u₀ v := by
    refine isPSH_of_antitone_seq (θ := fun m => (q' m : ℝ) * θ) (hq'lim.mul_const θ)
      (fun m => h₀.smul_rat (hq'pos' m))
      (fun v m m' hmm' => ereal_coe_mul_le_of_nonpos (hq'pos m) (hq'mono hmm') (hu₀ v))
      (fun v => tendsto_nhds_unique
        (tendsto_coe_mul_ereal hq'lim ht hq'pos (h₀.ne_top v))
        (tendsto_atTop_iInf fun m m' hmm' =>
          ereal_coe_mul_le_of_nonpos (hq'pos m) (hq'mono hmm') (hu₀ v)))
      ⟨triv, ereal_coe_mul_ne_bot ht.le h₀.apply_triv_ne_bot⟩
  -- `t u = t u₀ + t c`
  convert htu₀.add_const (t * c) using 2 with v
  rw [hu₀_def, ereal_coe_mul_add ht.le, ← EReal.coe_mul, add_assoc, ← EReal.coe_add, mul_neg,
    neg_add_cancel, EReal.coe_zero, add_zero]

/-- **`PSH(t θ) = t PSH(θ)`** (BJ22 PSH(i)), pointwise form. -/
theorem isPSH_smul_iff {t : ℝ} (ht : 0 < t) :
    IsPSH (t * θ) (fun v => (t : EReal) * u v) ↔ IsPSH θ u := by
  refine ⟨fun h => ?_, fun h => h.smul ht⟩
  have h' := h.smul (inv_pos.2 ht)
  rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul] at h'
  simpa only [ereal_inv_mul_mul ht.ne'] using h'

/-- **`PSH(t θ) = t PSH(θ)`** (BJ22 PSH(i)), as an equality of sets. -/
theorem setOf_isPSH_mul {t : ℝ} (ht : 0 < t) :
    {w : ProjBerk k n → EReal | IsPSH (t * θ) w} =
      (fun u v => (t : EReal) * u v) '' {u | IsPSH θ u} := by
  ext w
  constructor
  · intro hw
    refine ⟨fun v => ((t⁻¹ : ℝ) : EReal) * w v, ?_, funext fun v => ?_⟩
    · have h' := IsPSH.smul (u := w) hw (inv_pos.2 ht)
      rwa [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul] at h'
    · exact ereal_coe_mul_inv_mul ht.ne' (w v)
  · rintro ⟨u, hu, rfl⟩
    exact IsPSH.smul hu ht

/-! ### Convexity -/

/-- **Convexity** (BJ22 PSH(ii)): `a u + b u' ∈ PSH(θ)` for `u, u' ∈ PSH(θ)`, `a, b ≥ 0`,
`a + b = 1` (with `0 · (-∞) = 0`). -/
theorem IsPSH.convex_comb (h : IsPSH θ u) (h' : IsPSH θ u') {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : IsPSH θ fun v => (a : EReal) * u v + (b : EReal) * u' v := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · rw [zero_add] at hab
    subst hab
    simpa only [EReal.coe_zero, zero_mul, EReal.coe_one, one_mul, zero_add] using h'
  rcases eq_or_lt_of_le hb with rfl | hb'
  · rw [add_zero] at hab
    subst hab
    simpa only [EReal.coe_zero, zero_mul, EReal.coe_one, one_mul, add_zero] using h
  have h'' := (h.smul ha').add (h'.smul hb')
  rwa [← add_mul, hab, one_mul] at h''

/-! ### Finite maxima -/

/-- **BJ22 twopsh**: two `θ`-psh functions are limits of decreasing nets of FS functions
of common classes `aᵢ → θ`. On `ℙⁿ` the common classes are `max(aᵢ, a'ⱼ)` on the product net
(`IsFS.mono_class`). -/
theorem IsPSH.exists_common_net (h : IsPSH θ u) (h' : IsPSH θ u') :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (a : ι → ℚ)
      (φ φ' : ι → ProjBerk k n → EReal), (∀ i, IsFS (a i) (φ i)) ∧ (∀ i, IsFS (a i) (φ' i)) ∧
        Tendsto (fun i => (a i : ℝ)) atTop (𝓝 θ) ∧ (∀ v, Antitone fun i => φ i v) ∧
          (∀ v, Antitone fun i => φ' i v) ∧ (∀ v, Tendsto (fun i => φ i v) atTop (𝓝 (u v))) ∧
            ∀ v, Tendsto (fun i => φ' i v) atTop (𝓝 (u' v)) := by
  obtain ⟨ι, _, _, _, a, φ, hφ, ha, hanti, hlim⟩ := h.exists_tendsto
  obtain ⟨ι', _, _, _, a', φ', hφ', ha', hanti', hlim'⟩ := h'.exists_tendsto
  have : IsDirected (ι × ι') (· ≤ ·) := isDirected_prod
  refine ⟨ι × ι', inferInstance, inferInstance, inferInstance, fun p => Max.max (a p.1) (a' p.2),
    fun p => φ p.1, fun p => φ' p.2, fun p => (hφ p.1).mono_class (le_max_left _ _),
    fun p => (hφ' p.2).mono_class (le_max_right _ _), ?_,
    fun v p q hpq => hanti v (Prod.le_def.1 hpq).1, fun v p q hpq => hanti' v (Prod.le_def.1 hpq).2,
    fun v => (hlim v).comp tendsto_prod_fst_atTop, fun v => (hlim' v).comp tendsto_prod_snd_atTop⟩
  simp only [Rat.cast_max]
  have := (ha.comp tendsto_prod_fst_atTop).max (ha'.comp tendsto_prod_snd_atTop)
  rw [max_self] at this
  exact this

/-- **Maxima** (BJ22 PSH(ii)): `max(u, u') ∈ PSH(θ)` for `u, u' ∈ PSH(θ)`. -/
theorem IsPSH.max (h : IsPSH θ u) (h' : IsPSH θ u') : IsPSH θ fun v => max (u v) (u' v) := by
  have hfin := h.apply_triv_ne_bot
  obtain ⟨ι, _, _, _, a, φ, φ', hφ, hφ', ha, hanti, hanti', hlim, hlim'⟩ :=
    h.exists_common_net h'
  exact isPSH_of_tendsto ⟨triv, ne_bot_of_le_ne_bot hfin (le_max_left _ _)⟩ a
    (fun i v => Max.max (φ i v) (φ' i v)) (fun i => (hφ i).max (hφ' i)) ha
    (fun v _ _ hij => max_le_max (hanti v hij) (hanti' v hij)) fun v => (hlim v).max (hlim' v)

/-- **Finite maxima** (BJ22 PSH(ii)). -/
theorem isPSH_finset_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {w : ι → ProjBerk k n → EReal} (hw : ∀ i ∈ s, IsPSH θ (w i)) :
    IsPSH θ fun v => s.sup' hs fun i => w i v := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa only [Finset.sup'_singleton] using hw a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    simp only [Finset.sup'_cons hs]
    exact (hw a (Finset.mem_cons_self a s)).max
      (ih fun i hi => hw i (Finset.mem_cons_of_mem hi))

/-! ### Uniform limits -/

/-- **Uniform limits** (BJ22 PSH(ii)): if `uᵢ ∈ PSH(θ)` converges uniformly to `w` along a
nontrivial filter, in the sense that eventually `uᵢ ≤ w + ε` and `w ≤ uᵢ + ε` everywhere, then
`w ∈ PSH(θ)`. Pick `u_{iₘ}` with `ε = 2⁻ᵐ`; then `u_{iₘ} + 3 · 2⁻ᵐ` decreases to `w`, and PSH2
applies. -/
theorem isPSH_of_uniform_limit {ι : Type*} {l : Filter ι} [l.NeBot]
    {w : ι → ProjBerk k n → EReal} (hw : ∀ i, IsPSH θ (w i)) {u : ProjBerk k n → EReal}
    (hunif : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ v, w i v ≤ u v + (ε : EReal) ∧
      u v ≤ w i v + (ε : EReal)) : IsPSH θ u := by
  have hε : ∀ m : ℕ, (0 : ℝ) < (1 / 2) ^ m := fun m => by positivity
  choose i hi using fun m => (hunif _ (hε m)).exists
  set ε : ℕ → ℝ := fun m => (1 / 2) ^ m with hε_def
  have hεsucc : ∀ m, ε m + ε (m + 1) + 3 * ε (m + 1) = 3 * ε m := fun m => by
    simp only [hε_def, pow_succ]; ring
  have hutop : ∀ v, u v ≠ ⊤ := fun v => by
    intro htop
    have := (hi 0 v).2
    rw [htop, top_le_iff] at this
    exact EReal.add_ne_top ((hw (i 0)).ne_top v) (EReal.coe_ne_top _) this
  set ψ : ℕ → ProjBerk k n → EReal := fun m v => w (i m) v + ((3 * ε m : ℝ) : EReal) with hψ_def
  have hanti : ∀ v, Antitone fun m => ψ m v := fun v => antitone_nat_of_succ_le fun m => by
    calc ψ (m + 1) v ≤ u v + (ε (m + 1) : EReal) + ((3 * ε (m + 1) : ℝ) : EReal) :=
          add_le_add_left (hi (m + 1) v).1 _
      _ ≤ w (i m) v + (ε m : EReal) + (ε (m + 1) : EReal) + ((3 * ε (m + 1) : ℝ) : EReal) :=
          add_le_add_left (add_le_add_left (hi m v).2 _) _
      _ = ψ m v := by
          rw [hψ_def, add_assoc, add_assoc, ← EReal.coe_add, ← EReal.coe_add, ← add_assoc,
            hεsucc]
  refine isPSH_of_antitone_seq (θ := fun _ => θ) tendsto_const_nhds
    (fun m => (hw (i m)).add_const _) hanti (fun v => ?_) ⟨triv, ?_⟩
  · refine le_antisymm (le_iInf fun m => ?_) ?_
    · refine (hi m v).2.trans (add_le_add_right (EReal.coe_le_coe_iff.2 ?_) _)
      have := hε m
      linarith
    · have hlim : Tendsto (fun m => u v + ((4 * ε m : ℝ) : EReal)) atTop (𝓝 (u v)) := by
        have h0 : Tendsto (fun m => ((4 * ε m : ℝ) : EReal)) atTop (𝓝 ((0 : ℝ) : EReal)) := by
          refine EReal.tendsto_coe.2 ?_
          simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
            (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 4
        simpa only [EReal.coe_zero, add_zero] using
          tendsto_ereal_add tendsto_const_nhds h0 (hutop v) (EReal.coe_ne_top 0)
      refine ge_of_tendsto' hlim fun m => (iInf_le _ m).trans ?_
      calc ψ m v ≤ u v + (ε m : EReal) + ((3 * ε m : ℝ) : EReal) := add_le_add_left (hi m v).1 _
        _ = u v + ((4 * ε m : ℝ) : EReal) := by
          rw [add_assoc, ← EReal.coe_add]; ring_nf
  · intro hbot
    have := (hi 0 triv).1
    rw [hbot, EReal.bot_add, le_bot_iff] at this
    exact (hw (i 0)).apply_triv_ne_bot this

/-! ### The scaling action -/

/-- **The scaling action** (BJ22 PSH(ii)): `t · u ∈ PSH(θ)` for `u ∈ PSH(θ)` and `t > 0`,
where `(t · u)(v) = t u(t⁻¹ v)`; FS functions of class `a` are mapped to FS functions of class `a`
(`IsFS.scaleFun`). -/
theorem IsPSH.scaleFun (h : IsPSH θ u) (t : ℝ) (ht : 0 < t) : IsPSH θ (scaleFun t ht u) := by
  have hfin := h.apply_triv_ne_bot
  obtain ⟨ι, _, _, _, a, φ, hφ, ha, hanti, hlim⟩ := h.exists_tendsto
  refine isPSH_of_tendsto ⟨triv, ?_⟩ a (fun i => ProjBerk.scaleFun t ht (φ i))
    (fun i => (hφ i).scaleFun t ht) ha
    (fun v _ _ hij => ereal_coe_mul_monotone ht.le (hanti _ hij))
    fun v => tendsto_ereal_coe_mul (hlim _) t
  rw [ProjBerk.scaleFun, rpow_triv]
  exact ereal_coe_mul_ne_bot ht.le hfin

/-! ### Envelopes -/

/-- **Envelopes and constants** (FHX §2.3): `P_θ(φ + c) = P_θ(φ) + c` for `c ∈ ℝ`. -/
theorem envelope_add_const (φ : ProjBerk k n → EReal) (c : ℝ) :
    envelope θ (fun v => φ v + (c : EReal)) = fun v => envelope θ φ v + (c : EReal) := by
  funext v
  refine le_antisymm (iSup₂_le fun τ hτ => ?_) ?_
  · have h₁ : IsPSH θ fun w => τ w + ((-c : ℝ) : EReal) := hτ.1.add_const (-c)
    have h₂ : (fun w => τ w + ((-c : ℝ) : EReal)) ≤ φ := fun w => by
      have := add_le_add_left (hτ.2 w) ((-c : ℝ) : EReal)
      rwa [ereal_add_coe_add_neg] at this
    have := add_le_add_left (le_envelope h₁ h₂ v) (c : EReal)
    rwa [ereal_add_neg_add_coe] at this
  · have key : envelope θ φ v ≤ envelope θ (fun v => φ v + (c : EReal)) v + ((-c : ℝ) : EReal) := by
      refine iSup₂_le fun τ hτ => ?_
      have h₁ : IsPSH θ fun w => τ w + (c : EReal) := hτ.1.add_const c
      have h₂ : (fun w => τ w + (c : EReal)) ≤ fun w => φ w + (c : EReal) := fun w =>
        add_le_add_left (hτ.2 w) _
      have := add_le_add_left (le_envelope h₁ h₂ v) ((-c : ℝ) : EReal)
      rwa [ereal_add_coe_add_neg] at this
    have := add_le_add_left key (c : EReal)
    rwa [ereal_add_neg_add_coe] at this

/-- **Envelopes and scaling of the class** (FHX §2.3, §3): `P_{tθ}(t φ) = t P_θ(φ)` for real
`t > 0`, since `PSH(t θ) = t PSH(θ)`. -/
theorem envelope_mul (φ : ProjBerk k n → EReal) {t : ℝ} (ht : 0 < t) :
    envelope (t * θ) (fun v => (t : EReal) * φ v) = fun v => (t : EReal) * envelope θ φ v := by
  funext v
  have hinv : (0 : ℝ) ≤ t⁻¹ := (inv_pos.2 ht).le
  refine le_antisymm (iSup₂_le fun τ hτ => ?_) ?_
  · have h₁ : IsPSH θ fun w => ((t⁻¹ : ℝ) : EReal) * τ w := by
      have h' := hτ.1.smul (inv_pos.2 ht)
      rwa [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul] at h'
    have h₂ : (fun w => ((t⁻¹ : ℝ) : EReal) * τ w) ≤ φ := fun w => by
      have := ereal_coe_mul_monotone hinv (hτ.2 w)
      dsimp only at this ⊢
      rwa [ereal_inv_mul_mul ht.ne'] at this
    have := ereal_coe_mul_monotone ht.le (le_envelope h₁ h₂ v)
    dsimp only at this
    rwa [ereal_coe_mul_inv_mul ht.ne'] at this
  · have key : envelope θ φ v ≤
        ((t⁻¹ : ℝ) : EReal) * envelope (t * θ) (fun v => (t : EReal) * φ v) v := by
      refine iSup₂_le fun τ hτ => ?_
      have h₁ : IsPSH (t * θ) fun w => (t : EReal) * τ w := hτ.1.smul ht
      have h₂ : (fun w => (t : EReal) * τ w) ≤ fun w => (t : EReal) * φ w := fun w =>
        ereal_coe_mul_monotone ht.le (hτ.2 w)
      have := ereal_coe_mul_monotone hinv (le_envelope h₁ h₂ v)
      dsimp only at this
      rwa [ereal_inv_mul_mul ht.ne'] at this
    have := ereal_coe_mul_monotone ht.le key
    dsimp only at this
    rwa [ereal_coe_mul_inv_mul ht.ne'] at this

end ProjBerk

end EnvelopeProperty
