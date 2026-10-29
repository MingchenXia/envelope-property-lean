/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.PSHBasic
import Mathlib.Topology.Semicontinuity.Lindelof

/-!
# Regularization of `θ`-psh functions on `(ℙⁿ)^an`

This file proves, on the model `ProjBerk k n` of `(ℙⁿ)^an` (`EnvelopeProperty.Projective.Basic`),
the regularization results of Boucksom–Jonsson, *Global pluripotential theory over a trivially
valued field* (BJ22), used by Fang–Han–Xia, *The envelope property for unibranch projective
varieties* (FHX), §§3 and 5: every `θ`-psh function is the limit of a decreasing net of
**rational, finite-valued** Fubini–Study functions (BJ22 pshample), and, when `k` is
countable, of a decreasing **sequence** of them (BJ22 countreg, for countable `k` only).
The blueprint nodes are `lem:bj-fs-basic`, `thm:bj-regularization`, `lem:bj-lindelof`,
`cor:bj-countable-regularization` and `rmk:bj-countable-deviation` of `bj22.tex`.

## Operations on Fubini–Study functions (`lem:bj-fs-basic`)

Writing `H^gf_ℝ(a)`, `H^gf_ℚ(a)`, `H_ℚ(a)` for `ProjBerk.IsFS a`, `ProjBerk.IsRatFS a`,
`ProjBerk.IsFiniteRatFS a`:

1. class raising `H(a) ⊆ H(a')` for `a ≤ a'` (`ProjBerk.IsRatFS.mono_class`,
   `ProjBerk.IsFiniteRatFS.mono_class`; `ProjBerk.IsFS.mono_class` is in `PSHBasic`);
2. `c H(a) = H(c a)` for `c ∈ ℚ_{>0}` (`ProjBerk.isFS_smul_iff`, `ProjBerk.isRatFS_smul_iff`,
   `ProjBerk.isFiniteRatFS_smul_iff`);
3. addition of rational constants and truncation by rational constants
   (`ProjBerk.IsRatFS.add_const`, `ProjBerk.IsFiniteRatFS.add_const`,
   `ProjBerk.IsRatFS.max_const`); constants, maxima and sums are in `FS`;
4. every `φ ∈ H^gf_ℝ(a)` is the limit of a decreasing sequence in `H_ℚ(a)`, all of whose
   terms are `> φ` (`ProjBerk.IsFS.exists_antitone_finiteRatFS`): replace the weights `λ_j` by
   rationals `q_j^{(N)} ∈ (λ_j + m/(N+2), λ_j + m/(N+1))` (`ProjBerk.FSData.reweight`) and
   truncate at `-N`.

## Regularization (`thm:bj-regularization`)

* `ProjBerk.IsPSH.exists_finiteRatFS_net` (part (1)): `u ∈ PSH(θ)` is the infimum of a decreasing
  net `u_α ∈ H_ℚ(a_α)` with rational `a_α > θ`, `a_α` decreasing, `a_α → θ`, and `u < u_α`.
* `ProjBerk.IsPSH.exists_finiteRatFS_net_of_rat` (part (2)): if `θ = a ∈ ℚ_{>0}`, the classes
  can all be taken equal to `a`.

**Deviation from the blueprint proof.** The blueprint derives (1) from the rational form of PSH2
(`thm:bj-psh2`(1) with `H_ℚ`) and (2) from `lem:bj-psh-diagonal` with `T` a point. The available
Lean form of `lem:bj-psh-diagonal` (`EnvelopeProperty.IsDecrNetLimit.of_antitone_of_finite`)
needs families stable under addition of *all real* constants, which `H_ℚ(a)` is not. We
therefore index the net directly by the set of pairs `(b, f)` with `b ∈ ℚ`, `b > θ`,
`f ∈ H_ℚ(b)` and `u < f` pointwise, ordered by `b' ≤ b`, `f' ≤ f`
(`EnvelopeProperty.exists_antitone_net_of_directed`). Directedness is Dini's argument on the
compact space `(ℙⁿ)^an` (`EnvelopeProperty.exists_forall_lt_of_antitone`) applied to an
approximating net of `u` and then to the rational approximants of `lem:bj-fs-basic`(4)
(`ProjBerk.IsPSH.exists_finiteRatFS_lt_le`); the pointwise limit comes from
`ProjBerk.IsPSH.exists_finiteRatFS_lt_apply_lt`. For (2) the same construction is run inside
`H_ℚ(a)`, the class-`a` approximants being obtained, after normalizing `u < 0`, as `τ⁻¹ f` with
`f ∈ H_ℚ(τ a)`, `τ ∈ ℚ_{>1}` close to `1` (again by Dini) — the blueprint's scaling step
(`ProjBerk.IsPSH.exists_finiteRatFS_lt_le_of_rat`). As a by-product the classes in (1) are
decreasing, and all approximants lie strictly above `u`.

## Countable regularization (`lem:bj-lindelof`, `cor:bj-countable-regularization`)

* `EnvelopeProperty.exists_monotone_iInf_eq` (`lem:bj-lindelof`): on a hereditarily Lindelöf
  (e.g. second countable) space, a decreasing net of usc functions has the same infimum as its
  restriction to a monotone sequence of indices, which can be chosen above any given sequence;
  the countable subfamily comes from Mathlib's `exists_countable_upperSemicontinuous_isGLB`.
* `ProjBerk.instSecondCountableTopology`: `(ℙⁿ)^an` is second countable for countable `k`.
* `ProjBerk.IsPSH.exists_finiteRatFS_seq` and `ProjBerk.IsPSH.exists_finiteRatFS_seq_of_rat`:
  for countable `k`, the nets of (1) and (2) can be replaced by sequences; in (1) the rational
  classes `a_m` decrease to `θ`.

As explained in `rmk:bj-countable-deviation`, BJ22's Corollary 12.18 holds for all `k` but is
proved with the energy theory of BJ22 §§7–12; countability of `k` is the standing assumption of
FHX §5, which is where sequences are needed.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

/-! ### Topological lemmas -/

section Topological

/-- `{x | f x < g x}` is open for `f` upper semicontinuous and `g` continuous. -/
theorem isOpen_setOf_lt_of_upperSemicontinuous {X γ : Type*} [TopologicalSpace X] [LinearOrder γ]
    [DenselyOrdered γ] [TopologicalSpace γ] [OrderTopology γ] {f g : X → γ}
    (hf : UpperSemicontinuous f) (hg : Continuous g) : IsOpen {x | f x < g x} := by
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  obtain ⟨y, hy₁, hy₂⟩ := exists_between (show f x < g x from hx)
  filter_upwards [hf x y hy₁, hg.continuousAt.eventually (lt_mem_nhds hy₂)] with x' h₁ h₂
  exact h₁.trans h₂

/-- **Dini's argument.** On a compact space, if a decreasing net of usc functions `fᵢ` satisfies
`∀ x, ∃ i, fᵢ(x) < g(x)` for a continuous `g`, then `fᵢ < g` everywhere for some (hence every
larger) `i`. -/
theorem exists_forall_lt_of_antitone {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] {γ : Type*} [LinearOrder γ]
    [DenselyOrdered γ] [TopologicalSpace γ] [OrderTopology γ] {f : ι → K → γ}
    (hf : ∀ i, UpperSemicontinuous (f i)) (hanti : ∀ x, Antitone fun i => f i x) {g : K → γ}
    (hg : Continuous g) (h : ∀ x, ∃ i, f i x < g x) : ∃ i, ∀ x, f i x < g x := by
  obtain ⟨i, hi⟩ := isCompact_univ.elim_directed_cover (fun i => {x | f i x < g x})
    (fun i => isOpen_setOf_lt_of_upperSemicontinuous (hf i) hg)
    (fun x _ => mem_iUnion.2 (h x)) fun i i' => by
      obtain ⟨i'', h₁, h₂⟩ := directed_of (· ≤ ·) i i'
      exact ⟨i'', fun x hx => lt_of_le_of_lt (hanti x h₁) hx,
        fun x hx => lt_of_le_of_lt (hanti x h₂) hx⟩
  exact ⟨i, fun x => hi (mem_univ x)⟩

/-- **Countable subnets** (`lem:bj-lindelof`). Let `Z` be hereditarily Lindelöf (e.g. second
countable) and `(uᵢ)` a decreasing net of usc functions `Z → [-∞, +∞]`. Then there is a monotone
sequence of indices `i₀ ≤ i₁ ≤ ⋯`, which can be chosen above any given sequence `j`, with
`infₘ u_{iₘ} = infᵢ uᵢ`. -/
theorem exists_monotone_iInf_eq {Z : Type*} [TopologicalSpace Z] [HereditarilyLindelofSpace Z]
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] {u : ι → Z → EReal}
    (hu : ∀ i, UpperSemicontinuous (u i)) (hanti : ∀ z, Antitone fun i => u i z) (j : ℕ → ι) :
    ∃ i : ℕ → ι, Monotone i ∧ (∀ m, j m ≤ i m) ∧ ∀ z, ⨅ m, u (i m) z = ⨅ i, u i z := by
  classical
  obtain ⟨𝓕, h𝓕, h𝓕c, hglb⟩ := exists_countable_upperSemicontinuous_isGLB
    (s := ⨅ i, u i) (𝓕 := range u) (by rintro _ ⟨i, rfl⟩; exact hu i) isGLB_iInf
  -- an index for each member of the countable subfamily
  have hidx : ∀ f : 𝓕, ∃ i, u i = f := fun f => h𝓕 f.2
  choose idx hidx using hidx
  have : Countable 𝓕 := h𝓕c.to_subtype
  obtain ⟨e, he⟩ := ((countable_range idx).insert (Classical.arbitrary ι)).exists_eq_range
    (insert_nonempty _ _)
  -- the monotone sequence of indices
  choose ub hub₁ hub₂ using fun a b : ι => directed_of (· ≤ ·) a b
  let i : ℕ → ι := fun m => Nat.rec (ub (e 0) (j 0)) (fun m im => ub im (ub (e (m + 1))
    (j (m + 1)))) m
  have hi0 : i 0 = ub (e 0) (j 0) := rfl
  have hisucc : ∀ m, i (m + 1) = ub (i m) (ub (e (m + 1)) (j (m + 1))) := fun _ => rfl
  have hei : ∀ m, e m ≤ i m := fun m => by
    cases m with
    | zero => exact hi0 ▸ hub₁ _ _
    | succ m => exact (hisucc m).symm ▸ (hub₁ _ _).trans (hub₂ _ _)
  have hji : ∀ m, j m ≤ i m := fun m => by
    cases m with
    | zero => exact hi0 ▸ hub₂ _ _
    | succ m => exact (hisucc m).symm ▸ (hub₂ _ _).trans (hub₂ _ _)
  have hmono : Monotone i := monotone_nat_of_le_succ fun m => (hisucc m).symm ▸ hub₁ _ _
  refine ⟨i, hmono, hji, fun z => le_antisymm ?_ (le_iInf fun m => iInf_le _ _)⟩
  -- `infₘ u_{iₘ}` is a lower bound of the countable subfamily
  have hlb : (fun z => ⨅ m, u (i m) z) ∈ lowerBounds 𝓕 := by
    intro f hf z
    obtain ⟨m, hm⟩ : idx ⟨f, hf⟩ ∈ range e := he ▸ mem_insert_of_mem _ (mem_range_self _)
    calc ⨅ m, u (i m) z ≤ u (i m) z := iInf_le _ m
      _ ≤ u (e m) z := hanti z (hei m)
      _ = f z := by rw [hm, hidx ⟨f, hf⟩]
  have := hglb.2 hlb z
  simpa only [iInf_apply] using this

/-- A decreasing net from an approximation property: let `S` be a nonempty set of pairs
`(b, f)` (a rational label and a function), downward directed for the product order, such that
every `f` dominates `u` and `u` is the pointwise infimum of these `f`. Then `u` is the infimum of
a decreasing net indexed by `S` itself with the reversed product order; its labels decrease
too, and every member of `S` occurs in the net. -/
theorem exists_antitone_net_of_directed.{w} {K : Type w} (S : Set (ℚ × (K → EReal)))
    {u : K → EReal} (hne : S.Nonempty) (hdir : ∀ p ∈ S, ∀ q ∈ S, ∃ r ∈ S, r ≤ p ∧ r ≤ q)
    (hlow : ∀ p ∈ S, ∀ x, u x ≤ p.2 x) (hpt : ∀ x c, u x < c → ∃ p ∈ S, p.2 x < c) :
    ∃ (ι : Type w) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (a : ι → ℚ)
      (φ : ι → K → EReal), (∀ i, (a i, φ i) ∈ S) ∧ (∀ p ∈ S, ∃ i, (a i, φ i) = p) ∧
        Antitone a ∧ (∀ x, Antitone fun i => φ i x) ∧ ∀ x, u x = ⨅ i, φ i x := by
  -- the index set is `S` with the reversed product order
  have hle : ∀ p q : (↥S)ᵒᵈ, p ≤ q ↔
      ((OrderDual.ofDual q : S) : ℚ × (K → EReal)) ≤ (OrderDual.ofDual p : S) :=
    fun _ _ => Iff.rfl
  have hdir' : IsDirected (↥S)ᵒᵈ (· ≤ ·) := ⟨fun p q => by
    obtain ⟨r, hr, hrp, hrq⟩ := hdir _ (OrderDual.ofDual p).2 _ (OrderDual.ofDual q).2
    exact ⟨OrderDual.toDual ⟨r, hr⟩, (hle _ _).2 hrp, (hle _ _).2 hrq⟩⟩
  have : Nonempty S := hne.to_subtype
  refine ⟨(↥S)ᵒᵈ, inferInstance, hdir', inferInstance,
    fun p => ((OrderDual.ofDual p : S) : ℚ × (K → EReal)).1,
    fun p => ((OrderDual.ofDual p : S) : ℚ × (K → EReal)).2, fun p => (OrderDual.ofDual p).2,
    fun p hp => ⟨OrderDual.toDual ⟨p, hp⟩, rfl⟩,
    fun p q hpq => ((hle p q).1 hpq).1, fun x p q hpq => ((hle p q).1 hpq).2 x, fun x => ?_⟩
  refine le_antisymm (le_iInf fun p => hlow _ (OrderDual.ofDual p).2 x)
    (le_of_forall_gt_imp_ge_of_dense fun c hc => ?_)
  obtain ⟨p, hp, hpc⟩ := hpt x c hc
  exact (iInf_le _ (OrderDual.toDual (⟨p, hp⟩ : S))).trans hpc.le

end Topological

namespace ProjBerk

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-! ### Auxiliary facts on `EReal` -/

/-- Multiplication by a positive real is strictly monotone on `EReal`. -/
theorem ereal_coe_mul_lt_coe_mul {c : ℝ} (hc : 0 < c) {x y : EReal} (hxy : x < y) :
    (c : EReal) * x < (c : EReal) * y := by
  induction x using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos hc, bot_lt_iff_ne_bot]
    exact ereal_coe_mul_ne_bot hc.le (bot_lt_iff_ne_bot.1 hxy)
  | coe r =>
    induction y using EReal.rec with
    | bot => exact absurd hxy (not_lt_bot)
    | coe s =>
      rw [← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_lt_coe_iff]
      exact mul_lt_mul_of_pos_left (EReal.coe_lt_coe_iff.1 hxy) hc
    | top =>
      rw [EReal.coe_mul_top_of_pos hc, ← EReal.coe_mul]
      exact EReal.coe_lt_top _
  | top => exact absurd hxy (not_top_lt)

theorem ereal_lt_add_coe {x : EReal} (hx : x ≠ ⊥) (hx' : x ≠ ⊤) {c : ℝ} (hc : 0 < c) :
    x < x + (c : EReal) := by
  lift x to ℝ using ⟨hx', hx⟩
  rw [← EReal.coe_add, EReal.coe_lt_coe_iff]
  linarith

/-! ### Operations on Fubini–Study functions (`lem:bj-fs-basic`) -/

variable {a b : ℚ} {φ : ProjBerk k n → EReal}

/-- `lem:bj-fs-basic`(1): `H^gf_ℚ(a) ⊆ H^gf_ℚ(b)` for `a ≤ b`. -/
theorem IsRatFS.mono_class (h : IsRatFS a φ) (hab : a ≤ b) : IsRatFS b φ := by
  have h' := h.add (isRatFS_const (k := k) (n := n) (sub_nonneg.2 hab) 0)
  rw [add_sub_cancel] at h'
  simpa only [Rat.cast_zero, EReal.coe_zero, add_zero] using h'

/-- `lem:bj-fs-basic`(1): `H_ℚ(a) ⊆ H_ℚ(b)` for `a ≤ b`. -/
theorem IsFiniteRatFS.mono_class (h : IsFiniteRatFS a φ) (hab : a ≤ b) : IsFiniteRatFS b φ :=
  ⟨h.1.mono_class hab, h.2⟩

/-- `lem:bj-fs-basic`(2): `c H^gf_ℝ(a) = H^gf_ℝ(c a)` for `c ∈ ℚ_{>0}`. -/
theorem isFS_smul_iff {c : ℚ} (hc : 0 < c) :
    IsFS (c * a) (fun v => ((c : ℝ) : EReal) * φ v) ↔ IsFS a φ := by
  refine ⟨fun h => ?_, fun h => h.smul hc⟩
  have h' := h.smul (inv_pos.2 hc)
  rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at h'
  convert h' using 2 with v
  rw [Rat.cast_inv, ereal_inv_mul_mul (by exact_mod_cast hc.ne')]

/-- `lem:bj-fs-basic`(2): `c H^gf_ℚ(a) = H^gf_ℚ(c a)` for `c ∈ ℚ_{>0}`. -/
theorem isRatFS_smul_iff {c : ℚ} (hc : 0 < c) :
    IsRatFS (c * a) (fun v => ((c : ℝ) : EReal) * φ v) ↔ IsRatFS a φ := by
  refine ⟨fun h => ?_, fun h => h.smul hc⟩
  have h' := h.smul (inv_pos.2 hc)
  rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at h'
  convert h' using 2 with v
  rw [Rat.cast_inv, ereal_inv_mul_mul (by exact_mod_cast hc.ne')]

/-- `lem:bj-fs-basic`(2): `c H_ℚ(a) = H_ℚ(c a)` for `c ∈ ℚ_{>0}`. -/
theorem isFiniteRatFS_smul_iff {c : ℚ} (hc : 0 < c) :
    IsFiniteRatFS (c * a) (fun v => ((c : ℝ) : EReal) * φ v) ↔ IsFiniteRatFS a φ := by
  refine ⟨fun h => ?_, fun h => h.smul hc⟩
  have h' := h.smul (inv_pos.2 hc)
  rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at h'
  convert h' using 2 with v
  rw [Rat.cast_inv, ereal_inv_mul_mul (by exact_mod_cast hc.ne')]

/-- `lem:bj-fs-basic`(3): `H^gf_ℚ(a)` is stable under addition of rational constants. -/
theorem IsRatFS.add_const (h : IsRatFS a φ) (c : ℚ) :
    IsRatFS a fun v => φ v + ((c : ℝ) : EReal) := by
  simpa only [add_zero] using h.add (isRatFS_const (k := k) (n := n) le_rfl c)

/-- `lem:bj-fs-basic`(3): `H_ℚ(a)` is stable under addition of rational constants. -/
theorem IsFiniteRatFS.add_const (h : IsFiniteRatFS a φ) (c : ℚ) :
    IsFiniteRatFS a fun v => φ v + ((c : ℝ) : EReal) :=
  ⟨h.1.add_const c, fun v => ereal_add_coe_ne_bot (h.2 v) _⟩

/-- `lem:bj-fs-basic`(3), truncation: `max(φ, c)` is a finite rational FS function for
`φ ∈ H^gf_ℚ(a)` and `c ∈ ℚ`. -/
theorem IsRatFS.max_const (h : IsRatFS a φ) (c : ℚ) :
    IsFiniteRatFS a fun v => Max.max (φ v) ((c : ℝ) : EReal) :=
  ⟨h.max (isRatFS_const h.isFS.nonneg c), fun _ =>
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _)⟩

/-! #### Changing the weights -/

namespace FSData

variable (D : FSData k n a)

open Classical in
/-- The FS data `(m, d, (s_j, r(λ_j))_j)` obtained by changing the weights `λ_j` through a map
`r : ℝ → ℝ`. -/
def reweight (r : ℝ → ℝ) : FSData k n a where
  m := D.m
  m_pos := D.m_pos
  deg := D.deg
  deg_eq := D.deg_eq
  terms := D.terms.image fun t => (t.1, r t.2)
  isHomogeneous := by
    intro t ht
    obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.1 ht
    exact D.isHomogeneous t₀ h₀
  exists_ne_zero := by
    obtain ⟨t, ht, hne⟩ := D.exists_ne_zero
    exact ⟨_, Finset.mem_image_of_mem _ ht, hne⟩

theorem eval_reweight (r : ℝ → ℝ) (v : ProjBerk k n) :
    (D.reweight r).eval v =
      (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup fun t => termVal (t.1, r t.2) v := by
  classical
  rw [eval_def]
  congr 1
  change (D.terms.image fun t => (t.1, r t.2)).sup _ = _
  rw [Finset.sup_image]
  rfl

/-- Rational new weights give rational FS data. -/
theorem isRational_reweight {r : ℝ → ℝ} (hr : ∀ t ∈ D.terms, ∃ q : ℚ, r t.2 = q) :
    (D.reweight r).IsRational := by
  classical
  intro t ht
  obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.1 ht
  exact hr t₀ h₀

theorem eval_reweight_mono {r r' : ℝ → ℝ} (hr : ∀ t ∈ D.terms, r t.2 ≤ r' t.2)
    (v : ProjBerk k n) : (D.reweight r).eval v ≤ (D.reweight r').eval v := by
  rw [eval_reweight, eval_reweight]
  refine ereal_coe_mul_monotone D.inv_m_pos.le (Finset.sup_mono_fun fun t ht => ?_)
  rw [termVal_def, termVal_def]
  exact add_le_add_right (EReal.coe_le_coe_iff.2 (hr t ht)) _

/-- Shifting all weights by `m c` adds `c` to the FS function. -/
theorem eval_reweight_add (c : ℝ) (v : ProjBerk k n) :
    (D.reweight fun x => x + D.m * c).eval v = D.eval v + (c : EReal) := by
  have hsup : (D.terms.sup fun t => termVal (t.1, t.2 + D.m * c) v) =
      (D.terms.sup fun t => termVal t v) + ((D.m * c : ℝ) : EReal) := by
    rw [Finset.apply_sup_eq_sup_comp_of_linearOrder (s := D.terms)
      (fun x : EReal => x + ((D.m * c : ℝ) : EReal)) (fun _ _ h => add_le_add_left h _)
      (EReal.bot_add _)]
    refine Finset.sup_congr rfl fun t _ => ?_
    simp only [Function.comp_apply, termVal_def, EReal.coe_add, add_assoc]
  rw [eval_reweight, hsup, eval_def, ereal_coe_mul_add D.inv_m_pos.le, ← EReal.coe_mul,
    ← mul_assoc, inv_mul_cancel₀ D.m_ne_zero, one_mul]

theorem le_eval_reweight {r : ℝ → ℝ} {c : ℝ} (hr : ∀ t ∈ D.terms, t.2 + D.m * c ≤ r t.2)
    (v : ProjBerk k n) : D.eval v + (c : EReal) ≤ (D.reweight r).eval v := by
  rw [← eval_reweight_add]
  exact D.eval_reweight_mono hr v

theorem eval_reweight_le {r : ℝ → ℝ} {c : ℝ} (hr : ∀ t ∈ D.terms, r t.2 ≤ t.2 + D.m * c)
    (v : ProjBerk k n) : (D.reweight r).eval v ≤ D.eval v + (c : EReal) := by
  rw [← eval_reweight_add]
  exact D.eval_reweight_mono hr v

end FSData

/-- `lem:bj-fs-basic`(4): every real FS function `φ ∈ H^gf_ℝ(a)` is the pointwise limit (=
infimum) of a decreasing sequence `ψ_N ∈ H_ℚ(a)` of finite rational FS functions, with
`φ < ψ_N` everywhere: `ψ_N = max(m⁻¹ max_j (log|s_j| + q_j^{(N)}), -N)` with rationals
`q_j^{(N)} ∈ (λ_j + m/(N+2), λ_j + m/(N+1))`. -/
theorem IsFS.exists_antitone_finiteRatFS (h : IsFS a φ) :
    ∃ ψ : ℕ → ProjBerk k n → EReal, (∀ N, IsFiniteRatFS a (ψ N)) ∧
      (∀ v, Antitone fun N => ψ N v) ∧ (∀ N v, φ v < ψ N v) ∧ ∀ v, φ v = ⨅ N, ψ N v := by
  obtain ⟨D, rfl⟩ := h
  have hm : (0 : ℝ) < D.m := by exact_mod_cast D.m_pos
  have hδ : ∀ N : ℕ, (1 : ℝ) / ((N : ℝ) + 2) < 1 / ((N : ℝ) + 1) := fun N =>
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  choose q hq using fun (N : ℕ) (x : ℝ) => exists_rat_btwn
    (show x + D.m * (1 / ((N : ℝ) + 2)) < x + D.m * (1 / ((N : ℝ) + 1)) by
      have := mul_lt_mul_of_pos_left (hδ N) hm
      linarith)
  set E : ℕ → FSData k n a := fun N => D.reweight fun x => (q N x : ℝ) with hE
  have hlow : ∀ (N : ℕ) v, D.eval v + ((1 / ((N : ℝ) + 2) : ℝ) : EReal) ≤ (E N).eval v :=
    fun N v => D.le_eval_reweight (fun t _ => (hq N t.2).1.le) v
  have hup : ∀ (N : ℕ) v, (E N).eval v ≤ D.eval v + ((1 / ((N : ℝ) + 1) : ℝ) : EReal) :=
    fun N v => D.eval_reweight_le (fun t _ => (hq N t.2).2.le) v
  have hrat : ∀ N, (E N).IsRational := fun N =>
    D.isRational_reweight fun t _ => ⟨q N t.2, rfl⟩
  have hD := D.eval_ne_top
  refine ⟨fun N v => Max.max ((E N).eval v) (((-(N : ℚ) : ℚ) : ℝ) : EReal),
    fun N => IsRatFS.max_const ⟨E N, hrat N, rfl⟩ _, fun v => ?_, fun N v => ?_, fun v => ?_⟩
  · refine antitone_nat_of_succ_le fun N => max_le_max ?_ ?_
    · refine (hup (N + 1) v).trans ((le_of_eq ?_).trans (hlow N v))
      push_cast
      ring_nf
    · exact EReal.coe_le_coe_iff.2 (by push_cast; linarith)
  · by_cases hv : D.eval v = ⊥
    · rw [hv]
      exact lt_of_lt_of_le (bot_lt_iff_ne_bot.2 (EReal.coe_ne_bot _)) (le_max_right _ _)
    · exact (ereal_lt_add_coe hv (hD v) (by positivity)).trans_le
        ((hlow N v).trans (le_max_left _ _))
  · refine le_antisymm (le_iInf fun N => ?_) (le_of_forall_gt_imp_ge_of_dense fun c hc => ?_)
    · by_cases hv : D.eval v = ⊥
      · rw [hv]; exact bot_le
      · exact (ereal_lt_add_coe hv (hD v) (by positivity)).le.trans
          ((hlow N v).trans (le_max_left _ _))
    · obtain ⟨s, hs₁, hs₂⟩ := EReal.lt_iff_exists_real_btwn.1 hc
      -- choose `N` with `D.eval v + 1/(N+1) ≤ s` and `-N ≤ s`
      obtain ⟨N₁, hN₁⟩ : ∃ N : ℕ, D.eval v + ((1 / ((N : ℝ) + 1) : ℝ) : EReal) ≤ s := by
        by_cases hv : D.eval v = ⊥
        · exact ⟨0, by rw [hv, EReal.bot_add]; exact bot_le⟩
        · lift D.eval v to ℝ using ⟨hD v, hv⟩ with r hr
          have hrs : r < s := EReal.coe_lt_coe_iff.1 hs₁
          obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.2 hrs)
          exact ⟨N, by rw [← EReal.coe_add, EReal.coe_le_coe_iff]; linarith⟩
      obtain ⟨N₂, hN₂⟩ := exists_nat_ge (-s)
      set N := Max.max N₁ N₂
      refine (iInf_le _ N).trans (le_trans (max_le ?_ ?_) hs₂.le)
      · refine (hup N v).trans ((add_le_add_right (EReal.coe_le_coe_iff.2 ?_) _).trans hN₁)
        exact one_div_le_one_div_of_le (by positivity)
          (by have : (N₁ : ℝ) ≤ N := by exact_mod_cast le_max_left N₁ N₂
              linarith)
      · refine EReal.coe_le_coe_iff.2 ?_
        have : (N₂ : ℝ) ≤ N := by exact_mod_cast le_max_right N₁ N₂
        push_cast
        linarith

/-! ### Rational approximants of `θ`-psh functions -/

variable {θ : ℝ} {u : ProjBerk k n → EReal}

/-- **Rational approximants below a continuous majorant.** If `u ∈ PSH(θ)`, `b > θ` is
rational and `g` is a continuous function with `u < g`, there is `f ∈ H_ℚ(b)` with
`u < f ≤ g`. This is Dini's argument, applied to an approximating net of `u` and then to the
rational approximants of `lem:bj-fs-basic`(4). -/
theorem IsPSH.exists_finiteRatFS_lt_le (h : IsPSH θ u) {b : ℚ} (hb : θ < b)
    {g : ProjBerk k n → EReal} (hg : Continuous g) (hug : ∀ v, u v < g v) :
    ∃ f, IsFiniteRatFS b f ∧ (∀ v, u v < f v) ∧ ∀ v, f v ≤ g v := by
  obtain ⟨-, -, ι, _, _, _, a, φ, hφ, ha, hanti, hu⟩ := h
  obtain ⟨i₁, hi₁⟩ := exists_forall_lt_of_antitone
    (fun i => (hφ i).continuous.upperSemicontinuous) hanti hg fun v => by
      have := hug v
      rw [hu v] at this
      exact iInf_lt_iff.1 this
  obtain ⟨i, hi, hab⟩ := ((eventually_ge_atTop i₁).and (ha.eventually (gt_mem_nhds hb))).exists
  obtain ⟨ψ, hψ, hψanti, hψgt, hψinf⟩ := (hφ i).exists_antitone_finiteRatFS
  obtain ⟨N, hN⟩ := exists_forall_lt_of_antitone
    (fun N => (hψ N).isFS.continuous.upperSemicontinuous) hψanti hg fun v => by
      have : φ i v < g v := (hanti v hi).trans_lt (hi₁ v)
      rw [hψinf v] at this
      exact iInf_lt_iff.1 this
  refine ⟨ψ N, (hψ N).mono_class (by exact_mod_cast hab.le), fun v => ?_, fun v => (hN v).le⟩
  calc u v ≤ φ i v := by rw [hu v]; exact iInf_le _ i
    _ < ψ N v := hψgt N v

/-- **Rational approximants at a point.** If `u ∈ PSH(θ)`, `b > θ` is rational and
`u(v) < c`, there is `f ∈ H_ℚ(b)` with `u < f` and `f(v) < c`. -/
theorem IsPSH.exists_finiteRatFS_lt_apply_lt (h : IsPSH θ u) {b : ℚ} (hb : θ < b)
    {v : ProjBerk k n} {c : EReal} (hc : u v < c) :
    ∃ f, IsFiniteRatFS b f ∧ (∀ w, u w < f w) ∧ f v < c := by
  obtain ⟨-, -, ι, _, _, _, a, φ, hφ, ha, hanti, hu⟩ := h
  rw [hu v] at hc
  obtain ⟨i₀, hi₀⟩ := iInf_lt_iff.1 hc
  obtain ⟨i, hi, hab⟩ := ((eventually_ge_atTop i₀).and (ha.eventually (gt_mem_nhds hb))).exists
  obtain ⟨ψ, hψ, -, hψgt, hψinf⟩ := (hφ i).exists_antitone_finiteRatFS
  have : φ i v < c := (hanti v hi).trans_lt hi₀
  rw [hψinf v] at this
  obtain ⟨N, hN⟩ := iInf_lt_iff.1 this
  refine ⟨ψ N, (hψ N).mono_class (by exact_mod_cast hab.le), fun w => ?_, hN⟩
  calc u w ≤ φ i w := by rw [hu w]; exact iInf_le _ i
    _ < ψ N w := hψgt N w

/-- Rational approximants of fixed class `a ∈ ℚ_{>0}` below a continuous majorant, for
`u ∈ PSH(a)` with `u < 0`: the scaling step of `thm:bj-regularization`(2). For `τ ∈ ℚ_{>1}`
close to `1` (found by Dini's argument), `u < τ min(g, 0)`; an approximant `f ∈ H_ℚ(τ a)` with
`u < f ≤ τ min(g, 0)` gives `τ⁻¹ f ∈ H_ℚ(a)` with `u ≤ τ⁻¹ u < τ⁻¹ f ≤ g`. -/
theorem IsPSH.exists_finiteRatFS_lt_le_of_neg {a : ℚ} (ha : 0 < a) (h : IsPSH (a : ℝ) u)
    (hu0 : ∀ v, u v < 0) {g : ProjBerk k n → EReal} (hg : Continuous g)
    (hug : ∀ v, u v < g v) : ∃ f, IsFiniteRatFS a f ∧ (∀ v, u v < f v) ∧ ∀ v, f v ≤ g v := by
  set g₀ : ProjBerk k n → EReal := fun v => min (g v) 0 with hg₀_def
  have hg₀ : Continuous g₀ := hg.min continuous_const
  have hug₀ : ∀ v, u v < g₀ v := fun v => lt_min (hug v) (hu0 v)
  -- the scaling factors `σₘ = τₘ⁻¹ = (m + 1) / (m + 2) ↑ 1`
  set σ : ℕ → ℚ := fun m => (m + 1) / (m + 2) with hσ_def
  have hσpos : ∀ m, (0 : ℝ) < σ m := fun m => by simp only [hσ_def]; push_cast; positivity
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
  -- Dini: `σₘ u < g₀` everywhere for some `m`
  obtain ⟨m, hm⟩ := exists_forall_lt_of_antitone (f := fun m v => ((σ m : ℝ) : EReal) * u v)
    (fun m => (continuous_ereal_coe_mul (hσpos m).ne').comp_upperSemicontinuous
      h.upperSemicontinuous (ereal_coe_mul_monotone (hσpos m).le))
    (fun v _ _ hmm' => ereal_coe_mul_le_of_nonpos (hσpos _) (hσmono hmm') (hu0 v).le) hg₀
    fun v => by
      have := tendsto_coe_mul_ereal hσlim one_pos hσpos (h.ne_top v)
      rw [EReal.coe_one, one_mul] at this
      exact (this.eventually (gt_mem_nhds (hug₀ v))).exists
  -- the class `τ a` with `τ = σₘ⁻¹ > 1`
  have hσq : (0 : ℚ) < σ m := by exact_mod_cast hσpos m
  have hτa : (a : ℝ) < (((σ m)⁻¹ * a : ℚ) : ℝ) := by
    push_cast
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    rw [lt_mul_iff_one_lt_left ha']
    exact one_lt_inv_iff₀.2 ⟨hσpos m, hσlt m⟩
  obtain ⟨f, hf, huf, hfg⟩ := h.exists_finiteRatFS_lt_le hτa
    (g := fun v => (((σ m)⁻¹ : ℝ) : EReal) * g₀ v)
    ((continuous_ereal_coe_mul (inv_ne_zero (hσpos m).ne')).comp hg₀) fun v => by
      have := ereal_coe_mul_lt_coe_mul (inv_pos.2 (hσpos m)) (hm v)
      rwa [ereal_inv_mul_mul (hσpos m).ne'] at this
  refine ⟨fun v => ((σ m : ℝ) : EReal) * f v, ?_, fun v => ?_, fun v => ?_⟩
  · have := hf.smul hσq
    rwa [← mul_assoc, mul_inv_cancel₀ hσq.ne', one_mul] at this
  · calc u v ≤ ((σ m : ℝ) : EReal) * u v := by
          simpa only [EReal.coe_one, one_mul] using
            ereal_coe_mul_le_of_nonpos (hσpos m) (hσlt m).le (hu0 v).le
      _ < ((σ m : ℝ) : EReal) * f v := ereal_coe_mul_lt_coe_mul (hσpos m) (huf v)
  · calc ((σ m : ℝ) : EReal) * f v ≤ ((σ m : ℝ) : EReal) * ((((σ m)⁻¹ : ℝ) : EReal) * g₀ v) :=
          ereal_coe_mul_monotone (hσpos m).le (hfg v)
      _ = g₀ v := ereal_coe_mul_inv_mul (hσpos m).ne' _
      _ ≤ g v := min_le_left _ _

/-- Rational approximants of fixed class `a ∈ ℚ_{>0}` below a continuous majorant: for
`u ∈ PSH(a)` and continuous `g > u` there is `f ∈ H_ℚ(a)` with `u < f ≤ g`. -/
theorem IsPSH.exists_finiteRatFS_lt_le_of_rat {a : ℚ} (ha : 0 < a) (h : IsPSH (a : ℝ) u)
    {g : ProjBerk k n → EReal} (hg : Continuous g) (hug : ∀ v, u v < g v) :
    ∃ f, IsFiniteRatFS a f ∧ (∀ v, u v < f v) ∧ ∀ v, f v ≤ g v := by
  -- normalize `u < 0` by subtracting a rational constant `M > sup u = u(v_triv)`
  obtain ⟨M, hM⟩ := exists_rat_gt (u triv).toReal
  have hu' := h.add_const (-(M : ℝ))
  obtain ⟨f, hf, huf, hfg⟩ := hu'.exists_finiteRatFS_lt_le_of_neg ha
    (fun v => by
      have h₁ : u v < (M : ℝ) :=
        (h.le_toReal_apply_triv v).trans_lt (EReal.coe_lt_coe_iff.2 hM)
      have := EReal.add_lt_add_right_coe h₁ (-(M : ℝ))
      rwa [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at this)
    (g := fun v => g v + ((-(M : ℝ) : ℝ) : EReal)) (continuous_ereal_add_coe _ |>.comp hg)
    fun v => EReal.add_lt_add_right_coe (hug v) _
  refine ⟨fun v => f v + ((M : ℝ) : EReal), hf.add_const M, fun v => ?_, fun v => ?_⟩
  · have := EReal.add_lt_add_right_coe (huf v) (M : ℝ)
    rwa [ereal_add_neg_add_coe] at this
  · have := add_le_add_left (hfg v) ((M : ℝ) : EReal)
    rwa [ereal_add_neg_add_coe] at this

/-- Rational approximants of fixed class `a ∈ ℚ_{>0}` at a point: for `u ∈ PSH(a)` and
`u(v) < c` there is `f ∈ H_ℚ(a)` with `u < f` and `f(v) < c`. -/
theorem IsPSH.exists_finiteRatFS_lt_apply_lt_of_rat {a : ℚ} (ha : 0 < a) (h : IsPSH (a : ℝ) u)
    {v : ProjBerk k n} {c : EReal} (hc : u v < c) :
    ∃ f, IsFiniteRatFS a f ∧ (∀ w, u w < f w) ∧ f v < c := by
  obtain ⟨f₀, hf₀, huf₀, hf₀c⟩ :=
    h.exists_finiteRatFS_lt_apply_lt (b := a + 1) (by push_cast; linarith) hc
  obtain ⟨f, hf, huf, hff₀⟩ := h.exists_finiteRatFS_lt_le_of_rat ha hf₀.isFS.continuous huf₀
  exact ⟨f, hf, huf, (hff₀ v).trans_lt hf₀c⟩

/-! ### Regularization (`thm:bj-regularization`) -/

/-- **Regularization** (BJ22 pshample, `thm:bj-regularization`(1)): every `u ∈ PSH(θ)`
is the pointwise limit (= infimum) of a decreasing net `u_α ∈ H_ℚ(a_α)` of finite-valued
rational FS functions whose rational classes `a_α > θ` decrease to `θ`; moreover `u < u_α`. -/
theorem IsPSH.exists_finiteRatFS_net (h : IsPSH θ u) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (a : ι → ℚ)
      (φ : ι → ProjBerk k n → EReal), (∀ i, IsFiniteRatFS (a i) (φ i)) ∧ (∀ i, θ < a i) ∧
        Antitone a ∧ Tendsto (fun i => (a i : ℝ)) atTop (𝓝 θ) ∧
          (∀ v, Antitone fun i => φ i v) ∧ (∀ i v, u v < φ i v) ∧ ∀ v, u v = ⨅ i, φ i v := by
  set S : Set (ℚ × (ProjBerk k n → EReal)) :=
    {p | θ < p.1 ∧ IsFiniteRatFS p.1 p.2 ∧ ∀ v, u v < p.2 v} with hS
  -- every rational `b > θ` occurs as a class in `S`
  have hex : ∀ b : ℚ, θ < b → ∃ f, (b, f) ∈ S := fun b hb => by
    obtain ⟨f, hf, huf, -⟩ := h.exists_finiteRatFS_lt_le hb (g := fun _ => ⊤)
      continuous_const h.lt_top
    exact ⟨f, hb, hf, huf⟩
  obtain ⟨ι, _, _, _, a, φ, hmem, hsurj, hanti_a, hanti, hinf⟩ :=
    exists_antitone_net_of_directed S (u := u) (by
      obtain ⟨b, hb⟩ := exists_rat_gt θ
      obtain ⟨f, hf⟩ := hex b hb
      exact ⟨_, hf⟩)
      (fun p hp q hq => by
        obtain ⟨f, hf, huf, hfg⟩ := h.exists_finiteRatFS_lt_le (b := min p.1 q.1)
          (by rw [Rat.cast_min]; exact lt_min hp.1 hq.1)
          (g := fun v => min (p.2 v) (q.2 v)) (hp.2.1.isFS.continuous.min hq.2.1.isFS.continuous)
          fun v => lt_min (hp.2.2 v) (hq.2.2 v)
        refine ⟨(min p.1 q.1, f), ⟨?_, hf, huf⟩, ⟨min_le_left _ _, fun v => (hfg v).trans
          (min_le_left _ _)⟩, ⟨min_le_right _ _, fun v => (hfg v).trans (min_le_right _ _)⟩⟩
        rw [Rat.cast_min]; exact lt_min hp.1 hq.1)
      (fun p hp v => (hp.2.2 v).le)
      fun v c hc => by
        obtain ⟨b, hb⟩ := exists_rat_gt θ
        obtain ⟨f, hf, huf, hfc⟩ := h.exists_finiteRatFS_lt_apply_lt hb hc
        exact ⟨(b, f), ⟨hb, hf, huf⟩, hfc⟩
  refine ⟨ι, inferInstance, inferInstance, inferInstance, a, φ, fun i => (hmem i).2.1,
    fun i => (hmem i).1, hanti_a, ?_, hanti, fun i => (hmem i).2.2, hinf⟩
  refine tendsto_order.2 ⟨fun b' hb' => Eventually.of_forall fun i => hb'.trans (hmem i).1,
    fun b' hb' => ?_⟩
  obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn hb'
  obtain ⟨f, hf⟩ := hex b hb₁
  obtain ⟨i₀, hi₀⟩ := hsurj _ hf
  refine eventually_atTop.2 ⟨i₀, fun i hi => lt_of_le_of_lt ?_ hb₂⟩
  have : a i ≤ a i₀ := hanti_a hi
  rw [Prod.mk.injEq] at hi₀
  rw [← hi₀.1]
  exact_mod_cast this

/-- **Regularization in a fixed class** (BJ22 pshample, `thm:bj-regularization`(2)): if
`a ∈ ℚ_{>0}`, every `u ∈ PSH(a)` is the pointwise limit (= infimum) of a decreasing net in
`H_ℚ(a)`, all of whose members are `> u`. -/
theorem IsPSH.exists_finiteRatFS_net_of_rat {a : ℚ} (ha : 0 < a) (h : IsPSH (a : ℝ) u) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (φ : ι → ProjBerk k n → EReal), (∀ i, IsFiniteRatFS a (φ i)) ∧
        (∀ v, Antitone fun i => φ i v) ∧ (∀ i v, u v < φ i v) ∧ ∀ v, u v = ⨅ i, φ i v := by
  set S : Set (ℚ × (ProjBerk k n → EReal)) :=
    {p | p.1 = a ∧ IsFiniteRatFS a p.2 ∧ ∀ v, u v < p.2 v} with hS
  obtain ⟨ι, _, _, _, a', φ, hmem, -, -, hanti, hinf⟩ :=
    exists_antitone_net_of_directed S (u := u) (by
      obtain ⟨f, hf, huf, -⟩ := h.exists_finiteRatFS_lt_le_of_rat ha (g := fun _ => ⊤)
        continuous_const h.lt_top
      exact ⟨(a, f), rfl, hf, huf⟩)
      (fun p hp q hq => by
        obtain ⟨f, hf, huf, hfg⟩ := h.exists_finiteRatFS_lt_le_of_rat ha
          (g := fun v => min (p.2 v) (q.2 v)) (hp.2.1.isFS.continuous.min hq.2.1.isFS.continuous)
          fun v => lt_min (hp.2.2 v) (hq.2.2 v)
        exact ⟨(a, f), ⟨rfl, hf, huf⟩, ⟨hp.1.ge, fun v => (hfg v).trans (min_le_left _ _)⟩,
          ⟨hq.1.ge, fun v => (hfg v).trans (min_le_right _ _)⟩⟩)
      (fun p hp v => (hp.2.2 v).le)
      fun v c hc => by
        obtain ⟨f, hf, huf, hfc⟩ := h.exists_finiteRatFS_lt_apply_lt_of_rat ha hc
        exact ⟨(a, f), ⟨rfl, hf, huf⟩, hfc⟩
  exact ⟨ι, inferInstance, inferInstance, inferInstance, φ, fun i => (hmem i).2.1, hanti,
    fun i => (hmem i).2.2, hinf⟩

/-! ### Countable regularization (`cor:bj-countable-regularization`) -/

/-- For countable `k`, `(ℙⁿ)^an` is second countable: it is a subspace of `Berk k k[x₀, …, xₙ]`,
which embeds in the countable product `ℝ_{≥0}^{k[x₀, …, xₙ]}`. -/
instance instSecondCountableTopology [Countable k] : SecondCountableTopology (ProjBerk k n) :=
  isEmbedding_val.secondCountableTopology

/-- **Countable regularization** (BJ22 countreg for countable `k`,
`cor:bj-countable-regularization` with `thm:bj-regularization`(1)): if `k` is countable, every
`u ∈ PSH(θ)` is the pointwise limit (= infimum) of a decreasing sequence `u_m ∈ H_ℚ(a_m)` of
finite-valued rational FS functions whose rational classes `a_m > θ` decrease to `θ`; moreover
`u < u_m`. -/
theorem IsPSH.exists_finiteRatFS_seq [Countable k] (h : IsPSH θ u) :
    ∃ (a : ℕ → ℚ) (φ : ℕ → ProjBerk k n → EReal), (∀ m, IsFiniteRatFS (a m) (φ m)) ∧
      (∀ m, θ < a m) ∧ Antitone a ∧ Tendsto (fun m => (a m : ℝ)) atTop (𝓝 θ) ∧
        (∀ v, Antitone fun m => φ m v) ∧ (∀ m v, u v < φ m v) ∧ ∀ v, u v = ⨅ m, φ m v := by
  obtain ⟨ι, _, _, _, a, φ, hφ, hθa, hanti_a, ha, hanti, hlt, hinf⟩ := h.exists_finiteRatFS_net
  have hj : ∀ m : ℕ, ∃ j : ι, ∀ i ≥ j, (a i : ℝ) < θ + 1 / ((m : ℝ) + 1) := fun m =>
    eventually_atTop.1 (ha.eventually (gt_mem_nhds (lt_add_of_pos_right θ (by positivity))))
  choose j hj using hj
  obtain ⟨i, hmono, hji, hiInf⟩ := exists_monotone_iInf_eq
    (fun i => (hφ i).isFS.continuous.upperSemicontinuous) hanti j
  refine ⟨fun m => a (i m), fun m => φ (i m), fun m => hφ (i m), fun m => hθa (i m),
    hanti_a.comp_monotone hmono, ?_, fun v m m' hmm' => hanti v (hmono hmm'),
    fun m => hlt (i m), fun v => by rw [hiInf v, hinf v]⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun m => (hθa (i m)).le) fun m => (hj m (i m) (hji m)).le
  simpa only [add_zero] using
    tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- **Countable regularization in a fixed class** (BJ22 countreg for countable `k`,
`cor:bj-countable-regularization` with `thm:bj-regularization`(2)): if `k` is countable and
`a ∈ ℚ_{>0}`, every `u ∈ PSH(a)` is the pointwise limit (= infimum) of a decreasing sequence in
`H_ℚ(a)`, all of whose terms are `> u`. -/
theorem IsPSH.exists_finiteRatFS_seq_of_rat [Countable k] {a : ℚ} (ha : 0 < a)
    (h : IsPSH (a : ℝ) u) :
    ∃ φ : ℕ → ProjBerk k n → EReal, (∀ m, IsFiniteRatFS a (φ m)) ∧
      (∀ v, Antitone fun m => φ m v) ∧ (∀ m v, u v < φ m v) ∧ ∀ v, u v = ⨅ m, φ m v := by
  obtain ⟨ι, _, _, _, φ, hφ, hanti, hlt, hinf⟩ := h.exists_finiteRatFS_net_of_rat ha
  obtain ⟨i, hmono, -, hiInf⟩ := exists_monotone_iInf_eq
    (fun i => (hφ i).isFS.continuous.upperSemicontinuous) hanti
    fun _ => Classical.arbitrary ι
  exact ⟨fun m => φ (i m), fun m => hφ (i m), fun v m m' hmm' => hanti v (hmono hmm'),
    fun m => hlt (i m), fun v => by rw [hiInf v, hinf v]⟩

end ProjBerk

end EnvelopeProperty
