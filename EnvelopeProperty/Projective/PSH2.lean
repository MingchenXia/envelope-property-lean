/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.PSH

/-!
# Decreasing limits of decreasing limits, and the property PSH2 on `(ℙⁿ)^an`

This file formalizes Boucksom–Jonsson, *Global pluripotential theory over a trivially valued
field* (BJ22), Lemma 4.6 (PSH) and the property (PSH2) of Theorem 4.5 (psh12) for the
model `ProjBerk k n` of `(ℙⁿ)^an` (`EnvelopeProperty.Projective.Basic`); (PSH2) is item (1) of
Fang–Han–Xia, *The envelope property for unibranch projective varieties*, `prop:BJ-package`.

## The topological lemma (PSH)

Let `K` be a compact space, `S` a set with families `F_s` (`s ∈ S`) of continuous functions
`K → [-∞, +∞)` stable under addition of real constants, and `ρ : S → T` a map to a metrizable
space. For `t ∈ T`, `F̃_t` is the set of pointwise limits of decreasing nets `f_i ∈ F_{s_i}` with
`ρ(s_i) → t` (`EnvelopeProperty.IsDecrNetLimit`). BJ22 states that `F̃̃_t = F̃_t`: a decreasing
limit of `g_i ∈ F̃_{t_i}` with `t_i → t` lies in `F̃_t`. The proof considers the directed set of
triples `(i, j, ε)` (`equ:directed`), ordered by `i ≥ i'`, `f_{i,j} + ε ≤ f_{i',j'} + ε'` on `K`
and `d(t_{i,j}, t_i) + ε ≤ d(t_{i',j'}, t_{i'}) + ε'`, directedness coming from Dini's argument on
the compact `K`.

**Deviation from BJ22.** As written, the directedness argument fails at points where the
approximants take the value `-∞`: if `f_{i₁,j₁}(x) = -∞` while every `f_{i₃,j}(x)` is finite, no
triple `(i₃, j, ε)` dominates `(i₁, j₁, ε₁)` (the strict inequality `g_{i₃} + ε₃ < f_{i₁,j₁} + ε₁`
claimed in `equ:i3i1` fails at `x`). We therefore prove

* `EnvelopeProperty.IsDecrNetLimit.of_antitone_of_finite`: BJ22's argument, verbatim, when all
  functions in the families are real valued (then `equ:i3i1` holds); and
* `EnvelopeProperty.IsDecrNetLimit.of_antitone` (PSH): the general statement under the
  additional hypothesis that the families are stable under `f ↦ max(f, c)` for real `c`, which
  reduces it to the finite case by truncation (`IsDecrNetLimit.truncate`). In BJ22's application
  (the families `𝓗^gf_ℝ(L)`) this hypothesis holds when `L` is semiample, in particular on `ℙⁿ`,
  where every effective `L = O(a)` is semiample: there it is `ProjBerk.IsFS.max` with
  `ProjBerk.isFS_const`. It fails when `L` is effective but not semiample: `max(φ, c)` is finite
  valued, and a finite-valued member of `𝓗^gf_ℝ(L)` lies in `𝓗_ℝ(L) = 𝓗^gf_ℝ(L) ∩ C⁰`, which is
  nonempty only for semiample `L` (BJ22 (2.12), `equ:cHnempty`; BJ22 FS says nothing about
  maxima with constants). So this route does not give PSH2 at psef classes outside the nef cone
  (ERRATA EP-1.1, blueprint `rmk:gl-nonnef`).

## PSH2 on `(ℙⁿ)^an`

`ProjBerk.isPSH_iff_isDecrNetLimit` identifies `θ`-psh functions with the generically finite usc
functions in `F̃_θ` for `S = ℚ` (the classes `O(a)`), `F_a = 𝓗^gf_ℝ(O(a))` and `ρ(a) = a ∈ ℝ`, and
PSH gives

* `ProjBerk.isPSH_of_antitone` (**PSH2**): if `uᵢ ∈ PSH(θᵢ)` is a decreasing net, `θᵢ → θ`, and
  the limit `u = infᵢ uᵢ` is generically finite (`u ≢ -∞`), then `u ∈ PSH(θ)`;
* `ProjBerk.isPSH_of_tendsto_of_antitone` (limit form) and `ProjBerk.isPSH_of_antitone_seq`
  (sequences).
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

/-! ### Auxiliary facts -/

/-- Adding a real constant commutes with infima in `EReal`. -/
theorem ereal_iInf_add_coe {ι : Sort*} (a : ι → EReal) (c : ℝ) :
    (⨅ i, a i) + (c : EReal) = ⨅ i, (a i + (c : EReal)) :=
  Monotone.map_iInf_of_continuousAt (f := fun x : EReal => x + (c : EReal))
    (ProjBerk.continuous_ereal_add_coe c).continuousAt (fun _ _ h => add_le_add_left h _)
    (EReal.top_add_coe c)

/-- `x ≤ x + ε` for `ε ≥ 0`. -/
theorem ereal_le_add_coe {ε : ℝ} (hε : 0 ≤ ε) (x : EReal) : x ≤ x + (ε : EReal) :=
  le_add_of_nonneg_right (by exact_mod_cast hε)

/-- The product of two directed preorders is directed. -/
theorem isDirected_prod {α β : Type*} [Preorder α] [Preorder β] [IsDirected α (· ≤ ·)]
    [IsDirected β (· ≤ ·)] : IsDirected (α × β) (· ≤ ·) :=
  ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    obtain ⟨d, had, hbd⟩ := directed_of (· ≤ ·) a.2 b.2
    exact ⟨(c, d), ⟨hac, had⟩, ⟨hbc, hbd⟩⟩⟩

/-- `infₘ max(a, -m) = a` in `EReal`. -/
theorem ereal_iInf_max_neg_nat (a : EReal) : ⨅ m : ℕ, max a (-((m : ℝ) : EReal)) = a := by
  refine le_antisymm ?_ (le_iInf fun m => le_max_left _ _)
  induction a using EReal.rec with
  | bot =>
    refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    induction c using EReal.rec with
    | bot => exact absurd hc (lt_irrefl _)
    | coe r =>
      obtain ⟨m, hm⟩ := exists_nat_gt (-r)
      refine (iInf_le _ m).trans ?_
      rw [max_eq_right bot_le]
      exact_mod_cast (neg_lt.1 hm).le
    | top => exact le_top
  | coe r =>
    obtain ⟨m, hm⟩ := exists_nat_gt (-r)
    refine (iInf_le _ m).trans ?_
    rw [max_eq_left]
    exact_mod_cast (neg_lt.1 hm).le
  | top => exact le_top

/-! ### Decreasing limits of decreasing limits (PSH) -/

section DecrNetLimit

/-- **BJ22's `F̃_t`** (PSH): `g` is the pointwise limit (= infimum) of a decreasing net
`fᵢ ∈ F_{sᵢ}`, indexed by a nonempty directed preorder in the universe `w`, such that
`ρ(sᵢ) → t`. -/
def IsDecrNetLimit.{w, uK, uS, uT} {K : Type uK} {S : Type uS} {T : Type uT} [TopologicalSpace T]
    (F : S → Set (K → EReal)) (ρ : S → T) (t : T) (g : K → EReal) : Prop :=
  ∃ (ι : Type w) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (s : ι → S)
    (f : ι → K → EReal), (∀ i, f i ∈ F (s i)) ∧ Tendsto (fun i => ρ (s i)) atTop (𝓝 t) ∧
      (∀ x, Antitone fun i => f i x) ∧ ∀ x, g x = ⨅ i, f i x

universe w

/-- The index set of triples `(i, j, ε)`, `i ∈ I`, `j ∈ J_i`, `ε > 0`, of BJ22's proof of
PSH (`equ:directed`). -/
structure DecrNetTriple {I : Type w} (J : I → Type w) where
  /-- The index of the outer net. -/
  i : I
  /-- The index of the inner net. -/
  j : J i
  /-- The positive constant. -/
  ε : ℝ
  ε_pos : 0 < ε

variable {K : Type*} {S : Type*} {T : Type*} [TopologicalSpace T]
  {F F' : S → Set (K → EReal)} {ρ : S → T}

theorem IsDecrNetLimit.mono (hF : ∀ s, F s ⊆ F' s) {t : T} {g : K → EReal}
    (h : IsDecrNetLimit.{w} F ρ t g) : IsDecrNetLimit.{w} F' ρ t g := by
  obtain ⟨ι, _, _, _, s, f, hf, hs, hanti, hg⟩ := h
  exact ⟨ι, inferInstance, inferInstance, inferInstance, s, f, fun i => hF _ (hf i), hs, hanti,
    hg⟩

/-- Truncation: if the families are stable under `f ↦ max(f, c)` and avoid `+∞`, every element
of `F̃_t` is a decreasing limit of real-valued members of the families, namely of the net
`(j, m) ↦ max(f_j, -m)`. -/
theorem IsDecrNetLimit.truncate
    (hmax : ∀ s, ∀ f ∈ F s, ∀ c : ℝ, (fun x => max (f x) (c : EReal)) ∈ F s)
    (hne_top : ∀ s, ∀ f ∈ F s, ∀ x, f x ≠ ⊤) {t : T} {g : K → EReal}
    (h : IsDecrNetLimit.{w} F ρ t g) :
    IsDecrNetLimit.{w} (fun s => {f ∈ F s | ∀ x, f x ≠ ⊥ ∧ f x ≠ ⊤}) ρ t g := by
  obtain ⟨ι, _, _, _, s, f, hf, hs, hanti, hg⟩ := h
  have : IsDirected (ι × ULift.{w} ℕ) (· ≤ ·) := isDirected_prod
  have hfst : Tendsto (Prod.fst : ι × ULift.{w} ℕ → ι) atTop atTop :=
    tendsto_atTop_atTop.2 fun i => ⟨(i, ⟨0⟩), fun p hp => hp.1⟩
  refine ⟨ι × ULift.{w} ℕ, inferInstance, inferInstance, inferInstance, fun p => s p.1,
    fun p x => max (f p.1 x) (-((p.2.down : ℝ) : EReal)), fun p => ⟨?_, fun x => ⟨?_, ?_⟩⟩,
    hs.comp hfst, fun x p q hpq => ?_, fun x => ?_⟩
  · simpa only [EReal.coe_neg] using hmax _ _ (hf p.1) (-(p.2.down : ℝ))
  · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _)
  · rw [Ne, max_eq_top, not_or]
    exact ⟨hne_top _ _ (hf p.1) x, EReal.coe_ne_top _⟩
  · refine max_le_max (hanti x hpq.1) ?_
    have : (p.2.down : ℝ) ≤ q.2.down := by exact_mod_cast hpq.2
    exact_mod_cast neg_le_neg this
  · rw [hg x, iInf_prod]
    refine iInf_congr fun i => ?_
    rw [← ereal_iInf_max_neg_nat (f i x)]
    exact (Equiv.ulift.iInf_comp (g := fun m : ℕ => max (f i x) (-((m : ℝ) : EReal)))).symm

/-- **BJ22 PSH, real-valued case.** Let `K` be compact, `F_s` families of continuous
real-valued functions `K → EReal` stable under adding real constants, and `ρ : S → T` a map to a
metrizable space. If `g = infᵢ gᵢ` is the limit of a decreasing net `gᵢ ∈ F̃_{tᵢ}` with
`tᵢ → t`, then `g ∈ F̃_t`. This is BJ22's proof via the directed set of triples `(i, j, ε)`. -/
theorem IsDecrNetLimit.of_antitone_of_finite [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace.PseudoMetrizableSpace T]
    (hcont : ∀ s, ∀ f ∈ F s, Continuous f) (hfin : ∀ s, ∀ f ∈ F s, ∀ x, f x ≠ ⊥ ∧ f x ≠ ⊤)
    (hadd : ∀ s, ∀ f ∈ F s, ∀ c : ℝ, (fun x => f x + (c : EReal)) ∈ F s)
    {I : Type w} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {τ : I → T} {t : T}
    (hτ : Tendsto τ atTop (𝓝 t)) {g : I → K → EReal}
    (hg : ∀ i, IsDecrNetLimit.{w} F ρ (τ i) (g i)) (hanti : ∀ x, Antitone fun i => g i x)
    {g₀ : K → EReal} (hg₀ : ∀ x, g₀ x = ⨅ i, g i x) : IsDecrNetLimit.{w} F ρ t g₀ := by
  let _ := TopologicalSpace.pseudoMetrizableSpacePseudoMetric T
  choose J instJ dirJ neJ s f hfF hs hfanti hfg using hg
  -- real values of the approximants
  have hreal : ∀ i j x, ((f i j x).toReal : EReal) = f i j x := fun i j x =>
    EReal.coe_toReal (hfin _ _ (hfF i j) x).2 (hfin _ _ (hfF i j) x).1
  have hcontf : ∀ i j, Continuous (f i j) := fun i j => hcont _ _ (hfF i j)
  -- the directed set of triples `(i, j, ε)`
  let A := DecrNetTriple J
  let fA : A → K → EReal := fun α x => f α.i α.j x + (α.ε : EReal)
  let D : A → ℝ := fun α => dist (ρ (s α.i α.j)) (τ α.i) + α.ε
  let R : A → A → Prop := fun α β => α.i ≤ β.i ∧ (∀ x, fA β x ≤ fA α x) ∧ D β ≤ D α
  let instA : Preorder A :=
    { le := R
      lt := fun α β => R α β ∧ ¬ R β α
      le_refl := fun α => ⟨le_rfl, fun _ => le_rfl, le_rfl⟩
      le_trans := fun _ _ _ h₁ h₂ =>
        ⟨h₁.1.trans h₂.1, fun x => (h₂.2.1 x).trans (h₁.2.1 x), h₂.2.2.trans h₁.2.2⟩
      lt_iff_le_not_ge := fun _ _ => Iff.rfl }
  have hle : ∀ α β : A, α ≤ β ↔ α.i ≤ β.i ∧ (∀ x, fA β x ≤ fA α x) ∧ D β ≤ D α :=
    fun _ _ => Iff.rfl
  -- directedness, by Dini's argument on the compact `K`
  have hdir : IsDirected A (· ≤ ·) := by
    refine ⟨fun α₁ α₂ => ?_⟩
    obtain ⟨i₁, j₁, ε₁, hε₁⟩ := α₁
    obtain ⟨i₂, j₂, ε₂, hε₂⟩ := α₂
    obtain ⟨i₃, h13, h23⟩ := directed_of (· ≤ ·) i₁ i₂
    set ε₃ := min ε₁ ε₂ / 2 with hε₃_def
    have hε₃ : 0 < ε₃ := half_pos (lt_min hε₁ hε₂)
    have hε₃₁ : ε₃ < ε₁ := by
      have := min_le_left ε₁ ε₂; rw [hε₃_def]; linarith
    have hε₃₂ : ε₃ < ε₂ := by
      have := min_le_right ε₁ ε₂; rw [hε₃_def]; linarith
    let m : K → EReal := fun x => min (f i₁ j₁ x + (ε₁ : EReal)) (f i₂ j₂ x + (ε₂ : EReal))
    have hm : Continuous m :=
      ((ProjBerk.continuous_ereal_add_coe ε₁).comp (hcontf i₁ j₁)).min
        ((ProjBerk.continuous_ereal_add_coe ε₂).comp (hcontf i₂ j₂))
    let U : J i₃ → Set K := fun j => {x | f i₃ j x + (ε₃ : EReal) < m x}
    have hUopen : ∀ j, IsOpen (U j) := fun j =>
      isOpen_lt ((ProjBerk.continuous_ereal_add_coe ε₃).comp (hcontf i₃ j)) hm
    have hUmono : ∀ j j', j ≤ j' → U j ⊆ U j' := fun j j' h x hx =>
      lt_of_le_of_lt (add_le_add_left (hfanti i₃ x h) _) hx
    have hUdir : Directed (· ⊆ ·) U := fun j j' => by
      obtain ⟨j'', h, h'⟩ := directed_of (· ≤ ·) j j'
      exact ⟨j'', hUmono _ _ h, hUmono _ _ h'⟩
    have hUcover : (univ : Set K) ⊆ ⋃ j, U j := by
      intro x _
      -- `g_{i₃} + ε₃ < min (f_{i₁,j₁} + ε₁) (f_{i₂,j₂} + ε₂)` (BJ22 `equ:i3i1`)
      have key : ∀ (i : I) (j : J i) (ε : ℝ), i ≤ i₃ → ε₃ < ε →
          g i₃ x + (ε₃ : EReal) < f i j x + (ε : EReal) := by
        intro i j ε hi hε
        have h1 : g i₃ x ≤ f i j x :=
          (hanti x hi).trans ((hfg i x).trans_le (iInf_le _ j))
        refine lt_of_le_of_lt (add_le_add_left h1 _) ?_
        rw [← hreal i j x, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_lt_coe_iff]
        linarith
      have h := lt_min (key i₁ j₁ ε₁ h13 hε₃₁) (key i₂ j₂ ε₂ h23 hε₃₂)
      rw [hfg i₃ x, ereal_iInf_add_coe] at h
      obtain ⟨j, hj⟩ := iInf_lt_iff.1 h
      exact mem_iUnion.2 ⟨j, hj⟩
    obtain ⟨j₃', hj₃'⟩ := isCompact_univ.elim_directed_cover U hUopen hUcover hUdir
    have hev := (eventually_ge_atTop j₃').and
      (Metric.tendsto_nhds.1 (hs i₃) (min ε₁ ε₂ / 2) hε₃)
    obtain ⟨j₃, hj₃, hdist⟩ := hev.exists
    refine ⟨⟨i₃, j₃, ε₃, hε₃⟩, ?_, ?_⟩
    · refine ⟨h13, fun x => ?_, ?_⟩
      · have hx : x ∈ U j₃' := hj₃' (mem_univ x)
        exact (lt_of_le_of_lt (add_le_add_left (hfanti i₃ x hj₃) _) hx).le.trans
          (min_le_left _ _)
      · change dist (ρ (s i₃ j₃)) (τ i₃) + ε₃ ≤ dist (ρ (s i₁ j₁)) (τ i₁) + ε₁
        have := dist_nonneg (x := ρ (s i₁ j₁)) (y := τ i₁)
        have := min_le_left ε₁ ε₂
        linarith
    · refine ⟨h23, fun x => ?_, ?_⟩
      · have hx : x ∈ U j₃' := hj₃' (mem_univ x)
        exact (lt_of_le_of_lt (add_le_add_left (hfanti i₃ x hj₃) _) hx).le.trans
          (min_le_right _ _)
      · change dist (ρ (s i₃ j₃)) (τ i₃) + ε₃ ≤ dist (ρ (s i₂ j₂)) (τ i₂) + ε₂
        have := dist_nonneg (x := ρ (s i₂ j₂)) (y := τ i₂)
        have := min_le_right ε₁ ε₂
        linarith
  have : Nonempty A := ⟨⟨Classical.arbitrary I, Classical.arbitrary _, 1, one_pos⟩⟩
  refine ⟨A, instA, hdir, inferInstance, fun α => s α.i α.j, fA,
    fun α => hadd _ _ (hfF α.i α.j) α.ε, ?_, fun x α β h => ((hle α β).1 h).2.1 x,
    fun x => ?_⟩
  · -- convergence of the classes
    refine Metric.tendsto_nhds.2 fun δ hδ => ?_
    obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 hτ (δ / 2) (half_pos hδ))
    obtain ⟨j₀, hj₀⟩ := (Metric.tendsto_nhds.1 (hs i₀) (δ / 4) (by positivity)).exists
    refine eventually_atTop.2 ⟨⟨i₀, j₀, δ / 4, by positivity⟩, fun α hα => ?_⟩
    obtain ⟨hi, -, hD⟩ := (hle _ α).1 hα
    have h1 := hi₀ α.i hi
    change dist (ρ (s α.i α.j)) (τ α.i) + α.ε ≤ dist (ρ (s i₀ j₀)) (τ i₀) + δ / 4 at hD
    have h2 := α.ε_pos
    calc dist (ρ (s α.i α.j)) t ≤ dist (ρ (s α.i α.j)) (τ α.i) + dist (τ α.i) t :=
          dist_triangle _ _ _
      _ < δ := by linarith
  · -- pointwise convergence
    refine le_antisymm (le_iInf fun α => ?_) (le_of_forall_gt_imp_ge_of_dense fun c hc => ?_)
    · calc g₀ x ≤ g α.i x := by rw [hg₀ x]; exact iInf_le _ _
        _ ≤ f α.i α.j x := by rw [hfg α.i x]; exact iInf_le _ _
        _ ≤ fA α x := ereal_le_add_coe α.ε_pos.le _
    · rw [hg₀ x] at hc
      obtain ⟨i, hi⟩ := iInf_lt_iff.1 hc
      rw [hfg i x] at hi
      obtain ⟨j, hj⟩ := iInf_lt_iff.1 hi
      have hr := hreal i j x
      set r := (f i j x).toReal
      rw [← hr] at hj
      obtain ⟨q, hq₁, hq₂⟩ := EReal.lt_iff_exists_real_btwn.1 hj
      have hq : r < q := EReal.coe_lt_coe_iff.1 hq₁
      refine (iInf_le _ ⟨i, j, q - r, sub_pos.2 hq⟩).trans ?_
      change f i j x + ((q - r : ℝ) : EReal) ≤ c
      rw [← hr, ← EReal.coe_add, add_sub_cancel]
      exact hq₂.le

/-- **BJ22 PSH** (with the truncation hypothesis, see the module docstring): let `K` be
compact, `F_s` families of continuous functions `K → [-∞, +∞)` stable under addition of real
constants and under `f ↦ max(f, c)`, and `ρ : S → T` a map to a metrizable space. If `g` is the
pointwise limit of a decreasing net `gᵢ ∈ F̃_{tᵢ}` with `tᵢ → t`, then `g ∈ F̃_t`. -/
theorem IsDecrNetLimit.of_antitone [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace.PseudoMetrizableSpace T]
    (hcont : ∀ s, ∀ f ∈ F s, Continuous f) (hne_top : ∀ s, ∀ f ∈ F s, ∀ x, f x ≠ ⊤)
    (hadd : ∀ s, ∀ f ∈ F s, ∀ c : ℝ, (fun x => f x + (c : EReal)) ∈ F s)
    (hmax : ∀ s, ∀ f ∈ F s, ∀ c : ℝ, (fun x => max (f x) (c : EReal)) ∈ F s)
    {I : Type w} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {τ : I → T} {t : T}
    (hτ : Tendsto τ atTop (𝓝 t)) {g : I → K → EReal}
    (hg : ∀ i, IsDecrNetLimit.{w} F ρ (τ i) (g i)) (hanti : ∀ x, Antitone fun i => g i x)
    {g₀ : K → EReal} (hg₀ : ∀ x, g₀ x = ⨅ i, g i x) : IsDecrNetLimit.{w} F ρ t g₀ := by
  refine IsDecrNetLimit.mono (F := fun s => {f ∈ F s | ∀ x, f x ≠ ⊥ ∧ f x ≠ ⊤})
    (fun s f hf => hf.1) ?_
  refine IsDecrNetLimit.of_antitone_of_finite (F := fun s => {f ∈ F s | ∀ x, f x ≠ ⊥ ∧ f x ≠ ⊤})
    (fun s f hf => hcont s f hf.1) (fun s f hf => hf.2)
    (fun s f hf c => Set.mem_sep (hadd s f hf.1 c) fun x => ⟨?_, ?_⟩) hτ
    (fun i => (hg i).truncate hmax hne_top) hanti hg₀
  · rw [Ne, EReal.add_eq_bot_iff, not_or]
    exact ⟨(hf.2 x).1, EReal.coe_ne_bot c⟩
  · exact EReal.add_ne_top (hf.2 x).2 (EReal.coe_ne_top c)

end DecrNetLimit

/-! ### PSH2 on `(ℙⁿ)^an` -/

namespace ProjBerk

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- FS functions of class `a` are stable under adding a real constant. -/
theorem IsFS.add_const {a : ℚ} {φ : ProjBerk k n → EReal} (h : IsFS a φ) (c : ℝ) :
    IsFS a fun v => φ v + (c : EReal) := by
  simpa only [add_zero] using h.add (isFS_const (k := k) (n := n) le_rfl c)

/-- FS functions of class `a` are stable under maxima with real constants. -/
theorem IsFS.max_const {a : ℚ} {φ : ProjBerk k n → EReal} (h : IsFS a φ) (c : ℝ) :
    IsFS a fun v => Max.max (φ v) (c : EReal) :=
  h.max (isFS_const h.nonneg c)

/-- `θ`-psh functions are exactly the generically finite usc functions in BJ22's `F̃_θ`, for the
families `F_a = 𝓗^gf_ℝ(O(a))`, `a ∈ ℚ`, and `ρ(a) = a ∈ ℝ = N¹(ℙⁿ)_ℝ`. -/
theorem isPSH_iff_isDecrNetLimit {θ : ℝ} {u : ProjBerk k n → EReal} :
    IsPSH θ u ↔ (∃ v, u v ≠ ⊥) ∧ UpperSemicontinuous u ∧
      IsDecrNetLimit.{u} (fun a : ℚ => {φ : ProjBerk k n → EReal | IsFS a φ})
        (fun a : ℚ => (a : ℝ)) θ u :=
  Iff.rfl

/-- **PSH2** (BJ22 psh12, FHX `prop:BJ-package`(1)): if `uᵢ ∈ PSH(θᵢ)` is a decreasing
net with `θᵢ → θ`, and the pointwise limit `u = infᵢ uᵢ` is generically finite, then
`u ∈ PSH(θ)`. -/
theorem isPSH_of_antitone {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {θ : ι → ℝ} {θ₀ : ℝ} (hθ : Tendsto θ atTop (𝓝 θ₀)) {u : ι → ProjBerk k n → EReal}
    (hu : ∀ i, IsPSH (θ i) (u i)) (hanti : ∀ v, Antitone fun i => u i v)
    {w : ProjBerk k n → EReal} (hw : ∀ v, w v = ⨅ i, u i v) (hfin : ∃ v, w v ≠ ⊥) :
    IsPSH θ₀ w := by
  refine isPSH_iff_isDecrNetLimit.2 ⟨hfin, ?_, ?_⟩
  · rw [show w = fun v => ⨅ i, u i v from funext hw]
    exact upperSemicontinuous_iInf fun i => (hu i).upperSemicontinuous
  · exact IsDecrNetLimit.of_antitone (F := fun a : ℚ => {φ : ProjBerk k n → EReal | IsFS a φ})
      (ρ := fun a : ℚ => (a : ℝ)) (fun a φ hφ => IsFS.continuous hφ)
      (fun a φ hφ => IsFS.ne_top hφ) (fun a φ hφ c => IsFS.add_const hφ c)
      (fun a φ hφ c => IsFS.max_const hφ c) hθ (fun i => (isPSH_iff_isDecrNetLimit.1 (hu i)).2.2)
      hanti hw

/-- **PSH2**, limit form. -/
theorem isPSH_of_tendsto_of_antitone {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] {θ : ι → ℝ} {θ₀ : ℝ} (hθ : Tendsto θ atTop (𝓝 θ₀))
    {u : ι → ProjBerk k n → EReal} (hu : ∀ i, IsPSH (θ i) (u i))
    (hanti : ∀ v, Antitone fun i => u i v) {w : ProjBerk k n → EReal}
    (hw : ∀ v, Tendsto (fun i => u i v) atTop (𝓝 (w v))) (hfin : ∃ v, w v ≠ ⊥) :
    IsPSH θ₀ w :=
  isPSH_of_antitone hθ hu hanti
    (fun v => tendsto_nhds_unique (hw v) (tendsto_atTop_iInf (hanti v))) hfin

/-- **PSH2** for decreasing sequences. -/
theorem isPSH_of_antitone_seq {θ : ℕ → ℝ} {θ₀ : ℝ} (hθ : Tendsto θ atTop (𝓝 θ₀))
    {u : ℕ → ProjBerk k n → EReal} (hu : ∀ m, IsPSH (θ m) (u m))
    (hanti : ∀ v, Antitone fun m => u m v) {w : ProjBerk k n → EReal}
    (hw : ∀ v, w v = ⨅ m, u m v) (hfin : ∃ v, w v ≠ ⊥) : IsPSH θ₀ w := by
  have hdown : Tendsto (ULift.down : ULift.{u} ℕ → ℕ) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨ULift.up b, fun a ha => ha⟩
  refine isPSH_of_antitone (ι := ULift.{u} ℕ) (hθ.comp hdown) (fun m => hu m.down)
    (fun v _ _ h => hanti v h) (fun v => ?_) hfin
  rw [hw v]
  exact (Equiv.ulift.iInf_comp (g := fun m => u m v)).symm

end ProjBerk

end EnvelopeProperty
