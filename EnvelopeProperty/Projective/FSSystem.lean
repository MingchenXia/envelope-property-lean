/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.Regularization

/-!
# Fubini–Study systems and their psh functions

This file develops, once and for all, the elementary part of the theory of `θ`-psh functions of
Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field* (BJ22), §4.1–4.2,
for an abstract family of "Fubini–Study functions" indexed by classes `a ∈ ℚ^r_{≥0}`. It is used
by Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX), Corollary 5.26
(`cor:normal-weak-global`) through the blueprint chapter `projective-general.tex`
(`subsec:pg-fs-systems`); the instances are `X = V(I) ⊆ ℙ^M` (rank `1`), blowups
`X' ⊆ ℙ^M × ℙ^{M'}` (rank `2`) and `(ℙⁿ)^an` itself
(`EnvelopeProperty.Projective.FSSystemProjBerk`).

## Fubini–Study systems (`def:pg-fs-system`)

A **Fubini–Study system** of rank `r` on a space `K` with a trivial point `⋆`
(`EnvelopeProperty.FSSystem`) consists of predicates `IsFS a` (`𝓗(a)`, BJ22's `𝓗^gf_ℝ`) and
`IsFinFS a` (`𝓗_fin(a)`, BJ22's `𝓗_ℚ`) on functions `K → [-∞, +∞)`, for `a ∈ ℚ^r`, such that

* functions in `𝓗(a)` are continuous, and `𝓗(a) = ∅` unless `a ≥ 0` (the blueprint assigns
  sets only to `a ∈ ℚ^r_{≥0}`);
* (FS1) every `f ∈ 𝓗(a)` has `f(⋆) ∈ ℝ` and `f ≤ f(⋆)`;
* `𝓗_fin(a) ⊆ 𝓗(a)` consists of real-valued functions;
* (FS2) `𝓗(a) ⊆ 𝓗(b)` and `𝓗_fin(a) ⊆ 𝓗_fin(b)` for `a ≤ b` (coordinatewise);
* (FS3) `𝓗(a)` contains the real constants, `𝓗_fin(a)` the rational constants (`a ≥ 0`), and
  both are stable under binary maxima;
* (FS4) `𝓗(a) + 𝓗(b) ⊆ 𝓗(a + b)`, `𝓗_fin(a) + 𝓗_fin(b) ⊆ 𝓗_fin(a + b)`, `c 𝓗(a) ⊆ 𝓗(c a)`
  and `c 𝓗_fin(a) ⊆ 𝓗_fin(c a)` for `c ∈ ℚ_{>0}`;
* (FS5) every `f ∈ 𝓗(a)` is the limit of a decreasing sequence in `𝓗_fin(a)`.

The remaining clauses of the blueprint's (FS3) — stability under addition of real (resp. rational)
constants and under maxima with real (resp. rational) constants — follow from (FS3) and (FS4)
with the class `0` (`FSSystem.IsFS.add_const`, `FSSystem.IsFS.max_const`,
`FSSystem.IsFinFS.add_const`, `FSSystem.IsFinFS.max_const`), and are therefore not fields.
Compactness of `K` is a typeclass assumption of the theorems that use it; Hausdorffness is never
used.

## Psh functions (`def:pg-psh`)

`FSSystem.IsPSH θ u`, for `θ ∈ ℝ^r`: `u ≢ -∞`, `u` is usc, and `u` is the pointwise limit (= the
infimum) of a decreasing net `fᵢ ∈ 𝓗(aᵢ)` with `aᵢ → θ` (BJ22 Definition 4.1, with the classes
restricted to the cone of the `r` coordinate classes, see `rmk:pg-fs-system`).

## Main results

* `FSSystem.IsPSH.nonneg`, `FSSystem.IsPSH.le_apply_triv`, `FSSystem.IsPSH.apply_triv_ne_bot`,
  `FSSystem.IsPSH.apply_triv_ne_top`, `FSSystem.IsPSH.iSup_eq` (**maximum principle**,
  `prop:pg-maxprin`): `θ ≥ 0`, `u(⋆) ∈ ℝ` and `u ≤ u(⋆)`.
* `FSSystem.IsFS.isPSH` (PSH1), `FSSystem.isPSH_iff_exists_isFinFS` (psh functions are the
  generically finite decreasing limits of nets in `𝓗_fin(bᵦ)`, `bᵦ → θ`) and
  `FSSystem.isPSH_of_antitone` (**PSH2**), with the variants `FSSystem.isPSH_of_tendsto_of_antitone`
  and `FSSystem.isPSH_of_antitone_seq` (`thm:pg-psh2`).
* `FSSystem.IsPSH.add`, `FSSystem.IsPSH.smul_rat`, `FSSystem.IsPSH.smul`,
  `FSSystem.isPSH_smul_iff`, `FSSystem.setOf_isPSH_smul`, `FSSystem.IsPSH.max`,
  `FSSystem.isPSH_finset_sup'`, `FSSystem.IsPSH.add_const`, `FSSystem.isPSH_const`,
  `FSSystem.IsPSH.mono_class` (`thm:pg-psh-basic`).

Regularization is in `EnvelopeProperty.Projective.FSSystemRegularization`.

## The diagonal lemma with rational constants

PSH2 uses BJ22's Lemma 4.6 (PSH, `lem:bj-psh-diagonal`) in the form
`EnvelopeProperty.IsDecrNetLimit.of_antitone` (the families `𝓗(a)` are stable under real
constants and maxima with real constants). For the finite families `𝓗_fin(a)`, which are only
stable under addition of rational constants, we prove the blueprint's form of the lemma,
`EnvelopeProperty.IsDecrNetLimit.of_antitone_of_finite_rat` (real-valued continuous families stable
under addition of positive rational constants); its proof is BJ22's, with rational `ε` in the
directed set of triples `(i, j, ε)`. The existing `IsDecrNetLimit.of_antitone_of_finite` needs
stability under all real constants.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

/-! ### Generic net lemmas -/

section DecrNetLimit

universe w

/-- The index set of triples `(i, j, ε)`, `i ∈ I`, `j ∈ J_i`, `ε ∈ ℚ_{>0}`, of the proof of
BJ22 PSH (`equ:directed`) with rational constants. -/
structure DecrNetTripleRat {I : Type w} (J : I → Type w) where
  /-- The index of the outer net. -/
  i : I
  /-- The index of the inner net. -/
  j : J i
  /-- The positive rational constant. -/
  ε : ℚ
  ε_pos : 0 < ε

variable {K : Type*} {S : Type*} {T : Type*} [TopologicalSpace T]
  {F : S → Set (K → EReal)} {ρ : S → T}

/-- A decreasing **sequence** `fₙ ∈ F_{sₙ}` with `ρ(sₙ) → t` gives an element of `F̃_t`. -/
theorem IsDecrNetLimit.of_seq {t : T} {g : K → EReal} (s : ℕ → S) (f : ℕ → K → EReal)
    (hf : ∀ n, f n ∈ F (s n)) (hs : Tendsto (fun n => ρ (s n)) atTop (𝓝 t))
    (hanti : ∀ x, Antitone fun n => f n x) (hg : ∀ x, g x = ⨅ n, f n x) :
    IsDecrNetLimit.{w} F ρ t g := by
  have hdown : Tendsto (ULift.down : ULift.{w} ℕ → ℕ) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨ULift.up b, fun a ha => ha⟩
  refine ⟨ULift.{w} ℕ, inferInstance, inferInstance, inferInstance, fun n => s n.down,
    fun n => f n.down, fun n => hf n.down, hs.comp hdown, fun x m n hmn => hanti x hmn,
    fun x => ?_⟩
  rw [hg x]
  exact (Equiv.ulift.iInf_comp (g := fun n => f n x)).symm

/-- **BJ22 PSH for real-valued families stable under positive rational constants**
(`lem:bj-psh-diagonal` as stated in the blueprint). Let `K` be compact, `F_s` families of
continuous real-valued functions `K → EReal` stable under addition of positive rational
constants, and `ρ : S → T` a map to a metrizable space. If `g₀ = infᵢ gᵢ` is the limit of a
decreasing net `gᵢ ∈ F̃_{tᵢ}` with `tᵢ → t`, then `g₀ ∈ F̃_t`. The proof is BJ22's, via the
directed set of triples `(i, j, ε)` with `ε ∈ ℚ_{>0}`. -/
theorem IsDecrNetLimit.of_antitone_of_finite_rat [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace.PseudoMetrizableSpace T]
    (hcont : ∀ s, ∀ f ∈ F s, Continuous f) (hfin : ∀ s, ∀ f ∈ F s, ∀ x, f x ≠ ⊥ ∧ f x ≠ ⊤)
    (hadd : ∀ s, ∀ f ∈ F s, ∀ c : ℚ, 0 < c → (fun x => f x + ((c : ℝ) : EReal)) ∈ F s)
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
  let A := DecrNetTripleRat J
  let fA : A → K → EReal := fun α x => f α.i α.j x + ((α.ε : ℝ) : EReal)
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
    set ε₃ : ℚ := min ε₁ ε₂ / 2 with hε₃_def
    have hε₃ : 0 < ε₃ := half_pos (lt_min hε₁ hε₂)
    have h2ε₁ : 2 * ε₃ ≤ ε₁ := by
      have := min_le_left ε₁ ε₂; rw [hε₃_def]; linarith
    have h2ε₂ : 2 * ε₃ ≤ ε₂ := by
      have := min_le_right ε₁ ε₂; rw [hε₃_def]; linarith
    have hε₃r : (0 : ℝ) < ε₃ := by exact_mod_cast hε₃
    have h2ε₁r : 2 * (ε₃ : ℝ) ≤ ε₁ := by exact_mod_cast h2ε₁
    have h2ε₂r : 2 * (ε₃ : ℝ) ≤ ε₂ := by exact_mod_cast h2ε₂
    let m : K → EReal := fun x =>
      min (f i₁ j₁ x + ((ε₁ : ℝ) : EReal)) (f i₂ j₂ x + ((ε₂ : ℝ) : EReal))
    have hm : Continuous m :=
      ((ProjBerk.continuous_ereal_add_coe ε₁).comp (hcontf i₁ j₁)).min
        ((ProjBerk.continuous_ereal_add_coe ε₂).comp (hcontf i₂ j₂))
    let U : J i₃ → Set K := fun j => {x | f i₃ j x + ((ε₃ : ℝ) : EReal) < m x}
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
      have key : ∀ (i : I) (j : J i) (ε : ℝ), i ≤ i₃ → (ε₃ : ℝ) < ε →
          g i₃ x + ((ε₃ : ℝ) : EReal) < f i j x + (ε : EReal) := by
        intro i j ε hi hε
        have h1 : g i₃ x ≤ f i j x :=
          (hanti x hi).trans ((hfg i x).trans_le (iInf_le _ j))
        refine lt_of_le_of_lt (add_le_add_left h1 _) ?_
        rw [← hreal i j x, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_lt_coe_iff]
        linarith
      have h := lt_min (key i₁ j₁ ε₁ h13 (by linarith)) (key i₂ j₂ ε₂ h23 (by linarith))
      rw [hfg i₃ x, ereal_iInf_add_coe] at h
      obtain ⟨j, hj⟩ := iInf_lt_iff.1 h
      exact mem_iUnion.2 ⟨j, hj⟩
    obtain ⟨j₃', hj₃'⟩ := isCompact_univ.elim_directed_cover U hUopen hUcover hUdir
    have hev := (eventually_ge_atTop j₃').and (Metric.tendsto_nhds.1 (hs i₃) (ε₃ : ℝ) hε₃r)
    obtain ⟨j₃, hj₃, hdist⟩ := hev.exists
    refine ⟨⟨i₃, j₃, ε₃, hε₃⟩, ?_, ?_⟩
    · refine ⟨h13, fun x => ?_, ?_⟩
      · have hx : x ∈ U j₃' := hj₃' (mem_univ x)
        exact (lt_of_le_of_lt (add_le_add_left (hfanti i₃ x hj₃) _) hx).le.trans
          (min_le_left _ _)
      · change dist (ρ (s i₃ j₃)) (τ i₃) + (ε₃ : ℝ) ≤ dist (ρ (s i₁ j₁)) (τ i₁) + (ε₁ : ℝ)
        have := dist_nonneg (x := ρ (s i₁ j₁)) (y := τ i₁)
        linarith
    · refine ⟨h23, fun x => ?_, ?_⟩
      · have hx : x ∈ U j₃' := hj₃' (mem_univ x)
        exact (lt_of_le_of_lt (add_le_add_left (hfanti i₃ x hj₃) _) hx).le.trans
          (min_le_right _ _)
      · change dist (ρ (s i₃ j₃)) (τ i₃) + (ε₃ : ℝ) ≤ dist (ρ (s i₂ j₂)) (τ i₂) + (ε₂ : ℝ)
        have := dist_nonneg (x := ρ (s i₂ j₂)) (y := τ i₂)
        linarith
  have : Nonempty A := ⟨⟨Classical.arbitrary I, Classical.arbitrary _, 1, one_pos⟩⟩
  refine ⟨A, instA, hdir, inferInstance, fun α => s α.i α.j, fA,
    fun α => hadd _ _ (hfF α.i α.j) α.ε α.ε_pos, ?_, fun x α β h => ((hle α β).1 h).2.1 x,
    fun x => ?_⟩
  · -- convergence of the classes
    refine Metric.tendsto_nhds.2 fun δ hδ => ?_
    obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 hτ (δ / 2) (half_pos hδ))
    obtain ⟨j₀, hj₀⟩ := (Metric.tendsto_nhds.1 (hs i₀) (δ / 4) (by positivity)).exists
    obtain ⟨ε₀, hε₀, hε₀δ⟩ := exists_rat_btwn (show (0 : ℝ) < δ / 4 by positivity)
    refine eventually_atTop.2 ⟨⟨i₀, j₀, ε₀, by exact_mod_cast hε₀⟩, fun α hα => ?_⟩
    obtain ⟨hi, -, hD⟩ := (hle _ α).1 hα
    have h1 := hi₀ α.i hi
    change dist (ρ (s α.i α.j)) (τ α.i) + (α.ε : ℝ) ≤ dist (ρ (s i₀ j₀)) (τ i₀) + (ε₀ : ℝ)
      at hD
    have h2 : (0 : ℝ) < α.ε := by exact_mod_cast α.ε_pos
    calc dist (ρ (s α.i α.j)) t ≤ dist (ρ (s α.i α.j)) (τ α.i) + dist (τ α.i) t :=
          dist_triangle _ _ _
      _ < δ := by linarith
  · -- pointwise convergence
    refine le_antisymm (le_iInf fun α => ?_) (le_of_forall_gt_imp_ge_of_dense fun c hc => ?_)
    · calc g₀ x ≤ g α.i x := by rw [hg₀ x]; exact iInf_le _ _
        _ ≤ f α.i α.j x := by rw [hfg α.i x]; exact iInf_le _ _
        _ ≤ fA α x := ereal_le_add_coe (by exact_mod_cast α.ε_pos.le) _
    · rw [hg₀ x] at hc
      obtain ⟨i, hi⟩ := iInf_lt_iff.1 hc
      rw [hfg i x] at hi
      obtain ⟨j, hj⟩ := iInf_lt_iff.1 hi
      have hr := hreal i j x
      set r := (f i j x).toReal
      rw [← hr] at hj
      obtain ⟨q, hq₁, hq₂⟩ := EReal.lt_iff_exists_real_btwn.1 hj
      have hq : r < q := EReal.coe_lt_coe_iff.1 hq₁
      obtain ⟨ε, hε, hεq⟩ := exists_rat_btwn (sub_pos.2 hq)
      refine (iInf_le _ ⟨i, j, ε, by exact_mod_cast hε⟩).trans ?_
      change f i j x + ((ε : ℝ) : EReal) ≤ c
      rw [← hr, ← EReal.coe_add]
      refine le_trans ?_ hq₂.le
      exact EReal.coe_le_coe_iff.2 (by linarith)

end DecrNetLimit

/-! ### Auxiliary facts -/

/-- Multiplication by a positive real commutes with infima in `EReal`. -/
theorem ereal_coe_mul_iInf {ι : Sort*} {c : ℝ} (hc : 0 < c) (a : ι → EReal) :
    (c : EReal) * ⨅ i, a i = ⨅ i, (c : EReal) * a i :=
  Monotone.map_iInf_of_continuousAt (f := fun x : EReal => (c : EReal) * x)
    (ProjBerk.continuous_ereal_coe_mul hc.ne').continuousAt
    (ProjBerk.ereal_coe_mul_monotone hc.le) (EReal.coe_mul_top_of_pos hc)

/-- For an antitone family on a directed preorder, the infimum over a tail `{i | i₀ ≤ i}` is the
infimum over all indices. -/
theorem iInf_subtype_le_eq_iInf_of_antitone {ι α : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [CompleteLattice α] {f : ι → α} (hf : Antitone f) (i₀ : ι) :
    ⨅ i : {i // i₀ ≤ i}, f i = ⨅ i, f i := by
  refine le_antisymm (le_iInf fun i => ?_) (le_iInf fun i => iInf_le _ _)
  obtain ⟨j, h₁, h₂⟩ := directed_of (· ≤ ·) i₀ i
  exact (iInf_le _ (⟨j, h₁⟩ : {i // i₀ ≤ i})).trans (hf h₂)

/-- A tail `{i | i₀ ≤ i}` of a directed preorder is directed. -/
theorem isDirected_subtype_le {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] (i₀ : ι) :
    IsDirected {i // i₀ ≤ i} (· ≤ ·) :=
  ⟨fun i j => by
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i.1 j.1
    exact ⟨⟨k, i.2.trans hik⟩, hik, hjk⟩⟩

/-- Rational vectors decreasing strictly to a real vector. -/
theorem exists_seq_rat_vec_gt_tendsto {r : ℕ} (θ : Fin r → ℝ) :
    ∃ a : ℕ → Fin r → ℚ, (∀ n c, θ c < a n c) ∧
      Tendsto (fun n c => (a n c : ℝ)) atTop (𝓝 θ) := by
  choose q hq using fun c => Real.exists_seq_rat_strictAnti_tendsto (θ c)
  exact ⟨fun n c => q c n, fun n c => (hq c).2.1 n, tendsto_pi_nhds.2 fun c => (hq c).2.2⟩

/-! ### Fubini–Study systems -/

universe u

/-- A **Fubini–Study system** of rank `r` on `(K, ⋆)` (`def:pg-fs-system`; modelled on BJ22
`defi:FS`, FS, FSgenfin): predicates `IsFS a` (the Fubini–Study functions
`𝓗(a)` of class `a`) and `IsFinFS a` (the finite rational ones, `𝓗_fin(a)`) on functions
`K → [-∞, +∞)`, for `a ∈ ℚ^r`, satisfying the axioms (FS1)–(FS5). `𝓗(a)` is empty unless
`a ≥ 0`. -/
structure FSSystem (K : Type u) [TopologicalSpace K] (r : ℕ) where
  /-- The trivial point `⋆`. -/
  triv : K
  /-- `IsFS a f`: `f` is a Fubini–Study function of class `a`, `f ∈ 𝓗(a)`. -/
  IsFS : (Fin r → ℚ) → (K → EReal) → Prop
  /-- `IsFinFS a f`: `f` is a finite rational Fubini–Study function of class `a`,
  `f ∈ 𝓗_fin(a)`. -/
  IsFinFS : (Fin r → ℚ) → (K → EReal) → Prop
  /-- Fubini–Study functions are continuous. -/
  continuous_of_isFS : ∀ {a f}, IsFS a f → Continuous f
  /-- Only classes `a ≥ 0` carry Fubini–Study functions. -/
  nonneg_of_isFS : ∀ {a f}, IsFS a f → 0 ≤ a
  /-- (FS1) `f(⋆) ≠ -∞`. -/
  apply_triv_ne_bot : ∀ {a f}, IsFS a f → f triv ≠ ⊥
  /-- (FS1) `f(⋆) ≠ +∞`. -/
  apply_triv_ne_top : ∀ {a f}, IsFS a f → f triv ≠ ⊤
  /-- (FS1) `f ≤ f(⋆)`. -/
  le_apply_triv : ∀ {a f}, IsFS a f → ∀ x, f x ≤ f triv
  /-- `𝓗_fin(a) ⊆ 𝓗(a)`. -/
  isFS_of_isFinFS : ∀ {a f}, IsFinFS a f → IsFS a f
  /-- Functions in `𝓗_fin(a)` are real valued. -/
  ne_bot_of_isFinFS : ∀ {a f}, IsFinFS a f → ∀ x, f x ≠ ⊥
  /-- (FS2) `𝓗(a) ⊆ 𝓗(b)` for `a ≤ b`. -/
  isFS_mono : ∀ {a b f}, IsFS a f → a ≤ b → IsFS b f
  /-- (FS2) `𝓗_fin(a) ⊆ 𝓗_fin(b)` for `a ≤ b`. -/
  isFinFS_mono : ∀ {a b f}, IsFinFS a f → a ≤ b → IsFinFS b f
  /-- (FS3) real constants are in `𝓗(a)` for `a ≥ 0`. -/
  isFS_const : ∀ {a}, 0 ≤ a → ∀ c : ℝ, IsFS a fun _ => (c : EReal)
  /-- (FS3) rational constants are in `𝓗_fin(a)` for `a ≥ 0`. -/
  isFinFS_const : ∀ {a}, 0 ≤ a → ∀ c : ℚ, IsFinFS a fun _ => ((c : ℝ) : EReal)
  /-- (FS3) `𝓗(a)` is stable under maxima. -/
  isFS_max : ∀ {a f g}, IsFS a f → IsFS a g → IsFS a fun x => Max.max (f x) (g x)
  /-- (FS3) `𝓗_fin(a)` is stable under maxima. -/
  isFinFS_max : ∀ {a f g}, IsFinFS a f → IsFinFS a g → IsFinFS a fun x => Max.max (f x) (g x)
  /-- (FS4) `𝓗(a) + 𝓗(b) ⊆ 𝓗(a + b)`. -/
  isFS_add : ∀ {a b f g}, IsFS a f → IsFS b g → IsFS (a + b) fun x => f x + g x
  /-- (FS4) `𝓗_fin(a) + 𝓗_fin(b) ⊆ 𝓗_fin(a + b)`. -/
  isFinFS_add : ∀ {a b f g}, IsFinFS a f → IsFinFS b g → IsFinFS (a + b) fun x => f x + g x
  /-- (FS4) `c 𝓗(a) ⊆ 𝓗(c a)` for `c ∈ ℚ_{>0}`. -/
  isFS_smul : ∀ {a f} {c : ℚ}, 0 < c → IsFS a f →
    IsFS (c • a) fun x => ((c : ℝ) : EReal) * f x
  /-- (FS4) `c 𝓗_fin(a) ⊆ 𝓗_fin(c a)` for `c ∈ ℚ_{>0}`. -/
  isFinFS_smul : ∀ {a f} {c : ℚ}, 0 < c → IsFinFS a f →
    IsFinFS (c • a) fun x => ((c : ℝ) : EReal) * f x
  /-- (FS5) every `f ∈ 𝓗(a)` is the limit of a decreasing sequence in `𝓗_fin(a)`. -/
  exists_antitone_isFinFS : ∀ {a f}, IsFS a f → ∃ g : ℕ → K → EReal,
    (∀ n, IsFinFS a (g n)) ∧ (∀ x, Antitone fun n => g n x) ∧ ∀ x, f x = ⨅ n, g n x

namespace FSSystem

variable {K : Type u} [TopologicalSpace K] {r : ℕ} {F : FSSystem K r}
  {a b : Fin r → ℚ} {f g : K → EReal}

/-! ### Fubini–Study functions -/

theorem IsFS.continuous (h : F.IsFS a f) : Continuous f := F.continuous_of_isFS h

theorem IsFS.nonneg (h : F.IsFS a f) : 0 ≤ a := F.nonneg_of_isFS h

theorem IsFS.apply_triv_ne_bot (h : F.IsFS a f) : f F.triv ≠ ⊥ := F.apply_triv_ne_bot h

theorem IsFS.apply_triv_ne_top (h : F.IsFS a f) : f F.triv ≠ ⊤ := F.apply_triv_ne_top h

/-- (FS1) `f ≤ f(⋆)`. -/
theorem IsFS.le_apply_triv (h : F.IsFS a f) (x : K) : f x ≤ f F.triv := F.le_apply_triv h x

/-- Fubini–Study functions take values in `[-∞, +∞)`. -/
theorem IsFS.ne_top (h : F.IsFS a f) (x : K) : f x ≠ ⊤ :=
  ne_top_of_le_ne_top h.apply_triv_ne_top (h.le_apply_triv x)

theorem IsFS.mono (h : F.IsFS a f) (hab : a ≤ b) : F.IsFS b f := F.isFS_mono h hab

theorem IsFS.max (hf : F.IsFS a f) (hg : F.IsFS a g) : F.IsFS a fun x => Max.max (f x) (g x) :=
  F.isFS_max hf hg

theorem IsFS.add (hf : F.IsFS a f) (hg : F.IsFS b g) : F.IsFS (a + b) fun x => f x + g x :=
  F.isFS_add hf hg

theorem IsFS.smul (h : F.IsFS a f) {c : ℚ} (hc : 0 < c) :
    F.IsFS (c • a) fun x => ((c : ℝ) : EReal) * f x :=
  F.isFS_smul hc h

/-- (FS3) `𝓗(a)` is stable under addition of real constants. -/
theorem IsFS.add_const (h : F.IsFS a f) (c : ℝ) : F.IsFS a fun x => f x + (c : EReal) := by
  simpa only [add_zero] using h.add (F.isFS_const (a := 0) le_rfl c)

/-- (FS3) `𝓗(a)` is stable under maxima with real constants. -/
theorem IsFS.max_const (h : F.IsFS a f) (c : ℝ) :
    F.IsFS a fun x => Max.max (f x) (c : EReal) :=
  h.max (F.isFS_const h.nonneg c)

/-- (FS5) every `f ∈ 𝓗(a)` is the limit of a decreasing sequence in `𝓗_fin(a)`. -/
theorem IsFS.exists_antitone_isFinFS (h : F.IsFS a f) : ∃ g : ℕ → K → EReal,
    (∀ n, F.IsFinFS a (g n)) ∧ (∀ x, Antitone fun n => g n x) ∧ ∀ x, f x = ⨅ n, g n x :=
  F.exists_antitone_isFinFS h

theorem IsFinFS.isFS (h : F.IsFinFS a f) : F.IsFS a f := F.isFS_of_isFinFS h

theorem IsFinFS.ne_bot (h : F.IsFinFS a f) (x : K) : f x ≠ ⊥ := F.ne_bot_of_isFinFS h x

theorem IsFinFS.ne_top (h : F.IsFinFS a f) (x : K) : f x ≠ ⊤ := h.isFS.ne_top x

theorem IsFinFS.continuous (h : F.IsFinFS a f) : Continuous f := h.isFS.continuous

theorem IsFinFS.nonneg (h : F.IsFinFS a f) : 0 ≤ a := h.isFS.nonneg

theorem IsFinFS.mono (h : F.IsFinFS a f) (hab : a ≤ b) : F.IsFinFS b f := F.isFinFS_mono h hab

theorem IsFinFS.max (hf : F.IsFinFS a f) (hg : F.IsFinFS a g) :
    F.IsFinFS a fun x => Max.max (f x) (g x) :=
  F.isFinFS_max hf hg

theorem IsFinFS.add (hf : F.IsFinFS a f) (hg : F.IsFinFS b g) :
    F.IsFinFS (a + b) fun x => f x + g x :=
  F.isFinFS_add hf hg

theorem IsFinFS.smul (h : F.IsFinFS a f) {c : ℚ} (hc : 0 < c) :
    F.IsFinFS (c • a) fun x => ((c : ℝ) : EReal) * f x :=
  F.isFinFS_smul hc h

/-- (FS3) `𝓗_fin(a)` is stable under addition of rational constants. -/
theorem IsFinFS.add_const (h : F.IsFinFS a f) (c : ℚ) :
    F.IsFinFS a fun x => f x + ((c : ℝ) : EReal) := by
  simpa only [add_zero] using h.add (F.isFinFS_const (a := 0) le_rfl c)

/-- (FS3) `𝓗_fin(a)` is stable under maxima with rational constants. -/
theorem IsFinFS.max_const (h : F.IsFinFS a f) (c : ℚ) :
    F.IsFinFS a fun x => Max.max (f x) ((c : ℝ) : EReal) :=
  h.max (F.isFinFS_const h.nonneg c)

/-! ### Psh functions (`def:pg-psh`) -/

/-- **`θ`-psh functions** of a Fubini–Study system (`def:pg-psh`, BJ22 Definition 4.1): `u` is
not identically `-∞`, upper semicontinuous, and the pointwise limit (= infimum) of a decreasing
net `fᵢ ∈ 𝓗(aᵢ)`, indexed by a nonempty directed preorder in the universe of `K`, with
`aᵢ → θ` in `ℝ^r`. -/
def IsPSH (F : FSSystem K r) (θ : Fin r → ℝ) (u : K → EReal) : Prop :=
  (∃ x, u x ≠ ⊥) ∧ UpperSemicontinuous u ∧
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (a : ι → Fin r → ℚ) (f : ι → K → EReal), (∀ i, F.IsFS (a i) (f i)) ∧
        Tendsto (fun i c => (a i c : ℝ)) atTop (𝓝 θ) ∧ (∀ x, Antitone fun i => f i x) ∧
          ∀ x, u x = ⨅ i, f i x

variable {θ θ' : Fin r → ℝ} {u u' : K → EReal}

/-- `θ`-psh functions are the generically finite usc functions in BJ22's `F̃_θ`
(`IsDecrNetLimit`) for the families `𝓗(a)` and the classes `a ↦ a ∈ ℝ^r`. -/
theorem isPSH_iff_isDecrNetLimit : F.IsPSH θ u ↔ (∃ x, u x ≠ ⊥) ∧ UpperSemicontinuous u ∧
    IsDecrNetLimit.{u} (fun a => {f | F.IsFS a f}) (fun a c => (a c : ℝ)) θ u :=
  Iff.rfl

theorem IsPSH.exists_ne_bot (h : F.IsPSH θ u) : ∃ x, u x ≠ ⊥ := h.1

theorem IsPSH.upperSemicontinuous (h : F.IsPSH θ u) : UpperSemicontinuous u := h.2.1

/-- Constructing a `θ`-psh function from a decreasing net of Fubini–Study functions: upper
semicontinuity is automatic for an infimum of continuous functions. -/
theorem isPSH_of_iInf (hfin : ∃ x, u x ≠ ⊥) {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] (a : ι → Fin r → ℚ) (f : ι → K → EReal) (hf : ∀ i, F.IsFS (a i) (f i))
    (ha : Tendsto (fun i c => (a i c : ℝ)) atTop (𝓝 θ)) (hanti : ∀ x, Antitone fun i => f i x)
    (hu : ∀ x, u x = ⨅ i, f i x) : F.IsPSH θ u := by
  refine ⟨hfin, ?_, ι, inferInstance, inferInstance, inferInstance, a, f, hf, ha, hanti, hu⟩
  rw [show u = fun x => ⨅ i, f i x from funext hu]
  exact upperSemicontinuous_iInf fun i => (hf i).continuous.upperSemicontinuous

/-- The definition in its limit form. -/
theorem isPSH_of_tendsto (hfin : ∃ x, u x ≠ ⊥) {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] (a : ι → Fin r → ℚ) (f : ι → K → EReal) (hf : ∀ i, F.IsFS (a i) (f i))
    (ha : Tendsto (fun i c => (a i c : ℝ)) atTop (𝓝 θ)) (hanti : ∀ x, Antitone fun i => f i x)
    (hu : ∀ x, Tendsto (fun i => f i x) atTop (𝓝 (u x))) : F.IsPSH θ u :=
  isPSH_of_iInf hfin a f hf ha hanti fun x =>
    tendsto_nhds_unique (hu x) (tendsto_atTop_iInf (hanti x))

/-- A `θ`-psh function is the limit of a decreasing net of Fubini–Study functions with classes
converging to `θ`, in the limit form. -/
theorem IsPSH.exists_tendsto (h : F.IsPSH θ u) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (a : ι → Fin r → ℚ) (f : ι → K → EReal), (∀ i, F.IsFS (a i) (f i)) ∧
        Tendsto (fun i c => (a i c : ℝ)) atTop (𝓝 θ) ∧ (∀ x, Antitone fun i => f i x) ∧
          ∀ x, Tendsto (fun i => f i x) atTop (𝓝 (u x)) := by
  obtain ⟨-, -, ι, _, _, _, a, f, hf, ha, hanti, hu⟩ := h
  exact ⟨ι, inferInstance, inferInstance, inferInstance, a, f, hf, ha, hanti, fun x => by
    rw [hu x]; exact tendsto_atTop_iInf (hanti x)⟩

/-! ### The maximum principle (`prop:pg-maxprin`) -/

/-- `PSH(θ) ≠ ∅` forces `θ ≥ 0` (`prop:pg-maxprin`): the classes `aᵢ ≥ 0` converge to `θ`. -/
theorem IsPSH.nonneg (h : F.IsPSH θ u) : 0 ≤ θ := by
  obtain ⟨-, -, ι, _, _, _, a, f, hf, ha, -, -⟩ := h
  intro c
  refine ge_of_tendsto (tendsto_pi_nhds.1 ha c) (Eventually.of_forall fun i => ?_)
  have := (hf i).nonneg c
  simp only [Pi.zero_apply] at this ⊢
  exact_mod_cast this

/-- **The maximum principle** (`prop:pg-maxprin`), pointwise form: `u ≤ u(⋆)`. -/
theorem IsPSH.le_apply_triv (h : F.IsPSH θ u) (x : K) : u x ≤ u F.triv := by
  obtain ⟨-, -, ι, _, _, _, a, f, hf, -, -, hu⟩ := h
  rw [hu x, hu F.triv]
  exact iInf_mono fun i => (hf i).le_apply_triv x

/-- A `θ`-psh function is finite at `⋆`. -/
theorem IsPSH.apply_triv_ne_bot (h : F.IsPSH θ u) : u F.triv ≠ ⊥ := by
  obtain ⟨x, hx⟩ := h.exists_ne_bot
  exact ne_bot_of_le_ne_bot hx (h.le_apply_triv x)

/-- `u(⋆) < +∞`. -/
theorem IsPSH.apply_triv_ne_top (h : F.IsPSH θ u) : u F.triv ≠ ⊤ := by
  obtain ⟨-, -, ι, _, _, _, a, f, hf, -, -, hu⟩ := h
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  rw [hu F.triv]
  exact ne_top_of_le_ne_top (hf i).apply_triv_ne_top (iInf_le _ i)

/-- `θ`-psh functions take values `< +∞`. -/
theorem IsPSH.ne_top (h : F.IsPSH θ u) (x : K) : u x ≠ ⊤ :=
  ne_top_of_le_ne_top h.apply_triv_ne_top (h.le_apply_triv x)

/-- `u(⋆)` is a real number. -/
theorem IsPSH.coe_toReal_apply_triv (h : F.IsPSH θ u) :
    ((u F.triv).toReal : EReal) = u F.triv :=
  EReal.coe_toReal h.apply_triv_ne_top h.apply_triv_ne_bot

/-- A `θ`-psh function is bounded above by the real number `u(⋆)`. -/
theorem IsPSH.le_toReal_apply_triv (h : F.IsPSH θ u) (x : K) :
    u x ≤ ((u F.triv).toReal : EReal) := by
  rw [h.coe_toReal_apply_triv]
  exact h.le_apply_triv x

/-- **The maximum principle** (`prop:pg-maxprin`; BJ22 maxprin, pshconvex): a
`θ`-psh function attains its supremum at `⋆`. -/
theorem IsPSH.iSup_eq (h : F.IsPSH θ u) : ⨆ x, u x = u F.triv :=
  le_antisymm (iSup_le h.le_apply_triv) (le_iSup u F.triv)

/-! ### PSH1 and PSH2 (`thm:pg-psh2`) -/

/-- **PSH1** (`thm:pg-psh2`(1)): `𝓗(a) ⊆ PSH(a)` (constant net). -/
theorem IsFS.isPSH (h : F.IsFS a f) : F.IsPSH (fun c => (a c : ℝ)) f :=
  isPSH_of_iInf ⟨F.triv, h.apply_triv_ne_bot⟩ (ι := PUnit.{u + 1}) (fun _ => a) (fun _ => f)
    (fun _ => h) tendsto_const_nhds (fun _ _ _ _ => le_rfl) fun _ => (iInf_const).symm

theorem IsFinFS.isPSH (h : F.IsFinFS a f) : F.IsPSH (fun c => (a c : ℝ)) f :=
  h.isFS.isPSH

/-- `θ`-psh functions are decreasing limits of **finite** Fubini–Study functions
(`thm:pg-psh2`(2), forward direction), as an element of BJ22's `F̃_θ` for the families
`𝓗_fin(b)`: each approximant `fᵢ ∈ 𝓗(aᵢ)` is a decreasing limit of a sequence in `𝓗_fin(aᵢ)`
(FS5), and the diagonal lemma `IsDecrNetLimit.of_antitone_of_finite_rat` applies. -/
theorem IsPSH.isDecrNetLimit_isFinFS [CompactSpace K] (h : F.IsPSH θ u) :
    IsDecrNetLimit.{u} (fun a => {f | F.IsFinFS a f}) (fun a c => (a c : ℝ)) θ u := by
  obtain ⟨-, -, ι, _, _, _, a, f, hf, ha, hanti, hu⟩ := h
  refine IsDecrNetLimit.of_antitone_of_finite_rat (F := fun a => {f | F.IsFinFS a f})
    (ρ := fun a c => (a c : ℝ)) (fun _ g hg => IsFinFS.continuous hg)
    (fun _ g hg x => ⟨IsFinFS.ne_bot hg x, IsFinFS.ne_top hg x⟩)
    (fun _ g hg c _ => IsFinFS.add_const hg c) ha (fun i => ?_) hanti hu
  obtain ⟨g, hg, hganti, hgf⟩ := (hf i).exists_antitone_isFinFS
  exact IsDecrNetLimit.of_seq (fun _ => a i) g hg tendsto_const_nhds hganti hgf

/-- `θ`-psh functions are decreasing limits of nets of **finite** Fubini–Study functions with
classes converging to `θ` (`thm:pg-psh2`(2), forward direction). -/
theorem IsPSH.exists_isFinFS_net [CompactSpace K] (h : F.IsPSH θ u) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (b : ι → Fin r → ℚ) (g : ι → K → EReal), (∀ i, F.IsFinFS (b i) (g i)) ∧
        Tendsto (fun i c => (b i c : ℝ)) atTop (𝓝 θ) ∧ (∀ x, Antitone fun i => g i x) ∧
          ∀ x, u x = ⨅ i, g i x :=
  h.isDecrNetLimit_isFinFS

/-- **`thm:pg-psh2`(2)**: `u` is `θ`-psh iff `u ≢ -∞` and `u` is the limit of a decreasing net
`gᵦ ∈ 𝓗_fin(bᵦ)` with `bᵦ → θ`. -/
theorem isPSH_iff_exists_isFinFS [CompactSpace K] : F.IsPSH θ u ↔ (∃ x, u x ≠ ⊥) ∧
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (b : ι → Fin r → ℚ) (g : ι → K → EReal), (∀ i, F.IsFinFS (b i) (g i)) ∧
        Tendsto (fun i c => (b i c : ℝ)) atTop (𝓝 θ) ∧ (∀ x, Antitone fun i => g i x) ∧
          ∀ x, u x = ⨅ i, g i x := by
  refine ⟨fun h => ⟨h.exists_ne_bot, h.exists_isFinFS_net⟩, ?_⟩
  rintro ⟨hfin, ι, _, _, _, b, g, hg, hb, hanti, hu⟩
  exact isPSH_of_iInf hfin b g (fun i => (hg i).isFS) hb hanti hu

/-- **PSH2** (`thm:pg-psh2`(3); BJ22 psh12): if `uᵢ ∈ PSH(θᵢ)` is a decreasing net with
`θᵢ → θ` and the pointwise limit `w = infᵢ uᵢ` is not identically `-∞`, then `w ∈ PSH(θ)`. -/
theorem isPSH_of_antitone [CompactSpace K] {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] {θ : ι → Fin r → ℝ} {θ₀ : Fin r → ℝ} (hθ : Tendsto θ atTop (𝓝 θ₀))
    {u : ι → K → EReal} (hu : ∀ i, F.IsPSH (θ i) (u i)) (hanti : ∀ x, Antitone fun i => u i x)
    {w : K → EReal} (hw : ∀ x, w x = ⨅ i, u i x) (hfin : ∃ x, w x ≠ ⊥) : F.IsPSH θ₀ w := by
  refine isPSH_iff_isDecrNetLimit.2 ⟨hfin, ?_, ?_⟩
  · rw [show w = fun x => ⨅ i, u i x from funext hw]
    exact upperSemicontinuous_iInf fun i => (hu i).upperSemicontinuous
  · exact IsDecrNetLimit.of_antitone (F := fun a => {f | F.IsFS a f})
      (ρ := fun a c => (a c : ℝ)) (fun _ f hf => IsFS.continuous hf)
      (fun _ f hf => IsFS.ne_top hf) (fun _ f hf c => IsFS.add_const hf c)
      (fun _ f hf c => IsFS.max_const hf c) hθ (fun i => (hu i).2.2) hanti hw

/-- **PSH2**, limit form. -/
theorem isPSH_of_tendsto_of_antitone [CompactSpace K] {ι : Type u} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] {θ : ι → Fin r → ℝ} {θ₀ : Fin r → ℝ}
    (hθ : Tendsto θ atTop (𝓝 θ₀)) {u : ι → K → EReal} (hu : ∀ i, F.IsPSH (θ i) (u i))
    (hanti : ∀ x, Antitone fun i => u i x) {w : K → EReal}
    (hw : ∀ x, Tendsto (fun i => u i x) atTop (𝓝 (w x))) (hfin : ∃ x, w x ≠ ⊥) :
    F.IsPSH θ₀ w :=
  isPSH_of_antitone hθ hu hanti
    (fun x => tendsto_nhds_unique (hw x) (tendsto_atTop_iInf (hanti x))) hfin

/-- **PSH2** for decreasing sequences. -/
theorem isPSH_of_antitone_seq [CompactSpace K] {θ : ℕ → Fin r → ℝ} {θ₀ : Fin r → ℝ}
    (hθ : Tendsto θ atTop (𝓝 θ₀)) {u : ℕ → K → EReal} (hu : ∀ m, F.IsPSH (θ m) (u m))
    (hanti : ∀ x, Antitone fun m => u m x) {w : K → EReal} (hw : ∀ x, w x = ⨅ m, u m x)
    (hfin : ∃ x, w x ≠ ⊥) : F.IsPSH θ₀ w := by
  have hdown : Tendsto (ULift.down : ULift.{u} ℕ → ℕ) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨ULift.up b, fun a ha => ha⟩
  refine isPSH_of_antitone (ι := ULift.{u} ℕ) (hθ.comp hdown) (fun m => hu m.down)
    (fun x _ _ h => hanti x h) (fun x => ?_) hfin
  rw [hw x]
  exact (Equiv.ulift.iInf_comp (g := fun m => u m x)).symm

/-! ### Basic properties (`thm:pg-psh-basic`) -/

/-- **Adding a real constant** preserves `θ`-psh functions (`thm:pg-psh-basic`(2)). -/
theorem IsPSH.add_const (h : F.IsPSH θ u) (c : ℝ) : F.IsPSH θ fun x => u x + (c : EReal) := by
  have hfin := h.apply_triv_ne_bot
  obtain ⟨ι, _, _, _, a, f, hf, ha, hanti, hlim⟩ := h.exists_tendsto
  exact isPSH_of_tendsto ⟨F.triv, ProjBerk.ereal_add_coe_ne_bot hfin c⟩ a
    (fun i x => f i x + (c : EReal)) (fun i => (hf i).add_const c) ha
    (fun x _ _ hij => add_le_add_left (hanti x hij) _)
    fun x => ((ProjBerk.continuous_ereal_add_coe c).tendsto _).comp (hlim x)

/-- **Sums** (`thm:pg-psh-basic`(1)): `PSH(θ) + PSH(θ') ⊆ PSH(θ + θ')`, using the product net. -/
theorem IsPSH.add (h : F.IsPSH θ u) (h' : F.IsPSH θ' u') :
    F.IsPSH (θ + θ') fun x => u x + u' x := by
  have hfin := h.apply_triv_ne_bot
  have hfin' := h'.apply_triv_ne_bot
  have htop := h.ne_top
  have htop' := h'.ne_top
  obtain ⟨ι, _, _, _, a, f, hf, ha, hanti, hlim⟩ := h.exists_tendsto
  obtain ⟨ι', _, _, _, a', f', hf', ha', hanti', hlim'⟩ := h'.exists_tendsto
  have : IsDirected (ι × ι') (· ≤ ·) := isDirected_prod
  refine isPSH_of_tendsto (ι := ι × ι') ⟨F.triv, ?_⟩ (fun p => a p.1 + a' p.2)
    (fun p x => f p.1 x + f' p.2 x) (fun p => (hf p.1).add (hf' p.2)) ?_
    (fun x p q hpq => add_le_add (hanti x (Prod.le_def.1 hpq).1)
      (hanti' x (Prod.le_def.1 hpq).2)) fun x =>
      ProjBerk.tendsto_ereal_add ((hlim x).comp ProjBerk.tendsto_prod_fst_atTop)
        ((hlim' x).comp ProjBerk.tendsto_prod_snd_atTop) (htop x) (htop' x)
  · rw [Ne, EReal.add_eq_bot_iff, not_or]
    exact ⟨hfin, hfin'⟩
  · simp only [Pi.add_apply, Rat.cast_add]
    exact (ha.comp ProjBerk.tendsto_prod_fst_atTop).add
      (ha'.comp ProjBerk.tendsto_prod_snd_atTop)

/-- Positive rational multiples: `c PSH(θ) ⊆ PSH(c θ)` for `c ∈ ℚ_{>0}`. -/
theorem IsPSH.smul_rat (h : F.IsPSH θ u) {c : ℚ} (hc : 0 < c) :
    F.IsPSH ((c : ℝ) • θ) fun x => ((c : ℝ) : EReal) * u x := by
  have hfin := h.apply_triv_ne_bot
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  obtain ⟨ι, _, _, _, a, f, hf, ha, hanti, hlim⟩ := h.exists_tendsto
  refine isPSH_of_tendsto ⟨F.triv, ProjBerk.ereal_coe_mul_ne_bot hc'.le hfin⟩ (fun i => c • a i)
    (fun i x => ((c : ℝ) : EReal) * f i x) (fun i => (hf i).smul hc) ?_
    (fun x _ _ hij => ProjBerk.ereal_coe_mul_monotone hc'.le (hanti x hij))
    fun x => ProjBerk.tendsto_ereal_coe_mul (hlim x) c
  have := ha.const_smul (c : ℝ)
  refine this.congr fun i => ?_
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul]

/-- **Positive real multiples** (`thm:pg-psh-basic`(1)): `t PSH(θ) ⊆ PSH(t θ)` for `t > 0`.
After replacing `u` with `u - u(⋆) ≤ 0`, take rationals `tₘ ↑ t`: then `tₘ u ∈ PSH(tₘ θ)`
decreases to `t u`, and PSH2 applies. -/
theorem IsPSH.smul [CompactSpace K] (h : F.IsPSH θ u) {t : ℝ} (ht : 0 < t) :
    F.IsPSH (t • θ) fun x => (t : EReal) * u x := by
  set c := (u F.triv).toReal with hc_def
  set u₀ : K → EReal := fun x => u x + ((-c : ℝ) : EReal) with hu₀_def
  have h₀ : F.IsPSH θ u₀ := h.add_const (-c)
  have hu₀ : ∀ x, u₀ x ≤ 0 := fun x => by
    have := add_le_add_left (h.le_toReal_apply_triv x) ((-c : ℝ) : EReal)
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
  have htu₀ : F.IsPSH (t • θ) fun x => (t : EReal) * u₀ x := by
    refine isPSH_of_antitone_seq (θ := fun m => (q' m : ℝ) • θ) (hq'lim.smul_const θ)
      (fun m => h₀.smul_rat (hq'pos' m))
      (fun x m m' hmm' => ProjBerk.ereal_coe_mul_le_of_nonpos (hq'pos m) (hq'mono hmm') (hu₀ x))
      (fun x => tendsto_nhds_unique
        (ProjBerk.tendsto_coe_mul_ereal hq'lim ht hq'pos (h₀.ne_top x))
        (tendsto_atTop_iInf fun m m' hmm' =>
          ProjBerk.ereal_coe_mul_le_of_nonpos (hq'pos m) (hq'mono hmm') (hu₀ x)))
      ⟨F.triv, ProjBerk.ereal_coe_mul_ne_bot ht.le h₀.apply_triv_ne_bot⟩
  -- `t u = t u₀ + t c`
  convert htu₀.add_const (t * c) using 2 with x
  rw [hu₀_def, ProjBerk.ereal_coe_mul_add ht.le, ← EReal.coe_mul, add_assoc, ← EReal.coe_add,
    mul_neg, neg_add_cancel, EReal.coe_zero, add_zero]

/-- **`PSH(t θ) = t PSH(θ)`** (`thm:pg-psh-basic`(1)), pointwise form. -/
theorem isPSH_smul_iff [CompactSpace K] {t : ℝ} (ht : 0 < t) :
    F.IsPSH (t • θ) (fun x => (t : EReal) * u x) ↔ F.IsPSH θ u := by
  refine ⟨fun h => ?_, fun h => h.smul ht⟩
  have h' := h.smul (inv_pos.2 ht)
  rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h'
  simpa only [ProjBerk.ereal_inv_mul_mul ht.ne'] using h'

/-- **`PSH(t θ) = t PSH(θ)`** (`thm:pg-psh-basic`(1)), as an equality of sets. -/
theorem setOf_isPSH_smul [CompactSpace K] {t : ℝ} (ht : 0 < t) :
    {w : K → EReal | F.IsPSH (t • θ) w} =
      (fun u x => (t : EReal) * u x) '' {u | F.IsPSH θ u} := by
  ext w
  constructor
  · intro hw
    refine ⟨fun x => ((t⁻¹ : ℝ) : EReal) * w x, ?_, funext fun x => ?_⟩
    · have h' := IsPSH.smul (u := w) hw (inv_pos.2 ht)
      rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h'
    · exact ProjBerk.ereal_coe_mul_inv_mul ht.ne' (w x)
  · rintro ⟨u, hu, rfl⟩
    exact IsPSH.smul hu ht

/-- **Maxima** (`thm:pg-psh-basic`(2); BJ22 twopsh): `max(u, u') ∈ PSH(θ)` for
`u, u' ∈ PSH(θ)`. On the product net, both approximants are Fubini–Study functions of the
coordinatewise maximum of their classes (FS2), which converges to `θ`. -/
theorem IsPSH.max (h : F.IsPSH θ u) (h' : F.IsPSH θ u') :
    F.IsPSH θ fun x => Max.max (u x) (u' x) := by
  have hfin := h.apply_triv_ne_bot
  obtain ⟨ι, _, _, _, a, f, hf, ha, hanti, hlim⟩ := h.exists_tendsto
  obtain ⟨ι', _, _, _, a', f', hf', ha', hanti', hlim'⟩ := h'.exists_tendsto
  have : IsDirected (ι × ι') (· ≤ ·) := isDirected_prod
  refine isPSH_of_tendsto (ι := ι × ι') ⟨F.triv, ne_bot_of_le_ne_bot hfin (le_max_left _ _)⟩
    (fun p c => Max.max (a p.1 c) (a' p.2 c)) (fun p x => Max.max (f p.1 x) (f' p.2 x))
    (fun p => ((hf p.1).mono fun c => le_max_left _ _).max
      ((hf' p.2).mono fun c => le_max_right _ _)) ?_
    (fun x p q hpq => max_le_max (hanti x (Prod.le_def.1 hpq).1)
      (hanti' x (Prod.le_def.1 hpq).2))
    fun x => ((hlim x).comp ProjBerk.tendsto_prod_fst_atTop).max
      ((hlim' x).comp ProjBerk.tendsto_prod_snd_atTop)
  refine tendsto_pi_nhds.2 fun c => ?_
  have := ((tendsto_pi_nhds.1 ha c).comp ProjBerk.tendsto_prod_fst_atTop).max
    ((tendsto_pi_nhds.1 ha' c).comp ProjBerk.tendsto_prod_snd_atTop)
  rw [max_self] at this
  refine this.congr fun p => ?_
  simp only [Function.comp_apply, Rat.cast_max]

/-- **Finite maxima** (`thm:pg-psh-basic`(2)). -/
theorem isPSH_finset_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {w : ι → K → EReal}
    (hw : ∀ i ∈ s, F.IsPSH θ (w i)) : F.IsPSH θ fun x => s.sup' hs fun i => w i x := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa only [Finset.sup'_singleton] using hw a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    simp only [Finset.sup'_cons hs]
    exact (hw a (Finset.mem_cons_self a s)).max
      (ih fun i hi => hw i (Finset.mem_cons_of_mem hi))

/-- **Constants** are `θ`-psh for every `θ ≥ 0` (`thm:pg-psh-basic`(2)): they lie in `𝓗(aₙ)`
for rational vectors `aₙ > θ` converging to `θ`. -/
theorem isPSH_const (hθ : 0 ≤ θ) (c : ℝ) : F.IsPSH θ fun _ => (c : EReal) := by
  obtain ⟨a, hθa, ha⟩ := exists_seq_rat_vec_gt_tendsto θ
  have ha0 : ∀ n, 0 ≤ a n := fun n j => by
    have : (0 : ℝ) < a n j := (hθ j).trans_lt (hθa n j)
    exact_mod_cast this.le
  have hdown : Tendsto (ULift.down : ULift.{u} ℕ → ℕ) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨ULift.up b, fun a ha => ha⟩
  exact isPSH_of_iInf ⟨F.triv, EReal.coe_ne_bot c⟩ (ι := ULift.{u} ℕ) (fun n => a n.down)
    (fun _ _ => (c : EReal)) (fun n => F.isFS_const (ha0 n.down) c) (ha.comp hdown)
    (fun _ _ _ _ => le_rfl) fun _ => iInf_const.symm

/-- **Monotonicity in the class** (`thm:pg-psh-basic`(3)): `PSH(θ) ⊆ PSH(θ')` for `θ ≤ θ'`
(coordinatewise), by adding the function `0`, which is `(θ' - θ)`-psh since `θ' - θ ≥ 0`. -/
theorem IsPSH.mono_class (h : F.IsPSH θ u) (hθθ' : θ ≤ θ') : F.IsPSH θ' u := by
  have h' := h.add (isPSH_const (F := F) (sub_nonneg.2 hθθ') 0)
  rw [add_sub_cancel] at h'
  simpa only [EReal.coe_zero, add_zero] using h'

end FSSystem

end EnvelopeProperty
