/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.Scaling
import EnvelopeProperty.Global.Legendre

/-!
# The homogeneous theory on a model

Let `𝒳 = (K, S, z)` be an integral multiprojective model (`EnvelopeProperty.MultiModel`,
`def:gl-model`). This file implements the blueprint nodes `thm:gl-homog-fs`, `cor:gl-pshhom`,
`lem:gl-action-convex` and `thm:gl-homog-decomposition` of the global chapter `global.tex` of the
formalization of Fang–Han–Xia, *The envelope property for unibranch projective varieties*
(FHX, revision `832e086`, `prop:BJ-package`(3), `eq:Legendre-reconstruction`), following
Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field* (BJ22),
`thm:homogFS`, `cor:pshhom`, `lem:actionconvex`, `thm:homogpsh` (§§6.2–6.3). The scaling action,
homogenization and Legendre slices are in `EnvelopeProperty.Global.Scaling`, the one-variable
Legendre formula `lem:gl-legendre` in `EnvelopeProperty.Global.Legendre`. Nothing here depends on
BJ22 Theorem 6.21 or its consequences.

## Homogenization of Fubini–Study functions (`thm:gl-homog-fs`)

`MultiModel.IsRatFS X a φ` (`𝓗^gf_ℚ`): `φ = m⁻¹ max_t (log |f_t| + λ_t)` with rational weights
`λ_t` and sections not all zero. `MultiModel.IsRatFS.isHomFS_homogenization`: if `φ(⋆) ≥ 0`, then
`φ̂ ∈ 𝓗_hom(𝒳, a)`; otherwise `φ̂ ≡ -∞` (`MultiModel.homogenization_eq_bot`). The proof is the
blueprint's: `m φ̂(v) = inf_{s > 0} max_t (log |f_t|(v) + s λ_t)` is the Legendre value
`EnvelopeProperty.legendreMax` (`lem:gl-legendre`, entries `-∞` allowed), a maximum of the
`log |f_t|` (`λ_t ≥ 0`) and of the convex combinations `w log |f_l| + (1 - w) log |f_t|`
(`λ_t > 0 > λ_l`, `w = λ_t / (λ_t - λ_l) = n / b ∈ ℚ`), i.e. of `b⁻¹ log |f_l^n f_t^{b - n}|`; each
of these is a homogeneous FS datum of class `a` (with its own `m b`), and their maximum is one
(`MultiModel.FSData.exists_eval_finset_sup`).

## Homogeneous psh functions (`cor:gl-pshhom`)

* `MultiModel.IsPSH.exists_isRatFS_net`: every `u ∈ PSH(𝒳, θ)` (any `θ ∈ ℝ^r`) is the limit of a
  decreasing net of FS functions with **rational** weights, classes `a_α → θ`. The real weights of
  a defining net `φ_α` are rounded up to rationals within `1/(n+1)`; the net
  `φ_{α,n} ∈ [φ_α + 1/(n+2), φ_α + 1/(n+1)]` is decreasing for the order on `ι × ℕ` given by
  `(α, n) ≤ (β, k) ↔ (α, n) = (β, k) ∨ (α ≤ β ∧ n < k)` (`EnvelopeProperty.RatRoundIndex`). No
  diagonal lemma (and no semiampleness) is needed.
* `MultiModel.IsPSH.isPSHHom_homogenization`, `MultiModel.IsPSH.exists_isHomFS_net`: if
  `u(⋆) ≥ 0`, then `û ∈ PSH_hom(𝒳, θ)` and `û` is the limit of a decreasing net in
  `𝓗_hom(𝒳, a_α)`, `a_α → θ`; `MultiModel.IsPSH.homogenization_eq_bot`: `û ≡ -∞` if `u(⋆) < 0`.

## Convexity along rays (`lem:gl-action-convex`)

For `u ∈ PSH(𝒳, θ)` and `v ∈ 𝒳^an`, `g(t) = (t · u)(v)` (`MultiModel.rayFun`):
`MultiModel.IsPSH.scaleFun_le` (`g(t) ≤ t u(⋆)`), `MultiModel.IsPSH.scaleFun_convex` (convexity
inequality in `[-∞, ∞)`), `MultiModel.IsPSH.scaleFun_eq_bot_or_ne_bot` (`g ≡ -∞` or `g` is
finite) and `MultiModel.IsPSH.convexOn_rayFun` (`g` is a finite convex function on `(0, ∞)` when
`u(v) ≠ -∞`).

## Homogeneous decomposition (`thm:gl-homog-decomposition`)

For `u ∈ PSH(𝒳, θ)` and `b = u(⋆)`: `MultiModel.IsPSH.isPSHHom_legendreSlice` (`û_λ ∈ PSH_hom` for
`λ < b`), `MultiModel.legendreSlice_antitone`, `MultiModel.legendreSlice_mono` (in `Scaling`), and
`MultiModel.IsPSH.eq_iSup_legendreSlice`: `u = sup_{λ < b} (û_λ + λ)` pointwise. The proof avoids
Fenchel duality: a subgradient `c ≤ b` of the finite convex function `g` at `t = 1`
(`EnvelopeProperty.exists_subgradient_one_of_convexOn_Ioi`, the right derivative) gives
`û_{c - ε}(v) + (c - ε) ≥ g(1) - ε = u(v) - ε`.

## Deviations from the blueprint

* `cor:gl-pshhom` is proved for every `θ ∈ ℝ^r` with the rounding net above, exactly as in the
  blueprint's proof; the rational-weight regularization `MultiModel.IsPSH.exists_isRatFS_net` is
  exported separately since `thm:gl-comparison` uses it.
* The pointwise decomposition `thm:gl-homog-decomposition` is proved with a subgradient at `t = 1`
  instead of the Fenchel–Moreau theorem; the restriction to `λ < b` follows from `c ≤ b`.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### The rounding index -/

/-- The index set `ι × ℕ` with the order `(α, n) ≤ (β, k) ↔ (α, n) = (β, k) ∨ (α ≤ β ∧ n < k)`,
used to round real weights of a decreasing net of Fubini–Study functions to rational ones without
a diagonal argument (proof of `cor:gl-pshhom`). -/
def RatRoundIndex (ι : Type*) : Type _ := ι × ℕ

namespace RatRoundIndex

variable {ι : Type*}

instance [Preorder ι] : Preorder (RatRoundIndex ι) where
  le p q := p = q ∨ ((p : ι × ℕ).1 ≤ (q : ι × ℕ).1 ∧ (p : ι × ℕ).2 < (q : ι × ℕ).2)
  le_refl _ := Or.inl rfl
  le_trans p q w := by
    rintro (rfl | ⟨h₁, h₂⟩) (rfl | ⟨h₃, h₄⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨h₃, h₄⟩
    · exact Or.inr ⟨h₁, h₂⟩
    · exact Or.inr ⟨h₁.trans h₃, h₂.trans h₄⟩

theorem le_def [Preorder ι] {p q : RatRoundIndex ι} :
    p ≤ q ↔ p = q ∨ ((p : ι × ℕ).1 ≤ (q : ι × ℕ).1 ∧ (p : ι × ℕ).2 < (q : ι × ℕ).2) :=
  Iff.rfl

instance [Preorder ι] [IsDirected ι (· ≤ ·)] : IsDirected (RatRoundIndex ι) (· ≤ ·) where
  directed p q := by
    obtain ⟨c, hpc, hqc⟩ := directed_of (· ≤ ·) (p : ι × ℕ).1 (q : ι × ℕ).1
    refine ⟨(show ι × ℕ from (c, max (p : ι × ℕ).2 (q : ι × ℕ).2 + 1)), Or.inr ⟨hpc, ?_⟩,
      Or.inr ⟨hqc, ?_⟩⟩
    · change (p : ι × ℕ).2 < max (p : ι × ℕ).2 (q : ι × ℕ).2 + 1
      omega
    · change (q : ι × ℕ).2 < max (p : ι × ℕ).2 (q : ι × ℕ).2 + 1
      omega

instance [Nonempty ι] : Nonempty (RatRoundIndex ι) :=
  ⟨(show ι × ℕ from (Classical.arbitrary ι, 0))⟩

/-- The projection `ι × ℕ → ι` tends to `atTop`. -/
theorem tendsto_fst [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] :
    Tendsto (fun p : RatRoundIndex ι => (p : ι × ℕ).1) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun α₀ => ⟨(show ι × ℕ from (α₀, 0)), fun p hp => ?_⟩
  rcases hp with rfl | ⟨h, -⟩
  · exact le_rfl
  · exact h

end RatRoundIndex

/-! ### A subgradient of a convex function -/

/-- A convex function on `(0, ∞)` has a subgradient at `1` (its right derivative). -/
theorem exists_subgradient_one_of_convexOn_Ioi {G : ℝ → ℝ} (hG : ConvexOn ℝ (Ioi 0) G) :
    ∃ c : ℝ, ∀ t : ℝ, 0 < t → G 1 + c * (t - 1) ≤ G t := by
  have h1 : (1 : ℝ) ∈ interior (Ioi (0 : ℝ)) := by
    rw [isOpen_Ioi.interior_eq]
    exact mem_Ioi.2 zero_lt_one
  refine ⟨derivWithin G (Ioi (1 : ℝ)) 1, fun t ht => ?_⟩
  rcases lt_trichotomy t 1 with hlt | rfl | hgt
  · have h₁ := hG.slope_le_leftDeriv_of_mem_interior ht h1 hlt
    have h₂ := hG.leftDeriv_le_rightDeriv_of_mem_interior h1
    rw [slope_def_field] at h₁
    have h₃ : (G 1 - G t) / (1 - t) ≤ derivWithin G (Ioi 1) 1 := h₁.trans h₂
    rw [div_le_iff₀ (by linarith)] at h₃
    nlinarith
  · simp
  · have h₁ := hG.rightDeriv_le_slope_of_mem_interior h1 (mem_Ioi.2 ht) hgt
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h₁
    linarith

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  (X : MultiModel k K r)

/-! ### Fubini–Study functions with rational weights -/

/-- **Fubini–Study functions with rational weights** (`𝓗^gf_ℚ(𝒳, a)`, BJ22 `defi:FS`):
`φ = m⁻¹ max_t (log |f_t| + λ_t)` with `λ_t ∈ ℚ` and sections `f_t ∈ R_{m a}` not all zero. -/
def IsRatFS (a : Fin r → ℚ) (φ : X.an → EReal) : Prop :=
  ∃ D : X.FSData a, D.IsRational ∧ (∃ p ∈ D.terms, p.1 ≠ 0) ∧ ∀ v, φ v = D.eval v

variable {X} {a : Fin r → ℚ} {φ : X.an → EReal}

theorem IsRatFS.isFS (h : X.IsRatFS a φ) : X.IsFS a φ := by
  obtain ⟨D, -, hD, hφ⟩ := h
  exact ⟨D, hD, hφ⟩

theorem IsHomFS.isRatFS (h : X.IsHomFS a φ) : X.IsRatFS a φ := by
  obtain ⟨D, hD0, hD, hφ⟩ := h
  exact ⟨D, fun p hp => ⟨0, by rw [hD0 p hp, Rat.cast_zero]⟩, hD, hφ⟩

theorem IsFinFS.isRatFS (h : X.IsFinFS a φ) : X.IsRatFS a φ := by
  obtain ⟨D, hDr, hD, hφ⟩ := h
  obtain ⟨p, hp, hne⟩ := hD X.triv
  refine ⟨D, hDr, ⟨p, hp, fun h0 => hne ?_⟩, hφ⟩
  rw [h0, secAbs_zero]

/-! ### Folding homogeneous data -/

namespace FSData

/-- The data `(m, m a, ∅)`, evaluating to `-∞`. -/
def empty (D : X.FSData a) : X.FSData a where
  m := D.m
  m_pos := D.m_pos
  deg := D.deg
  deg_eq := D.deg_eq
  terms := ∅
  mem_sections _ h := absurd h (Finset.notMem_empty _)

theorem eval_empty (D : X.FSData a) (v : X.an) : D.empty.eval v = ⊥ := by
  rw [eval_def]
  change _ * (∅ : Finset (K × ℝ)).sup _ = ⊥
  rw [Finset.sup_empty]
  exact EReal.coe_mul_bot_of_pos D.inv_m_pos

/-- The maximum of two data with zero weights has zero weights. -/
theorem weights_zero_sup {D D' : X.FSData a} (hD : ∀ p ∈ D.terms, p.2 = 0)
    (hD' : ∀ p ∈ D'.terms, p.2 = 0) : ∀ p ∈ (D.sup D').terms, p.2 = 0 := by
  classical
  intro p hp
  rcases Finset.mem_union.1 hp with h | h
  · obtain ⟨p₀, hp₀, rfl⟩ := mem_scaleTerms.1 h
    simp [hD p₀ hp₀]
  · obtain ⟨p₀, hp₀, rfl⟩ := mem_scaleTerms.1 h
    simp [hD' p₀ hp₀]

/-- A finite maximum of homogeneous FS data of class `a` is a homogeneous FS datum of class `a`
(given one datum `D₀` of class `a` to start from). -/
theorem exists_eval_finset_sup (D₀ : X.FSData a) {ι : Type*} (E : Finset ι)
    (g : ι → X.an → EReal)
    (hg : ∀ e ∈ E, ∃ D : X.FSData a, (∀ p ∈ D.terms, p.2 = 0) ∧ ∀ v, D.eval v = g e v) :
    ∃ D : X.FSData a, (∀ p ∈ D.terms, p.2 = 0) ∧ ∀ v, D.eval v = E.sup fun e => g e v := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    exact ⟨D₀.empty, fun p hp => absurd hp (Finset.notMem_empty _), fun v => by
      rw [eval_empty, Finset.sup_empty]⟩
  | insert e E he ih =>
    obtain ⟨D', hD'0, hD'⟩ := ih fun e' he' => hg e' (Finset.mem_insert_of_mem he')
    obtain ⟨De, hDe0, hDe⟩ := hg e (Finset.mem_insert_self e E)
    refine ⟨De.sup D', weights_zero_sup hDe0 hD'0, fun v => ?_⟩
    rw [eval_sup, hDe, hD', Finset.sup_insert]

/-- The single-term datum `(m, m a, {(f, 0)})` of class `a`, for `f ∈ R_{m a}`. -/
def termZero (D : X.FSData a) {f : K} (hf : f ∈ X.sections D.deg) : X.FSData a where
  m := D.m
  m_pos := D.m_pos
  deg := D.deg
  deg_eq := D.deg_eq
  terms := {(f, 0)}
  mem_sections p hp := by
    rw [Finset.mem_singleton] at hp
    subst hp
    exact hf

theorem eval_termZero (D : X.FSData a) {f : K} (hf : f ∈ X.sections D.deg) (v : X.an) :
    (D.termZero hf).eval v = (((D.m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 D.deg f := by
  rw [eval_def]
  change _ * ({(f, 0)} : Finset (K × ℝ)).sup (fun p => X.termVal D.deg p v) = _
  rw [Finset.sup_singleton, termVal_def, EReal.coe_zero, add_zero]
  rfl

/-- The single-term datum `(m b, b (m a), {(g, 0)})` of class `a`, for `g ∈ R_{b m a}`. -/
def powZero (D : X.FSData a) {b : ℕ} (hb : 0 < b) {g : K} (hg : g ∈ X.sections (b • D.deg)) :
    X.FSData a where
  m := D.m * b
  m_pos := Nat.mul_pos D.m_pos hb
  deg := b • D.deg
  deg_eq c := by
    rw [intCast_nsmul_apply, D.deg_eq, Nat.cast_mul]
    ring
  terms := {(g, 0)}
  mem_sections p hp := by
    rw [Finset.mem_singleton] at hp
    subst hp
    exact hg

theorem eval_powZero (D : X.FSData a) {b : ℕ} (hb : 0 < b) {g : K}
    (hg : g ∈ X.sections (b • D.deg)) (v : X.an) :
    (D.powZero hb hg).eval v =
      ((((D.m : ℝ) * b)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 (b • D.deg) g := by
  rw [eval_def]
  change ((((D.m * b : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
    ({(g, 0)} : Finset (K × ℝ)).sup (fun p => X.termVal (b • D.deg) p v) = _
  rw [Finset.sup_singleton, termVal_def, EReal.coe_zero, add_zero, Nat.cast_mul]

end FSData

/-! ### Homogenization of Fubini–Study functions (`thm:gl-homog-fs`) -/

/-- The homogenization of an FS datum is `m⁻¹` times the Legendre value of the
`log |f_t|(v)` with slopes `λ_t` (`lem:gl-legendre`). -/
theorem FSData.homogenization_eval (D : X.FSData a) (v : X.an) :
    X.homogenization D.eval v = (((D.m : ℝ)⁻¹ : ℝ) : EReal) *
      legendreMax D.terms Prod.snd (fun p => X.logSecAbs v.1 D.deg p.1) := by
  have hs : ∀ (t : ℝ) (ht : 0 < t), X.scaleFun t ht D.eval v = (((D.m : ℝ)⁻¹ : ℝ) : EReal) *
      D.terms.sup (fun p => X.logSecAbs v.1 D.deg p.1 + ((t * p.2 : ℝ) : EReal)) := by
    intro t ht
    rw [FSData.scaleFun_eval, FSData.eval_reweight]
    rfl
  calc X.homogenization D.eval v
      = ⨅ (t : ℝ) (_ : 0 < t), (((D.m : ℝ)⁻¹ : ℝ) : EReal) *
          D.terms.sup (fun p => X.logSecAbs v.1 D.deg p.1 + ((t * p.2 : ℝ) : EReal)) :=
        iInf_congr fun t => iInf_congr fun ht => hs t ht
    _ = (((D.m : ℝ)⁻¹ : ℝ) : EReal) * ⨅ (t : ℝ) (_ : 0 < t),
          D.terms.sup (fun p => X.logSecAbs v.1 D.deg p.1 + ((t * p.2 : ℝ) : EReal)) := by
        rw [ereal_coe_mul_iInf D.inv_m_pos]
        exact iInf_congr fun t => (ereal_coe_mul_iInf D.inv_m_pos _).symm
    _ = _ := by
        rw [iInf_sup_add_mul_eq_legendreMax D.terms Prod.snd _
          fun p _ => logSecAbs_ne_top _ _ _]

/-- The pair terms of the Legendre value are homogeneous FS functions of class `a`: for
`λ_t > 0 > λ_l` rational, `w = λ_t / (λ_t - λ_l) = n / b`, and
`m⁻¹ (w log |f_l| + (1 - w) log |f_t|) = (m b)⁻¹ log |f_l^n f_t^{b - n}|`. -/
theorem FSData.exists_pairTerm (D : X.FSData a) (hDr : D.IsRational) {q : (K × ℝ) × (K × ℝ)}
    (hq₁ : q.1 ∈ D.terms) (hq₂ : q.2 ∈ D.terms) (hpos : 0 < q.1.2) (hneg : q.2.2 < 0) :
    ∃ E : X.FSData a, (∀ p ∈ E.terms, p.2 = 0) ∧ ∀ v, E.eval v =
      (((D.m : ℝ)⁻¹ : ℝ) : EReal) *
        legendrePairTerm Prod.snd (fun p => X.logSecAbs v.1 D.deg p.1) q := by
  obtain ⟨r₁, hr₁⟩ := hDr q.1 hq₁
  obtain ⟨r₂, hr₂⟩ := hDr q.2 hq₂
  obtain ⟨hw0, hw'0, hsum, -⟩ := legendre_weights_pos hpos hneg
  set w : ℚ := r₁ / (r₁ - r₂) with hw
  have hwr : (w : ℝ) = q.1.2 / (q.1.2 - q.2.2) := by
    rw [hw, hr₁, hr₂]
    push_cast
    rfl
  set b : ℕ := w.den with hb
  set n : ℕ := w.num.toNat with hn
  have hbpos : 0 < b := w.den_pos
  have hwpos : 0 < w := by exact_mod_cast (hwr ▸ hw0 : (0 : ℝ) < w)
  have hnum : ((n : ℤ) : ℤ) = w.num := Int.toNat_of_nonneg (Rat.num_nonneg.2 hwpos.le)
  have hwnb : (w : ℝ) = (n : ℝ) / (b : ℝ) := by
    rw [Rat.cast_def, ← hnum]
    push_cast
    rfl
  have hw1 : (w : ℝ) < 1 := by
    rw [hwr]
    linarith
  have hnb : n ≤ b := by
    have : (n : ℝ) / b < 1 := hwnb ▸ hw1
    rw [div_lt_one (by exact_mod_cast hbpos)] at this
    exact_mod_cast this.le
  have hdeg : n • D.deg + (b - n) • D.deg = b • D.deg := by
    rw [← add_nsmul, Nat.add_sub_cancel' hnb]
  have hg : q.2.1 ^ n * q.1.1 ^ (b - n) ∈ X.sections (b • D.deg) := by
    rw [← hdeg]
    exact mul_mem_sections (pow_mem_sections (D.mem_sections _ hq₂) n)
      (pow_mem_sections (D.mem_sections _ hq₁) (b - n))
  refine ⟨D.powZero hbpos hg, fun p hp => ?_, fun v => ?_⟩
  · change p ∈ ({(q.2.1 ^ n * q.1.1 ^ (b - n), 0)} : Finset (K × ℝ)) at hp
    rw [Finset.mem_singleton] at hp
    rw [hp]
  · rw [FSData.eval_powZero, ← hdeg,
      logSecAbs_mul v.2.2 (pow_mem_sections (D.mem_sections _ hq₂) n)
        (pow_mem_sections (D.mem_sections _ hq₁) (b - n)),
      logSecAbs_pow v.2.2 (D.mem_sections _ hq₂), logSecAbs_pow v.2.2 (D.mem_sections _ hq₁),
      legendrePairTerm, ← EReal.coe_natCast, ← EReal.coe_natCast]
    have hm : (0 : ℝ) < D.m := by exact_mod_cast D.m_pos
    have hb' : (0 : ℝ) < b := by exact_mod_cast hbpos
    rw [ProjBerk.ereal_coe_mul_add (by positivity), ProjBerk.ereal_coe_mul_add (by positivity),
      ProjBerk.ereal_coe_mul_coe_mul, ProjBerk.ereal_coe_mul_coe_mul,
      ProjBerk.ereal_coe_mul_coe_mul, ProjBerk.ereal_coe_mul_coe_mul]
    have h₁ : ((D.m : ℝ) * b)⁻¹ * (n : ℝ) = (D.m : ℝ)⁻¹ * (q.1.2 / (q.1.2 - q.2.2)) := by
      rw [← hwr, hwnb]
      field_simp
    have h₂ : ((D.m : ℝ) * b)⁻¹ * ((b - n : ℕ) : ℝ) =
        (D.m : ℝ)⁻¹ * (-q.2.2 / (q.1.2 - q.2.2)) := by
      have : -q.2.2 / (q.1.2 - q.2.2) = 1 - (w : ℝ) := by rw [hwr]; linarith
      rw [this, hwnb, Nat.cast_sub hnb]
      field_simp
    rw [h₁, h₂]

/-- **`thm:gl-homog-fs`** (BJ22 `thm:homogFS`): if `φ ∈ 𝓗^gf_ℚ(𝒳, a)` has `φ(⋆) ≥ 0`, its
homogenization `φ̂` lies in `𝓗_hom(𝒳, a)`. -/
theorem IsRatFS.isHomFS_homogenization (h : X.IsRatFS a φ) (h0 : 0 ≤ φ X.triv) :
    X.IsHomFS a (X.homogenization φ) := by
  classical
  obtain ⟨D, hDr, -, hφ⟩ := h
  have hφD : φ = D.eval := funext hφ
  subst hφD
  set c : EReal := (((D.m : ℝ)⁻¹ : ℝ) : EReal) with hc
  set y : X.an → K × ℝ → EReal := fun v p => X.logSecAbs v.1 D.deg p.1 with hy
  set A := D.terms.filter fun p => 0 ≤ p.2 with hA
  set B := (D.terms ×ˢ D.terms).filter fun q => 0 < q.1.2 ∧ q.2.2 < 0 with hB
  obtain ⟨D₁, hD₁0, hD₁⟩ := FSData.exists_eval_finset_sup D A (fun p v => c * y v p)
    fun p hp => ⟨D.termZero (D.mem_sections p (Finset.mem_filter.1 hp).1),
      fun p' hp' => by
        change p' ∈ ({(p.1, 0)} : Finset (K × ℝ)) at hp'
        rw [Finset.mem_singleton] at hp'
        rw [hp'],
      fun v => FSData.eval_termZero _ _ v⟩
  obtain ⟨D₂, hD₂0, hD₂⟩ := FSData.exists_eval_finset_sup D B
    (fun q v => c * legendrePairTerm Prod.snd (y v) q) fun q hq => by
      obtain ⟨hq, hpos, hneg⟩ := Finset.mem_filter.1 hq
      obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.1 hq
      exact D.exists_pairTerm hDr hq₁ hq₂ hpos hneg
  have heval : ∀ v, (D₁.sup D₂).eval v = X.homogenization D.eval v := by
    intro v
    rw [FSData.eval_sup, hD₁, hD₂, FSData.homogenization_eval, legendreMax,
      ProjBerk.ereal_coe_mul_max D.inv_m_pos.le, ProjBerk.ereal_coe_mul_finset_sup D.inv_m_pos,
      ProjBerk.ereal_coe_mul_finset_sup D.inv_m_pos]
  refine ⟨D₁.sup D₂, FSData.weights_zero_sup hD₁0 hD₂0, ?_, fun v => (heval v).symm⟩
  rw [← FSData.eval_triv_ne_bot_iff, heval,
    homogenization_triv_of_nonneg h0 (D.eval_ne_top _)]
  exact EReal.zero_ne_bot

/-! ### Homogeneous psh functions (`cor:gl-pshhom`) -/

variable {θ : Fin r → ℝ} {u : X.an → EReal}

/-- **Rational regularization** (proof of `cor:gl-pshhom`, used in `thm:gl-comparison`): every
`u ∈ PSH(𝒳, θ)`, `θ ∈ ℝ^r` arbitrary, is the limit of a decreasing net of Fubini–Study functions
with rational weights, with classes `a_α → θ`. -/
theorem IsPSH.exists_isRatFS_net (h : X.IsPSH θ u) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (a : ι → Fin r → ℚ) (f : ι → X.an → EReal), (∀ i, X.IsRatFS (a i) (f i)) ∧
        Tendsto (fun i c => (a i c : ℝ)) atTop (𝓝 θ) ∧ (∀ v, Antitone fun i => f i v) ∧
          ∀ v, u v = ⨅ i, f i v := by
  classical
  obtain ⟨-, -, ι, _, _, _, a, f, hf, ha, hanti, hu⟩ := h
  choose D hD0 hfD using hf
  have hδ : ∀ N : ℕ, (1 : ℝ) / ((N : ℝ) + 2) < 1 / ((N : ℝ) + 1) := fun N =>
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  choose q hq using fun (i : ι) (N : ℕ) (x : ℝ) => exists_rat_btwn
    (show x + (D i).m * (1 / ((N : ℝ) + 2)) < x + (D i).m * (1 / ((N : ℝ) + 1)) by
      have hm : (0 : ℝ) < (D i).m := by exact_mod_cast (D i).m_pos
      have := mul_lt_mul_of_pos_left (hδ N) hm
      linarith)
  set R : ι → ℕ → X.an → EReal := fun i N => ((D i).reweight fun x => (q i N x : ℝ)).eval
    with hR
  have hlow : ∀ i (N : ℕ) v, f i v + ((1 / ((N : ℝ) + 2) : ℝ) : EReal) ≤ R i N v := fun i N v => by
    rw [hfD]
    exact (D i).le_eval_reweight (fun t _ => (hq i N t.2).1.le) v
  have hup : ∀ i (N : ℕ) v, R i N v ≤ f i v + ((1 / ((N : ℝ) + 1) : ℝ) : EReal) := fun i N v => by
    rw [hfD]
    exact (D i).eval_reweight_le (fun t _ => (hq i N t.2).2.le) v
  refine ⟨RatRoundIndex ι, inferInstance, inferInstance, inferInstance,
    fun p => a (p : ι × ℕ).1, fun p => R (p : ι × ℕ).1 (p : ι × ℕ).2, fun p => ?_, ?_,
    fun v p p' hpp' => ?_, fun v => ?_⟩
  · obtain ⟨t, ht, ht0⟩ := hD0 (p : ι × ℕ).1
    exact ⟨_, (D _).isRational_reweight fun t _ => ⟨q _ _ t.2, rfl⟩,
      ⟨(t.1, (q (p : ι × ℕ).1 (p : ι × ℕ).2 t.2 : ℝ)), Finset.mem_image_of_mem
        (fun t => (t.1, (q (p : ι × ℕ).1 (p : ι × ℕ).2 t.2 : ℝ))) ht, ht0⟩, fun _ => rfl⟩
  · exact ha.comp RatRoundIndex.tendsto_fst
  · rcases hpp' with rfl | ⟨h₁, h₂⟩
    · exact le_rfl
    · refine (hup _ _ v).trans (le_trans ?_ (hlow _ _ v))
      refine add_le_add (hanti v h₁) (EReal.coe_le_coe_iff.2 ?_)
      have : ((p : ι × ℕ).2 : ℝ) + 1 ≤ ((p' : ι × ℕ).2 : ℝ) := by exact_mod_cast h₂
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · refine le_antisymm (le_iInf fun p => ?_) (ProjBerk.ereal_le_of_forall_pos_le_add fun ε hε => ?_)
    · rw [hu v]
      have hnn : (0 : ℝ) ≤ 1 / (((p : ι × ℕ).2 : ℝ) + 2) :=
        one_div_nonneg.2 (by linarith [Nat.cast_nonneg (α := ℝ) (p : ι × ℕ).2])
      exact (iInf_le _ _).trans ((ereal_le_add_coe hnn _).trans (hlow _ _ v))
    · obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      calc ⨅ p : RatRoundIndex ι, R (p : ι × ℕ).1 (p : ι × ℕ).2 v
          ≤ ⨅ i, R i N v := le_iInf fun i => iInf_le (fun p : RatRoundIndex ι =>
            R (p : ι × ℕ).1 (p : ι × ℕ).2 v) (show ι × ℕ from (i, N))
        _ ≤ ⨅ i, (f i v + ((1 / ((N : ℝ) + 1) : ℝ) : EReal)) := iInf_mono fun i => hup i N v
        _ = u v + ((1 / ((N : ℝ) + 1) : ℝ) : EReal) := by rw [← ereal_iInf_add_coe, hu v]
        _ ≤ u v + (ε : EReal) := add_le_add le_rfl (EReal.coe_le_coe_iff.2 hN.le)

/-- **`cor:gl-pshhom`(ii)** (BJ22 `cor:pshhom`(ii)): if `u ∈ PSH(𝒳, θ)` has `u(⋆) ≥ 0`, then `û` is
the limit of a decreasing net `ψ_α ∈ 𝓗_hom(𝒳, a_α)` with `a_α → θ`. -/
theorem IsPSH.exists_isHomFS_net (h : X.IsPSH θ u) (h0 : 0 ≤ u X.triv) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (a : ι → Fin r → ℚ) (f : ι → X.an → EReal), (∀ i, X.IsHomFS (a i) (f i)) ∧
        Tendsto (fun i c => (a i c : ℝ)) atTop (𝓝 θ) ∧ (∀ v, Antitone fun i => f i v) ∧
          ∀ v, X.homogenization u v = ⨅ i, f i v := by
  obtain ⟨ι, _, _, _, a, f, hf, ha, hanti, hu⟩ := h.exists_isRatFS_net
  refine ⟨ι, inferInstance, inferInstance, inferInstance, a, fun i => X.homogenization (f i),
    fun i => (hf i).isHomFS_homogenization (h0.trans ?_), ha,
    fun v i j hij => homogenization_mono (fun w => hanti w hij) v, fun v => ?_⟩
  · rw [hu X.triv]
    exact iInf_le _ i
  · rw [show u = fun w => ⨅ i, f i w from funext hu, homogenization_iInf]

/-- **`cor:gl-pshhom`(i)** (BJ22 `cor:pshhom`(i)): if `u ∈ PSH(𝒳, θ)` has `u(⋆) ≥ 0`, then
`û ∈ PSH_hom(𝒳, θ)`. -/
theorem IsPSH.isPSHHom_homogenization (h : X.IsPSH θ u) (h0 : 0 ≤ u X.triv) :
    X.IsPSHHom θ (X.homogenization u) := by
  obtain ⟨ι, _, _, _, a, f, hf, ha, hanti, hu⟩ := h.exists_isHomFS_net h0
  refine ⟨FSSystemC.isPSH_of_iInf (F := X.fsSystem) ⟨X.triv, ?_⟩ a f (fun i => (hf i).isFS) ha
    hanti hu, isScaleHomogeneous_homogenization u⟩
  rw [homogenization_triv_of_nonneg h0 (FSSystemC.IsPSH.apply_triv_ne_top h)]
  exact EReal.zero_ne_bot

/-- **`cor:gl-pshhom`**, second case (BJ22 `lem:genpos`): if `u(⋆) < 0`, then `û ≡ -∞`. -/
theorem IsPSH.homogenization_eq_bot (h : X.IsPSH θ u) (h0 : u X.triv < 0) (v : X.an) :
    X.homogenization u v = ⊥ :=
  MultiModel.homogenization_eq_bot h.le_apply_triv h0 v

/-- **`thm:gl-homog-fs`**, second case: if `φ ∈ 𝓗(𝒳, a)` has `φ(⋆) < 0`, then `φ̂ ≡ -∞`. -/
theorem IsFS.homogenization_eq_bot (h : X.IsFS a φ) (h0 : φ X.triv < 0) (v : X.an) :
    X.homogenization φ v = ⊥ :=
  MultiModel.homogenization_eq_bot h.le_apply_triv h0 v

/-- A homogeneous `θ`-psh function is the limit of a decreasing net `ψ_α ∈ 𝓗_hom(𝒳, a_α)` with
`a_α → θ` (`cor:gl-pshhom`(ii) for `u = û`, `u(⋆) = 0`). -/
theorem IsPSHHom.exists_isHomFS_net (h : X.IsPSHHom θ u) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (a : ι → Fin r → ℚ) (f : ι → X.an → EReal), (∀ i, X.IsHomFS (a i) (f i)) ∧
        Tendsto (fun i c => (a i c : ℝ)) atTop (𝓝 θ) ∧ (∀ v, Antitone fun i => f i v) ∧
          ∀ v, u v = ⨅ i, f i v := by
  have h0 : 0 ≤ u X.triv := h.apply_triv_eq_zero.ge
  have := h.1.exists_isHomFS_net h0
  rwa [h.2.homogenization_eq] at this

/-- Maxima of homogeneous functions are homogeneous. -/
theorem IsScaleHomogeneous.max {u u' : X.an → EReal} (h : X.IsScaleHomogeneous u)
    (h' : X.IsScaleHomogeneous u') : X.IsScaleHomogeneous fun v => Max.max (u v) (u' v) :=
  fun t ht v => by
    dsimp only
    rw [h t ht v, h' t ht v, ProjBerk.ereal_coe_mul_max ht.le]

/-- Sums of homogeneous functions are homogeneous. -/
theorem IsScaleHomogeneous.add {u u' : X.an → EReal} (h : X.IsScaleHomogeneous u)
    (h' : X.IsScaleHomogeneous u') : X.IsScaleHomogeneous fun v => u v + u' v :=
  fun t ht v => by
    dsimp only
    rw [h t ht v, h' t ht v, ProjBerk.ereal_coe_mul_add ht.le]

/-- `PSH_hom(𝒳, θ)` is stable under maxima. -/
theorem IsPSHHom.max {u u' : X.an → EReal} (h : X.IsPSHHom θ u) (h' : X.IsPSHHom θ u') :
    X.IsPSHHom θ fun v => Max.max (u v) (u' v) :=
  ⟨h.1.max h'.1, h.2.max h'.2⟩

/-- `PSH_hom(𝒳, θ) + PSH_hom(𝒳, θ') ⊆ PSH_hom(𝒳, θ + θ')`. -/
theorem IsPSHHom.add {θ' : Fin r → ℝ} {u u' : X.an → EReal} (h : X.IsPSHHom θ u)
    (h' : X.IsPSHHom θ' u') : X.IsPSHHom (θ + θ') fun v => u v + u' v :=
  ⟨h.1.add h'.1, h.2.add h'.2⟩

/-! ### Convexity along rays (`lem:gl-action-convex`) -/

variable (X) in
/-- The function `g(t) = (t · u)(v)` of `lem:gl-action-convex` (`⊥` for `t ≤ 0`). -/
def rayFun (u : X.an → EReal) (v : X.an) (t : ℝ) : EReal :=
  if ht : 0 < t then X.scaleFun t ht u v else ⊥

theorem rayFun_of_pos (u : X.an → EReal) (v : X.an) {t : ℝ} (ht : 0 < t) :
    X.rayFun u v t = X.scaleFun t ht u v :=
  dif_pos ht

/-- **`lem:gl-action-convex`**: `g(t) = (t · u)(v) ≤ t u(⋆)`. -/
theorem IsPSH.scaleFun_le (h : X.IsPSH θ u) (t : ℝ) (ht : 0 < t) (v : X.an) :
    X.scaleFun t ht u v ≤ (t : EReal) * u X.triv :=
  ProjBerk.ereal_coe_mul_monotone ht.le (h.le_apply_triv _)

/-- The convexity inequality for one term `t ↦ L + t λ`, `L ∈ [-∞, ∞)`. -/
theorem ereal_add_coe_mul_convex {L : EReal} (hL : L ≠ ⊤) (lam : ℝ) {t₁ t₂ α β : ℝ}
    (hαβ : α + β = 1) :
    L + (((α * t₁ + β * t₂) * lam : ℝ) : EReal) ≤
      (α : EReal) * (L + ((t₁ * lam : ℝ) : EReal)) +
        (β : EReal) * (L + ((t₂ * lam : ℝ) : EReal)) := by
  induction L using EReal.rec with
  | bot =>
    rw [EReal.bot_add]
    exact bot_le
  | coe L =>
    rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul,
      ← EReal.coe_add, EReal.coe_le_coe_iff]
    have : L = (α + β) * L := by rw [hαβ, one_mul]
    nlinarith [this]
  | top => exact absurd rfl hL

/-- FS functions are convex along rays: `t ↦ (t · φ)(v) = m⁻¹ max_j (log |f_j|(v) + t λ_j)`. -/
theorem FSData.scaleFun_eval_convex (D : X.FSData a) (v : X.an) {t₁ t₂ t : ℝ} (h₁ : 0 < t₁)
    (h₂ : 0 < t₂) (ht : 0 < t) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hteq : t = α * t₁ + β * t₂) :
    X.scaleFun t ht D.eval v ≤
      (α : EReal) * X.scaleFun t₁ h₁ D.eval v + (β : EReal) * X.scaleFun t₂ h₂ D.eval v := by
  have hc0 : (0 : ℝ) ≤ (D.m : ℝ)⁻¹ := D.inv_m_pos.le
  have key : ∀ (s : ℝ) (hs : 0 < s), X.scaleFun s hs D.eval v =
      (((D.m : ℝ)⁻¹ : ℝ) : EReal) *
        D.terms.sup (fun p => X.logSecAbs v.1 D.deg p.1 + ((s * p.2 : ℝ) : EReal)) := by
    intro s hs
    rw [FSData.scaleFun_eval, FSData.eval_reweight]
    rfl
  rw [key t ht, key t₁ h₁, key t₂ h₂]
  have hsup : (D.terms.sup fun p => X.logSecAbs v.1 D.deg p.1 + ((t * p.2 : ℝ) : EReal)) ≤
      (α : EReal) * (D.terms.sup fun p => X.logSecAbs v.1 D.deg p.1 + ((t₁ * p.2 : ℝ) : EReal)) +
      (β : EReal) *
        (D.terms.sup fun p => X.logSecAbs v.1 D.deg p.1 + ((t₂ * p.2 : ℝ) : EReal)) := by
    refine Finset.sup_le fun p hp => ?_
    rw [hteq]
    refine (ereal_add_coe_mul_convex (logSecAbs_ne_top _ _ _) p.2 hαβ).trans ?_
    exact add_le_add
      (ProjBerk.ereal_coe_mul_monotone hα (Finset.le_sup
        (f := fun p : K × ℝ => X.logSecAbs v.1 D.deg p.1 + ((t₁ * p.2 : ℝ) : EReal)) hp))
      (ProjBerk.ereal_coe_mul_monotone hβ (Finset.le_sup
        (f := fun p : K × ℝ => X.logSecAbs v.1 D.deg p.1 + ((t₂ * p.2 : ℝ) : EReal)) hp))
  refine (ProjBerk.ereal_coe_mul_monotone hc0 hsup).trans (le_of_eq ?_)
  dsimp only
  rw [ProjBerk.ereal_coe_mul_add hc0, ProjBerk.ereal_coe_mul_coe_mul,
    ProjBerk.ereal_coe_mul_coe_mul, mul_comm (D.m : ℝ)⁻¹ α, mul_comm (D.m : ℝ)⁻¹ β,
    ← ProjBerk.ereal_coe_mul_coe_mul, ← ProjBerk.ereal_coe_mul_coe_mul]

/-- **`lem:gl-action-convex`** (BJ22 `lem:actionconvex`): `t ↦ (t · u)(v)` is convex on `(0, ∞)`
in the sense `g(α t₁ + β t₂) ≤ α g(t₁) + β g(t₂)` for `α, β ≥ 0`, `α + β = 1`. -/
theorem IsPSH.scaleFun_convex (h : X.IsPSH θ u) (v : X.an) {t₁ t₂ t : ℝ} (h₁ : 0 < t₁)
    (h₂ : 0 < t₂) (ht : 0 < t) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hteq : t = α * t₁ + β * t₂) :
    X.scaleFun t ht u v ≤
      (α : EReal) * X.scaleFun t₁ h₁ u v + (β : EReal) * X.scaleFun t₂ h₂ u v := by
  have hne_top : ∀ (s : ℝ) (hs : 0 < s), X.scaleFun s hs u v ≠ ⊤ := fun s hs =>
    ProjBerk.ereal_coe_mul_ne_top hs.le (FSSystemC.IsPSH.ne_top h _)
  obtain ⟨-, -, ι, _, _, _, a, f, hf, -, hanti, hu⟩ := h
  have hscale : ∀ (s : ℝ) (hs : 0 < s), X.scaleFun s hs u v = ⨅ i, X.scaleFun s hs (f i) v :=
    fun s hs => by
      rw [show u = fun w => ⨅ i, f i w from funext hu, scaleFun_iInf]
  have hlim : ∀ (s : ℝ) (hs : 0 < s),
      Tendsto (fun i => X.scaleFun s hs (f i) v) atTop (𝓝 (X.scaleFun s hs u v)) :=
    fun s hs => by
      rw [hscale s hs]
      exact tendsto_atTop_iInf fun i j hij => scaleFun_mono hs (fun w => hanti w hij) v
  have hlim' := ProjBerk.tendsto_ereal_add (ProjBerk.tendsto_ereal_coe_mul (hlim t₁ h₁) α)
    (ProjBerk.tendsto_ereal_coe_mul (hlim t₂ h₂) β)
    (ProjBerk.ereal_coe_mul_ne_top hα (hne_top _ _))
    (ProjBerk.ereal_coe_mul_ne_top hβ (hne_top _ _))
  refine ge_of_tendsto hlim' (Eventually.of_forall fun i => ?_)
  obtain ⟨D, -, hD⟩ := hf i
  calc X.scaleFun t ht u v ≤ X.scaleFun t ht (f i) v := by rw [hscale]; exact iInf_le _ i
    _ ≤ _ := by
      rw [show f i = D.eval from funext hD]
      exact D.scaleFun_eval_convex v h₁ h₂ ht hα hβ hαβ hteq

/-- **`lem:gl-action-convex`**: if `g(t₀) ≠ -∞` for one `t₀ > 0`, then `g(t) ≠ -∞` for all
`t > 0` (write `t₀` as a convex combination of `t` and `t₀² / t` with positive weights). -/
theorem IsPSH.scaleFun_ne_bot (h : X.IsPSH θ u) {v : X.an} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hv : X.scaleFun t₀ ht₀ u v ≠ ⊥) (t : ℝ) (ht : 0 < t) : X.scaleFun t ht u v ≠ ⊥ := by
  intro hbot
  have hα : 0 < t₀ / (t + t₀) := div_pos ht₀ (by linarith)
  have hβ : 0 ≤ t / (t + t₀) := (div_pos ht (by linarith)).le
  have h₂ : 0 < t₀ ^ 2 / t := by positivity
  have hsum : t₀ / (t + t₀) + t / (t + t₀) = 1 := by
    rw [← add_div, add_comm, div_self (by linarith)]
  have hconv := h.scaleFun_convex v ht h₂ ht₀ hα.le hβ hsum (by field_simp)
  rw [hbot, EReal.coe_mul_bot_of_pos hα, EReal.bot_add, le_bot_iff] at hconv
  exact hv hconv

/-- **`lem:gl-action-convex`**: `g ≡ -∞` on `(0, ∞)`, or `g` is finite on `(0, ∞)`. -/
theorem IsPSH.scaleFun_eq_bot_or_ne_bot (h : X.IsPSH θ u) (v : X.an) :
    (∀ (t : ℝ) (ht : 0 < t), X.scaleFun t ht u v = ⊥) ∨
      ∀ (t : ℝ) (ht : 0 < t), X.scaleFun t ht u v ≠ ⊥ := by
  by_cases hex : ∃ (t₀ : ℝ) (ht₀ : 0 < t₀), X.scaleFun t₀ ht₀ u v ≠ ⊥
  · obtain ⟨t₀, ht₀, hv⟩ := hex
    exact Or.inr (h.scaleFun_ne_bot ht₀ hv)
  · simp only [not_exists, not_not] at hex
    exact Or.inl hex

/-- **`lem:gl-action-convex`**: if `u(v) ≠ -∞`, then `g(t) = (t · u)(v)` is a finite convex
function on `(0, ∞)`. -/
theorem IsPSH.convexOn_rayFun (h : X.IsPSH θ u) {v : X.an} (hv : u v ≠ ⊥) :
    ConvexOn ℝ (Ioi 0) fun t => (X.rayFun u v t).toReal := by
  have hv1 : X.scaleFun 1 one_pos u v ≠ ⊥ := by rwa [scaleFun_one]
  have hfin : ∀ (t : ℝ) (ht : 0 < t), X.scaleFun t ht u v ≠ ⊥ := h.scaleFun_ne_bot one_pos hv1
  have htop : ∀ (t : ℝ) (ht : 0 < t), X.scaleFun t ht u v ≠ ⊤ := fun t ht =>
    ProjBerk.ereal_coe_mul_ne_top ht.le (FSSystemC.IsPSH.ne_top h _)
  refine ⟨convex_Ioi 0, fun x hx y hy α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  have hxy : 0 < α * x + β * y := by
    rcases hα.lt_or_eq with hα' | rfl
    · positivity
    · rw [zero_add] at hαβ
      subst hαβ
      simpa using hy'
  have hconv := h.scaleFun_convex v hx' hy' hxy hα hβ hαβ rfl
  rw [rayFun_of_pos u v hxy, rayFun_of_pos u v hx', rayFun_of_pos u v hy',
    ← EReal.coe_le_coe_iff, EReal.coe_toReal (htop _ hxy) (hfin _ hxy), EReal.coe_add,
    EReal.coe_mul, EReal.coe_mul, EReal.coe_toReal (htop _ hx') (hfin _ hx'),
    EReal.coe_toReal (htop _ hy') (hfin _ hy')]
  exact hconv

/-! ### Homogeneous decomposition (`thm:gl-homog-decomposition`) -/

/-- `u - λ = u + (-λ)` in `EReal`. -/
theorem ereal_sub_coe_eq_add_coe_neg (x : EReal) (lam : ℝ) :
    x - (lam : EReal) = x + ((-lam : ℝ) : EReal) := by
  rw [sub_eq_add_neg, EReal.coe_neg]

/-- **`thm:gl-homog-decomposition`**: for `u ∈ PSH(𝒳, θ)` and `λ < u(⋆)`, the Legendre slice
`û_λ` lies in `PSH_hom(𝒳, θ)` (`cor:gl-pshhom` applied to `u - λ`). -/
theorem IsPSH.isPSHHom_legendreSlice (h : X.IsPSH θ u) {lam : ℝ}
    (hlam : (lam : EReal) ≤ u X.triv) : X.IsPSHHom θ (X.legendreSlice u lam) := by
  have h' : X.IsPSH θ fun v => u v - (lam : EReal) := by
    simp only [ereal_sub_coe_eq_add_coe_neg]
    exact h.add_const (-lam)
  refine h'.isPSHHom_homogenization ?_
  rw [ereal_sub_coe_eq_add_coe_neg]
  lift u X.triv to ℝ using ⟨FSSystemC.IsPSH.apply_triv_ne_top h,
    FSSystemC.IsPSH.apply_triv_ne_bot h⟩ with b hb
  rw [← EReal.coe_add, EReal.coe_nonneg]
  have : lam ≤ b := by exact_mod_cast hlam
  linarith

/-- **`thm:gl-homog-decomposition`** (BJ22 `thm:homogpsh`, FHX `eq:Legendre-reconstruction`):
every `u ∈ PSH(𝒳, θ)` is the pointwise supremum `u = sup_{λ < u(⋆)} (û_λ + λ)`. -/
theorem IsPSH.eq_iSup_legendreSlice (h : X.IsPSH θ u) (v : X.an) :
    u v = ⨆ (lam : ℝ) (_ : (lam : EReal) < u X.triv), X.legendreSlice u lam v + (lam : EReal) := by
  refine le_antisymm ?_ (iSup₂_le fun lam _ => legendreSlice_add_le u lam v)
  by_cases hv : u v = ⊥
  · rw [hv]
    exact bot_le
  have hv1 : X.scaleFun 1 one_pos u v ≠ ⊥ := by rwa [scaleFun_one]
  have hfin : ∀ (t : ℝ) (ht : 0 < t), X.scaleFun t ht u v ≠ ⊥ := h.scaleFun_ne_bot one_pos hv1
  have htop : ∀ (t : ℝ) (ht : 0 < t), X.scaleFun t ht u v ≠ ⊤ := fun t ht =>
    ProjBerk.ereal_coe_mul_ne_top ht.le (FSSystemC.IsPSH.ne_top h _)
  set G : ℝ → ℝ := fun t => (X.rayFun u v t).toReal with hG
  have hGt : ∀ (t : ℝ) (ht : 0 < t), (G t : EReal) = X.scaleFun t ht u v := fun t ht => by
    rw [hG]
    simp only
    rw [rayFun_of_pos u v ht, EReal.coe_toReal (htop t ht) (hfin t ht)]
  obtain ⟨c, hc⟩ := exists_subgradient_one_of_convexOn_Ioi (h.convexOn_rayFun hv)
  lift u X.triv to ℝ using ⟨FSSystemC.IsPSH.apply_triv_ne_top h,
    FSSystemC.IsPSH.apply_triv_ne_bot h⟩ with b hb
  -- `G t ≤ t b`
  have hGb : ∀ t : ℝ, 0 < t → G t ≤ t * b := fun t ht => by
    have := h.scaleFun_le t ht v
    rw [← hb, ← hGt t ht, ← EReal.coe_mul, EReal.coe_le_coe_iff] at this
    exact this
  -- the subgradient is `≤ b`
  have hcb : c ≤ b := by
    by_contra hcb
    rw [not_le] at hcb
    set t : ℝ := Max.max 1 ((c - G 1) / (c - b) + 1) with ht
    have htpos : 0 < t := lt_of_lt_of_le one_pos (le_max_left _ _)
    have h₁ : (c - G 1) / (c - b) < t := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
    rw [div_lt_iff₀ (by linarith)] at h₁
    have h₂ := hc t htpos
    have h₃ := hGb t htpos
    nlinarith
  have hG1 : (G 1 : EReal) = u v := by rw [hGt 1 one_pos, scaleFun_one]
  refine ProjBerk.ereal_le_of_forall_pos_le_add fun ε hε => ?_
  have hlam : ((c - ε : ℝ) : EReal) < (b : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)
  refine le_trans ?_ (add_le_add (le_iSup₂ (f := fun (lam : ℝ) (_ : (lam : EReal) < (b : EReal)) =>
    X.legendreSlice u lam v + (lam : EReal)) (c - ε) hlam) le_rfl)
  -- `û_{c - ε}(v) ≥ G 1 - c`
  have hslice : ((G 1 - c : ℝ) : EReal) ≤ X.legendreSlice u (c - ε) v := by
    refine le_iInf₂ fun t ht => ?_
    have hx := hfin t ht
    have hx' := htop t ht
    rw [scaleFun_apply] at hx hx' ⊢
    have hxb : u (X.rpow t⁻¹ (inv_pos.2 ht) v) ≠ ⊥ := fun h0 => hx (by
      rw [h0, EReal.coe_mul_bot_of_pos ht])
    have hxt : u (X.rpow t⁻¹ (inv_pos.2 ht) v) ≠ ⊤ := FSSystemC.IsPSH.ne_top h _
    have hGt' := hGt t ht
    rw [scaleFun_apply] at hGt'
    lift u (X.rpow t⁻¹ (inv_pos.2 ht) v) to ℝ using ⟨hxt, hxb⟩ with x hx''
    rw [← EReal.coe_mul, EReal.coe_eq_coe_iff] at hGt'
    rw [← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    have := hc t ht
    nlinarith
  rw [← hG1]
  calc (G 1 : EReal) = ((G 1 - c : ℝ) : EReal) + ((c - ε : ℝ) : EReal) + (ε : EReal) := by
        rw [← EReal.coe_add, ← EReal.coe_add]
        congr 1
        ring
    _ ≤ X.legendreSlice u (c - ε) v + ((c - ε : ℝ) : EReal) + (ε : EReal) :=
        add_le_add (add_le_add hslice le_rfl) le_rfl

end MultiModel

end EnvelopeProperty
