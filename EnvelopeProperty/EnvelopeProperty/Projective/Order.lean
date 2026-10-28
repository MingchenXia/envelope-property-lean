/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.PSH

/-!
# Partial order, scaling action and maximum principle on `(ℙⁿ)^an`

This file transcribes, on the model `ProjBerk k n` of `(ℙⁿ)^an`
(`EnvelopeProperty.Projective.Basic`), the following material of Boucksom–Jonsson, *Global
pluripotential theory over a trivially valued field* (BJ22), §1.1 and §4.2, and Fang–Han–Xia,
*The envelope property for unibranch projective varieties*, `prop:BJ-package`(6).

* **The partial order** (BJ22 §1.1, "Partial order and scaling action"): `v ≤ w` iff
  `w(𝔟) ≥ v(𝔟)` for all ideals, i.e. `|f|_w ≤ |f|_v` for all `f`. On the model this is
  `v ≤ w ↔ ∀ f, |f|_w ≤ |f|_v` over all polynomials `f` (equivalently all forms, the points being
  graded). The trivial valuation is the least element (`ProjBerk.triv_le`, the `OrderBot`
  instance), the case `Y = X` of BJ22 `exam:vYZ` for the irreducible `ℙⁿ`.
* **The scaling action** (BJ22 §1.1, FHX `eq:scaling-action`): `|f|_{t·v} = |f|_v ^ t` for
  `t > 0` (`ProjBerk.rpow`; it preserves gradedness and the normalization), which is continuous,
  order preserving and fixes `v_triv`; and the induced action `(t · u)(v) = t u(t⁻¹ v)` on
  functions (BJ22 `equ:scale`, `ProjBerk.scaleFun`), with homogeneous functions
  (`ProjBerk.IsScaleHomogeneous`, `u(tv) = t u(v)`) as its fixed points.
* BJ22 `prop:FS`(i),(ii) and `lem:FSconvex`: FS functions are decreasing, invariant under the
  scaling action (real constants), and convex and decreasing along rays `t ↦ φ(tv)`.
* BJ22 `prop:pshconvex`(i),(iii) and `lem:maxprin`: `θ`-psh functions are decreasing
  (`ProjBerk.IsPSH.antitone`) and convex and decreasing along rays; the **maximum principle**
  `sup u = u(v_triv) ∈ ℝ` (`ProjBerk.IsPSH.iSup_eq`, FHX `prop:BJ-package`(6)); homogeneous psh
  functions vanish at `v_triv`, hence are `≤ 0`.

Convexity of an `EReal`-valued function of `t` is stated as the inequality
`u((a t₁ + b t₂) v) ≤ a u(t₁ v) + b u(t₂ v)` for `a, b ≥ 0`, `a + b = 1`, since `EReal` is not
an ordered `ℝ`-module.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

namespace ProjBerk

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-! ### The partial order -/

/-- The partial order of BJ22 §1.1: `v ≤ w` iff `|f|_w ≤ |f|_v` for all `f`, i.e. `w(f) ≥ v(f)`
in additive notation. -/
instance : PartialOrder (ProjBerk k n) where
  le v w := ∀ f, w.1.val f ≤ v.1.val f
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ f := (h₂ f).trans (h₁ f)
  le_antisymm _ _ h₁ h₂ := ext (Berk.ext_val fun f => le_antisymm (h₂ f) (h₁ f))

theorem le_def {v w : ProjBerk k n} : v ≤ w ↔ ∀ f, w.1.val f ≤ v.1.val f := Iff.rfl

/-- The trivial valuation is the least element of `(ℙⁿ)^an`. -/
theorem triv_le (v : ProjBerk k n) : triv ≤ v := fun f => by
  by_cases hf : f = 0
  · simp [hf]
  · rw [triv_val_of_ne_zero hf]
    exact val_le_one v f

instance : OrderBot (ProjBerk k n) where
  bot := triv
  bot_le := triv_le

theorem bot_eq_triv : (⊥ : ProjBerk k n) = triv := rfl

/-- `log|s|` is decreasing. -/
theorem logAbs_antitone (s : MvPolynomial (Fin (n + 1)) k) :
    Antitone (logAbs s : ProjBerk k n → EReal) := fun _ _ h => by
  rw [logAbs_def, logAbs_def]
  exact ENNReal.log_monotone (ENNReal.coe_le_coe.2 (h s))

theorem termVal_antitone (t : MvPolynomial (Fin (n + 1)) k × ℝ) :
    Antitone (termVal t : ProjBerk k n → EReal) := fun _ _ h =>
  add_le_add_left (logAbs_antitone t.1 h) _

/-- **FS functions are decreasing** (BJ22 `prop:FS`(i)). -/
theorem FSData.antitone_eval {a : ℚ} (D : FSData k n a) : Antitone D.eval := fun _ _ h => by
  rw [D.eval_def, D.eval_def]
  exact ereal_coe_mul_monotone D.inv_m_pos.le
    (Finset.sup_mono_fun fun t _ => termVal_antitone t h)

theorem IsFS.antitone {a : ℚ} {φ : ProjBerk k n → EReal} (h : IsFS a φ) : Antitone φ := by
  obtain ⟨D, rfl⟩ := h
  exact D.antitone_eval

/-! ### `θ`-psh functions are decreasing; the maximum principle -/

variable {θ : ℝ} {u : ProjBerk k n → EReal}

/-- **`θ`-psh functions are decreasing** (BJ22 `prop:pshconvex`(i)): they are infima of
decreasing FS functions. -/
theorem IsPSH.antitone (h : IsPSH θ u) : Antitone u := by
  obtain ⟨-, -, ι, _, _, _, a, φ, hφ, -, -, hu⟩ := h
  intro v w hvw
  rw [hu v, hu w]
  exact iInf_mono fun i => (hφ i).antitone hvw

/-- For a decreasing function, generic finiteness is finiteness at `v_triv` (BJ22
`lem:maxprin`(ii)). -/
theorem exists_ne_bot_iff_of_antitone {f : ProjBerk k n → EReal} (hf : Antitone f) :
    (∃ v, f v ≠ ⊥) ↔ f triv ≠ ⊥ :=
  ⟨fun ⟨v, hv⟩ => ne_bot_of_le_ne_bot hv (hf (triv_le v)), fun h => ⟨triv, h⟩⟩

/-- The maximum principle, pointwise form: `u ≤ u(v_triv)`. -/
theorem IsPSH.le_apply_triv (h : IsPSH θ u) (v : ProjBerk k n) : u v ≤ u triv :=
  h.antitone (triv_le v)

/-- A `θ`-psh function is finite at `v_triv`. -/
theorem IsPSH.apply_triv_ne_bot (h : IsPSH θ u) : u triv ≠ ⊥ :=
  (exists_ne_bot_iff_of_antitone h.antitone).1 h.exists_ne_bot

/-- `u(v_triv)` is a real number. -/
theorem IsPSH.coe_toReal_apply_triv (h : IsPSH θ u) : ((u triv).toReal : EReal) = u triv :=
  EReal.coe_toReal (h.ne_top triv) h.apply_triv_ne_bot

/-- **The maximum principle** (BJ22 `lem:maxprin`, `prop:pshconvex`(ii); FHX
`prop:BJ-package`(6)): a `θ`-psh function attains its supremum at the trivial valuation. -/
theorem IsPSH.iSup_eq (h : IsPSH θ u) : ⨆ v, u v = u triv :=
  le_antisymm (iSup_le h.le_apply_triv) (le_iSup u triv)

theorem IsPSH.isGreatest (h : IsPSH θ u) : IsGreatest (range u) (u triv) :=
  ⟨mem_range_self _, by rintro _ ⟨v, rfl⟩; exact h.le_apply_triv v⟩

/-- A `θ`-psh function is bounded above by the real number `u(v_triv)`. -/
theorem IsPSH.le_toReal_apply_triv (h : IsPSH θ u) (v : ProjBerk k n) :
    u v ≤ ((u triv).toReal : EReal) := by
  rw [h.coe_toReal_apply_triv]
  exact h.le_apply_triv v

/-! ### The scaling action -/

/-- The **scaling action** of `t > 0` on `(ℙⁿ)^an` (BJ22 §1.1, FHX `eq:scaling-action`):
`|f|_{t·v} = |f|_v ^ t`, i.e. `(tv)(f) = t v(f)`; it preserves gradedness and the normalization
`max_i |xᵢ| = 1`. -/
def rpow (t : ℝ) (ht : 0 < t) (v : ProjBerk k n) : ProjBerk k n :=
  ⟨Berk.rpow t ht v.1, (isGraded_iff _).2 fun f d => by
      simp only [Berk.rpow_val_apply]
      exact NNReal.rpow_le_rpow ((isGraded_iff _).1 v.isGraded f d) ht.le, by
    simp only [Berk.rpow_val_apply]
    refine le_antisymm (Finset.sup_le fun i _ => NNReal.rpow_le_one (val_X_le_one v i) ht.le) ?_
    obtain ⟨j, hj⟩ := exists_val_X_eq_one v
    refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun i => v.1.val (MvPolynomial.X i) ^ t)
      (Finset.mem_univ j))
    simp [hj]⟩

@[simp]
theorem rpow_val (t : ℝ) (ht : 0 < t) (v : ProjBerk k n) :
    (rpow t ht v).1 = Berk.rpow t ht v.1 := rfl

theorem rpow_val_apply (t : ℝ) (ht : 0 < t) (v : ProjBerk k n)
    (f : MvPolynomial (Fin (n + 1)) k) : (rpow t ht v).1.val f = v.1.val f ^ t := rfl

/-- `log|s|(t·v) = t log|s|(v)`. -/
theorem logAbs_rpow (s : MvPolynomial (Fin (n + 1)) k) (t : ℝ) (ht : 0 < t)
    (v : ProjBerk k n) : logAbs s (rpow t ht v) = (t : EReal) * logAbs s v :=
  Berk.logAbs_rpow t ht s v.1

@[fun_prop]
theorem continuous_rpow (t : ℝ) (ht : 0 < t) : Continuous (rpow (k := k) (n := n) t ht) :=
  isEmbedding_val.continuous_iff.2 ((Berk.continuous_rpow t ht).comp continuous_val)

@[simp]
theorem rpow_one (v : ProjBerk k n) : rpow 1 one_pos v = v :=
  ext (Berk.rpow_one v.1)

theorem rpow_rpow (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (v : ProjBerk k n) :
    rpow s hs (rpow t ht v) = rpow (t * s) (mul_pos ht hs) v :=
  ext (Berk.rpow_rpow s t hs ht v.1)

theorem rpow_inv_rpow (t : ℝ) (ht : 0 < t) (v : ProjBerk k n) :
    rpow t⁻¹ (inv_pos.2 ht) (rpow t ht v) = v := by
  rw [rpow_rpow]
  convert rpow_one v using 2
  exact mul_inv_cancel₀ ht.ne'

theorem rpow_rpow_inv (t : ℝ) (ht : 0 < t) (v : ProjBerk k n) :
    rpow t ht (rpow t⁻¹ (inv_pos.2 ht) v) = v := by
  rw [rpow_rpow]
  convert rpow_one v using 2
  exact inv_mul_cancel₀ ht.ne'

/-- The trivial valuation is fixed by the scaling action. -/
@[simp]
theorem rpow_triv (t : ℝ) (ht : 0 < t) : rpow t ht (triv : ProjBerk k n) = triv :=
  ext (Berk.rpow_triv t ht)

/-- The scaling action is order preserving. -/
theorem rpow_mono (t : ℝ) (ht : 0 < t) : Monotone (rpow (k := k) (n := n) t ht) :=
  fun _ _ h f => NNReal.rpow_le_rpow (h f) ht.le

/-- `t ↦ t·v` is increasing: `s·v ≤ t·v` for `s ≤ t`, since `|f|_v ≤ 1`. -/
theorem rpow_le_rpow_left {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s ≤ t)
    (v : ProjBerk k n) : rpow s hs v ≤ rpow t ht v := fun f => by
  rw [rpow_val_apply, rpow_val_apply]
  rcases eq_zero_or_pos (v.1.val f) with h0 | h0
  · rw [h0, NNReal.zero_rpow ht.ne', NNReal.zero_rpow hs.ne']
  · exact NNReal.rpow_le_rpow_of_exponent_ge h0 (val_le_one v f) hst

/-- The induced **scaling action on functions** (BJ22 `equ:scale`): `(t · u)(v) = t u(t⁻¹ v)`. -/
def scaleFun (t : ℝ) (ht : 0 < t) (u : ProjBerk k n → EReal) (v : ProjBerk k n) : EReal :=
  (t : EReal) * u (rpow t⁻¹ (inv_pos.2 ht) v)

/-- `u` is **homogeneous** (BJ22 §1.1): `u(t v) = t u(v)` for all `t > 0`. -/
def IsScaleHomogeneous (u : ProjBerk k n → EReal) : Prop :=
  ∀ (t : ℝ) (ht : 0 < t) (v : ProjBerk k n), u (rpow t ht v) = (t : EReal) * u v

theorem ereal_coe_mul_inv_mul {t : ℝ} (ht : t ≠ 0) (x : EReal) :
    (t : EReal) * ((t⁻¹ : ℝ) * x) = x := by
  rw [ereal_coe_mul_coe_mul, mul_inv_cancel₀ ht, EReal.coe_one, one_mul]

/-- Homogeneous functions are the fixed points of the scaling action (BJ22 §1.1). -/
theorem isScaleHomogeneous_iff_scaleFun_eq {u : ProjBerk k n → EReal} :
    IsScaleHomogeneous u ↔ ∀ (t : ℝ) (ht : 0 < t), scaleFun t ht u = u := by
  constructor
  · intro h t ht
    funext v
    rw [scaleFun, h t⁻¹ (inv_pos.2 ht), ereal_coe_mul_inv_mul ht.ne']
  · intro h t ht v
    have := congrFun (h t ht) (rpow t ht v)
    rw [scaleFun, rpow_inv_rpow] at this
    exact this.symm

/-! ### Fubini–Study functions and the scaling action -/

namespace FSData

variable {a : ℚ}

open Classical in
/-- The data `(s_j, t λ_j)`: `t · φ = m⁻¹ max_j (log|s_j| + t λ_j)` (BJ22, after `prop:FS`). -/
def scaleConst (D : FSData k n a) (t : ℝ) : FSData k n a where
  m := D.m
  m_pos := D.m_pos
  deg := D.deg
  deg_eq := D.deg_eq
  terms := D.terms.image fun p => (p.1, t * p.2)
  isHomogeneous := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    exact D.isHomogeneous q hq
  exists_ne_zero := by
    obtain ⟨q, hq, hne⟩ := D.exists_ne_zero
    exact ⟨_, Finset.mem_image_of_mem _ hq, hne⟩

theorem eval_scaleConst (D : FSData k n a) (t : ℝ) (v : ProjBerk k n) :
    (D.scaleConst t).eval v = (((D.m : ℝ)⁻¹ : ℝ) : EReal) *
      D.terms.sup fun p => logAbs p.1 v + ((t * p.2 : ℝ) : EReal) := by
  classical
  rw [eval_def]
  change (((D.m : ℝ)⁻¹ : ℝ) : EReal) * (D.terms.image fun p => (p.1, t * p.2)).sup _ = _
  rw [Finset.sup_image]
  rfl

/-- **FS functions are invariant under the scaling action** (BJ22 `prop:FS`(ii), real
constants): `t · φ = m⁻¹ max_j (log|s_j| + t λ_j)`. -/
theorem scaleFun_eval (D : FSData k n a) (t : ℝ) (ht : 0 < t) :
    scaleFun t ht D.eval = (D.scaleConst t).eval := by
  funext v
  rw [scaleFun, eval_scaleConst, eval_def, ← mul_assoc, ← EReal.coe_mul, mul_comm t,
    EReal.coe_mul, mul_assoc, ereal_coe_mul_finset_sup ht]
  congr 1
  refine Finset.sup_congr rfl fun p _ => ?_
  rw [termVal_def, logAbs_rpow, ereal_coe_mul_add ht.le, ereal_coe_mul_inv_mul ht.ne',
    EReal.coe_mul]

/-- FS functions along rays: `φ(t v) = m⁻¹ max_j (t log|s_j|(v) + λ_j)`. -/
theorem eval_rpow (D : FSData k n a) (t : ℝ) (ht : 0 < t) (v : ProjBerk k n) :
    D.eval (rpow t ht v) =
      (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup fun p => (t : EReal) * logAbs p.1 v + p.2 := by
  rw [eval_def]
  simp only [termVal_def, logAbs_rpow]

/-- The convexity inequality for one term `t ↦ t L + λ`, `L ∈ [-∞, ∞)`. -/
theorem ereal_affine_convex {L : EReal} (hL : L ≠ ⊤) (lam : ℝ) {t₁ t₂ a b : ℝ}
    (h₁ : 0 < t₁) (h₂ : 0 < t₂) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ((a * t₁ + b * t₂ : ℝ) : EReal) * L + lam ≤
      (a : EReal) * ((t₁ : EReal) * L + lam) + (b : EReal) * ((t₂ : EReal) * L + lam) := by
  induction L using EReal.rec with
  | bot =>
    have hpos : 0 < a * t₁ + b * t₂ := by
      rcases eq_or_lt_of_le ha with rfl | ha'
      · simp only [zero_add, zero_mul] at hab ⊢; rw [hab, one_mul]; exact h₂
      · positivity
    rw [EReal.coe_mul_bot_of_pos hpos, EReal.bot_add]
    exact bot_le
  | coe L =>
    rw [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul,
      ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have : lam = (a + b) * lam := by rw [hab, one_mul]
    nlinarith [this]
  | top => exact absurd rfl hL

/-- **FS functions are convex along rays** (BJ22 `lem:FSconvex`): for `a, b ≥ 0`, `a + b = 1`,
`φ((a t₁ + b t₂) v) ≤ a φ(t₁ v) + b φ(t₂ v)`. -/
theorem eval_rpow_convex (D : FSData k n a) (v : ProjBerk k n) {t₁ t₂ t : ℝ} (h₁ : 0 < t₁)
    (h₂ : 0 < t₂) (ht : 0 < t) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hteq : t = α * t₁ + β * t₂) :
    D.eval (rpow t ht v) ≤
      (α : EReal) * D.eval (rpow t₁ h₁ v) + (β : EReal) * D.eval (rpow t₂ h₂ v) := by
  subst hteq
  rw [eval_rpow, eval_rpow, eval_rpow]
  set c : ℝ := (D.m : ℝ)⁻¹ with hc
  have hc0 : 0 ≤ c := D.inv_m_pos.le
  set X := D.terms.sup fun p => (t₁ : EReal) * logAbs p.1 v + p.2
  set Y := D.terms.sup fun p => (t₂ : EReal) * logAbs p.1 v + p.2
  have hX : X ≠ ⊤ := by
    refine ne_of_lt ((Finset.sup_lt_iff bot_lt_top).2 fun p _ => lt_top_iff_ne_top.2 ?_)
    exact EReal.add_ne_top (ereal_coe_mul_ne_top h₁.le (logAbs_ne_top _ _)) (EReal.coe_ne_top _)
  have hY : Y ≠ ⊤ := by
    refine ne_of_lt ((Finset.sup_lt_iff bot_lt_top).2 fun p _ => lt_top_iff_ne_top.2 ?_)
    exact EReal.add_ne_top (ereal_coe_mul_ne_top h₂.le (logAbs_ne_top _ _)) (EReal.coe_ne_top _)
  have hsup : (D.terms.sup fun p => ((α * t₁ + β * t₂ : ℝ) : EReal) * logAbs p.1 v + p.2) ≤
      (α : EReal) * X + (β : EReal) * Y := by
    refine Finset.sup_le fun p hp => (ereal_affine_convex (logAbs_ne_top _ _) p.2 h₁ h₂ hα hβ
      hαβ).trans ?_
    exact add_le_add (ereal_coe_mul_monotone hα (Finset.le_sup (f := fun p =>
      (t₁ : EReal) * logAbs p.1 v + p.2) hp)) (ereal_coe_mul_monotone hβ (Finset.le_sup
      (f := fun p => (t₂ : EReal) * logAbs p.1 v + p.2) hp))
  refine (ereal_coe_mul_monotone hc0 hsup).trans (le_of_eq ?_)
  change (c : EReal) * ((α : EReal) * X + (β : EReal) * Y) = _
  rw [ereal_coe_mul_add hc0, ereal_coe_mul_coe_mul, ereal_coe_mul_coe_mul, mul_comm c α,
    mul_comm c β, ← ereal_coe_mul_coe_mul, ← ereal_coe_mul_coe_mul]

end FSData

theorem IsFS.scaleFun {a : ℚ} {φ : ProjBerk k n → EReal} (h : IsFS a φ) (t : ℝ) (ht : 0 < t) :
    IsFS a (scaleFun t ht φ) := by
  obtain ⟨D, rfl⟩ := h
  exact ⟨D.scaleConst t, D.scaleFun_eval t ht⟩

/-! ### `θ`-psh functions along rays -/

/-- Multiplication by a real constant preserves limits in `EReal`. -/
theorem tendsto_ereal_coe_mul {ι : Type*} {l : Filter ι} {f : ι → EReal} {x : EReal}
    (hf : Tendsto f l (𝓝 x)) (c : ℝ) :
    Tendsto (fun i => (c : EReal) * f i) l (𝓝 ((c : EReal) * x)) := by
  by_cases hc : c = 0
  · simp only [hc, EReal.coe_zero, zero_mul]
    exact tendsto_const_nhds
  · exact ((continuous_ereal_coe_mul hc).tendsto x).comp hf

/-- The sum of two convergent `EReal`-valued families with limits `< +∞`. -/
theorem tendsto_ereal_add {ι : Type*} {l : Filter ι} {f g : ι → EReal} {x y : EReal}
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    Tendsto (fun i => f i + g i) l (𝓝 (x + y)) :=
  (EReal.continuousAt_add (p := (x, y)) (Or.inl hx) (Or.inr hy)).tendsto.comp (hf.prodMk_nhds hg)

/-- **`θ`-psh functions are convex along rays** (BJ22 `prop:pshconvex`(iii)):
`u((a t₁ + b t₂) v) ≤ a u(t₁ v) + b u(t₂ v)` for `a, b ≥ 0`, `a + b = 1`. -/
theorem IsPSH.rpow_convex (h : IsPSH θ u) (v : ProjBerk k n) {t₁ t₂ t : ℝ} (h₁ : 0 < t₁)
    (h₂ : 0 < t₂) (ht : 0 < t) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hteq : t = α * t₁ + β * t₂) :
    u (rpow t ht v) ≤ (α : EReal) * u (rpow t₁ h₁ v) + (β : EReal) * u (rpow t₂ h₂ v) := by
  have hne_top := h.ne_top
  obtain ⟨-, -, ι, _, _, _, a, φ, hφ, -, hanti, hu⟩ := h
  have hlim : ∀ w, Tendsto (fun i => φ i w) atTop (𝓝 (u w)) := fun w => by
    rw [hu w]; exact tendsto_atTop_iInf (hanti w)
  have hlim' := tendsto_ereal_add (tendsto_ereal_coe_mul (hlim (rpow t₁ h₁ v)) α)
    (tendsto_ereal_coe_mul (hlim (rpow t₂ h₂ v)) β)
    (ereal_coe_mul_ne_top hα (hne_top _)) (ereal_coe_mul_ne_top hβ (hne_top _))
  refine ge_of_tendsto hlim' (Eventually.of_forall fun i => ?_)
  obtain ⟨D, hD⟩ := hφ i
  calc u (rpow t ht v) ≤ φ i (rpow t ht v) := by rw [hu]; exact iInf_le _ i
    _ ≤ _ := by
      rw [hD]
      exact D.eval_rpow_convex v h₁ h₂ ht hα hβ hαβ hteq

/-- **`θ`-psh functions are decreasing along rays** (BJ22 `prop:pshconvex`(iii)). -/
theorem IsPSH.rpow_antitone (h : IsPSH θ u) (v : ProjBerk k n) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) (hst : s ≤ t) : u (rpow t ht v) ≤ u (rpow s hs v) :=
  h.antitone (rpow_le_rpow_left hs ht hst v)

/-- **Homogeneous `θ`-psh functions vanish at `v_triv`** (FHX `prop:BJ-package`(6)), `v_triv`
being a fixed point of the scaling action. -/
theorem IsPSH.apply_triv_eq_zero (h : IsPSH θ u) (hu : IsScaleHomogeneous u) : u triv = 0 := by
  have h2 := hu 2 two_pos triv
  rw [rpow_triv, ← h.coe_toReal_apply_triv, ← EReal.coe_mul] at h2
  rw [← h.coe_toReal_apply_triv]
  have : (u triv).toReal = 2 * (u triv).toReal := EReal.coe_injective h2
  exact_mod_cast (by linarith : (u triv).toReal = 0)

/-- Homogeneous `θ`-psh functions are `≤ 0` (FHX `prop:BJ-package`(6)). -/
theorem IsPSH.nonpos (h : IsPSH θ u) (hu : IsScaleHomogeneous u) (v : ProjBerk k n) : u v ≤ 0 :=
  (h.le_apply_triv v).trans (h.apply_triv_eq_zero hu).le

end ProjBerk

end EnvelopeProperty
