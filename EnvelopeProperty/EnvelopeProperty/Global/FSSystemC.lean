/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.FSSystemEnvelope

/-!
# Fubini–Study systems with a semiample cone

This file implements the blueprint nodes `def:gl-fs-system` and `thm:gl-fs-system-theory` of the
global chapter `global.tex` of the formalization of Fang–Han–Xia, *The envelope property for
unibranch projective varieties* (FHX, revision `832e086`, §2), together with the class-free parts
of `lem:gl-cones` and `lem:gl-ep-basic` (plan PLAN-68 §2 item 5, decisions D-M1 and D-H4).

## Fubini–Study systems with a semiample cone (`def:gl-fs-system`)

`EnvelopeProperty.FSSystemC K r` generalizes the Fubini–Study systems
`EnvelopeProperty.FSSystem K r` of `def:pg-fs-system` (Boucksom–Jonsson, *Global pluripotential
theory over a trivially valued field* (BJ22), `defi:FS`, `prop:FS`): the classes are **all**
`a ∈ ℚ^r` (the families `𝓗(a)` may be empty), and the system comes with a convex cone
`C ⊆ ℚ^r` (`FSSystemC.C`, a `ConvexCone ℚ (Fin r → ℚ)`) containing `ℚ^r_{≥0}`, the
*semiample cone*. The axioms are (FS1), (FS2), (FS4) for all classes, stability of `𝓗(a)` and
`𝓗_fin(a)` under binary maxima for all classes, and (FS3) (constants) and (FS5) (approximation by
`𝓗_fin(a)`) for `a ∈ C`. Stability under addition of real constants holds for every class (it is
(FS4) with the constants of class `0 ∈ C`, `FSSystemC.IsFS.add_const`), and `C + ℚ^r_{≥0} ⊆ C`
is `ConvexCone.add_mem`. A Fubini–Study system in the sense of `def:pg-fs-system` is the case
`C = ℚ^r_{≥0}` (`FSSystem.toFSSystemC`); the two notions of psh functions, envelopes and the
envelope property agree (`FSSystem.toFSSystemC_isPSH_iff`, `FSSystem.toFSSystemC_envelope`,
`FSSystem.toFSSystemC_hasEnvelopeProperty_iff`), and `C̄ = ℝ^r_{≥0}`
(`FSSystem.coneClosure_toFSSystemC`).

## The closure of the cone (`lem:gl-cones`, class-free part)

`EnvelopeProperty.ratClosure C ⊆ ℝ^r` is the closure of the image of `C ⊆ ℚ^r`; for the
semiample cone of a model it is the model-nef cone `N(𝒳)`. For a convex cone `C ⊇ ℚ^r_{≥0}`:

* `EnvelopeProperty.mem_of_lt_of_mem_ratClosure`: every rational `a > θ` (coordinatewise) with
  `θ ∈ C̄` lies in `C`. This elementary fact replaces the replacement of classes in the proof of
  `thm:gl-fs-system-theory`(2);
* `EnvelopeProperty.mem_ratClosure_of_nonneg`, `EnvelopeProperty.add_mem_ratClosure`,
  `EnvelopeProperty.smul_mem_ratClosure`, `EnvelopeProperty.isClosed_ratClosure`: `C̄` is a closed
  convex cone containing `ℝ^r_{≥0}` (`lem:gl-cones`(1), second half);
* `EnvelopeProperty.exists_mem_ge_tendsto_of_mem_ratClosure` (`lem:gl-cones`(3)): if `θ ∈ C̄` and
  `a_α → θ` is a net in `ℚ^r`, then `a'_{(α, n)} = a_α ⊔ q_n` (with rationals `q_n > θ`,
  `q_n → θ`) is a net in `C` on the index set `I × ℕ` with `a'_{(α,n)} ≥ a_α` and
  `a'_{(α,n)} → θ`.

## Psh theory (`thm:gl-fs-system-theory`)

`FSSystemC.IsPSH F θ u` for `θ ∈ ℝ^r` is BJ22 Definition 4.1 with the classes of the system:
`u ≢ -∞` usc, the limit of a decreasing net `fᵢ ∈ 𝓗(aᵢ)`, `aᵢ → θ`.

Part (1), for **every** `θ ∈ ℝ^r`: `FSSystemC.IsFS.isPSH` (`𝓗(a) ⊆ PSH(a)`), the maximum
principle `FSSystemC.IsPSH.le_apply_triv`, `FSSystemC.IsPSH.apply_triv_ne_bot`,
`FSSystemC.IsPSH.apply_triv_ne_top`, `FSSystemC.IsPSH.iSup_eq`, maxima
`FSSystemC.IsPSH.max`, `FSSystemC.isPSH_finset_sup'`, translates `FSSystemC.IsPSH.add_const`, sums
`FSSystemC.IsPSH.add`, rational scaling `FSSystemC.IsPSH.smul_rat` and monotonicity
`FSSystemC.IsPSH.mono_class`. These are the proofs of `prop:pg-maxprin` and `thm:pg-psh-basic`,
without the conclusion `θ ≥ 0`.

Part (2), for `θ ∈ C̄` (`FSSystemC.coneClosure`):

* `FSSystemC.isPSH_of_antitone`, `FSSystemC.isPSH_of_tendsto_of_antitone`,
  `FSSystemC.isPSH_of_antitone_seq` (**PSH2**, BJ22 `thm:psh12` for nets `uᵢ ∈ PSH(θᵢ)`,
  `θᵢ → θ`);
* `FSSystemC.IsPSH.smul`, `FSSystemC.isPSH_smul_iff`, `FSSystemC.setOf_isPSH_smul` (real scaling);
* `FSSystemC.isPSH_const` (real constants);
* `FSSystemC.IsPSH.exists_isFinFS_net`, `FSSystemC.isPSH_iff_exists_isFinFS`,
  `FSSystemC.IsPSH.exists_isFinFS_net_gt`, `FSSystemC.IsPSH.exists_isFinFS_net_of_pos` (for rational
  positive `θ`), and, for second countable `K`, `FSSystemC.IsPSH.exists_isFinFS_seq_gt`,
  `FSSystemC.IsPSH.exists_isFinFS_seq_of_pos`, `FSSystemC.IsPSH.exists_isFinFS_seq_dyadic`
  (regularization, `thm:pg-regularization`, `cor:pg-countable-regularization`).

## Envelopes (`def:gl-psh`, `lem:gl-ep-basic`)

`FSSystemC.envelope F θ φ` (`P_θ(φ)`) and `FSSystemC.HasEnvelopeProperty F θ` are the definitions of
`def:sg-ep`. `lem:gl-ep-basic`: `FSSystemC.HasEnvelopeProperty.of_tendsto` (part (1), for
`θ ∈ C̄`), `FSSystemC.hasEnvelopeProperty_smul_iff` (part (2), `EP(θ) ↔ EP(tθ)` for `θ ∈ C̄`,
`t > 0`, using `EnvelopeProperty.uscReg_coe_mul`),
`FSSystemC.hasEnvelopeProperty_of_forall_not_isPSH`
(part (3)).

## Deviations from the blueprint

* `lem:gl-cones`(3) is false as stated for nets with a greatest index (e.g. a constant net at a
  rational `θ ∈ C̄ ∖ C`, which exists when `C` is not closed: no net in `C` indexed by a
  one-point set converges to `θ`); its proof needs indices `n(α) → ∞`. The Lean statement
  re-indexes the net by `I × ℕ`, which is what every use needs.
* The proof of PSH2 (`thm:gl-fs-system-theory`(2)) does not replace the classes of the
  approximating nets of the `uᵢ` by classes relative to the limit `θ` (which does not produce
  nets converging to classes `τᵢ → θ`, as the diagonal lemma requires). Instead each `uᵢ` is
  regarded as psh of class `τ_{(i, n)} = θᵢ ⊔ θ + (n + 1)⁻¹ 𝟙 > θ` (monotonicity), so that the
  classes of its approximating net are eventually `> θ`, hence in `C`
  (`EnvelopeProperty.mem_of_lt_of_mem_ratClosure`); the diagonal lemma
  `IsDecrNetLimit.of_antitone` then applies to the families `𝓗(a)`, `a ∈ C`
  (`FSSystemC.isDecrNetLimit_semiampleFS_of_antitone`) on the index set `I × ℕ`.
* `lem:gl-ep-basic`(1) is stated for sequences of classes (`ℝ^r` is metrizable).
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

/-! ### Auxiliary facts on `EReal` and usc regularization -/

/-- Multiplication by a positive real commutes with suprema in `EReal`. -/
theorem ereal_coe_mul_iSup {ι : Sort*} {c : ℝ} (hc : 0 < c) (a : ι → EReal) :
    (c : EReal) * ⨆ i, a i = ⨆ i, (c : EReal) * a i :=
  Monotone.map_iSup_of_continuousAt (f := fun x : EReal => (c : EReal) * x)
    (ProjBerk.continuous_ereal_coe_mul hc.ne').continuousAt
    (ProjBerk.ereal_coe_mul_monotone hc.le) (EReal.coe_mul_bot_of_pos hc)

/-- The usc regularization commutes with multiplication by a positive real:
`(t f)^⋆ = t f^⋆`, since `x ↦ t x` is an increasing homeomorphism of `[-∞, +∞]`. -/
theorem uscReg_coe_mul {X : Type*} [TopologicalSpace X] {t : ℝ} (ht : 0 < t) (f : X → EReal) :
    uscReg (fun x => (t : EReal) * f x) = fun x => (t : EReal) * uscReg f x := by
  have hcont := ProjBerk.continuous_ereal_coe_mul ht.ne'
  have hmono := ProjBerk.ereal_coe_mul_monotone ht.le
  have hcont' := ProjBerk.continuous_ereal_coe_mul (inv_ne_zero ht.ne')
  have hmono' := ProjBerk.ereal_coe_mul_monotone (inv_pos.2 ht).le
  refine le_antisymm (uscReg_le_of_le (hcont.comp_upperSemicontinuous
    (upperSemicontinuous_uscReg f) hmono) fun x => hmono (le_uscReg f x)) fun x => ?_
  have hle : uscReg f ≤ fun x => ((t⁻¹ : ℝ) : EReal) * uscReg (fun x => (t : EReal) * f x) x :=
    uscReg_le_of_le (hcont'.comp_upperSemicontinuous (upperSemicontinuous_uscReg _) hmono')
      fun x => by
        have := hmono' (le_uscReg (fun x => (t : EReal) * f x) x)
        simpa only [ProjBerk.ereal_inv_mul_mul ht.ne'] using this
  have := hmono (hle x)
  simpa only [ProjBerk.ereal_coe_mul_inv_mul ht.ne'] using this

/-- A tail `{i | i₀ ≤ i}` of a directed preorder is cofinal. -/
theorem tendsto_subtype_val_atTop {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] (i₀ : ι) :
    Tendsto (Subtype.val : {i // i₀ ≤ i} → ι) atTop atTop := by
  have := isDirected_subtype_le i₀
  have : Nonempty {i // i₀ ≤ i} := ⟨⟨i₀, le_rfl⟩⟩
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨c, h₁, h₂⟩ := directed_of (· ≤ ·) i₀ b
  exact eventually_atTop.2 ⟨⟨c, h₁⟩, fun j hj => h₂.trans hj⟩

/-! ### Rational cones and their closures (`lem:gl-cones`) -/

section RatCone

variable {r : ℕ}

/-- The closure `C̄ ⊆ ℝ^r` of a set `C ⊆ ℚ^r` of rational classes, i.e. of its image under the
coordinatewise cast `ℚ^r → ℝ^r`. For the semiample cone `C(𝒳)` of a model this is the model-nef
cone `N(𝒳)` (`def:gl-cones`). -/
def ratClosure (C : Set (Fin r → ℚ)) : Set (Fin r → ℝ) :=
  closure ((fun (a : Fin r → ℚ) (c : Fin r) => (a c : ℝ)) '' C)

theorem isClosed_ratClosure (C : Set (Fin r → ℚ)) : IsClosed (ratClosure C) :=
  isClosed_closure

theorem coe_mem_ratClosure {C : Set (Fin r → ℚ)} {a : Fin r → ℚ} (ha : a ∈ C) :
    (fun c => (a c : ℝ)) ∈ ratClosure C :=
  subset_closure ⟨a, ha, rfl⟩

theorem ratClosure_mono {C C' : Set (Fin r → ℚ)} (h : C ⊆ C') : ratClosure C ⊆ ratClosure C' :=
  closure_mono (image_mono h)

/-- The closure of a convex cone is closed under addition. -/
theorem add_mem_ratClosure {C : ConvexCone ℚ (Fin r → ℚ)} {θ θ' : Fin r → ℝ}
    (hθ : θ ∈ ratClosure (C : Set (Fin r → ℚ))) (hθ' : θ' ∈ ratClosure (C : Set (Fin r → ℚ))) :
    θ + θ' ∈ ratClosure (C : Set (Fin r → ℚ)) := by
  refine map_mem_closure₂ (f := fun x y : Fin r → ℝ => x + y) continuous_add hθ hθ' ?_
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  refine ⟨a + b, C.add_mem ha hb, ?_⟩
  funext c
  simp

/-- The closure of a convex cone of rational vectors is closed under multiplication by positive
reals. -/
theorem smul_mem_ratClosure {C : ConvexCone ℚ (Fin r → ℚ)} {θ : Fin r → ℝ}
    (hθ : θ ∈ ratClosure (C : Set (Fin r → ℚ))) {t : ℝ} (ht : 0 < t) :
    t • θ ∈ ratClosure (C : Set (Fin r → ℚ)) := by
  have h₁ : ∀ a ∈ (C : Set (Fin r → ℚ)),
      t • (fun c => (a c : ℝ)) ∈ ratClosure (C : Set (Fin r → ℚ)) := by
    intro a ha
    obtain ⟨q, -, hqt, hq⟩ := Real.exists_seq_rat_strictAnti_tendsto t
    have hqpos : ∀ n, (0 : ℚ) < q n := fun n => by exact_mod_cast ht.trans (hqt n)
    refine mem_closure_of_tendsto (hq.smul_const (fun c => (a c : ℝ)))
      (Eventually.of_forall fun n => ⟨q n • a, C.smul_mem (hqpos n) ha, ?_⟩)
    funext c
    simp
  have h₂ := map_mem_closure (f := fun x : Fin r → ℝ => t • x) (continuous_const_smul t) hθ
    (t := ratClosure (C : Set (Fin r → ℚ))) fun x hx => by
      obtain ⟨a, ha, rfl⟩ := hx
      exact h₁ a ha
  rwa [ratClosure, closure_closure] at h₂

variable {C : ConvexCone ℚ (Fin r → ℚ)} (hC : ∀ a : Fin r → ℚ, 0 ≤ a → a ∈ C)
include hC

/-- If `θ ∈ C̄`, every rational vector `a > θ` (coordinatewise) lies in `C`: some `b ∈ C` satisfies
`b < a`, and `a = b + (a - b) ∈ C + ℚ^r_{≥0} ⊆ C`. -/
theorem mem_of_lt_of_mem_ratClosure {θ : Fin r → ℝ} (hθ : θ ∈ ratClosure (C : Set (Fin r → ℚ)))
    {a : Fin r → ℚ} (ha : ∀ c, θ c < a c) : a ∈ C := by
  have hU : IsOpen {x : Fin r → ℝ | ∀ c, x c < a c} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun c => isOpen_lt (continuous_apply c) continuous_const
  obtain ⟨_, hx, b, hb, rfl⟩ := mem_closure_iff.1 hθ _ hU ha
  have hba : 0 ≤ a - b := fun c => by
    have h₁ : (b c : ℝ) < a c := hx c
    have h₂ : b c ≤ a c := by exact_mod_cast h₁.le
    simpa only [Pi.zero_apply, Pi.sub_apply, sub_nonneg] using h₂
  have := C.add_mem hb (hC _ hba)
  rwa [add_sub_cancel] at this

/-- `ℝ^r_{≥0} ⊆ C̄` (`lem:gl-cones`(1)). -/
theorem mem_ratClosure_of_nonneg {θ : Fin r → ℝ} (hθ : 0 ≤ θ) :
    θ ∈ ratClosure (C : Set (Fin r → ℚ)) := by
  obtain ⟨a, hθa, ha⟩ := exists_seq_rat_vec_gt_tendsto θ
  refine mem_closure_of_tendsto ha (Eventually.of_forall fun n => ⟨a n, hC _ fun c => ?_, rfl⟩)
  have h : (0 : ℝ) < a n c := (hθ c).trans_lt (hθa n c)
  show (0 : ℚ) ≤ a n c
  exact_mod_cast h.le

/-- **`lem:gl-cones`(3)**, re-indexed by `I × ℕ`: if `θ ∈ C̄` and `a_α → θ` is a net in `ℚ^r`,
then `a'_{(α, n)} = a_α ⊔ q_n`, for rationals `q_n > θ` with `q_n → θ`, is a net in `C` with
`a'_{(α, n)} ≥ a_α` and `a'_{(α, n)} → θ`. (Without re-indexing the statement fails for nets with
a greatest index, e.g. constant nets at a rational point of `C̄ ∖ C`.) -/
theorem exists_mem_ge_tendsto_of_mem_ratClosure {θ : Fin r → ℝ}
    (hθ : θ ∈ ratClosure (C : Set (Fin r → ℚ))) {ι : Type*} [Preorder ι] {a : ι → Fin r → ℚ}
    (ha : Tendsto (fun i c => (a i c : ℝ)) atTop (𝓝 θ)) :
    ∃ a' : ι × ℕ → Fin r → ℚ, (∀ p, a' p ∈ C) ∧ (∀ p, a p.1 ≤ a' p) ∧
      Tendsto (fun p c => (a' p c : ℝ)) atTop (𝓝 θ) := by
  obtain ⟨q, hθq, hq⟩ := exists_seq_rat_vec_gt_tendsto θ
  refine ⟨fun p => a p.1 ⊔ q p.2, fun p => mem_of_lt_of_mem_ratClosure hC hθ fun c => ?_,
    fun p => le_sup_left, ?_⟩
  · have h : q p.2 c ≤ (a p.1 ⊔ q p.2) c := (le_sup_right : q p.2 ≤ a p.1 ⊔ q p.2) c
    exact (hθq p.2 c).trans_le (by exact_mod_cast h)
  · refine tendsto_pi_nhds.2 fun c => ?_
    have h := ((tendsto_pi_nhds.1 ha c).comp ProjBerk.tendsto_prod_fst_atTop).max
      ((tendsto_pi_nhds.1 hq c).comp ProjBerk.tendsto_prod_snd_atTop)
    rw [max_self] at h
    refine h.congr fun p => ?_
    simp [Rat.cast_max]

end RatCone

/-! ### Fubini–Study systems with a semiample cone (`def:gl-fs-system`) -/

universe u

/-- A **Fubini–Study system with semiample cone `C`** of rank `r` on `(K, ⋆)` (`def:gl-fs-system`;
modelled on BJ22 `defi:FS`, `prop:FS`, `lem:FSgenfin`): predicates `IsFS a` (`𝓗(a)`) and
`IsFinFS a` (`𝓗_fin(a)`) on functions `K → [-∞, +∞)` for **all** classes `a ∈ ℚ^r`, and a convex
cone `C ⊆ ℚ^r` containing `ℚ^r_{≥0}`, such that (FS1), (FS2), (FS4) and stability under binary
maxima hold for all classes, and (FS3) (constants) and (FS5) (decreasing approximation by
`𝓗_fin(a)`) hold for `a ∈ C`. -/
structure FSSystemC (K : Type u) [TopologicalSpace K] (r : ℕ) where
  /-- The trivial point `⋆`. -/
  triv : K
  /-- The semiample cone `C ⊆ ℚ^r`. -/
  C : ConvexCone ℚ (Fin r → ℚ)
  /-- `ℚ^r_{≥0} ⊆ C`. -/
  nonneg_mem_C : ∀ a : Fin r → ℚ, 0 ≤ a → a ∈ C
  /-- `IsFS a f`: `f ∈ 𝓗(a)`. -/
  IsFS : (Fin r → ℚ) → (K → EReal) → Prop
  /-- `IsFinFS a f`: `f ∈ 𝓗_fin(a)`. -/
  IsFinFS : (Fin r → ℚ) → (K → EReal) → Prop
  /-- Fubini–Study functions are continuous. -/
  continuous_of_isFS : ∀ {a f}, IsFS a f → Continuous f
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
  /-- (FS3) real constants are in `𝓗(a)` for `a ∈ C`. -/
  isFS_const : ∀ {a}, a ∈ C → ∀ c : ℝ, IsFS a fun _ => (c : EReal)
  /-- (FS3) rational constants are in `𝓗_fin(a)` for `a ∈ C`. -/
  isFinFS_const : ∀ {a}, a ∈ C → ∀ c : ℚ, IsFinFS a fun _ => ((c : ℝ) : EReal)
  /-- `𝓗(a)` is stable under maxima. -/
  isFS_max : ∀ {a f g}, IsFS a f → IsFS a g → IsFS a fun x => Max.max (f x) (g x)
  /-- `𝓗_fin(a)` is stable under maxima. -/
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
  /-- (FS5) for `a ∈ C`, every `f ∈ 𝓗(a)` is the limit of a decreasing sequence in
  `𝓗_fin(a)`. -/
  exists_antitone_isFinFS : ∀ {a f}, a ∈ C → IsFS a f → ∃ g : ℕ → K → EReal,
    (∀ n, IsFinFS a (g n)) ∧ (∀ x, Antitone fun n => g n x) ∧ ∀ x, f x = ⨅ n, g n x

namespace FSSystemC

variable {K : Type u} [TopologicalSpace K] {r : ℕ} {F : FSSystemC K r}
  {a b : Fin r → ℚ} {f g : K → EReal}

/-! ### The cone and its closure -/

theorem zero_mem_C : (0 : Fin r → ℚ) ∈ F.C :=
  F.nonneg_mem_C 0 le_rfl

/-- `C + ℚ^r_{≥0} ⊆ C`. -/
theorem mem_C_of_le (ha : a ∈ F.C) (hab : a ≤ b) : b ∈ F.C := by
  have := F.C.add_mem ha (F.nonneg_mem_C (b - a) (sub_nonneg.2 hab))
  rwa [add_sub_cancel] at this

variable (F) in
/-- The closure `C̄ ⊆ ℝ^r` of the semiample cone (`thm:gl-fs-system-theory`); for the system of
a model this is the model-nef cone `N(𝒳)`. -/
def coneClosure : Set (Fin r → ℝ) :=
  ratClosure (F.C : Set (Fin r → ℚ))

variable (F) in
theorem isClosed_coneClosure : IsClosed F.coneClosure :=
  isClosed_ratClosure _

theorem coe_mem_coneClosure (ha : a ∈ F.C) : (fun c => (a c : ℝ)) ∈ F.coneClosure :=
  coe_mem_ratClosure ha

/-- `ℝ^r_{≥0} ⊆ C̄`. -/
theorem mem_coneClosure_of_nonneg {θ : Fin r → ℝ} (hθ : 0 ≤ θ) : θ ∈ F.coneClosure :=
  mem_ratClosure_of_nonneg F.nonneg_mem_C hθ

theorem add_mem_coneClosure {θ θ' : Fin r → ℝ} (hθ : θ ∈ F.coneClosure)
    (hθ' : θ' ∈ F.coneClosure) : θ + θ' ∈ F.coneClosure :=
  add_mem_ratClosure hθ hθ'

theorem smul_mem_coneClosure {θ : Fin r → ℝ} (hθ : θ ∈ F.coneClosure) {t : ℝ} (ht : 0 < t) :
    t • θ ∈ F.coneClosure :=
  smul_mem_ratClosure hθ ht

/-- Rational vectors `a > θ` with `θ ∈ C̄` lie in `C`. -/
theorem mem_C_of_lt {θ : Fin r → ℝ} (hθ : θ ∈ F.coneClosure) (ha : ∀ c, θ c < a c) : a ∈ F.C :=
  mem_of_lt_of_mem_ratClosure F.nonneg_mem_C hθ ha

/-! ### Fubini–Study functions -/

theorem IsFS.continuous (h : F.IsFS a f) : Continuous f := F.continuous_of_isFS h

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

/-- `𝓗(a)` is stable under addition of real constants, for every class `a` ((FS4) with the
constants of class `0 ∈ C`). -/
theorem IsFS.add_const (h : F.IsFS a f) (c : ℝ) : F.IsFS a fun x => f x + (c : EReal) := by
  simpa only [add_zero] using h.add (F.isFS_const zero_mem_C c)

/-- (FS3) `𝓗(a)` is stable under maxima with real constants for `a ∈ C`. -/
theorem IsFS.max_const (h : F.IsFS a f) (ha : a ∈ F.C) (c : ℝ) :
    F.IsFS a fun x => Max.max (f x) (c : EReal) :=
  h.max (F.isFS_const ha c)

/-- (FS5) for `a ∈ C`. -/
theorem IsFS.exists_antitone_isFinFS (h : F.IsFS a f) (ha : a ∈ F.C) : ∃ g : ℕ → K → EReal,
    (∀ n, F.IsFinFS a (g n)) ∧ (∀ x, Antitone fun n => g n x) ∧ ∀ x, f x = ⨅ n, g n x :=
  F.exists_antitone_isFinFS ha h

theorem IsFinFS.isFS (h : F.IsFinFS a f) : F.IsFS a f := F.isFS_of_isFinFS h

theorem IsFinFS.ne_bot (h : F.IsFinFS a f) (x : K) : f x ≠ ⊥ := F.ne_bot_of_isFinFS h x

theorem IsFinFS.ne_top (h : F.IsFinFS a f) (x : K) : f x ≠ ⊤ := h.isFS.ne_top x

theorem IsFinFS.continuous (h : F.IsFinFS a f) : Continuous f := h.isFS.continuous

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

/-- `𝓗_fin(a)` is stable under addition of rational constants. -/
theorem IsFinFS.add_const (h : F.IsFinFS a f) (c : ℚ) :
    F.IsFinFS a fun x => f x + ((c : ℝ) : EReal) := by
  simpa only [add_zero] using h.add (F.isFinFS_const zero_mem_C c)

/-- (FS3) `𝓗_fin(a)` is stable under maxima with rational constants for `a ∈ C`. -/
theorem IsFinFS.max_const (h : F.IsFinFS a f) (ha : a ∈ F.C) (c : ℚ) :
    F.IsFinFS a fun x => Max.max (f x) ((c : ℝ) : EReal) :=
  h.max (F.isFinFS_const ha c)

variable (F) in
/-- The families `𝓗(a)` restricted to the classes `a ∈ C` (empty for `a ∉ C`); these are the
families to which the diagonal lemma applies (they are stable under maxima with constants). -/
def semiampleFS (a : Fin r → ℚ) : Set (K → EReal) :=
  {f | a ∈ F.C ∧ F.IsFS a f}

/-! ### Psh functions -/

variable (F) in
/-- **`θ`-psh functions** of a Fubini–Study system with semiample cone (`def:gl-fs-system`,
BJ22 Definition 4.1): `u` is not identically `-∞`, upper semicontinuous, and the pointwise limit
(= infimum) of a decreasing net `fᵢ ∈ 𝓗(aᵢ)`, indexed by a nonempty directed preorder in the
universe of `K`, with `aᵢ → θ` in `ℝ^r`. -/
def IsPSH (θ : Fin r → ℝ) (u : K → EReal) : Prop :=
  (∃ x, u x ≠ ⊥) ∧ UpperSemicontinuous u ∧
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (a : ι → Fin r → ℚ) (f : ι → K → EReal), (∀ i, F.IsFS (a i) (f i)) ∧
        Tendsto (fun i c => (a i c : ℝ)) atTop (𝓝 θ) ∧ (∀ x, Antitone fun i => f i x) ∧
          ∀ x, u x = ⨅ i, f i x

variable {θ θ' : Fin r → ℝ} {u u' : K → EReal}

/-- `θ`-psh functions are the generically finite usc functions in BJ22's `F̃_θ`
(`IsDecrNetLimit`) for the families `𝓗(a)`. -/
theorem isPSH_iff_isDecrNetLimit : F.IsPSH θ u ↔ (∃ x, u x ≠ ⊥) ∧ UpperSemicontinuous u ∧
    IsDecrNetLimit.{u} (fun a => {f | F.IsFS a f}) (fun a c => (a c : ℝ)) θ u :=
  Iff.rfl

theorem IsPSH.exists_ne_bot (h : F.IsPSH θ u) : ∃ x, u x ≠ ⊥ := h.1

theorem IsPSH.upperSemicontinuous (h : F.IsPSH θ u) : UpperSemicontinuous u := h.2.1

/-- Constructing a `θ`-psh function from a decreasing net of Fubini–Study functions. -/
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

/-- A `θ`-psh function is the limit of a decreasing net of Fubini–Study functions, in the limit
form. -/
theorem IsPSH.exists_tendsto (h : F.IsPSH θ u) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (a : ι → Fin r → ℚ) (f : ι → K → EReal), (∀ i, F.IsFS (a i) (f i)) ∧
        Tendsto (fun i c => (a i c : ℝ)) atTop (𝓝 θ) ∧ (∀ x, Antitone fun i => f i x) ∧
          ∀ x, Tendsto (fun i => f i x) atTop (𝓝 (u x)) := by
  obtain ⟨-, -, ι, _, _, _, a, f, hf, ha, hanti, hu⟩ := h
  exact ⟨ι, inferInstance, inferInstance, inferInstance, a, f, hf, ha, hanti, fun x => by
    rw [hu x]; exact tendsto_atTop_iInf (hanti x)⟩

/-! ### Part (1): the maximum principle -/

/-- **The maximum principle** (`thm:gl-fs-system-theory`(1)), pointwise form: `u ≤ u(⋆)`. -/
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

/-- **The maximum principle** (`thm:gl-fs-system-theory`(1)): a `θ`-psh function attains its
supremum at `⋆`. -/
theorem IsPSH.iSup_eq (h : F.IsPSH θ u) : ⨆ x, u x = u F.triv :=
  le_antisymm (iSup_le h.le_apply_triv) (le_iSup u F.triv)

/-! ### Part (1): PSH1, maxima, translates, sums, rational scaling, monotonicity -/

/-- **PSH1** (`thm:gl-fs-system-theory`(1)): `𝓗(a) ⊆ PSH(a)` (constant net). -/
theorem IsFS.isPSH (h : F.IsFS a f) : F.IsPSH (fun c => (a c : ℝ)) f :=
  isPSH_of_iInf ⟨F.triv, h.apply_triv_ne_bot⟩ (ι := PUnit.{u + 1}) (fun _ => a) (fun _ => f)
    (fun _ => h) tendsto_const_nhds (fun _ _ _ _ => le_rfl) fun _ => (iInf_const).symm

theorem IsFinFS.isPSH (h : F.IsFinFS a f) : F.IsPSH (fun c => (a c : ℝ)) f :=
  h.isFS.isPSH

/-- **Adding a real constant** preserves `θ`-psh functions (`thm:gl-fs-system-theory`(1)). -/
theorem IsPSH.add_const (h : F.IsPSH θ u) (c : ℝ) : F.IsPSH θ fun x => u x + (c : EReal) := by
  have hfin := h.apply_triv_ne_bot
  obtain ⟨ι, _, _, _, a, f, hf, ha, hanti, hlim⟩ := h.exists_tendsto
  exact isPSH_of_tendsto ⟨F.triv, ProjBerk.ereal_add_coe_ne_bot hfin c⟩ a
    (fun i x => f i x + (c : EReal)) (fun i => (hf i).add_const c) ha
    (fun x _ _ hij => add_le_add_left (hanti x hij) _)
    fun x => ((ProjBerk.continuous_ereal_add_coe c).tendsto _).comp (hlim x)

/-- **Sums** (`thm:gl-fs-system-theory`(1)): `PSH(θ) + PSH(θ') ⊆ PSH(θ + θ')`, using the product
net. -/
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

/-- **Positive rational multiples** (`thm:gl-fs-system-theory`(1)): `c PSH(θ) ⊆ PSH(c θ)` for
`c ∈ ℚ_{>0}`. -/
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

/-- **Maxima** (`thm:gl-fs-system-theory`(1); BJ22 `lem:twopsh`): on the product net, both
approximants are Fubini–Study functions of the coordinatewise maximum of their classes (FS2). -/
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

/-- **Finite maxima** (`thm:gl-fs-system-theory`(1)). -/
theorem isPSH_finset_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {w : ι → K → EReal}
    (hw : ∀ i ∈ s, F.IsPSH θ (w i)) : F.IsPSH θ fun x => s.sup' hs fun i => w i x := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa only [Finset.sup'_singleton] using hw a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    simp only [Finset.sup'_cons hs]
    exact (hw a (Finset.mem_cons_self a s)).max
      (ih fun i hi => hw i (Finset.mem_cons_of_mem hi))

/-- **Constants** are `θ`-psh for every `θ ∈ C̄` (`thm:gl-fs-system-theory`(2)): they lie in
`𝓗(aₙ)` for rational vectors `aₙ > θ` converging to `θ`, which lie in `C`. -/
theorem isPSH_const (hθ : θ ∈ F.coneClosure) (c : ℝ) : F.IsPSH θ fun _ => (c : EReal) := by
  obtain ⟨a, hθa, ha⟩ := exists_seq_rat_vec_gt_tendsto θ
  have hdown : Tendsto (ULift.down : ULift.{u} ℕ → ℕ) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨ULift.up b, fun a ha => ha⟩
  exact isPSH_of_iInf ⟨F.triv, EReal.coe_ne_bot c⟩ (ι := ULift.{u} ℕ) (fun n => a n.down)
    (fun _ _ => (c : EReal)) (fun n => F.isFS_const (mem_C_of_lt hθ (hθa n.down)) c)
    (ha.comp hdown) (fun _ _ _ _ => le_rfl) fun _ => iInf_const.symm

/-- Constants are `θ`-psh for `θ ≥ 0`. -/
theorem isPSH_const_of_nonneg (hθ : 0 ≤ θ) (c : ℝ) : F.IsPSH θ fun _ => (c : EReal) :=
  isPSH_const (mem_coneClosure_of_nonneg hθ) c

/-- **Monotonicity in the class** (`thm:gl-fs-system-theory`(1)): `PSH(θ) ⊆ PSH(θ')` for
`θ ≤ θ'`, by adding the function `0`, which is `(θ' - θ)`-psh. -/
theorem IsPSH.mono_class (h : F.IsPSH θ u) (hθθ' : θ ≤ θ') : F.IsPSH θ' u := by
  have h' := h.add (isPSH_const_of_nonneg (F := F) (sub_nonneg.2 hθθ') 0)
  rw [add_sub_cancel] at h'
  simpa only [EReal.coe_zero, add_zero] using h'

/-! ### Part (2): approximating nets with classes in `C`, and PSH2 -/

/-- If `u ∈ PSH(τ)` and `τ > θ₀` coordinatewise for some `θ₀ ∈ C̄`, then the classes of an
approximating net of `u` are eventually `> θ₀`, hence in `C`: `u` is a decreasing limit of a net
in the families `𝓗(a)`, `a ∈ C`. -/
theorem IsPSH.isDecrNetLimit_semiampleFS_of_lt {τ : Fin r → ℝ} (h : F.IsPSH τ u)
    {θ₀ : Fin r → ℝ} (hθ₀ : θ₀ ∈ F.coneClosure) (hlt : ∀ c, θ₀ c < τ c) :
    IsDecrNetLimit.{u} F.semiampleFS (fun a c => (a c : ℝ)) τ u := by
  obtain ⟨-, -, ι, _, _, _, a, f, hf, ha, hanti, hu⟩ := h
  have hev : ∀ᶠ i in atTop, a i ∈ F.C := by
    have : ∀ᶠ i in atTop, ∀ c, θ₀ c < a i c :=
      eventually_all.2 fun c => (tendsto_pi_nhds.1 ha c).eventually (lt_mem_nhds (hlt c))
    exact this.mono fun i hi => mem_C_of_lt hθ₀ hi
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 hev
  have := isDirected_subtype_le i₀
  have : Nonempty {i // i₀ ≤ i} := ⟨⟨i₀, le_rfl⟩⟩
  refine ⟨{i // i₀ ≤ i}, inferInstance, inferInstance, inferInstance, fun i => a i, fun i => f i,
    fun i => ⟨hi₀ i i.2, hf i⟩, ha.comp (tendsto_subtype_val_atTop i₀),
    fun x i j hij => hanti x hij, fun x => ?_⟩
  rw [hu x]
  exact (iInf_subtype_le_eq_iInf_of_antitone (f := fun i => f i x) (hanti x) i₀).symm

/-- **The diagonal lemma for `C̄`** (`thm:gl-fs-system-theory`(2)): if `θ₀ ∈ C̄`, `uᵢ ∈ PSH(θᵢ)` is
a decreasing net with `θᵢ → θ₀` and `w = infᵢ uᵢ`, then `w` is the limit of a decreasing net in
the families `𝓗(a)`, `a ∈ C`, with classes converging to `θ₀`. On the index set `I × ℕ`, `uᵢ` is
psh of class `τ_{(i, n)} = θᵢ ⊔ θ₀ + (n + 1)⁻¹ 𝟙 > θ₀`, and BJ22 `lem:PSH`
(`IsDecrNetLimit.of_antitone`) applies to the families `𝓗(a)`, `a ∈ C`, which are stable under
addition of and maxima with real constants. -/
theorem isDecrNetLimit_semiampleFS_of_antitone [CompactSpace K] {θ₀ : Fin r → ℝ}
    (hθ₀ : θ₀ ∈ F.coneClosure) {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {θ : ι → Fin r → ℝ} (hθ : Tendsto θ atTop (𝓝 θ₀)) {u : ι → K → EReal}
    (hu : ∀ i, F.IsPSH (θ i) (u i)) (hanti : ∀ x, Antitone fun i => u i x) {w : K → EReal}
    (hw : ∀ x, w x = ⨅ i, u i x) :
    IsDecrNetLimit.{u} F.semiampleFS (fun a c => (a c : ℝ)) θ₀ w := by
  have : IsDirected (ι × ULift.{u} ℕ) (· ≤ ·) := isDirected_prod
  set τ : ι × ULift.{u} ℕ → Fin r → ℝ :=
    fun p c => Max.max (θ p.1 c) (θ₀ c) + 1 / ((p.2.down : ℝ) + 1) with hτ_def
  have hτ : Tendsto τ atTop (𝓝 θ₀) := by
    refine tendsto_pi_nhds.2 fun c => ?_
    have h₁ := ((tendsto_pi_nhds.1 hθ c).comp ProjBerk.tendsto_prod_fst_atTop).max
      (tendsto_const_nhds (x := θ₀ c) (f := (atTop : Filter (ι × ULift.{u} ℕ))))
    have hdown : Tendsto (fun p : ι × ULift.{u} ℕ => p.2.down) atTop atTop :=
      (tendsto_atTop_atTop.2 fun n => ⟨ULift.up n, fun m hm => hm⟩).comp
        ProjBerk.tendsto_prod_snd_atTop
    have h₂ := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hdown
    have := h₁.add h₂
    rw [max_self, add_zero] at this
    exact this
  have hlt : ∀ p c, θ₀ c < τ p c := fun p c =>
    (le_max_right _ _).trans_lt (lt_add_of_pos_right _ (by positivity))
  have hle : ∀ p, θ p.1 ≤ τ p := fun p c =>
    (le_max_left _ _).trans (le_add_of_nonneg_right (by positivity))
  have hg : ∀ p : ι × ULift.{u} ℕ,
      IsDecrNetLimit.{u} F.semiampleFS (fun a c => (a c : ℝ)) (τ p) (u p.1) := fun p =>
    ((hu p.1).mono_class (hle p)).isDecrNetLimit_semiampleFS_of_lt hθ₀ (hlt p)
  refine IsDecrNetLimit.of_antitone (F := F.semiampleFS) (ρ := fun a c => (a c : ℝ))
    (fun _ f hf => hf.2.continuous) (fun _ f hf => hf.2.ne_top)
    (fun _ f hf c => ⟨hf.1, hf.2.add_const c⟩) (fun _ f hf c => ⟨hf.1, hf.2.max_const hf.1 c⟩)
    (I := ι × ULift.{u} ℕ) (g := fun p => u p.1) hτ hg
    (fun x p q hpq => hanti x (Prod.le_def.1 hpq).1) fun x => ?_
  rw [hw x, iInf_prod]
  exact iInf_congr fun i => iInf_const.symm

/-- A `θ`-psh function with `θ ∈ C̄` is the limit of a decreasing net in the families `𝓗(a)`,
`a ∈ C`, with classes converging to `θ` (`lem:gl-cones`(3) in the form used by
`thm:gl-fs-system-theory`(2)). -/
theorem IsPSH.isDecrNetLimit_semiampleFS [CompactSpace K] (h : F.IsPSH θ u)
    (hθ : θ ∈ F.coneClosure) :
    IsDecrNetLimit.{u} F.semiampleFS (fun a c => (a c : ℝ)) θ u :=
  isDecrNetLimit_semiampleFS_of_antitone hθ (ι := PUnit.{u + 1}) (θ := fun _ => θ)
    tendsto_const_nhds (fun _ => h) (fun _ _ _ _ => le_rfl) fun _ => iInf_const.symm

/-- **PSH2** (`thm:gl-fs-system-theory`(2); BJ22 `thm:psh12`): if `θ₀ ∈ C̄`, `uᵢ ∈ PSH(θᵢ)` is a
decreasing net with `θᵢ → θ₀` and the pointwise limit `w = infᵢ uᵢ` is not identically `-∞`, then
`w ∈ PSH(θ₀)`. -/
theorem isPSH_of_antitone [CompactSpace K] {θ₀ : Fin r → ℝ} (hθ₀ : θ₀ ∈ F.coneClosure)
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] {θ : ι → Fin r → ℝ}
    (hθ : Tendsto θ atTop (𝓝 θ₀)) {u : ι → K → EReal} (hu : ∀ i, F.IsPSH (θ i) (u i))
    (hanti : ∀ x, Antitone fun i => u i x) {w : K → EReal} (hw : ∀ x, w x = ⨅ i, u i x)
    (hfin : ∃ x, w x ≠ ⊥) : F.IsPSH θ₀ w := by
  refine isPSH_iff_isDecrNetLimit.2 ⟨hfin, ?_,
    (isDecrNetLimit_semiampleFS_of_antitone hθ₀ hθ hu hanti hw).mono fun _ _ hf => hf.2⟩
  rw [show w = fun x => ⨅ i, u i x from funext hw]
  exact upperSemicontinuous_iInf fun i => (hu i).upperSemicontinuous

/-- **PSH2**, limit form. -/
theorem isPSH_of_tendsto_of_antitone [CompactSpace K] {θ₀ : Fin r → ℝ}
    (hθ₀ : θ₀ ∈ F.coneClosure) {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {θ : ι → Fin r → ℝ} (hθ : Tendsto θ atTop (𝓝 θ₀)) {u : ι → K → EReal}
    (hu : ∀ i, F.IsPSH (θ i) (u i)) (hanti : ∀ x, Antitone fun i => u i x) {w : K → EReal}
    (hw : ∀ x, Tendsto (fun i => u i x) atTop (𝓝 (w x))) (hfin : ∃ x, w x ≠ ⊥) :
    F.IsPSH θ₀ w :=
  isPSH_of_antitone hθ₀ hθ hu hanti
    (fun x => tendsto_nhds_unique (hw x) (tendsto_atTop_iInf (hanti x))) hfin

/-- **PSH2** for decreasing sequences. -/
theorem isPSH_of_antitone_seq [CompactSpace K] {θ₀ : Fin r → ℝ} (hθ₀ : θ₀ ∈ F.coneClosure)
    {θ : ℕ → Fin r → ℝ} (hθ : Tendsto θ atTop (𝓝 θ₀)) {u : ℕ → K → EReal}
    (hu : ∀ m, F.IsPSH (θ m) (u m)) (hanti : ∀ x, Antitone fun m => u m x) {w : K → EReal}
    (hw : ∀ x, w x = ⨅ m, u m x) (hfin : ∃ x, w x ≠ ⊥) : F.IsPSH θ₀ w := by
  have hdown : Tendsto (ULift.down : ULift.{u} ℕ → ℕ) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨ULift.up b, fun a ha => ha⟩
  refine isPSH_of_antitone hθ₀ (ι := ULift.{u} ℕ) (hθ.comp hdown) (fun m => hu m.down)
    (fun x _ _ h => hanti x h) (fun x => ?_) hfin
  rw [hw x]
  exact (Equiv.ulift.iInf_comp (g := fun m => u m x)).symm

/-! ### Part (2): real scaling -/

/-- **Positive real multiples** (`thm:gl-fs-system-theory`(2)): `t PSH(θ) ⊆ PSH(t θ)` for
`θ ∈ C̄` and real `t > 0`. After replacing `u` with `u - u(⋆) ≤ 0`, take rationals `tₘ ↑ t`:
`tₘ u ∈ PSH(tₘ θ)` decreases to `t u`, and PSH2 applies at `t θ ∈ C̄`. -/
theorem IsPSH.smul [CompactSpace K] (h : F.IsPSH θ u) (hθ : θ ∈ F.coneClosure) {t : ℝ}
    (ht : 0 < t) : F.IsPSH (t • θ) fun x => (t : EReal) * u x := by
  set c := (u F.triv).toReal with hc_def
  set u₀ : K → EReal := fun x => u x + ((-c : ℝ) : EReal) with hu₀_def
  have h₀ : F.IsPSH θ u₀ := h.add_const (-c)
  have hu₀ : ∀ x, u₀ x ≤ 0 := fun x => by
    have := add_le_add_left (h.le_toReal_apply_triv x) ((-c : ℝ) : EReal)
    rwa [← hc_def, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at this
  obtain ⟨q, hqmono, -, hq⟩ := Real.exists_seq_rat_strictMono_tendsto t
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hq.eventually (lt_mem_nhds ht))
  set q' : ℕ → ℚ := fun m => q (m + N) with hq'_def
  have hq'pos : ∀ m, (0 : ℝ) < q' m := fun m => hN _ (Nat.le_add_left N m)
  have hq'pos' : ∀ m, (0 : ℚ) < q' m := fun m => by exact_mod_cast hq'pos m
  have hq'lim : Tendsto (fun m => (q' m : ℝ)) atTop (𝓝 t) := hq.comp (tendsto_add_atTop_nat N)
  have hq'mono : Monotone fun m => (q' m : ℝ) := fun m m' h => by
    show (q (m + N) : ℝ) ≤ q (m' + N)
    exact_mod_cast hqmono.monotone (Nat.add_le_add_right h N)
  have htu₀ : F.IsPSH (t • θ) fun x => (t : EReal) * u₀ x := by
    refine isPSH_of_antitone_seq (smul_mem_coneClosure hθ ht) (θ := fun m => (q' m : ℝ) • θ)
      (hq'lim.smul_const θ) (fun m => h₀.smul_rat (hq'pos' m))
      (fun x m m' hmm' => ProjBerk.ereal_coe_mul_le_of_nonpos (hq'pos m) (hq'mono hmm') (hu₀ x))
      (fun x => tendsto_nhds_unique
        (ProjBerk.tendsto_coe_mul_ereal hq'lim ht hq'pos (h₀.ne_top x))
        (tendsto_atTop_iInf fun m m' hmm' =>
          ProjBerk.ereal_coe_mul_le_of_nonpos (hq'pos m) (hq'mono hmm') (hu₀ x)))
      ⟨F.triv, ProjBerk.ereal_coe_mul_ne_bot ht.le h₀.apply_triv_ne_bot⟩
  convert htu₀.add_const (t * c) using 2 with x
  rw [hu₀_def, ProjBerk.ereal_coe_mul_add ht.le, ← EReal.coe_mul, add_assoc, ← EReal.coe_add,
    mul_neg, neg_add_cancel, EReal.coe_zero, add_zero]

/-- **`PSH(t θ) = t PSH(θ)`** for `θ ∈ C̄` (`thm:gl-fs-system-theory`(2)), pointwise form. -/
theorem isPSH_smul_iff [CompactSpace K] (hθ : θ ∈ F.coneClosure) {t : ℝ} (ht : 0 < t) :
    F.IsPSH (t • θ) (fun x => (t : EReal) * u x) ↔ F.IsPSH θ u := by
  refine ⟨fun h => ?_, fun h => h.smul hθ ht⟩
  have h' := h.smul (smul_mem_coneClosure hθ ht) (inv_pos.2 ht)
  rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h'
  simpa only [ProjBerk.ereal_inv_mul_mul ht.ne'] using h'

/-- **`PSH(t θ) = t PSH(θ)`** for `θ ∈ C̄` (`thm:gl-fs-system-theory`(2)), as an equality of
sets. -/
theorem setOf_isPSH_smul [CompactSpace K] (hθ : θ ∈ F.coneClosure) {t : ℝ} (ht : 0 < t) :
    {w : K → EReal | F.IsPSH (t • θ) w} =
      (fun u x => (t : EReal) * u x) '' {u | F.IsPSH θ u} := by
  ext w
  constructor
  · intro hw
    refine ⟨fun x => ((t⁻¹ : ℝ) : EReal) * w x, ?_, funext fun x => ?_⟩
    · have h' := IsPSH.smul (u := w) hw (smul_mem_coneClosure hθ ht) (inv_pos.2 ht)
      rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h'
    · exact ProjBerk.ereal_coe_mul_inv_mul ht.ne' (w x)
  · rintro ⟨u, hu, rfl⟩
    exact IsPSH.smul hu hθ ht

/-! ### Part (2): regularization -/

/-- `θ`-psh functions with `θ ∈ C̄` are decreasing limits of **finite** Fubini–Study functions
(`thm:pg-psh2`(2) for the system), as an element of BJ22's `F̃_θ` for the families `𝓗_fin(b)`:
each approximant `fᵢ ∈ 𝓗(aᵢ)`, `aᵢ ∈ C`, is a decreasing limit of a sequence in `𝓗_fin(aᵢ)`
(FS5), and the diagonal lemma `IsDecrNetLimit.of_antitone_of_finite_rat` applies. -/
theorem IsPSH.isDecrNetLimit_isFinFS [CompactSpace K] (h : F.IsPSH θ u)
    (hθ : θ ∈ F.coneClosure) :
    IsDecrNetLimit.{u} (fun a => {f | F.IsFinFS a f}) (fun a c => (a c : ℝ)) θ u := by
  obtain ⟨ι, _, _, _, a, f, hf, ha, hanti, hu⟩ := h.isDecrNetLimit_semiampleFS hθ
  refine IsDecrNetLimit.of_antitone_of_finite_rat (F := fun a => {f | F.IsFinFS a f})
    (ρ := fun a c => (a c : ℝ)) (fun _ g hg => IsFinFS.continuous hg)
    (fun _ g hg x => ⟨IsFinFS.ne_bot hg x, IsFinFS.ne_top hg x⟩)
    (fun _ g hg c _ => IsFinFS.add_const hg c) ha (fun i => ?_) hanti hu
  obtain ⟨g, hg, hganti, hgf⟩ := (hf i).2.exists_antitone_isFinFS (hf i).1
  exact IsDecrNetLimit.of_seq (fun _ => a i) g hg tendsto_const_nhds hganti hgf

/-- `θ`-psh functions with `θ ∈ C̄` are decreasing limits of nets of **finite** Fubini–Study
functions with classes converging to `θ`. -/
theorem IsPSH.exists_isFinFS_net [CompactSpace K] (h : F.IsPSH θ u) (hθ : θ ∈ F.coneClosure) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (b : ι → Fin r → ℚ) (g : ι → K → EReal), (∀ i, F.IsFinFS (b i) (g i)) ∧
        Tendsto (fun i c => (b i c : ℝ)) atTop (𝓝 θ) ∧ (∀ x, Antitone fun i => g i x) ∧
          ∀ x, u x = ⨅ i, g i x :=
  h.isDecrNetLimit_isFinFS hθ

/-- For `θ ∈ C̄`, `u` is `θ`-psh iff `u ≢ -∞` and `u` is the limit of a decreasing net
`gᵦ ∈ 𝓗_fin(bᵦ)` with `bᵦ → θ`. -/
theorem isPSH_iff_exists_isFinFS [CompactSpace K] (hθ : θ ∈ F.coneClosure) :
    F.IsPSH θ u ↔ (∃ x, u x ≠ ⊥) ∧
      ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
        (b : ι → Fin r → ℚ) (g : ι → K → EReal), (∀ i, F.IsFinFS (b i) (g i)) ∧
          Tendsto (fun i c => (b i c : ℝ)) atTop (𝓝 θ) ∧ (∀ x, Antitone fun i => g i x) ∧
            ∀ x, u x = ⨅ i, g i x := by
  refine ⟨fun h => ⟨h.exists_ne_bot, h.exists_isFinFS_net hθ⟩, ?_⟩
  rintro ⟨hfin, ι, _, _, _, b, g, hg, hb, hanti, hu⟩
  exact isPSH_of_iInf hfin b g (fun i => (hg i).isFS) hb hanti hu

/-- **Regularization** (`thm:gl-fs-system-theory`(2) with `thm:pg-regularization`(1)): for
`θ ∈ C̄`, every `u ∈ PSH(θ)` is the pointwise limit (= infimum) of a decreasing net
`f_α ∈ 𝓗_fin(a_α)` with `a_α > θ` coordinatewise and `a_α → θ`. -/
theorem IsPSH.exists_isFinFS_net_gt [CompactSpace K] (h : F.IsPSH θ u) (hθ : θ ∈ F.coneClosure) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (a : ι → Fin r → ℚ) (f : ι → K → EReal), (∀ i, F.IsFinFS (a i) (f i)) ∧
        (∀ i c, θ c < a i c) ∧ Tendsto (fun i c => (a i c : ℝ)) atTop (𝓝 θ) ∧
          (∀ x, Antitone fun i => f i x) ∧ ∀ x, u x = ⨅ i, f i x := by
  obtain ⟨ι, _, _, _, b, g, hg, hb, hanti, hu⟩ := h.exists_isFinFS_net hθ
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

/-- **Regularization in a fixed class** (`thm:gl-fs-system-theory`(2) with
`thm:pg-regularization`(2)): if `θ ∈ ℚ^r` has positive coordinates, every `u ∈ PSH(θ)` is the
pointwise limit (= infimum) of a decreasing net in `𝓗_fin(θ)`. The proof is the one of
`FSSystem.IsPSH.exists_isFinFS_net_of_pos`. -/
theorem IsPSH.exists_isFinFS_net_of_pos [CompactSpace K] {θ : Fin r → ℚ} (hθ : ∀ c, 0 < θ c)
    (h : F.IsPSH (fun c => (θ c : ℝ)) u) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (f : ι → K → EReal), (∀ i, F.IsFinFS θ (f i)) ∧ (∀ x, Antitone fun i => f i x) ∧
        ∀ x, u x = ⨅ i, f i x := by
  have hθC : (fun c => (θ c : ℝ)) ∈ F.coneClosure :=
    coe_mem_coneClosure (F.nonneg_mem_C θ fun c => (hθ c).le)
  set G : Unit → Set (K → EReal) := fun _ => {f | F.IsFinFS θ f} with hG
  set ρ : Unit → ℝ := fun _ => 0 with hρ
  have hGcont : ∀ s, ∀ f ∈ G s, Continuous f := fun _ f hf => IsFinFS.continuous hf
  have hGfin : ∀ s, ∀ f ∈ G s, ∀ x, f x ≠ ⊥ ∧ f x ≠ ⊤ := fun _ f hf x =>
    ⟨IsFinFS.ne_bot hf x, IsFinFS.ne_top hf x⟩
  have hGadd : ∀ s, ∀ f ∈ G s, ∀ c : ℚ, 0 < c → (fun x => f x + ((c : ℝ) : EReal)) ∈ G s :=
    fun _ f hf c _ => IsFinFS.add_const hf c
  obtain ⟨M, hM⟩ := exists_rat_gt (u F.triv).toReal
  set u' : K → EReal := fun x => u x + ((-(M : ℝ) : ℝ) : EReal) with hu'_def
  have h' : F.IsPSH (fun c => (θ c : ℝ)) u' := h.add_const _
  have hu'0 : ∀ x, u' x ≤ 0 := fun x => by
    have h₁ : u x ≤ ((M : ℝ) : EReal) :=
      (h.le_toReal_apply_triv x).trans (EReal.coe_le_coe_iff.2 hM.le)
    have := add_le_add_left h₁ ((-(M : ℝ) : ℝ) : EReal)
    rwa [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at this
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
  have hstep : ∀ m, IsDecrNetLimit.{u} G ρ 0 fun x => ((σ m : ℝ) : EReal) * u' x := by
    intro m
    obtain ⟨ι, _, _, _, b, g, hg, hb, hanti, hu⟩ := h'.exists_isFinFS_net hθC
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
  have hanti' : ∀ x, Antitone fun m => ((σ m : ℝ) : EReal) * u' x := fun x m m' hmm' =>
    ProjBerk.ereal_coe_mul_le_of_nonpos (hσpos' m) (hσmono hmm') (hu'0 x)
  have hlim : ∀ x, u' x = ⨅ m, ((σ m : ℝ) : EReal) * u' x := fun x => by
    have := ProjBerk.tendsto_coe_mul_ereal hσlim one_pos hσpos' (h'.ne_top x)
    rw [EReal.coe_one, one_mul] at this
    exact tendsto_nhds_unique this (tendsto_atTop_iInf (hanti' x))
  have hu' : IsDecrNetLimit.{u} G ρ 0 u' :=
    IsDecrNetLimit.of_antitone_of_finite_rat hGcont hGfin hGadd (I := ULift.{u} ℕ)
      (τ := fun _ => (0 : ℝ)) tendsto_const_nhds
      (g := fun m x => ((σ m.down : ℝ) : EReal) * u' x) (fun m => hstep m.down)
      (fun x m m' hmm' => hanti' x hmm') fun x =>
        (hlim x).trans (Equiv.ulift.iInf_comp (g := fun m => ((σ m : ℝ) : EReal) * u' x)).symm
  obtain ⟨ι, _, _, _, s, f, hf, -, hanti, hinf⟩ := hu'
  refine ⟨ι, inferInstance, inferInstance, inferInstance, fun i x => f i x + ((M : ℝ) : EReal),
    fun i => IsFinFS.add_const (show F.IsFinFS θ (f i) from hf i) M,
    fun x i j hij => add_le_add_left (hanti x hij) _, fun x => ?_⟩
  rw [← ereal_iInf_add_coe, ← hinf x]
  exact (ProjBerk.ereal_add_neg_add_coe (u x) (M : ℝ)).symm

/-- **Countable regularization** (`thm:gl-fs-system-theory`(2) with
`cor:pg-countable-regularization`(1)): if `K` is second countable and `θ ∈ C̄`, every
`u ∈ PSH(θ)` is the pointwise limit of a decreasing **sequence** `f_m ∈ 𝓗_fin(a_m)` with
`a_m > θ` coordinatewise and `a_m → θ`. -/
theorem IsPSH.exists_isFinFS_seq_gt [CompactSpace K] [SecondCountableTopology K]
    (h : F.IsPSH θ u) (hθ : θ ∈ F.coneClosure) :
    ∃ (a : ℕ → Fin r → ℚ) (f : ℕ → K → EReal), (∀ m, F.IsFinFS (a m) (f m)) ∧
      (∀ m c, θ c < a m c) ∧ Tendsto (fun m c => (a m c : ℝ)) atTop (𝓝 θ) ∧
        (∀ x, Antitone fun m => f m x) ∧ ∀ x, u x = ⨅ m, f m x := by
  obtain ⟨ι, _, _, _, a, f, hf, hθa, ha, hanti, hinf⟩ := h.exists_isFinFS_net_gt hθ
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

/-- **Countable regularization in a fixed class** (`thm:gl-fs-system-theory`(2) with
`cor:pg-countable-regularization`(1)): if `K` is second countable and `θ ∈ ℚ^r` has positive
coordinates, every `u ∈ PSH(θ)` is the pointwise limit of a decreasing sequence in `𝓗_fin(θ)`. -/
theorem IsPSH.exists_isFinFS_seq_of_pos [CompactSpace K] [SecondCountableTopology K]
    {θ : Fin r → ℚ} (hθ : ∀ c, 0 < θ c) (h : F.IsPSH (fun c => (θ c : ℝ)) u) :
    ∃ f : ℕ → K → EReal, (∀ m, F.IsFinFS θ (f m)) ∧ (∀ x, Antitone fun m => f m x) ∧
      ∀ x, u x = ⨅ m, f m x := by
  obtain ⟨ι, _, _, _, f, hf, hanti, hinf⟩ := h.exists_isFinFS_net_of_pos hθ
  obtain ⟨i, hmono, -, hiInf⟩ := exists_monotone_iInf_eq
    (fun i => (hf i).continuous.upperSemicontinuous) hanti fun _ => Classical.arbitrary ι
  exact ⟨fun m => f (i m), fun m => hf (i m), fun x m m' hmm' => hanti x (hmono hmm'),
    fun x => by rw [hiInf x, hinf x]⟩

/-- **Dyadic countable regularization** (`thm:gl-fs-system-theory`(2) with
`cor:pg-countable-regularization`(2)): if `K` is second countable and `θ ∈ ℚ^r ∩ C̄`, every
`u ∈ PSH(θ)` is the pointwise limit of a decreasing sequence `f_k ∈ 𝓗_fin(θ + 2^{-k} 𝟙)`. -/
theorem IsPSH.exists_isFinFS_seq_dyadic [CompactSpace K] [SecondCountableTopology K]
    {θ : Fin r → ℚ} (hθ : (fun c => (θ c : ℝ)) ∈ F.coneClosure)
    (h : F.IsPSH (fun c => (θ c : ℝ)) u) :
    ∃ f : ℕ → K → EReal, (∀ k, F.IsFinFS (θ + fun _ => ((2 : ℚ) ^ k)⁻¹) (f k)) ∧
      (∀ x, Antitone fun k => f k x) ∧ ∀ x, u x = ⨅ k, f k x := by
  obtain ⟨a, f, hf, -, ha, hanti, hinf⟩ := h.exists_isFinFS_seq_gt hθ
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

/-! ### Envelopes and the envelope property (`def:gl-psh`, `lem:gl-ep-basic`) -/

variable (F) in
/-- The **psh envelope** `P_θ(φ)(x) = sup {τ(x) : τ ∈ PSH(θ), τ ≤ φ}` (`def:gl-psh`, `def:sg-ep`;
FHX §2.3): a pointwise supremum without usc regularization, `⊥` if there is no competitor. -/
def envelope (θ : Fin r → ℝ) (φ : K → EReal) (x : K) : EReal :=
  ⨆ (τ : K → EReal) (_ : F.IsPSH θ τ ∧ τ ≤ φ), τ x

variable (F) in
/-- The **envelope property** of a class `θ ∈ ℝ^r` (`def:gl-psh`; BJ22 §5.2): for every nonempty
family `S ⊆ PSH(θ)` uniformly bounded above, the usc regularization `(sup S)^⋆` of its pointwise
supremum is `θ`-psh. -/
def HasEnvelopeProperty (θ : Fin r → ℝ) : Prop :=
  ∀ S : Set (K → EReal), S.Nonempty → (∀ u ∈ S, F.IsPSH θ u) →
    (∃ C : ℝ, ∀ u ∈ S, ∀ x, u x ≤ C) → F.IsPSH θ (uscReg fun x => ⨆ u ∈ S, u x)

variable {φ ψ : K → EReal}

variable (F) in
/-- `P_θ(φ) ≤ φ`. -/
theorem envelope_le (θ : Fin r → ℝ) (φ : K → EReal) : F.envelope θ φ ≤ φ := fun x =>
  iSup₂_le fun _ hτ => hτ.2 x

/-- Every `θ`-psh competitor `τ ≤ φ` lies below `P_θ(φ)`. -/
theorem le_envelope {τ : K → EReal} (hτ : F.IsPSH θ τ) (hτφ : τ ≤ φ) : τ ≤ F.envelope θ φ :=
  fun x => le_iSup₂_of_le (f := fun (τ : K → EReal) (_ : F.IsPSH θ τ ∧ τ ≤ φ) => τ x) τ
    ⟨hτ, hτφ⟩ le_rfl

/-- The envelope is increasing in the obstacle. -/
theorem envelope_mono (h : φ ≤ ψ) : F.envelope θ φ ≤ F.envelope θ ψ := fun x =>
  iSup₂_le fun _ hτ => le_envelope hτ.1 (hτ.2.trans h) x

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

/-- **`lem:gl-ep-basic`(1)** (BJ22 `lem:envppty`): if `θ ∈ C̄` is the limit of a sequence of
classes `θⱼ ≥ θ` having the envelope property, then `θ` has the envelope property. The usc
regularization `u` of the supremum of a bounded family in `PSH(θ) ⊆ PSH(θⱼ)` is `θⱼ`-psh for
every `j`, hence `θ`-psh by PSH2 at `θ ∈ C̄` for the constant sequence `u`. -/
theorem HasEnvelopeProperty.of_tendsto [CompactSpace K] (hθ : θ ∈ F.coneClosure)
    {θs : ℕ → Fin r → ℝ} (hθs : Tendsto θs atTop (𝓝 θ)) (hle : ∀ j, θ ≤ θs j)
    (h : ∀ j, F.HasEnvelopeProperty (θs j)) : F.HasEnvelopeProperty θ := by
  intro S hSne hS hbdd
  have hU : ∀ j, F.IsPSH (θs j) (uscReg fun x => ⨆ u ∈ S, u x) := fun j =>
    h j S hSne (fun u hu => (hS u hu).mono_class (hle j)) hbdd
  obtain ⟨u, hu⟩ := hSne
  obtain ⟨x, hx⟩ := (hS u hu).exists_ne_bot
  exact isPSH_of_antitone_seq hθ hθs hU (fun _ _ _ _ => le_rfl) (fun _ => iInf_const.symm)
    ⟨x, ne_bot_of_le_ne_bot hx
      ((le_iSup₂ (f := fun (w : K → EReal) (_ : w ∈ S) => w x) u hu).trans
        (le_uscReg (fun x => ⨆ u ∈ S, u x) x))⟩

/-- `lem:gl-ep-basic`(1) with rational classes: if `θ ∈ C̄` and every `a ∈ ℚ^r` with `a > θ`
coordinatewise has the envelope property, so does `θ`. -/
theorem hasEnvelopeProperty_of_forall_rat_gt [CompactSpace K] (hθ : θ ∈ F.coneClosure)
    (h : ∀ a : Fin r → ℚ, (∀ c, θ c < a c) → F.HasEnvelopeProperty fun c => (a c : ℝ)) :
    F.HasEnvelopeProperty θ := by
  obtain ⟨a, hθa, ha⟩ := exists_seq_rat_vec_gt_tendsto θ
  exact HasEnvelopeProperty.of_tendsto hθ ha (fun j c => (hθa j c).le) fun j => h _ (hθa j)

/-- Scaling the envelope property: if `θ ∈ C̄` has the envelope property, so has `t θ` for real
`t > 0`, since `u ↦ t⁻¹ u` maps `PSH(t θ)` to `PSH(θ)` and `(sup t uᵢ)^⋆ = t (sup uᵢ)^⋆`. -/
theorem HasEnvelopeProperty.smul [CompactSpace K] (h : F.HasEnvelopeProperty θ)
    (hθ : θ ∈ F.coneClosure) {t : ℝ} (ht : 0 < t) : F.HasEnvelopeProperty (t • θ) := by
  intro S hSne hS hbdd
  obtain ⟨C₀, hC₀⟩ := hbdd
  have htθ : t • θ ∈ F.coneClosure := smul_mem_coneClosure hθ ht
  have hS' : ∀ w : S, F.IsPSH θ fun x => ((t⁻¹ : ℝ) : EReal) * w.1 x := fun w => by
    have h' := (hS w.1 w.2).smul htθ (inv_pos.2 ht)
    rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h'
  have : Nonempty S := hSne.to_subtype
  have hU := h.isPSH_uscReg_iSup hS' ⟨t⁻¹ * C₀, fun w x => by
    rw [EReal.coe_mul]
    exact ProjBerk.ereal_coe_mul_monotone (inv_pos.2 ht).le (hC₀ w.1 w.2 x)⟩
  have hU' := hU.smul hθ ht
  rw [← uscReg_coe_mul ht] at hU'
  convert hU' using 2
  funext x
  rw [ereal_coe_mul_iSup ht, iSup_subtype']
  simp only [ProjBerk.ereal_coe_mul_inv_mul ht.ne']

/-- **`lem:gl-ep-basic`(2)**: for `θ ∈ C̄` and real `t > 0`, `EP(θ) ↔ EP(t θ)`. -/
theorem hasEnvelopeProperty_smul_iff [CompactSpace K] (hθ : θ ∈ F.coneClosure) {t : ℝ}
    (ht : 0 < t) : F.HasEnvelopeProperty (t • θ) ↔ F.HasEnvelopeProperty θ := by
  refine ⟨fun h => ?_, fun h => h.smul hθ ht⟩
  have h' := h.smul (smul_mem_coneClosure hθ ht) (inv_pos.2 ht)
  rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h'

/-- **`lem:gl-ep-basic`(3)**: if `PSH(θ) = ∅`, then `θ` has the envelope property. -/
theorem hasEnvelopeProperty_of_forall_not_isPSH (h : ∀ u, ¬F.IsPSH θ u) :
    F.HasEnvelopeProperty θ :=
  fun _ ⟨u, hu⟩ hS _ => absurd (hS u hu) (h u)

end FSSystemC

/-! ### Fubini–Study systems as systems with the semiample cone `ℚ^r_{≥0}` -/

namespace FSSystem

variable {K : Type u} [TopologicalSpace K] {r : ℕ} (F : FSSystem K r)

/-- A Fubini–Study system (`def:pg-fs-system`) is a Fubini–Study system with semiample cone
`C = ℚ^r_{≥0}` (`def:gl-fs-system`), with the same families `𝓗(a)`, `𝓗_fin(a)`. -/
def toFSSystemC : FSSystemC K r where
  triv := F.triv
  C := ConvexCone.positive ℚ (Fin r → ℚ)
  nonneg_mem_C _ ha := ha
  IsFS := F.IsFS
  IsFinFS := F.IsFinFS
  continuous_of_isFS h := F.continuous_of_isFS h
  apply_triv_ne_bot h := F.apply_triv_ne_bot h
  apply_triv_ne_top h := F.apply_triv_ne_top h
  le_apply_triv h := F.le_apply_triv h
  isFS_of_isFinFS h := F.isFS_of_isFinFS h
  ne_bot_of_isFinFS h := F.ne_bot_of_isFinFS h
  isFS_mono h hab := F.isFS_mono h hab
  isFinFS_mono h hab := F.isFinFS_mono h hab
  isFS_const ha c := F.isFS_const ha c
  isFinFS_const ha c := F.isFinFS_const ha c
  isFS_max hf hg := F.isFS_max hf hg
  isFinFS_max hf hg := F.isFinFS_max hf hg
  isFS_add hf hg := F.isFS_add hf hg
  isFinFS_add hf hg := F.isFinFS_add hf hg
  isFS_smul hc h := F.isFS_smul hc h
  isFinFS_smul hc h := F.isFinFS_smul hc h
  exists_antitone_isFinFS _ h := F.exists_antitone_isFinFS h

variable {F} {θ : Fin r → ℝ} {u φ : K → EReal}

@[simp] theorem toFSSystemC_triv : F.toFSSystemC.triv = F.triv := rfl

theorem mem_toFSSystemC_C {a : Fin r → ℚ} : a ∈ F.toFSSystemC.C ↔ 0 ≤ a := Iff.rfl

theorem toFSSystemC_isFS_iff {a : Fin r → ℚ} {f : K → EReal} :
    F.toFSSystemC.IsFS a f ↔ F.IsFS a f :=
  Iff.rfl

theorem toFSSystemC_isFinFS_iff {a : Fin r → ℚ} {f : K → EReal} :
    F.toFSSystemC.IsFinFS a f ↔ F.IsFinFS a f :=
  Iff.rfl

/-- The psh functions of `F` and of `F.toFSSystemC` agree. -/
theorem toFSSystemC_isPSH_iff : F.toFSSystemC.IsPSH θ u ↔ F.IsPSH θ u :=
  Iff.rfl

/-- The envelopes of `F` and of `F.toFSSystemC` agree. -/
theorem toFSSystemC_envelope : F.toFSSystemC.envelope θ φ = F.envelope θ φ :=
  rfl

/-- The envelope property for `F` and for `F.toFSSystemC` agree, so that the results of
`EnvelopeProperty.Projective.FSSystemEnvelope` and `EnvelopeProperty.Projective.FSSystemPL` apply
to `F.toFSSystemC`. -/
theorem toFSSystemC_hasEnvelopeProperty_iff :
    F.toFSSystemC.HasEnvelopeProperty θ ↔ F.HasEnvelopeProperty θ :=
  Iff.rfl

/-- The closure of the semiample cone `ℚ^r_{≥0}` is `ℝ^r_{≥0}`. -/
theorem coneClosure_toFSSystemC : F.toFSSystemC.coneClosure = {θ | 0 ≤ θ} := by
  refine Subset.antisymm (closure_minimal ?_ (isClosed_le continuous_const continuous_id))
    fun θ hθ => FSSystemC.mem_coneClosure_of_nonneg hθ
  rintro _ ⟨a, ha, rfl⟩ c
  show (0 : ℝ) ≤ a c
  exact_mod_cast (ha : 0 ≤ a) c

end FSSystem

end EnvelopeProperty
