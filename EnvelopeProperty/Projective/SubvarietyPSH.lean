/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.Subvariety
import EnvelopeProperty.Projective.FSSystemRegularization

/-!
# Fubini–Study and psh functions on projective subvarieties `V(I) ⊆ ℙᴹ`

Let `X = V(I) ⊆ ℙᴹ` be a projective subvariety over a trivially valued field `k`
(`EnvelopeProperty.ProjSubvariety`: `I ⊆ R_M = k[x₀, …, x_M]` a homogeneous prime ideal not
containing all `xᵢ`), with analytification `X^an = V(I)^an ⊆ (ℙᴹ)^an` and trivial point `⋆`
(the trivial valuation of `R_M / I`). This file makes `(X^an, ⋆)` a Fubini–Study system of rank
one (`EnvelopeProperty.FSSystem`) and so defines the `θ`-psh functions on `X^an`, following the
blueprint chapter `projective-general.tex` (`subsec:pg-subvariety`), which supplies the global
psh theory used by Fang–Han–Xia, *The envelope property for unibranch projective varieties*
(FHX), Corollary 5.26 (`cor:normal-weak-global`), and by the positivity step of the Wu
discharge (`thm:wu-pos`, FHX Lemma 5.5 `lem:local-PL-positivity`). The definitions follow
Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field* (BJ22),
`defi:FS`, FS, FSgenfin, `defi:psh`, with the classes restricted to the multiples
`a O(1)` of the hyperplane class (`rmk:pg-subvariety-psh-comparison`).

## Main definitions

* `ProjSubvariety.IsFS X a f` (`def:pg-subvariety-fs`, `𝓗(X, a)`): `f = m⁻¹ max_t (log|s_t| + λ_t)`
  on `X^an`, given by Fubini–Study data `ProjBerk.FSData k M a` on `ℙᴹ` (`m ≥ 1`, forms `s_t` of
  degree `m a`, `λ_t ∈ ℝ`) at least one of whose forms is not in `I`. These are the restrictions
  to `X^an` of the Fubini–Study functions of class `a` on `ℙᴹ` whose forms are not all in `I`
  (`ProjSubvariety.isFS_iff_exists_restrict`).
* `ProjSubvariety.IsFinFS X a f` (`def:pg-subvariety-fs`, `𝓗_fin(X, a)`): moreover all `λ_t ∈ ℚ`
  and the `s_t` have no common zero on `X^an`. For real-valued functions this is
  `ProjSubvariety.IsFiniteFS` of `def:wu-proj-functions`(1) (`ProjSubvariety.isFinFS_coe_iff`).
* `ProjSubvariety.fsSystem X : FSSystem X.an 1` (`lem:pg-subvariety-fs-system`).
* `ProjSubvariety.IsPSH X θ u` (`def:pg-subvariety-psh`, `PSH(X, θ)`, `θ ∈ ℝ`): the `θ`-psh
  functions of `X.fsSystem`.

## Main results

* `ProjSubvariety.fsSystem` itself is the proof of `lem:pg-subvariety-fs-system`: the axioms
  (FS1)–(FS5) are `ProjSubvariety.IsFS.le_apply_triv` (via `ProjSubvariety.eval_le_eval_triv`:
  `|s|_x ≤ 1 = |s|_⋆` for `s ∉ I`, and `|s| = 0` on `X^an` for `s ∈ I`),
  `ProjSubvariety.IsFS.mono_class`, `ProjSubvariety.isFS_const`, `ProjSubvariety.IsFS.max`,
  `ProjSubvariety.IsFS.add`, `ProjSubvariety.IsFS.smul`,
  `ProjSubvariety.IsFS.exists_antitone_isFinFS` and their `IsFinFS` analogues. The conditions
  "some form `∉ I`" and "no common zero on `X^an`" are handled through
  `ProjSubvariety.exists_notMem_iff_eval_triv_ne_bot` and
  `ProjSubvariety.forall_exists_val_ne_zero_iff` (finiteness of the FS function at `⋆`,
  resp. everywhere on `X^an`), so that the closure properties follow from the formulas
  `FSData.eval_const`, `eval_sup`, `eval_add`, `eval_smul` of `Projective/FS.lean`.
  Second countability for countable `k`: `ProjSubvariety.secondCountableTopology_an`.
* Rank-one forms of the psh API of `EnvelopeProperty.Projective.FSSystem`:
  `ProjSubvariety.IsFS.isPSH`, `ProjSubvariety.IsFiniteFS.isPSH`, `ProjSubvariety.IsPSH.nonneg`,
  `ProjSubvariety.IsPSH.le_apply_triv`, `ProjSubvariety.IsPSH.add`, `ProjSubvariety.IsPSH.smul`,
  `ProjSubvariety.IsPSH.max`, `ProjSubvariety.IsPSH.add_const`, `ProjSubvariety.isPSH_const`,
  `ProjSubvariety.IsPSH.mono_class`, `ProjSubvariety.isPSH_of_antitone_seq` (PSH2).
* **Uniform approximation** (`lem:pg-uniform-approximation`):
  `ProjSubvariety.IsPSH.exists_isFinFS_le_lt`, `ProjSubvariety.IsPSH.exists_isFiniteFS_abs_sub_le`
  and the sequence form `ProjSubvariety.IsPSH.exists_seq_isFiniteFS_abs_sub_le` (with the class-one
  forms `ProjSubvariety.IsPSH.exists_isFiniteFS_one_abs_sub_le`,
  `ProjSubvariety.IsPSH.exists_seq_isFiniteFS_one_abs_sub_le`): for `a ∈ ℚ_{>0}`,
  a continuous real-valued `u ∈ PSH(X, a)` is a uniform limit of finite Fubini–Study functions of
  class `O(a)`, `|ψ_j - u| ≤ 2^{-j}`. The proof is the blueprint's: regularization in the fixed
  class `a` (`FSSystem.IsPSH.exists_isFinFS_net_of_pos`, `thm:pg-regularization`(2)) and Dini's
  argument on the compact space `X^an`. Countability of `k` is not used. With `a = 1` this is
  `thm:wu-bj-uniform` (`rmk:pg-uniform-approximation`).
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

namespace ProjBerk

namespace FSData

variable {k : Type u} [Field k] {M : ℕ} {a : ℚ}

/-- A Fubini–Study function on `(ℙᴹ)^an` is finite at a point iff one of its sections does not
vanish there. -/
theorem eval_ne_bot_iff_exists_val_ne_zero (D : FSData k M a) (v : ProjBerk k M) :
    D.eval v ≠ ⊥ ↔ ∃ t ∈ D.terms, v.1.val t.1 ≠ 0 := by
  refine ⟨fun h => ?_, fun ⟨t, ht, hv⟩ => D.eval_ne_bot_of_val_ne_zero ht hv⟩
  by_contra hcon
  apply h
  have hsup : (D.terms.sup fun t => termVal t v) = ⊥ := by
    rw [Finset.sup_eq_bot_iff]
    intro t ht
    have h0 : v.1.val t.1 = 0 := by
      by_contra h0
      exact hcon ⟨t, ht, h0⟩
    rw [termVal_def, (logAbs_eq_bot_iff t.1 v).2 h0, EReal.bot_add]
  rw [eval_def, hsup]
  exact EReal.coe_mul_bot_of_pos D.inv_m_pos

end FSData

end ProjBerk

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-! ### The trivial point -/

variable {X} in
/-- A form does not vanish at the trivial point `⋆` of `X` iff it is not in `I`. -/
theorem triv_val_ne_zero_iff {s : MvPolynomial (Fin (M + 1)) k} :
    (X.triv : ProjBerk k M).1.val s ≠ 0 ↔ s ∉ X.ideal :=
  ⟨fun h => notMem_ideal_of_val_ne_zero h, fun h => by
    rw [X.triv_val_of_notMem h]; exact one_ne_zero⟩

/-- `log|s|_⋆ = 0` for a form `s ∉ I`. -/
theorem logAbs_triv_of_notMem {s : MvPolynomial (Fin (M + 1)) k} (hs : s ∉ X.ideal) :
    ProjBerk.logAbs s (X.triv : ProjBerk k M) = 0 := by
  rw [ProjBerk.logAbs_def, X.triv_val_of_notMem hs, ENNReal.coe_one, ENNReal.log_one]

/-- Termwise (FS1): `log|s|_x + λ ≤ log|s|_⋆ + λ` on `X^an`, since `|s|_x ≤ 1 = |s|_⋆` for
`s ∉ I` and `|s|_x = 0` for `s ∈ I`. -/
theorem termVal_le_termVal_triv (t : MvPolynomial (Fin (M + 1)) k × ℝ) (v : X.an) :
    ProjBerk.termVal t v.1 ≤ ProjBerk.termVal t (X.triv : ProjBerk k M) := by
  by_cases ht : t.1 ∈ X.ideal
  · rw [ProjBerk.termVal_def, (ProjBerk.logAbs_eq_bot_iff t.1 v.1).2 (v.2 t.1 ht), EReal.bot_add]
    exact bot_le
  · rw [ProjBerk.termVal_def, ProjBerk.termVal_def, X.logAbs_triv_of_notMem ht]
    gcongr
    exact ProjBerk.logAbs_le_zero _ _

/-- (FS1) for Fubini–Study data on `X^an`: `f(x) ≤ f(⋆)`. -/
theorem eval_le_eval_triv {a : ℚ} (D : ProjBerk.FSData k M a) (v : X.an) :
    D.eval v.1 ≤ D.eval (X.triv : ProjBerk k M) := by
  rw [ProjBerk.FSData.eval_def, ProjBerk.FSData.eval_def]
  exact ProjBerk.ereal_coe_mul_monotone D.inv_m_pos.le
    (Finset.sup_mono_fun fun t _ => X.termVal_le_termVal_triv t v)

/-- Some form of the data is not in `I` iff the FS function is finite at `⋆`. -/
theorem exists_notMem_iff_eval_triv_ne_bot {a : ℚ} (D : ProjBerk.FSData k M a) :
    (∃ t ∈ D.terms, t.1 ∉ X.ideal) ↔ D.eval (X.triv : ProjBerk k M) ≠ ⊥ := by
  rw [D.eval_ne_bot_iff_exists_val_ne_zero]
  exact exists_congr fun t => and_congr_right fun _ => triv_val_ne_zero_iff.symm

/-- The forms of the data have no common zero on `X^an` iff the FS function is finite on
`X^an`. -/
theorem forall_exists_val_ne_zero_iff {a : ℚ} (D : ProjBerk.FSData k M a) :
    (∀ v ∈ X.an, ∃ t ∈ D.terms, v.1.val t.1 ≠ 0) ↔ ∀ v : X.an, D.eval v.1 ≠ ⊥ :=
  ⟨fun h v => (D.eval_ne_bot_iff_exists_val_ne_zero v.1).2 (h v.1 v.2),
    fun h v hv => (D.eval_ne_bot_iff_exists_val_ne_zero v).1 (h ⟨v, hv⟩)⟩

/-! ### Fubini–Study functions on `X^an` (`def:pg-subvariety-fs`) -/

/-- **Fubini–Study functions of class `O(a)` on `X^an`** (`def:pg-subvariety-fs`, `𝓗(X, a)`;
BJ22 `defi:FS`, FHX `eq:FS-function`): `f = m⁻¹ max_t (log|s_t| + λ_t)` on `X^an`, for
Fubini–Study data on `ℙᴹ` (`m ∈ ℤ_{>0}`, `m a ∈ ℕ`, finitely many forms `s_t` of degree `m a`,
`λ_t ∈ ℝ`) at least one of whose forms is not in `I`. -/
def IsFS (a : ℚ) (f : X.an → EReal) : Prop :=
  ∃ D : ProjBerk.FSData k M a, (∃ t ∈ D.terms, t.1 ∉ X.ideal) ∧ ∀ v : X.an, f v = D.eval v.1

/-- **Finite rational Fubini–Study functions of class `O(a)` on `X^an`**
(`def:pg-subvariety-fs`, `𝓗_fin(X, a)`; BJ22's `𝓗_ℚ`): as `IsFS`, with all `λ_t ∈ ℚ` and the
forms `s_t` having no common zero on `X^an`. For real-valued functions these are the finite
Fubini–Study functions `ProjSubvariety.IsFiniteFS` of `def:wu-proj-functions`(1)
(`ProjSubvariety.isFinFS_coe_iff`). -/
def IsFinFS (a : ℚ) (f : X.an → EReal) : Prop :=
  ∃ D : ProjBerk.FSData k M a, D.IsRational ∧ (∀ v ∈ X.an, ∃ t ∈ D.terms, v.1.val t.1 ≠ 0) ∧
    ∀ v : X.an, f v = D.eval v.1

variable {X} {a b : ℚ} {f g : X.an → EReal}

/-- `IsFS` in terms of finiteness at `⋆`. -/
theorem isFS_iff : X.IsFS a f ↔ ∃ D : ProjBerk.FSData k M a,
    D.eval (X.triv : ProjBerk k M) ≠ ⊥ ∧ ∀ v : X.an, f v = D.eval v.1 := by
  simp only [IsFS, exists_notMem_iff_eval_triv_ne_bot]

/-- `IsFinFS` in terms of finiteness on `X^an`. -/
theorem isFinFS_iff : X.IsFinFS a f ↔ ∃ D : ProjBerk.FSData k M a, D.IsRational ∧
    (∀ v : X.an, D.eval v.1 ≠ ⊥) ∧ ∀ v : X.an, f v = D.eval v.1 := by
  simp only [IsFinFS, forall_exists_val_ne_zero_iff]

/-- `𝓗(X, a)` consists of the restrictions to `X^an` of the Fubini–Study functions of class `a`
on `(ℙᴹ)^an` (`ProjBerk.IsFS`) whose forms are not all in `I`, i.e. which are finite at `⋆`
(`def:pg-subvariety-fs`). -/
theorem isFS_iff_exists_restrict : X.IsFS a f ↔ ∃ φ : ProjBerk k M → EReal, ProjBerk.IsFS a φ ∧
    φ (X.triv : ProjBerk k M) ≠ ⊥ ∧ ∀ v : X.an, f v = φ v.1 := by
  rw [isFS_iff]
  constructor
  · rintro ⟨D, hD, hf⟩
    exact ⟨D.eval, ⟨D, rfl⟩, hD, hf⟩
  · rintro ⟨φ, ⟨D, rfl⟩, hD, hf⟩
    exact ⟨D, hD, hf⟩

/-- `𝓗_fin(X, a)` consists of the restrictions to `X^an` of the rational Fubini–Study functions
of class `a` on `(ℙᴹ)^an` (`ProjBerk.IsRatFS`) that are finite on `X^an`. -/
theorem isFinFS_iff_exists_restrict : X.IsFinFS a f ↔ ∃ φ : ProjBerk k M → EReal,
    ProjBerk.IsRatFS a φ ∧ (∀ v : X.an, φ v.1 ≠ ⊥) ∧ ∀ v : X.an, f v = φ v.1 := by
  rw [isFinFS_iff]
  constructor
  · rintro ⟨D, hDr, hD, hf⟩
    exact ⟨D.eval, ⟨D, hDr, rfl⟩, hD, hf⟩
  · rintro ⟨φ, ⟨D, hDr, rfl⟩, hD, hf⟩
    exact ⟨D, hDr, hD, hf⟩

/-- For real-valued functions, `𝓗_fin(X, a)` is the set of finite Fubini–Study functions of
class `O(a)` of `def:wu-proj-functions`(1) (`ProjSubvariety.IsFiniteFS`). -/
theorem isFinFS_coe_iff {φ : X.an → ℝ} :
    X.IsFinFS a (fun v => (φ v : EReal)) ↔ X.IsFiniteFS a φ :=
  Iff.rfl

theorem IsFiniteFS.isFinFS {φ : X.an → ℝ} (h : X.IsFiniteFS a φ) :
    X.IsFinFS a fun v => (φ v : EReal) :=
  h

/-! #### The axioms (FS1)–(FS5) -/

theorem IsFS.continuous (h : X.IsFS a f) : Continuous f := by
  obtain ⟨D, -, hf⟩ := h
  rw [show f = fun v : X.an => D.eval v.1 from funext hf]
  exact D.continuous_eval.comp continuous_subtype_val

theorem IsFS.nonneg (h : X.IsFS a f) : 0 ≤ a := by
  obtain ⟨D, -, -⟩ := h
  exact D.a_nonneg

/-- (FS1) `f(⋆) ≠ -∞`. -/
theorem IsFS.apply_triv_ne_bot (h : X.IsFS a f) : f X.triv ≠ ⊥ := by
  obtain ⟨D, hD, hf⟩ := isFS_iff.1 h
  rw [hf]
  exact hD

theorem IsFS.ne_top (h : X.IsFS a f) (v : X.an) : f v ≠ ⊤ := by
  obtain ⟨D, -, hf⟩ := h
  rw [hf]
  exact D.eval_ne_top _

/-- (FS1) `f ≤ f(⋆)`. -/
theorem IsFS.le_apply_triv (h : X.IsFS a f) (v : X.an) : f v ≤ f X.triv := by
  obtain ⟨D, -, hf⟩ := h
  rw [hf, hf]
  exact X.eval_le_eval_triv D v

theorem IsFinFS.isFS (h : X.IsFinFS a f) : X.IsFS a f := by
  obtain ⟨D, -, hD, hf⟩ := h
  obtain ⟨t, ht, hv⟩ := hD X.triv.1 X.triv.2
  exact ⟨D, ⟨t, ht, notMem_ideal_of_val_ne_zero hv⟩, hf⟩

/-- Finite Fubini–Study functions are real valued. -/
theorem IsFinFS.ne_bot (h : X.IsFinFS a f) (v : X.an) : f v ≠ ⊥ := by
  obtain ⟨D, -, hD, hf⟩ := isFinFS_iff.1 h
  rw [hf]
  exact hD v

theorem IsFinFS.coe_toReal (h : X.IsFinFS a f) (v : X.an) : ((f v).toReal : EReal) = f v :=
  EReal.coe_toReal (h.isFS.ne_top v) (h.ne_bot v)

/-- A finite Fubini–Study function, as a real-valued function, is a finite Fubini–Study function
in the sense of `def:wu-proj-functions`(1). -/
theorem IsFinFS.isFiniteFS (h : X.IsFinFS a f) : X.IsFiniteFS a fun v => (f v).toReal := by
  rw [← isFinFS_coe_iff]
  simpa only [h.coe_toReal] using h

variable (X) in
/-- (FS3) real constants are Fubini–Study functions of every class `a ≥ 0`. -/
theorem isFS_const (ha : 0 ≤ a) (c : ℝ) : X.IsFS a fun _ => (c : EReal) := by
  refine isFS_iff.2 ⟨(ProjBerk.FSData.const a ha c : ProjBerk.FSData k M a), ?_, fun v =>
    (ProjBerk.FSData.eval_const a ha c v.1).symm⟩
  rw [ProjBerk.FSData.eval_const]
  exact EReal.coe_ne_bot c

variable (X) in
/-- (FS3) rational constants are finite Fubini–Study functions of every class `a ≥ 0`. -/
theorem isFinFS_const (ha : 0 ≤ a) (c : ℚ) : X.IsFinFS a fun _ => ((c : ℝ) : EReal) := by
  refine isFinFS_iff.2 ⟨(ProjBerk.FSData.const a ha (c : ℝ) : ProjBerk.FSData k M a),
    ProjBerk.FSData.isRational_const a ha c, fun v => ?_, fun v =>
    (ProjBerk.FSData.eval_const a ha (c : ℝ) v.1).symm⟩
  rw [ProjBerk.FSData.eval_const]
  exact EReal.coe_ne_bot _

/-- (FS3) maxima of Fubini–Study functions of the same class. -/
theorem IsFS.max (hf : X.IsFS a f) (hg : X.IsFS a g) : X.IsFS a fun v => max (f v) (g v) := by
  obtain ⟨D, hD, hf⟩ := isFS_iff.1 hf
  obtain ⟨D', -, hg⟩ := isFS_iff.1 hg
  refine isFS_iff.2 ⟨D.sup D', ?_, fun v => by rw [ProjBerk.FSData.eval_sup, hf, hg]⟩
  rw [ProjBerk.FSData.eval_sup]
  exact ne_bot_of_le_ne_bot hD (le_max_left _ _)

/-- (FS3) maxima of finite Fubini–Study functions of the same class. -/
theorem IsFinFS.max (hf : X.IsFinFS a f) (hg : X.IsFinFS a g) :
    X.IsFinFS a fun v => max (f v) (g v) := by
  obtain ⟨D, hDr, hD, hf⟩ := isFinFS_iff.1 hf
  obtain ⟨D', hD'r, -, hg⟩ := isFinFS_iff.1 hg
  refine isFinFS_iff.2 ⟨D.sup D', hDr.sup hD'r, fun v => ?_, fun v => by
    rw [ProjBerk.FSData.eval_sup, hf, hg]⟩
  rw [ProjBerk.FSData.eval_sup]
  exact ne_bot_of_le_ne_bot (hD v) (le_max_left _ _)

/-- (FS4) `𝓗(X, a) + 𝓗(X, b) ⊆ 𝓗(X, a + b)`. -/
theorem IsFS.add (hf : X.IsFS a f) (hg : X.IsFS b g) : X.IsFS (a + b) fun v => f v + g v := by
  obtain ⟨D, hD, hf⟩ := isFS_iff.1 hf
  obtain ⟨D', hD', hg⟩ := isFS_iff.1 hg
  refine isFS_iff.2 ⟨D.add D', ?_, fun v => by rw [ProjBerk.FSData.eval_add, hf, hg]⟩
  rw [ProjBerk.FSData.eval_add]
  exact EReal.add_ne_bot_iff.2 ⟨hD, hD'⟩

/-- (FS4) `𝓗_fin(X, a) + 𝓗_fin(X, b) ⊆ 𝓗_fin(X, a + b)`. -/
theorem IsFinFS.add (hf : X.IsFinFS a f) (hg : X.IsFinFS b g) :
    X.IsFinFS (a + b) fun v => f v + g v := by
  obtain ⟨D, hDr, hD, hf⟩ := isFinFS_iff.1 hf
  obtain ⟨D', hD'r, hD', hg⟩ := isFinFS_iff.1 hg
  refine isFinFS_iff.2 ⟨D.add D', hDr.add hD'r, fun v => ?_, fun v => by
    rw [ProjBerk.FSData.eval_add, hf, hg]⟩
  rw [ProjBerk.FSData.eval_add]
  exact EReal.add_ne_bot_iff.2 ⟨hD v, hD' v⟩

/-- (FS4) `c 𝓗(X, a) ⊆ 𝓗(X, c a)` for `c ∈ ℚ_{>0}`. -/
theorem IsFS.smul (h : X.IsFS a f) {c : ℚ} (hc : 0 < c) :
    X.IsFS (c * a) fun v => ((c : ℝ) : EReal) * f v := by
  obtain ⟨D, hD, hf⟩ := isFS_iff.1 h
  refine isFS_iff.2 ⟨D.smul c hc, ?_, fun v => by rw [ProjBerk.FSData.eval_smul, hf]⟩
  rw [ProjBerk.FSData.eval_smul]
  exact ProjBerk.ereal_coe_mul_ne_bot (by exact_mod_cast hc.le) hD

/-- (FS4) `c 𝓗_fin(X, a) ⊆ 𝓗_fin(X, c a)` for `c ∈ ℚ_{>0}`. -/
theorem IsFinFS.smul (h : X.IsFinFS a f) {c : ℚ} (hc : 0 < c) :
    X.IsFinFS (c * a) fun v => ((c : ℝ) : EReal) * f v := by
  obtain ⟨D, hDr, hD, hf⟩ := isFinFS_iff.1 h
  refine isFinFS_iff.2 ⟨D.smul c hc, hDr.smul hc, fun v => ?_, fun v => by
    rw [ProjBerk.FSData.eval_smul, hf]⟩
  rw [ProjBerk.FSData.eval_smul]
  exact ProjBerk.ereal_coe_mul_ne_bot (by exact_mod_cast hc.le) (hD v)

/-- (FS2) `𝓗(X, a) ⊆ 𝓗(X, b)` for `a ≤ b`: add the function `0 = max_j log|x_j^{m(b-a)}|` of
class `b - a`. -/
theorem IsFS.mono_class (h : X.IsFS a f) (hab : a ≤ b) : X.IsFS b f := by
  have h' := h.add (X.isFS_const (sub_nonneg.2 hab) 0)
  rw [add_sub_cancel] at h'
  simpa only [EReal.coe_zero, add_zero] using h'

/-- (FS2) `𝓗_fin(X, a) ⊆ 𝓗_fin(X, b)` for `a ≤ b`. -/
theorem IsFinFS.mono_class (h : X.IsFinFS a f) (hab : a ≤ b) : X.IsFinFS b f := by
  have h' := h.add (X.isFinFS_const (sub_nonneg.2 hab) 0)
  rw [add_sub_cancel] at h'
  simpa only [Rat.cast_zero, EReal.coe_zero, add_zero] using h'

/-- (FS5) every `f ∈ 𝓗(X, a)` is the limit of a decreasing sequence in `𝓗_fin(X, a)`: restrict
the rational approximants `max(m⁻¹ max_t (log|s_t| + λ_t^{(n)}), -n)` on `ℙᴹ`
(`ProjBerk.IsFS.exists_antitone_finiteRatFS`, `lem:bj-fs-basic`(4)), which are finite on all of
`(ℙᴹ)^an`. -/
theorem IsFS.exists_antitone_isFinFS (h : X.IsFS a f) : ∃ g : ℕ → X.an → EReal,
    (∀ n, X.IsFinFS a (g n)) ∧ (∀ x, Antitone fun n => g n x) ∧ ∀ x, f x = ⨅ n, g n x := by
  obtain ⟨D, -, hf⟩ := h
  obtain ⟨ψ, hψ, hanti, -, hinf⟩ :=
    ProjBerk.IsFS.exists_antitone_finiteRatFS (⟨D, rfl⟩ : ProjBerk.IsFS a D.eval)
  refine ⟨fun n v => ψ n v.1, fun n => ?_, fun v => hanti v.1, fun v => by rw [hf, hinf]⟩
  obtain ⟨⟨D', hD', hψD'⟩, hne⟩ := hψ n
  refine isFinFS_iff.2 ⟨D', hD', fun v => ?_, fun v => by simp only [hψD']⟩
  rw [← hψD']
  exact hne v.1

/-! ### The Fubini–Study system of `X` (`lem:pg-subvariety-fs-system`) -/

variable (X) in
/-- **`(X^an, ⋆)` is a Fubini–Study system of rank one** (`lem:pg-subvariety-fs-system`; BJ22
FS, FSgenfin), with `𝓗(a) = 𝓗(X, a 0)` and `𝓗_fin(a) = 𝓗_fin(X, a 0)` for
`a ∈ ℚ^1`. -/
def fsSystem : FSSystem X.an 1 where
  triv := X.triv
  IsFS a f := X.IsFS (a 0) f
  IsFinFS a f := X.IsFinFS (a 0) f
  continuous_of_isFS h := h.continuous
  nonneg_of_isFS h := fun c => by fin_cases c; exact h.nonneg
  apply_triv_ne_bot h := h.apply_triv_ne_bot
  apply_triv_ne_top h := h.ne_top _
  le_apply_triv h x := h.le_apply_triv x
  isFS_of_isFinFS h := h.isFS
  ne_bot_of_isFinFS h := h.ne_bot
  isFS_mono h hab := h.mono_class (hab 0)
  isFinFS_mono h hab := h.mono_class (hab 0)
  isFS_const ha c := X.isFS_const (ha 0) c
  isFinFS_const ha c := X.isFinFS_const (ha 0) c
  isFS_max hf hg := hf.max hg
  isFinFS_max hf hg := hf.max hg
  isFS_add hf hg := hf.add hg
  isFinFS_add hf hg := hf.add hg
  isFS_smul hc h := h.smul hc
  isFinFS_smul hc h := h.smul hc
  exists_antitone_isFinFS h := h.exists_antitone_isFinFS

@[simp] theorem fsSystem_triv : X.fsSystem.triv = X.triv := rfl

theorem fsSystem_isFS_iff {a : Fin 1 → ℚ} : X.fsSystem.IsFS a f ↔ X.IsFS (a 0) f :=
  Iff.rfl

theorem fsSystem_isFinFS_iff {a : Fin 1 → ℚ} : X.fsSystem.IsFinFS a f ↔ X.IsFinFS (a 0) f :=
  Iff.rfl

variable (X) in
/-- `X^an` is second countable for countable `k` (`lem:pg-subvariety-fs-system`): it is a
subspace of `(ℙᴹ)^an` (`ProjBerk.instSecondCountableTopology`). -/
theorem secondCountableTopology_an [Countable k] : SecondCountableTopology X.an :=
  inferInstance

/-! ### Psh functions on `X^an` (`def:pg-subvariety-psh`) -/

variable (X) in
/-- **`θ`-psh functions on `X^an`** (`def:pg-subvariety-psh`, `PSH(X, θ)` for `θ ∈ ℝ`; BJ22
Definition 4.1 with classes in `ℝ O(1)`, see `rmk:pg-subvariety-psh-comparison`): the `θ`-psh
functions (`def:pg-psh`, `FSSystem.IsPSH`) of the Fubini–Study system `X.fsSystem`. -/
abbrev IsPSH (θ : ℝ) (u : X.an → EReal) : Prop :=
  X.fsSystem.IsPSH (fun _ => θ) u

variable {θ θ' : ℝ} {u u' : X.an → EReal}

/-- PSH1 (`thm:pg-psh2`(1)): `𝓗(X, a) ⊆ PSH(X, a)`. -/
theorem IsFS.isPSH (h : X.IsFS a f) : X.IsPSH a f :=
  FSSystem.IsFS.isPSH (F := X.fsSystem) (a := fun _ => a) h

theorem IsFinFS.isPSH (h : X.IsFinFS a f) : X.IsPSH a f :=
  h.isFS.isPSH

/-- Finite Fubini–Study functions of class `O(a)` (`def:wu-proj-functions`(1)) are `a`-psh. -/
theorem IsFiniteFS.isPSH {φ : X.an → ℝ} (h : X.IsFiniteFS a φ) :
    X.IsPSH a fun v => (φ v : EReal) :=
  IsFinFS.isPSH h

/-- `PSH(X, θ) ≠ ∅` forces `θ ≥ 0` (`prop:pg-maxprin`). -/
theorem IsPSH.nonneg (h : X.IsPSH θ u) : 0 ≤ θ :=
  FSSystem.IsPSH.nonneg h 0

/-- **The maximum principle** (`prop:pg-maxprin`): `u ≤ u(⋆)`. -/
theorem IsPSH.le_apply_triv (h : X.IsPSH θ u) (x : X.an) : u x ≤ u X.triv :=
  FSSystem.IsPSH.le_apply_triv h x

/-- A `θ`-psh function is finite at `⋆` (`prop:pg-maxprin`). -/
theorem IsPSH.apply_triv_ne_bot (h : X.IsPSH θ u) : u X.triv ≠ ⊥ :=
  FSSystem.IsPSH.apply_triv_ne_bot h

/-- `PSH(X, θ) + PSH(X, θ') ⊆ PSH(X, θ + θ')` (`thm:pg-psh-basic`(1)). -/
theorem IsPSH.add (h : X.IsPSH θ u) (h' : X.IsPSH θ' u') :
    X.IsPSH (θ + θ') fun x => u x + u' x :=
  FSSystem.IsPSH.add h h'

/-- `t PSH(X, θ) ⊆ PSH(X, t θ)` for real `t > 0` (`thm:pg-psh-basic`(1)). -/
theorem IsPSH.smul (h : X.IsPSH θ u) {t : ℝ} (ht : 0 < t) :
    X.IsPSH (t * θ) fun x => (t : EReal) * u x :=
  FSSystem.IsPSH.smul h ht

/-- Maxima (`thm:pg-psh-basic`(2)). -/
theorem IsPSH.max (h : X.IsPSH θ u) (h' : X.IsPSH θ u') :
    X.IsPSH θ fun x => max (u x) (u' x) :=
  FSSystem.IsPSH.max h h'

/-- Adding real constants (`thm:pg-psh-basic`(2)). -/
theorem IsPSH.add_const (h : X.IsPSH θ u) (c : ℝ) : X.IsPSH θ fun x => u x + (c : EReal) :=
  FSSystem.IsPSH.add_const h c

variable (X) in
/-- Real constants are `θ`-psh for `θ ≥ 0` (`thm:pg-psh-basic`(2)). -/
theorem isPSH_const (hθ : 0 ≤ θ) (c : ℝ) : X.IsPSH θ fun _ => (c : EReal) :=
  FSSystem.isPSH_const (fun _ => hθ) c

/-- Monotonicity in the class (`thm:pg-psh-basic`(3)). -/
theorem IsPSH.mono_class (h : X.IsPSH θ u) (hθθ' : θ ≤ θ') : X.IsPSH θ' u :=
  FSSystem.IsPSH.mono_class h fun _ => hθθ'

/-- **PSH2** for decreasing sequences (`thm:pg-psh2`(3)): if `u_m ∈ PSH(X, θ_m)` decreases,
`θ_m → θ₀` and `w = inf_m u_m ≢ -∞`, then `w ∈ PSH(X, θ₀)`. -/
theorem isPSH_of_antitone_seq {θ : ℕ → ℝ} {θ₀ : ℝ} (hθ : Tendsto θ atTop (𝓝 θ₀))
    {u : ℕ → X.an → EReal} (hu : ∀ m, X.IsPSH (θ m) (u m)) (hanti : ∀ x, Antitone fun m => u m x)
    {w : X.an → EReal} (hw : ∀ x, w x = ⨅ m, u m x) (hfin : ∃ x, w x ≠ ⊥) : X.IsPSH θ₀ w :=
  FSSystem.isPSH_of_antitone_seq (θ := fun m _ => θ m) (tendsto_pi_nhds.2 fun _ => hθ) hu hanti
    hw hfin

/-! ### Uniform approximation (`lem:pg-uniform-approximation`) -/

/-- **Uniform approximation of continuous psh functions** (`lem:pg-uniform-approximation`), with
one-sided bounds: for `a ∈ ℚ_{>0}`, a continuous real-valued `u ∈ PSH(X, a)` and `ε > 0`, there
is `f ∈ 𝓗_fin(X, a)` with `u ≤ f < u + ε` on `X^an`. By regularization in the fixed class `a`
(`thm:pg-regularization`(2)), `u` is the limit of a decreasing net `f_α ∈ 𝓗_fin(X, a)`; the open
sets `{f_α < u + ε}` increase and cover the compact space `X^an`, so one of them is `X^an`. -/
theorem IsPSH.exists_isFinFS_le_lt (ha : 0 < a) {u : X.an → ℝ} (hu : Continuous u)
    (h : X.IsPSH a fun x => (u x : EReal)) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : X.an → EReal, X.IsFinFS a f ∧
      ∀ x, (u x : EReal) ≤ f x ∧ f x < ((u x + ε : ℝ) : EReal) := by
  obtain ⟨ι, _, _, _, f, hf, hanti, hinf⟩ :=
    FSSystem.IsPSH.exists_isFinFS_net_of_pos (θ := fun _ => a) (fun _ => ha) h
  let U : ι → Set X.an := fun i => {x | f i x < ((u x + ε : ℝ) : EReal)}
  have hUopen : ∀ i, IsOpen (U i) := fun i =>
    isOpen_lt (hf i).continuous (continuous_coe_real_ereal.comp (hu.add continuous_const))
  have hUmono : ∀ i j, i ≤ j → U i ⊆ U j := fun i j hij x hx =>
    lt_of_le_of_lt (hanti x hij) hx
  have hUdir : Directed (· ⊆ ·) U := fun i j => by
    obtain ⟨l, hil, hjl⟩ := directed_of (· ≤ ·) i j
    exact ⟨l, hUmono _ _ hil, hUmono _ _ hjl⟩
  have hUcover : (univ : Set X.an) ⊆ ⋃ i, U i := by
    intro x _
    have hlt : (u x : EReal) < ((u x + ε : ℝ) : EReal) :=
      EReal.coe_lt_coe_iff.2 (by linarith)
    rw [hinf x] at hlt
    obtain ⟨i, hi⟩ := iInf_lt_iff.1 hlt
    exact mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨i, hi⟩ := isCompact_univ.elim_directed_cover U hUopen hUcover hUdir
  exact ⟨f i, hf i, fun x => ⟨(hinf x).le.trans (iInf_le _ i), hi (mem_univ x)⟩⟩

/-- **Uniform approximation of continuous psh functions** (`lem:pg-uniform-approximation`): for
`a ∈ ℚ_{>0}`, a continuous real-valued `u ∈ PSH(X, a)` and `ε > 0`, there is a finite
Fubini–Study function `ψ` of class `O(a)` (`def:wu-proj-functions`(1)) with `|u - ψ| ≤ ε` on
`X^an`. For `a = 1` this is `thm:wu-bj-uniform` (`rmk:pg-uniform-approximation`). -/
theorem IsPSH.exists_isFiniteFS_abs_sub_le (ha : 0 < a) {u : X.an → ℝ} (hu : Continuous u)
    (h : X.IsPSH a fun x => (u x : EReal)) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : X.an → ℝ, X.IsFiniteFS a ψ ∧ ∀ x, |u x - ψ x| ≤ ε := by
  obtain ⟨f, hf, hle⟩ := h.exists_isFinFS_le_lt ha hu hε
  refine ⟨fun x => (f x).toReal, hf.isFiniteFS, fun x => ?_⟩
  have h1 := (hle x).1
  have h2 := (hle x).2
  rw [← hf.coe_toReal x] at h1 h2
  have h1' : u x ≤ (f x).toReal := EReal.coe_le_coe_iff.1 h1
  have h2' : (f x).toReal < u x + ε := EReal.coe_lt_coe_iff.1 h2
  rw [abs_le]
  constructor <;> linarith

/-- **Uniform approximation of continuous psh functions**, sequence form
(`lem:pg-uniform-approximation`): for `a ∈ ℚ_{>0}` and a continuous real-valued
`u ∈ PSH(X, a)` there are finite Fubini–Study functions `ψ_j` of class `O(a)` with
`|ψ_j - u| ≤ 2^{-j}` on `X^an`. -/
theorem IsPSH.exists_seq_isFiniteFS_abs_sub_le (ha : 0 < a) {u : X.an → ℝ} (hu : Continuous u)
    (h : X.IsPSH a fun x => (u x : EReal)) :
    ∃ ψ : ℕ → X.an → ℝ, (∀ j, X.IsFiniteFS a (ψ j)) ∧
      ∀ j x, |ψ j x - u x| ≤ ((2 : ℝ) ^ j)⁻¹ := by
  choose ψ hψ hle using fun j : ℕ =>
    h.exists_isFiniteFS_abs_sub_le ha hu (ε := ((2 : ℝ) ^ j)⁻¹) (by positivity)
  exact ⟨ψ, hψ, fun j x => by rw [abs_sub_comm]; exact hle j x⟩

/-- **`thm:wu-bj-uniform` for `X = V(I)`** (`lem:pg-uniform-approximation` with `a = 1`,
`rmk:pg-uniform-approximation`): a continuous real-valued `u ∈ PSH(X, 1)` is, for every `ε > 0`,
within `ε` of a finite Fubini–Study function of class `O(1)`. -/
theorem IsPSH.exists_isFiniteFS_one_abs_sub_le {u : X.an → ℝ} (hu : Continuous u)
    (h : X.IsPSH 1 fun x => (u x : EReal)) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : X.an → ℝ, X.IsFiniteFS 1 ψ ∧ ∀ x, |u x - ψ x| ≤ ε := by
  have h' : X.IsPSH ((1 : ℚ) : ℝ) fun x => (u x : EReal) := by
    rw [Rat.cast_one]
    exact h
  exact h'.exists_isFiniteFS_abs_sub_le one_pos hu hε

/-- **`thm:wu-bj-uniform` for `X = V(I)`**, sequence form: a continuous real-valued
`u ∈ PSH(X, 1)` is the uniform limit of finite Fubini–Study functions `ψ_j` of class `O(1)` with
`|ψ_j - u| ≤ 2^{-j}`. -/
theorem IsPSH.exists_seq_isFiniteFS_one_abs_sub_le {u : X.an → ℝ} (hu : Continuous u)
    (h : X.IsPSH 1 fun x => (u x : EReal)) :
    ∃ ψ : ℕ → X.an → ℝ, (∀ j, X.IsFiniteFS 1 (ψ j)) ∧
      ∀ j x, |ψ j x - u x| ≤ ((2 : ℝ) ^ j)⁻¹ := by
  have h' : X.IsPSH ((1 : ℚ) : ℝ) fun x => (u x : EReal) := by
    rw [Rat.cast_one]
    exact h
  exact h'.exists_seq_isFiniteFS_abs_sub_le one_pos hu

end ProjSubvariety

end EnvelopeProperty
