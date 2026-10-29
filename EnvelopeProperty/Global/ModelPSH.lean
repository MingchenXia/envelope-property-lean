/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.Sections

/-!
# Fubini–Study and psh functions on a model, and the envelope property

Let `𝒳 = (K, S, z)` be an integral multiprojective model of rank `r` over a trivially valued field
`k` (`EnvelopeProperty.MultiModel`, `def:gl-model`), with analytification `𝒳^an`
(`MultiModel.an`), sections `R_a` (`MultiModel.sections`, `def:gl-sections`) and semiample cone
`C(𝒳)` (`MultiModel.semiampleCone`, `def:gl-cones`). This file implements the blueprint nodes
`def:gl-fs`, `lem:gl-fs-system`, `def:gl-psh` and `lem:gl-ep-basic` of the global chapter
`global.tex` of the formalization of Fang–Han–Xia, *The envelope property for unibranch projective
varieties* (FHX, §2, `eq:FS-function`, `subsec:prelim-psh`,
`subsec:prelim-envelopes`); the definitions follow Boucksom–Jonsson, *Global pluripotential theory
over a trivially valued field* (BJ22), Definition 2.18, Proposition 2.19, Lemma 2.17, Definition 4.1, and the
rank-one and rank-two templates `EnvelopeProperty.Projective.SubvarietyPSH`,
`EnvelopeProperty.Projective.BlowupPSH`.

## Fubini–Study data (`def:gl-fs`)

`MultiModel.FSData X a` (for `a ∈ ℚ^r`) is the data of a Fubini–Study function
`m⁻¹ max_t (log |f_t| + λ_t)` of class `a`: an integer `m > 0`, the degree `m a ∈ ℤ^r`
(`FSData.deg`), and finitely many pairs `(f_t, λ_t)` with `f_t ∈ R_{m a}`, `λ_t ∈ ℝ`
(`MultiModel.FSData.eval`, using `log |f|_v = MultiModel.logSecAbs v (m a) f`). The operations are
those of `EnvelopeProperty.BiProjBerk.FSData`
(`EnvelopeProperty.Projective.BlowupPSH`):

* `FSData.sup`, `FSData.add`, `FSData.smul` (`eval_sup`, `eval_add`, `eval_smul`): maxima of data of
  the same class, sums and positive rational multiples, through the multiplicativity of `|·|`
  (`lem:gl-sections`(2));
* `FSData.ofBasePointFree` (`eval_ofBasePointFree`): a real constant `c` of a class `a ∈ C(𝒳)` is
  `m⁻¹ max_t (log |f_t| + m c)` for a base point free family `f_t ∈ R_{m a}`, by `lem:gl-cones`(2)
  (`max_t |f_t|_v = 1`);
* `FSData.reweight`, `FSData.exists_antitone_isRational` (BJ22 Lemma 2.17, for `a ∈ C(𝒳)`): the
  rational approximants `max(m⁻¹ max_t (log |f_t| + q_t^{(N)}), -N)`;
* `FSData.single`: the single term `log |f| + λ` of a section `f ∈ R_d`, `d ∈ ℤ^r`.

## Fubini–Study functions (`def:gl-fs`)

* `MultiModel.IsFS X a φ` (`𝓗(𝒳, a)`): `φ = m⁻¹ max_t (log |f_t| + λ_t)` on `𝒳^an` for data whose
  `f_t ∈ R_{m a}` are not all zero;
* `MultiModel.IsFinFS X a φ` (`𝓗_fin(𝒳, a)`): moreover `λ_t ∈ ℚ` and the `f_t` have no common zero
  on `𝒳^an` (then `a ∈ C(𝒳)`, `MultiModel.IsFinFS.mem_semiampleCone`);
* `MultiModel.IsHomFS X a φ` (`𝓗_hom(𝒳, a)`): all `λ_t = 0`.

## The system of a model (`lem:gl-fs-system`)

`MultiModel.fsSystem X: FSSystemC X.an r` is `(𝒳^an, ⋆)` with the families `𝓗(𝒳, a)`,
`𝓗_fin(𝒳, a)` and the semiample cone `C(𝒳)`; its closure is the model-nef cone
(`MultiModel.coneClosure_fsSystem`). The axioms are `IsFS.le_apply_triv` ((FS1): `|f| ≤ 1` on
`𝒳^an` and `|f|_⋆ = 1` for `f ≠ 0`, `lem:gl-sections`(3)), `IsFS.mono_class` ((FS2): add the
constant `0` of class `b - a ≥ 0`, whose family consists of monomials `z̃^γ`), `isFS_const`
((FS3), `a ∈ C(𝒳)`), `IsFS.max`, `IsFS.add`, `IsFS.smul` ((FS4)), `IsFS.exists_antitone_isFinFS`
((FS5), `a ∈ C(𝒳)`), and their `IsFinFS` analogues.

## Psh functions and the envelope property (`def:gl-psh`, `lem:gl-ep-basic`)

* `MultiModel.IsPSH X θ u` (`PSH(𝒳, θ)`, `θ ∈ ℝ^r`), `MultiModel.envelope X θ φ` (`P_θ(φ)`) and
  `MultiModel.HasEnvelopeProperty X θ` (`EP_𝒳(θ)`): those of `X.fsSystem`
  (`EnvelopeProperty.FSSystemC`). The psh theory of `thm:gl-fs-system-theory` applies; the main
  statements are restated for `𝒳`: part (1) for every `θ ∈ ℝ^r` (`MultiModel.IsFS.isPSH`,
  `MultiModel.IsPSH.le_apply_triv`, `MultiModel.IsPSH.max`, `MultiModel.IsPSH.add`,
  `MultiModel.IsPSH.add_const`, `MultiModel.IsPSH.smul_rat`, `MultiModel.IsPSH.mono_class`),
  part (2) for `θ ∈ N(𝒳)` (`MultiModel.isPSH_of_antitone` (PSH2), `MultiModel.IsPSH.smul`,
  `MultiModel.isPSH_const`, `MultiModel.IsPSH.exists_isFinFS_net_gt`,
  `MultiModel.IsPSH.exists_isFinFS_net_of_pos`, and for countable `k` the sequence forms
  `MultiModel.IsPSH.exists_isFinFS_seq_gt`, `MultiModel.IsPSH.exists_isFinFS_seq_of_pos`).
* `MultiModel.isPSH_logSecAbs`: `log |f| ∈ PSH(𝒳, d)` for `0 ≠ f ∈ R_d`, `d ∈ ℤ^r`.
* `lem:gl-ep-basic`: `MultiModel.HasEnvelopeProperty.of_tendsto` (part (1)),
  `MultiModel.hasEnvelopeProperty_smul_iff` (part (2)),
  `MultiModel.hasEnvelopeProperty_of_forall_not_isPSH` (part (3)).

`PSH_hom(𝒳, θ)` of `def:gl-psh` needs the scaling action of `def:gl-scaling` and is not
defined here.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  (X : MultiModel k K r)

/-! ### Terms `log |f| + λ` -/

/-- The value `log |f|_v + λ` of a term `t = (f, λ)` in degree `d ∈ ℤ^r` at `v ∈ 𝒳^an`. -/
def termVal (d : Fin r → ℤ) (t : K × ℝ) (v : X.an) : EReal :=
  X.logSecAbs v.1 d t.1 + (t.2 : EReal)

variable {X}

theorem termVal_def (d : Fin r → ℤ) (t : K × ℝ) (v : X.an) :
    X.termVal d t v = X.logSecAbs v.1 d t.1 + (t.2 : EReal) :=
  rfl

variable (X) in
@[fun_prop]
theorem continuous_termVal (d : Fin r → ℤ) (t : K × ℝ) : Continuous (X.termVal d t) :=
  (ProjBerk.continuous_ereal_add_coe t.2).comp
    ((X.continuous_logSecAbs d t.1).comp continuous_subtype_val)

theorem termVal_ne_top (d : Fin r → ℤ) (t : K × ℝ) (v : X.an) : X.termVal d t v ≠ ⊤ :=
  EReal.add_ne_top (logSecAbs_ne_top _ _ _) (EReal.coe_ne_top _)

/-- A term is finite at `v` iff its section does not vanish at `v`. -/
theorem termVal_ne_bot_iff (d : Fin r → ℤ) (t : K × ℝ) (v : X.an) :
    X.termVal d t v ≠ ⊥ ↔ X.secAbs v.1 d t.1 ≠ 0 := by
  rw [termVal_def, Ne, EReal.add_eq_bot_iff, not_or, logSecAbs_eq_bot_iff]
  exact and_iff_left (EReal.coe_ne_bot _)

/-- Termwise (FS1): `log |f|_v + λ ≤ log |f|_⋆ + λ`. -/
theorem termVal_le_termVal_triv {d : Fin r → ℤ} {t : K × ℝ} (ht : t.1 ∈ X.sections d)
    (v : X.an) : X.termVal d t v ≤ X.termVal d t X.triv := by
  by_cases h0 : t.1 = 0
  · rw [termVal_def, h0, logSecAbs_zero, EReal.bot_add]
    exact bot_le
  · rw [termVal_def, termVal_def, logSecAbs_triv ht h0]
    gcongr
    exact logSecAbs_le_zero v.2.2 _ _

/-- `log |f^n| + n λ = n (log |f| + λ)`. -/
theorem termVal_pow {d : Fin r → ℤ} {t : K × ℝ} (ht : t.1 ∈ X.sections d) (n : ℕ) (v : X.an) :
    X.termVal (n • d) (t.1 ^ n, (n : ℝ) * t.2) v = ((n : ℝ) : EReal) * X.termVal d t v := by
  have h := logSecAbs_pow v.2.2 ht n
  rw [← EReal.coe_natCast] at h
  rw [termVal_def, termVal_def, h, ProjBerk.ereal_coe_mul_add (Nat.cast_nonneg n), EReal.coe_mul]

/-- `log |f^p g^q| + (p λ + q λ') = p (log |f| + λ) + q (log |g| + λ')`. -/
theorem termVal_mul_pow {d d' : Fin r → ℤ} {t t' : K × ℝ} (ht : t.1 ∈ X.sections d)
    (ht' : t'.1 ∈ X.sections d') (p q : ℕ) (v : X.an) :
    X.termVal (p • d + q • d') (t.1 ^ p * t'.1 ^ q, (p : ℝ) * t.2 + (q : ℝ) * t'.2) v =
      ((p : ℝ) : EReal) * X.termVal d t v + ((q : ℝ) : EReal) * X.termVal d' t' v := by
  rw [← termVal_pow ht, ← termVal_pow ht', termVal_def, termVal_def, termVal_def,
    logSecAbs_mul v.2.2 (pow_mem_sections ht p) (pow_mem_sections ht' q), EReal.coe_add,
    add_add_add_comm]

open Classical in
/-- The family `(f_t^n, n λ_t)_t`, representing the same FS function with `m` replaced by `n m`. -/
def scaleTerms (n : ℕ) (T : Finset (K × ℝ)) : Finset (K × ℝ) :=
  T.image fun t => (t.1 ^ n, (n : ℝ) * t.2)

theorem mem_scaleTerms {n : ℕ} {T : Finset (K × ℝ)} {t : K × ℝ} :
    t ∈ scaleTerms n T ↔ ∃ t₀ ∈ T, (t₀.1 ^ n, (n : ℝ) * t₀.2) = t := by
  classical
  simp only [scaleTerms, Finset.mem_image]

theorem scaleTerms_mem_sections {d : Fin r → ℤ} {T : Finset (K × ℝ)}
    (hT : ∀ t ∈ T, t.1 ∈ X.sections d) {n : ℕ} :
    ∀ t ∈ scaleTerms n T, t.1 ∈ X.sections (n • d) := by
  intro t ht
  obtain ⟨t₀, h₀, rfl⟩ := mem_scaleTerms.1 ht
  exact pow_mem_sections (hT t₀ h₀) n

theorem sup_scaleTerms {n : ℕ} (hn : 0 < n) {d : Fin r → ℤ} {T : Finset (K × ℝ)}
    (hT : ∀ t ∈ T, t.1 ∈ X.sections d) (v : X.an) :
    (scaleTerms n T).sup (fun t => X.termVal (n • d) t v) =
      ((n : ℝ) : EReal) * T.sup fun t => X.termVal d t v := by
  classical
  rw [ProjBerk.ereal_coe_mul_finset_sup (by exact_mod_cast hn)]
  simp only [scaleTerms]
  convert Finset.sup_image T (fun t : K × ℝ => (t.1 ^ n, (n : ℝ) * t.2))
    (fun t => X.termVal (n • d) t v) using 1
  exact Finset.sup_congr rfl fun t ht => (termVal_pow (hT t ht) n v).symm

theorem isRational_scaleTerms {T : Finset (K × ℝ)} (hT : ∀ t ∈ T, ∃ q : ℚ, t.2 = q) (n : ℕ) :
    ∀ t ∈ scaleTerms n T, ∃ q : ℚ, t.2 = q := by
  intro t ht
  obtain ⟨t₀, h₀, rfl⟩ := mem_scaleTerms.1 ht
  obtain ⟨q, hq⟩ := hT t₀ h₀
  exact ⟨n * q, by simp [hq]⟩

/-- `((n • d)_c : ℚ) = n d_c`. -/
theorem intCast_nsmul_apply (n : ℕ) (d : Fin r → ℤ) (c : Fin r) :
    (((n • d) c : ℤ) : ℚ) = n * (d c : ℚ) := by
  rw [Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]

/-! ### Fubini–Study data (`def:gl-fs`) -/

variable (X) in
/-- The data of a **Fubini–Study function of class `a ∈ ℚ^r`** on `𝒳^an` (`def:gl-fs`; BJ22
Definition 2.18, FHX `eq:FS-function`): an integer `m > 0`, the degree `m a ∈ ℤ^r` and a finite family of
pairs `(f_t, λ_t)` of sections `f_t ∈ R_{m a}` and reals `λ_t`. The function is
`m⁻¹ max_t (log |f_t| + λ_t)` (`FSData.eval`); nonvanishing conditions are imposed in
`MultiModel.IsFS` and `MultiModel.IsFinFS`. -/
structure FSData (a : Fin r → ℚ) where
  /-- The integer `m > 0` with `m a ∈ ℤ^r`. -/
  m : ℕ
  m_pos : 0 < m
  /-- The degree `m a ∈ ℤ^r` of the sections. -/
  deg : Fin r → ℤ
  deg_eq : ∀ c, (deg c : ℚ) = m * a c
  /-- The finite family of pairs `(f_t, λ_t)`. -/
  terms : Finset (K × ℝ)
  /-- The `f_t` are sections of degree `m a`. -/
  mem_sections : ∀ t ∈ terms, t.1 ∈ X.sections deg

namespace FSData

variable {a a' : Fin r → ℚ}

/-- The Fubini–Study function `m⁻¹ max_t (log |f_t| + λ_t)` defined by the data. -/
def eval (D : X.FSData a) (v : X.an) : EReal :=
  (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup fun t => X.termVal D.deg t v

/-- The constants `λ_t` are rational. -/
def IsRational (D : X.FSData a) : Prop :=
  ∀ t ∈ D.terms, ∃ q : ℚ, t.2 = q

variable (D : X.FSData a)

theorem eval_def (v : X.an) :
    D.eval v = (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup fun t => X.termVal D.deg t v :=
  rfl

theorem m_ne_zero : (D.m : ℝ) ≠ 0 := by exact_mod_cast D.m_pos.ne'

theorem inv_m_pos : 0 < (D.m : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast D.m_pos)

@[fun_prop]
theorem continuous_eval : Continuous D.eval :=
  (ProjBerk.continuous_ereal_coe_mul (inv_ne_zero D.m_ne_zero)).comp
    (Continuous.finset_sup_apply fun t _ => X.continuous_termVal D.deg t)

theorem eval_ne_top (v : X.an) : D.eval v ≠ ⊤ := by
  refine ProjBerk.ereal_coe_mul_ne_top D.inv_m_pos.le (lt_top_iff_ne_top.1 ?_)
  exact (Finset.sup_lt_iff (bot_lt_top)).2 fun t _ => lt_top_iff_ne_top.2 (termVal_ne_top _ t v)

theorem termVal_le_eval_mul (v : X.an) {t : K × ℝ} (ht : t ∈ D.terms) :
    (((D.m : ℝ)⁻¹ : ℝ) : EReal) * X.termVal D.deg t v ≤ D.eval v :=
  ProjBerk.ereal_coe_mul_monotone D.inv_m_pos.le
    (Finset.le_sup (f := fun t => X.termVal D.deg t v) ht)

/-- An FS function is finite at a point iff one of its sections does not vanish there. -/
theorem eval_ne_bot_iff_exists_secAbs_ne_zero (v : X.an) :
    D.eval v ≠ ⊥ ↔ ∃ t ∈ D.terms, X.secAbs v.1 D.deg t.1 ≠ 0 := by
  constructor
  · intro h
    by_contra hcon
    apply h
    have hsup : (D.terms.sup fun t => X.termVal D.deg t v) = ⊥ := by
      rw [Finset.sup_eq_bot_iff]
      intro t ht
      by_contra h0
      exact hcon ⟨t, ht, (termVal_ne_bot_iff _ t v).1 h0⟩
    rw [eval_def, hsup]
    exact EReal.coe_mul_bot_of_pos D.inv_m_pos
  · rintro ⟨t, ht, hv⟩
    exact ne_bot_of_le_ne_bot
      (ProjBerk.ereal_coe_mul_ne_bot D.inv_m_pos.le ((termVal_ne_bot_iff _ t v).2 hv))
      (D.termVal_le_eval_mul v ht)

/-- An FS function is finite at `⋆` iff its sections are not all zero. -/
theorem eval_triv_ne_bot_iff : D.eval X.triv ≠ ⊥ ↔ ∃ t ∈ D.terms, t.1 ≠ 0 := by
  rw [eval_ne_bot_iff_exists_secAbs_ne_zero]
  refine exists_congr fun t => and_congr_right fun ht => ⟨fun h h0 => h ?_, fun h => ?_⟩
  · rw [h0, secAbs_zero]
  · rw [secAbs_triv (D.mem_sections t ht) h]
    exact one_ne_zero

/-- (FS1) `f(v) ≤ f(⋆)`. -/
theorem eval_le_eval_triv (v : X.an) : D.eval v ≤ D.eval X.triv := by
  rw [eval_def, eval_def]
  exact ProjBerk.ereal_coe_mul_monotone D.inv_m_pos.le
    (Finset.sup_mono_fun fun t ht => termVal_le_termVal_triv (D.mem_sections t ht) v)

/-! #### Maxima -/

theorem inv_m_mul_m_cancel (D D' : X.FSData a) :
    ((D.m : ℝ) * D'.m)⁻¹ * D'.m = (D.m : ℝ)⁻¹ := by
  field_simp [D.m_ne_zero, D'.m_ne_zero]

/-- Data of the same class have proportional degrees: `m (m' a) = m' (m a)`. -/
theorem nsmul_deg_eq (D D' : X.FSData a) : D.m • D'.deg = D'.m • D.deg := by
  funext c
  have h : (((D.m • D'.deg) c : ℤ) : ℚ) = (((D'.m • D.deg) c : ℤ) : ℚ) := by
    rw [intCast_nsmul_apply, intCast_nsmul_apply, D.deg_eq, D'.deg_eq]
    ring
  exact_mod_cast h

open Classical in
/-- The maximum of two FS functions of the same class (BJ22 Proposition 2.19): with `m'' = m m'`, join
the families `(f_t^{m'}, m' λ_t)` and `(f'_s^m, m λ'_s)`, of degree `m' (m a) = m (m' a)`. -/
def sup (D D' : X.FSData a) : X.FSData a where
  m := D.m * D'.m
  m_pos := Nat.mul_pos D.m_pos D'.m_pos
  deg := D'.m • D.deg
  deg_eq c := by
    rw [intCast_nsmul_apply, D.deg_eq, Nat.cast_mul]
    ring
  terms := scaleTerms D'.m D.terms ∪ scaleTerms D.m D'.terms
  mem_sections t ht := by
    rcases Finset.mem_union.1 ht with h | h
    · exact scaleTerms_mem_sections D.mem_sections t h
    · exact nsmul_deg_eq D D' ▸ scaleTerms_mem_sections D'.mem_sections t h

theorem eval_sup (D D' : X.FSData a) (v : X.an) :
    (D.sup D').eval v = max (D.eval v) (D'.eval v) := by
  classical
  have hm : (((D.sup D').m : ℕ) : ℝ) = (D.m : ℝ) * D'.m := Nat.cast_mul _ _
  have ht : (D.sup D').terms = scaleTerms D'.m D.terms ∪ scaleTerms D.m D'.terms := rfl
  have hd : (D.sup D').deg = D'.m • D.deg := rfl
  have h₁ : (scaleTerms D'.m D.terms).sup (fun t => X.termVal (D'.m • D.deg) t v) =
      ((D'.m : ℝ) : EReal) * D.terms.sup fun t => X.termVal D.deg t v :=
    sup_scaleTerms D'.m_pos D.mem_sections v
  have h₂ : (scaleTerms D.m D'.terms).sup (fun t => X.termVal (D'.m • D.deg) t v) =
      ((D.m : ℝ) : EReal) * D'.terms.sup fun t => X.termVal D'.deg t v := by
    rw [← nsmul_deg_eq D D']
    exact sup_scaleTerms D.m_pos D'.mem_sections v
  rw [eval_def, eval_def, eval_def, ht, hd, Finset.sup_union, h₁, h₂, hm,
    ProjBerk.ereal_coe_mul_max (inv_nonneg.2 (by positivity)), ProjBerk.ereal_coe_mul_coe_mul,
    ProjBerk.ereal_coe_mul_coe_mul, inv_m_mul_m_cancel, mul_comm (D.m : ℝ), inv_m_mul_m_cancel]

theorem IsRational.sup {D D' : X.FSData a} (h : D.IsRational) (h' : D'.IsRational) :
    (D.sup D').IsRational := by
  classical
  intro t ht
  rcases Finset.mem_union.1 ht with h1 | h1
  · exact isRational_scaleTerms h _ t h1
  · exact isRational_scaleTerms h' _ t h1

/-! #### Sums -/

open Classical in
/-- The sum of FS functions of classes `a` and `a'` is an FS function of class `a + a'` (BJ22
Proposition 2.19(iii)): with `m'' = m m'`, take the products `f_t^{m'} f'_s^m ∈ R_{m'' (a + a')}` with
constants `m' λ_t + m λ'_s`. -/
def add (D : X.FSData a) (D' : X.FSData a') : X.FSData (a + a') where
  m := D.m * D'.m
  m_pos := Nat.mul_pos D.m_pos D'.m_pos
  deg := D'.m • D.deg + D.m • D'.deg
  deg_eq c := by
    rw [Pi.add_apply, Int.cast_add, intCast_nsmul_apply, intCast_nsmul_apply, D.deg_eq, D'.deg_eq,
      Pi.add_apply, Nat.cast_mul]
    ring
  terms := (D.terms ×ˢ D'.terms).image fun p =>
    (p.1.1 ^ D'.m * p.2.1 ^ D.m, (D'.m : ℝ) * p.1.2 + (D.m : ℝ) * p.2.2)
  mem_sections t ht := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ht
    rw [Finset.mem_product] at hp
    exact mul_mem_sections (pow_mem_sections (D.mem_sections _ hp.1) _)
      (pow_mem_sections (D'.mem_sections _ hp.2) _)

theorem eval_add (D : X.FSData a) (D' : X.FSData a') (v : X.an) :
    (D.add D').eval v = D.eval v + D'.eval v := by
  classical
  have hm : (((D.add D').m : ℕ) : ℝ) = (D.m : ℝ) * D'.m := Nat.cast_mul _ _
  have hsup : ((D.add D').terms.sup fun t => X.termVal (D.add D').deg t v) =
      ((D'.m : ℝ) : EReal) * (D.terms.sup fun t => X.termVal D.deg t v) +
        ((D.m : ℝ) : EReal) * (D'.terms.sup fun t => X.termVal D'.deg t v) := by
    change ((D.terms ×ˢ D'.terms).image fun p =>
      (p.1.1 ^ D'.m * p.2.1 ^ D.m, (D'.m : ℝ) * p.1.2 + (D.m : ℝ) * p.2.2)).sup
        (fun t => X.termVal (D'.m • D.deg + D.m • D'.deg) t v) = _
    rw [Finset.sup_image, ProjBerk.ereal_coe_mul_finset_sup (by exact_mod_cast D'.m_pos),
      ProjBerk.ereal_coe_mul_finset_sup (by exact_mod_cast D.m_pos),
      ← ProjBerk.ereal_finset_sup_product_add]
    exact Finset.sup_congr rfl fun p hp => termVal_mul_pow
      (D.mem_sections _ (Finset.mem_product.1 hp).1) (D'.mem_sections _ (Finset.mem_product.1 hp).2)
      D'.m D.m v
  have h1 : ((D.m : ℝ) * D'.m)⁻¹ * D'.m = (D.m : ℝ)⁻¹ := by
    field_simp [D.m_ne_zero, D'.m_ne_zero]
  have h2 : ((D.m : ℝ) * D'.m)⁻¹ * D.m = (D'.m : ℝ)⁻¹ := by
    field_simp [D.m_ne_zero, D'.m_ne_zero]
  rw [eval_def, eval_def, eval_def, hsup, hm,
    ProjBerk.ereal_coe_mul_add (inv_nonneg.2 (by positivity)), ProjBerk.ereal_coe_mul_coe_mul,
    ProjBerk.ereal_coe_mul_coe_mul, h1, h2]

theorem IsRational.add {D : X.FSData a} {D' : X.FSData a'} (h : D.IsRational)
    (h' : D'.IsRational) : (D.add D').IsRational := by
  classical
  intro t ht
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ht
  rw [Finset.mem_product] at hp
  obtain ⟨q, hq⟩ := h _ hp.1
  obtain ⟨q', hq'⟩ := h' _ hp.2
  exact ⟨D'.m * q + D.m * q', by simp [hq, hq']⟩

/-! #### Positive rational multiples -/

/-- A positive rational multiple `c φ` of an FS function of class `a` is one of class `c a` (BJ22
Proposition 2.19(iii)): with `c = p / q` in lowest terms, take `(f_t^p, p λ_t)` and `q m`. -/
def smul (c : ℚ) (hc : 0 < c) (D : X.FSData a) : X.FSData (c • a) where
  m := c.den * D.m
  m_pos := Nat.mul_pos c.den_pos D.m_pos
  deg := c.num.toNat • D.deg
  deg_eq i := by
    have h : ((c.num.toNat : ℕ) : ℚ) = (c.num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hc.le)
    rw [intCast_nsmul_apply, h, D.deg_eq, Pi.smul_apply, smul_eq_mul, Nat.cast_mul,
      ← Rat.den_mul_eq_num]
    ring
  terms := scaleTerms c.num.toNat D.terms
  mem_sections := scaleTerms_mem_sections D.mem_sections

theorem eval_smul (c : ℚ) (hc : 0 < c) (D : X.FSData a) (v : X.an) :
    (D.smul c hc).eval v = ((c : ℝ) : EReal) * D.eval v := by
  have hp : 0 < c.num.toNat := by have := Rat.num_pos.2 hc; omega
  have hm : (((D.smul c hc).m : ℕ) : ℝ) = (c.den : ℝ) * D.m := Nat.cast_mul _ _
  have ht : (D.smul c hc).terms = scaleTerms c.num.toNat D.terms := rfl
  have hd : (D.smul c hc).deg = c.num.toNat • D.deg := rfl
  rw [eval_def, eval_def, hm, ht, hd, sup_scaleTerms hp D.mem_sections,
    ProjBerk.ereal_coe_mul_coe_mul, ProjBerk.ereal_coe_mul_coe_mul]
  congr 2
  have h : ((c.num.toNat : ℕ) : ℝ) = (c.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hc.le)
  have hd' : (c.den : ℝ) ≠ 0 := by exact_mod_cast c.den_ne_zero
  rw [h, Rat.cast_def]
  field_simp [D.m_ne_zero]

theorem IsRational.smul {c : ℚ} (hc : 0 < c) {D : X.FSData a} (h : D.IsRational) :
    (D.smul c hc).IsRational :=
  isRational_scaleTerms h _

/-! #### Constants of semiample classes -/

open Classical in
/-- The constant `c` as an FS function of a class `a ∈ C(𝒳)`: `m⁻¹ max_t (log |f_t| + m c)` for a
base point free family `f_t ∈ R_{m a}` (`lem:gl-fs-system`, (FS3)). -/
def ofBasePointFree {m : ℕ} (hm : 0 < m) {d : Fin r → ℤ} (hd : ∀ c, (d c : ℚ) = m * a c)
    {s : Finset K} (hs : X.IsBasePointFree d s) (c : ℝ) : X.FSData a where
  m := m
  m_pos := hm
  deg := d
  deg_eq := hd
  terms := s.image fun f => (f, (m : ℝ) * c)
  mem_sections t ht := by
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 ht
    exact hs.1 f hf

/-- The constant data evaluate to `c`, since `max_t |f_t|_v = 1` (`lem:gl-cones`(2)). -/
theorem eval_ofBasePointFree {m : ℕ} (hm : 0 < m) {d : Fin r → ℤ}
    (hd : ∀ c, (d c : ℚ) = m * a c) {s : Finset K} (hs : X.IsBasePointFree d s) (c : ℝ)
    (v : X.an) : (ofBasePointFree hm hd hs c).eval v = (c : EReal) := by
  classical
  change (((m : ℝ)⁻¹ : ℝ) : EReal) *
    ((s.image fun f => (f, (m : ℝ) * c)).sup fun t => X.termVal d t v) = (c : EReal)
  rw [Finset.sup_image]
  have h₁ : (s.sup fun f => X.logSecAbs v.1 d f) = 0 := by
    have h := Finset.apply_sup_eq_sup_comp_of_linearOrder (s := s)
      (f := fun f => X.secAbs v.1 d f) (fun x : ℝ≥0 => ENNReal.log (x : ℝ≥0∞))
      (fun x y hxy => ENNReal.log_monotone (ENNReal.coe_le_coe.2 hxy)) (by simp)
    rw [hs.sup_secAbs_eq_one v, ENNReal.coe_one, ENNReal.log_one] at h
    exact h.symm
  have h₂ := Finset.apply_sup_eq_sup_comp_of_linearOrder (s := s)
    (f := fun f => X.logSecAbs v.1 d f) (fun x : EReal => x + (((m : ℝ) * c : ℝ) : EReal))
    (fun _ _ hxy => add_le_add_left hxy _) (EReal.bot_add _)
  rw [h₁, zero_add] at h₂
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [show ((s.sup ((fun t => X.termVal d t v) ∘ fun f => (f, (m : ℝ) * c))) : EReal) =
    (((m : ℝ) * c : ℝ) : EReal) from h₂.symm, ← EReal.coe_mul, inv_mul_cancel_left₀ hm']

theorem isRational_ofBasePointFree {m : ℕ} (hm : 0 < m) {d : Fin r → ℤ}
    (hd : ∀ c, (d c : ℚ) = m * a c) {s : Finset K} (hs : X.IsBasePointFree d s) (c : ℚ) :
    (ofBasePointFree hm hd hs (c : ℝ)).IsRational := by
  classical
  intro t ht
  obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 ht
  exact ⟨m * c, by push_cast; ring⟩

/-! #### Changing the weights -/

open Classical in
/-- The data `(m, m a, (f_t, ρ(λ_t))_t)` obtained by changing the weights `λ_t` through a map
`ρ : ℝ → ℝ`. -/
def reweight (ρ : ℝ → ℝ) : X.FSData a where
  m := D.m
  m_pos := D.m_pos
  deg := D.deg
  deg_eq := D.deg_eq
  terms := D.terms.image fun t => (t.1, ρ t.2)
  mem_sections t ht := by
    obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.1 ht
    exact D.mem_sections t₀ h₀

theorem eval_reweight (ρ : ℝ → ℝ) (v : X.an) :
    (D.reweight ρ).eval v =
      (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup fun t => X.termVal D.deg (t.1, ρ t.2) v := by
  classical
  rw [eval_def]
  congr 1
  change (D.terms.image fun t => (t.1, ρ t.2)).sup _ = _
  rw [Finset.sup_image]
  rfl

theorem isRational_reweight {ρ : ℝ → ℝ} (hρ : ∀ t ∈ D.terms, ∃ q : ℚ, ρ t.2 = q) :
    (D.reweight ρ).IsRational := by
  classical
  intro t ht
  obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.1 ht
  exact hρ t₀ h₀

theorem eval_reweight_mono {ρ ρ' : ℝ → ℝ} (hρ : ∀ t ∈ D.terms, ρ t.2 ≤ ρ' t.2) (v : X.an) :
    (D.reweight ρ).eval v ≤ (D.reweight ρ').eval v := by
  rw [eval_reweight, eval_reweight]
  refine ProjBerk.ereal_coe_mul_monotone D.inv_m_pos.le (Finset.sup_mono_fun fun t ht => ?_)
  rw [termVal_def, termVal_def]
  exact add_le_add_right (EReal.coe_le_coe_iff.2 (hρ t ht)) _

/-- Shifting all weights by `m c` adds `c` to the FS function. -/
theorem eval_reweight_add (c : ℝ) (v : X.an) :
    (D.reweight fun x => x + D.m * c).eval v = D.eval v + (c : EReal) := by
  have hsup : (D.terms.sup fun t => X.termVal D.deg (t.1, t.2 + D.m * c) v) =
      (D.terms.sup fun t => X.termVal D.deg t v) + ((D.m * c : ℝ) : EReal) := by
    rw [Finset.apply_sup_eq_sup_comp_of_linearOrder (s := D.terms)
      (fun x : EReal => x + ((D.m * c : ℝ) : EReal)) (fun _ _ h => add_le_add_left h _)
      (EReal.bot_add _)]
    refine Finset.sup_congr rfl fun t _ => ?_
    simp only [Function.comp_apply, termVal_def, EReal.coe_add, add_assoc]
  rw [eval_reweight, hsup, eval_def, ProjBerk.ereal_coe_mul_add D.inv_m_pos.le,
    ← EReal.coe_mul, ← mul_assoc, inv_mul_cancel₀ D.m_ne_zero, one_mul]

theorem le_eval_reweight {ρ : ℝ → ℝ} {c : ℝ} (hρ : ∀ t ∈ D.terms, t.2 + D.m * c ≤ ρ t.2)
    (v : X.an) : D.eval v + (c : EReal) ≤ (D.reweight ρ).eval v := by
  rw [← eval_reweight_add]
  exact D.eval_reweight_mono hρ v

theorem eval_reweight_le {ρ : ℝ → ℝ} {c : ℝ} (hρ : ∀ t ∈ D.terms, ρ t.2 ≤ t.2 + D.m * c)
    (v : X.an) : (D.reweight ρ).eval v ≤ D.eval v + (c : EReal) := by
  rw [← eval_reweight_add]
  exact D.eval_reweight_mono hρ v

/-! #### Rational approximation (FS5) -/

/-- **Rational approximation** (BJ22 Lemma 2.17, for `a ∈ C(𝒳)`): every FS function of a
semiample class `a` is the pointwise limit (= infimum) of a decreasing sequence of real-valued
rational FS functions of class `a`, `max(m⁻¹ max_t (log |f_t| + q_t^{(N)}), -N)` with rationals
`q_t^{(N)} ∈ (λ_t + m/(N+2), λ_t + m/(N+1))`; the constant `-N` of class `a` exists since
`a ∈ C(𝒳)`. -/
theorem exists_antitone_isRational (ha : a ∈ X.semiampleCone) : ∃ E : ℕ → X.FSData a,
    (∀ N, (E N).IsRational) ∧ (∀ N v, (E N).eval v ≠ ⊥) ∧
      (∀ v, Antitone fun N => (E N).eval v) ∧ ∀ v, D.eval v = ⨅ N, (E N).eval v := by
  obtain ⟨m₀, d₀, s₀, hm₀, hd₀, hs₀⟩ := ha
  have hm : (0 : ℝ) < D.m := by exact_mod_cast D.m_pos
  have hδ : ∀ N : ℕ, (1 : ℝ) / ((N : ℝ) + 2) < 1 / ((N : ℝ) + 1) := fun N =>
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  choose q hq using fun (N : ℕ) (x : ℝ) => exists_rat_btwn
    (show x + D.m * (1 / ((N : ℝ) + 2)) < x + D.m * (1 / ((N : ℝ) + 1)) by
      have := mul_lt_mul_of_pos_left (hδ N) hm
      linarith)
  set R : ℕ → X.FSData a := fun N => D.reweight fun x => (q N x : ℝ) with hR
  have hlow : ∀ (N : ℕ) v, D.eval v + ((1 / ((N : ℝ) + 2) : ℝ) : EReal) ≤ (R N).eval v :=
    fun N v => D.le_eval_reweight (fun t _ => (hq N t.2).1.le) v
  have hup : ∀ (N : ℕ) v, (R N).eval v ≤ D.eval v + ((1 / ((N : ℝ) + 1) : ℝ) : EReal) :=
    fun N v => D.eval_reweight_le (fun t _ => (hq N t.2).2.le) v
  have hrat : ∀ N, (R N).IsRational := fun N =>
    D.isRational_reweight fun t _ => ⟨q N t.2, rfl⟩
  have hD := D.eval_ne_top
  set E : ℕ → X.FSData a := fun N =>
    (R N).sup (ofBasePointFree hm₀ hd₀ hs₀ ((-(N : ℚ) : ℚ) : ℝ)) with hE
  have hEval : ∀ N v, (E N).eval v = max ((R N).eval v) ((((-(N : ℚ) : ℚ) : ℝ) : EReal)) :=
    fun N v => by rw [hE, eval_sup, eval_ofBasePointFree]
  refine ⟨E, fun N => (hrat N).sup (isRational_ofBasePointFree _ _ _ _), fun N v => ?_,
    fun v => ?_, fun v => ?_⟩
  · rw [hEval]
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _)
  · refine antitone_nat_of_succ_le fun N => ?_
    rw [hEval, hEval]
    refine max_le_max ?_ ?_
    · refine (hup (N + 1) v).trans ((le_of_eq ?_).trans (hlow N v))
      push_cast
      ring_nf
    · exact EReal.coe_le_coe_iff.2 (by push_cast; linarith)
  · refine le_antisymm (le_iInf fun N => ?_) (le_of_forall_gt_imp_ge_of_dense fun c hc => ?_)
    · rw [hEval]
      by_cases hv : D.eval v = ⊥
      · rw [hv]; exact bot_le
      · exact (ProjBerk.ereal_lt_add_coe hv (hD v) (by positivity)).le.trans
          ((hlow N v).trans (le_max_left _ _))
    · obtain ⟨s, hs₁, hs₂⟩ := EReal.lt_iff_exists_real_btwn.1 hc
      obtain ⟨N₁, hN₁⟩ : ∃ N : ℕ, D.eval v + ((1 / ((N : ℝ) + 1) : ℝ) : EReal) ≤ s := by
        by_cases hv : D.eval v = ⊥
        · exact ⟨0, by rw [hv, EReal.bot_add]; exact bot_le⟩
        · lift D.eval v to ℝ using ⟨hD v, hv⟩ with ρ hρ
          have hρs : ρ < s := EReal.coe_lt_coe_iff.1 hs₁
          obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.2 hρs)
          exact ⟨N, by rw [← EReal.coe_add, EReal.coe_le_coe_iff]; linarith⟩
      obtain ⟨N₂, hN₂⟩ := exists_nat_ge (-s)
      set N := Max.max N₁ N₂
      refine (iInf_le _ N).trans ?_
      rw [hEval]
      refine le_trans (max_le ?_ ?_) hs₂.le
      · refine (hup N v).trans ((add_le_add_right (EReal.coe_le_coe_iff.2 ?_) _).trans hN₁)
        exact one_div_le_one_div_of_le (by positivity)
          (by have : (N₁ : ℝ) ≤ N := by exact_mod_cast le_max_left N₁ N₂
              linarith)
      · refine EReal.coe_le_coe_iff.2 ?_
        have : (N₂ : ℝ) ≤ N := by exact_mod_cast le_max_right N₁ N₂
        push_cast
        linarith

/-! #### Single terms -/

/-- The single term `log |f| + λ` as an FS function of class `d`, for a section `f ∈ R_d`,
`d ∈ ℤ^r` (`m = 1`). -/
def single {d : Fin r → ℤ} {f : K} (hf : f ∈ X.sections d) (c : ℝ) :
    X.FSData fun i => (d i : ℚ) where
  m := 1
  m_pos := one_pos
  deg := d
  deg_eq i := by simp
  terms := {(f, c)}
  mem_sections t ht := by
    rw [Finset.mem_singleton] at ht
    subst ht
    exact hf

theorem eval_single {d : Fin r → ℤ} {f : K} (hf : f ∈ X.sections d) (c : ℝ) (v : X.an) :
    (single hf c).eval v = X.termVal d (f, c) v := by
  change ((((1 : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * (({(f, c)} : Finset (K × ℝ)).sup
    fun t => X.termVal d t v) = _
  rw [Finset.sup_singleton, Nat.cast_one, inv_one, EReal.coe_one, one_mul]

end FSData

/-! ### Fubini–Study functions on `𝒳^an` (`def:gl-fs`) -/

variable (X) in
/-- **Fubini–Study functions of class `a ∈ ℚ^r`** on `𝒳^an` (`def:gl-fs`, `𝓗(𝒳, a)`; BJ22
Definition 2.18, FHX `eq:FS-function`): `φ = m⁻¹ max_t (log |f_t| + λ_t)` for an integer `m > 0` with
`m a ∈ ℤ^r`, finitely many sections `f_t ∈ R_{m a}`, not all zero, and `λ_t ∈ ℝ`. -/
def IsFS (a : Fin r → ℚ) (φ : X.an → EReal) : Prop :=
  ∃ D : X.FSData a, (∃ t ∈ D.terms, t.1 ≠ 0) ∧ ∀ v, φ v = D.eval v

variable (X) in
/-- **Finite rational Fubini–Study functions of class `a`** (`def:gl-fs`, `𝓗_fin(𝒳, a)`): as
`IsFS`, with all `λ_t ∈ ℚ` and the `f_t` without common zero on `𝒳^an`. -/
def IsFinFS (a : Fin r → ℚ) (φ : X.an → EReal) : Prop :=
  ∃ D : X.FSData a, D.IsRational ∧ (∀ v : X.an, ∃ t ∈ D.terms, X.secAbs v.1 D.deg t.1 ≠ 0) ∧
    ∀ v, φ v = D.eval v

variable (X) in
/-- **Homogeneous Fubini–Study functions of class `a`** (`def:gl-fs`, `𝓗_hom(𝒳, a)`): as `IsFS`,
with all `λ_t = 0`. -/
def IsHomFS (a : Fin r → ℚ) (φ : X.an → EReal) : Prop :=
  ∃ D : X.FSData a, (∀ t ∈ D.terms, t.2 = 0) ∧ (∃ t ∈ D.terms, t.1 ≠ 0) ∧ ∀ v, φ v = D.eval v

variable {a a' b : Fin r → ℚ} {φ ψ : X.an → EReal}

/-- `IsFS` in terms of finiteness at `⋆`. -/
theorem isFS_iff : X.IsFS a φ ↔ ∃ D : X.FSData a, D.eval X.triv ≠ ⊥ ∧ ∀ v, φ v = D.eval v := by
  simp only [IsFS, FSData.eval_triv_ne_bot_iff]

/-- `IsFinFS` in terms of finiteness on `𝒳^an`. -/
theorem isFinFS_iff : X.IsFinFS a φ ↔ ∃ D : X.FSData a, D.IsRational ∧
    (∀ v : X.an, D.eval v ≠ ⊥) ∧ ∀ v, φ v = D.eval v := by
  simp only [IsFinFS, FSData.eval_ne_bot_iff_exists_secAbs_ne_zero]

theorem IsHomFS.isFS (h : X.IsHomFS a φ) : X.IsFS a φ := by
  obtain ⟨D, -, hD, hφ⟩ := h
  exact ⟨D, hD, hφ⟩

/-- A class carrying a finite Fubini–Study function is semiample: `𝓗_fin(𝒳, a) = ∅` for
`a ∉ C(𝒳)`. -/
theorem IsFinFS.mem_semiampleCone (h : X.IsFinFS a φ) : a ∈ X.semiampleCone := by
  classical
  obtain ⟨D, -, hD, -⟩ := h
  refine ⟨D.m, D.deg, D.terms.image Prod.fst, D.m_pos, D.deg_eq, fun f hf => ?_, fun v => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hf
    exact D.mem_sections t ht
  · obtain ⟨t, ht, hne⟩ := hD v
    exact ⟨t.1, Finset.mem_image_of_mem _ ht, hne⟩

/-! #### The axioms (FS1)–(FS5) -/

theorem IsFS.continuous (h : X.IsFS a φ) : Continuous φ := by
  obtain ⟨D, -, hφ⟩ := h
  rw [show φ = D.eval from funext hφ]
  exact D.continuous_eval

/-- (FS1) `φ(⋆) ≠ -∞`. -/
theorem IsFS.apply_triv_ne_bot (h : X.IsFS a φ) : φ X.triv ≠ ⊥ := by
  obtain ⟨D, hD, hφ⟩ := isFS_iff.1 h
  rw [hφ]
  exact hD

theorem IsFS.ne_top (h : X.IsFS a φ) (v : X.an) : φ v ≠ ⊤ := by
  obtain ⟨D, -, hφ⟩ := h
  rw [hφ]
  exact D.eval_ne_top v

/-- (FS1) `φ ≤ φ(⋆)`. -/
theorem IsFS.le_apply_triv (h : X.IsFS a φ) (v : X.an) : φ v ≤ φ X.triv := by
  obtain ⟨D, -, hφ⟩ := h
  rw [hφ, hφ]
  exact D.eval_le_eval_triv v

theorem IsFinFS.isFS (h : X.IsFinFS a φ) : X.IsFS a φ := by
  obtain ⟨D, -, hD, hφ⟩ := isFinFS_iff.1 h
  exact isFS_iff.2 ⟨D, hD X.triv, hφ⟩

/-- Finite Fubini–Study functions are real valued. -/
theorem IsFinFS.ne_bot (h : X.IsFinFS a φ) (v : X.an) : φ v ≠ ⊥ := by
  obtain ⟨D, -, hD, hφ⟩ := isFinFS_iff.1 h
  rw [hφ]
  exact hD v

variable (X) in
/-- (FS3) real constants are Fubini–Study functions of every class `a ∈ C(𝒳)`. -/
theorem isFS_const (ha : a ∈ X.semiampleCone) (c : ℝ) : X.IsFS a fun _ => (c : EReal) := by
  obtain ⟨m, d, s, hm, hd, hs⟩ := ha
  refine isFS_iff.2 ⟨FSData.ofBasePointFree hm hd hs c, ?_, fun v =>
    (FSData.eval_ofBasePointFree hm hd hs c v).symm⟩
  rw [FSData.eval_ofBasePointFree]
  exact EReal.coe_ne_bot c

variable (X) in
/-- (FS3) rational constants are finite Fubini–Study functions of every class `a ∈ C(𝒳)`. -/
theorem isFinFS_const (ha : a ∈ X.semiampleCone) (c : ℚ) :
    X.IsFinFS a fun _ => ((c : ℝ) : EReal) := by
  obtain ⟨m, d, s, hm, hd, hs⟩ := ha
  refine isFinFS_iff.2 ⟨FSData.ofBasePointFree hm hd hs (c : ℝ),
    FSData.isRational_ofBasePointFree hm hd hs c, fun v => ?_, fun v =>
    (FSData.eval_ofBasePointFree hm hd hs (c : ℝ) v).symm⟩
  rw [FSData.eval_ofBasePointFree]
  exact EReal.coe_ne_bot _

/-- Maxima of Fubini–Study functions of the same class. -/
theorem IsFS.max (hφ : X.IsFS a φ) (hψ : X.IsFS a ψ) : X.IsFS a fun v => max (φ v) (ψ v) := by
  obtain ⟨D, hD, hφ⟩ := isFS_iff.1 hφ
  obtain ⟨D', -, hψ⟩ := isFS_iff.1 hψ
  refine isFS_iff.2 ⟨D.sup D', ?_, fun v => by rw [FSData.eval_sup, hφ, hψ]⟩
  rw [FSData.eval_sup]
  exact ne_bot_of_le_ne_bot hD (le_max_left _ _)

/-- Maxima of finite Fubini–Study functions of the same class. -/
theorem IsFinFS.max (hφ : X.IsFinFS a φ) (hψ : X.IsFinFS a ψ) :
    X.IsFinFS a fun v => max (φ v) (ψ v) := by
  obtain ⟨D, hDr, hD, hφ⟩ := isFinFS_iff.1 hφ
  obtain ⟨D', hD'r, -, hψ⟩ := isFinFS_iff.1 hψ
  refine isFinFS_iff.2 ⟨D.sup D', hDr.sup hD'r, fun v => ?_, fun v => by
    rw [FSData.eval_sup, hφ, hψ]⟩
  rw [FSData.eval_sup]
  exact ne_bot_of_le_ne_bot (hD v) (le_max_left _ _)

/-- (FS4) `𝓗(𝒳, a) + 𝓗(𝒳, a') ⊆ 𝓗(𝒳, a + a')`. -/
theorem IsFS.add (hφ : X.IsFS a φ) (hψ : X.IsFS a' ψ) : X.IsFS (a + a') fun v => φ v + ψ v := by
  obtain ⟨D, hD, hφ⟩ := isFS_iff.1 hφ
  obtain ⟨D', hD', hψ⟩ := isFS_iff.1 hψ
  refine isFS_iff.2 ⟨D.add D', ?_, fun v => by rw [FSData.eval_add, hφ, hψ]⟩
  rw [FSData.eval_add]
  exact EReal.add_ne_bot_iff.2 ⟨hD, hD'⟩

/-- (FS4) `𝓗_fin(𝒳, a) + 𝓗_fin(𝒳, a') ⊆ 𝓗_fin(𝒳, a + a')`. -/
theorem IsFinFS.add (hφ : X.IsFinFS a φ) (hψ : X.IsFinFS a' ψ) :
    X.IsFinFS (a + a') fun v => φ v + ψ v := by
  obtain ⟨D, hDr, hD, hφ⟩ := isFinFS_iff.1 hφ
  obtain ⟨D', hD'r, hD', hψ⟩ := isFinFS_iff.1 hψ
  refine isFinFS_iff.2 ⟨D.add D', hDr.add hD'r, fun v => ?_, fun v => by
    rw [FSData.eval_add, hφ, hψ]⟩
  rw [FSData.eval_add]
  exact EReal.add_ne_bot_iff.2 ⟨hD v, hD' v⟩

/-- (FS4) `c 𝓗(𝒳, a) ⊆ 𝓗(𝒳, c a)` for `c ∈ ℚ_{>0}`. -/
theorem IsFS.smul (h : X.IsFS a φ) {c : ℚ} (hc : 0 < c) :
    X.IsFS (c • a) fun v => ((c : ℝ) : EReal) * φ v := by
  obtain ⟨D, hD, hφ⟩ := isFS_iff.1 h
  refine isFS_iff.2 ⟨D.smul c hc, ?_, fun v => by rw [FSData.eval_smul, hφ]⟩
  rw [FSData.eval_smul]
  exact ProjBerk.ereal_coe_mul_ne_bot (by exact_mod_cast hc.le) hD

/-- (FS4) `c 𝓗_fin(𝒳, a) ⊆ 𝓗_fin(𝒳, c a)` for `c ∈ ℚ_{>0}`. -/
theorem IsFinFS.smul (h : X.IsFinFS a φ) {c : ℚ} (hc : 0 < c) :
    X.IsFinFS (c • a) fun v => ((c : ℝ) : EReal) * φ v := by
  obtain ⟨D, hDr, hD, hφ⟩ := isFinFS_iff.1 h
  refine isFinFS_iff.2 ⟨D.smul c hc, hDr.smul hc, fun v => ?_, fun v => by
    rw [FSData.eval_smul, hφ]⟩
  rw [FSData.eval_smul]
  exact ProjBerk.ereal_coe_mul_ne_bot (by exact_mod_cast hc.le) (hD v)

/-- (FS2) `𝓗(𝒳, a) ⊆ 𝓗(𝒳, b)` for `a ≤ b`: add the constant `0` of class `b - a ≥ 0`, whose family
consists of monomials `z̃^γ` with `max_γ |z̃^γ| = 1`. -/
theorem IsFS.mono_class (h : X.IsFS a φ) (hab : a ≤ b) : X.IsFS b φ := by
  have h' := h.add (X.isFS_const (X.nonneg_mem_semiampleCone (sub_nonneg.2 hab)) 0)
  rw [add_sub_cancel] at h'
  simpa only [EReal.coe_zero, add_zero] using h'

/-- (FS2) `𝓗_fin(𝒳, a) ⊆ 𝓗_fin(𝒳, b)` for `a ≤ b`. -/
theorem IsFinFS.mono_class (h : X.IsFinFS a φ) (hab : a ≤ b) : X.IsFinFS b φ := by
  have h' := h.add (X.isFinFS_const (X.nonneg_mem_semiampleCone (sub_nonneg.2 hab)) 0)
  rw [add_sub_cancel] at h'
  simpa only [Rat.cast_zero, EReal.coe_zero, add_zero] using h'

/-- (FS5) for `a ∈ C(𝒳)`: every `φ ∈ 𝓗(𝒳, a)` is the limit of a decreasing sequence in
`𝓗_fin(𝒳, a)`. -/
theorem IsFS.exists_antitone_isFinFS (h : X.IsFS a φ) (ha : a ∈ X.semiampleCone) :
    ∃ g : ℕ → X.an → EReal, (∀ n, X.IsFinFS a (g n)) ∧ (∀ v, Antitone fun n => g n v) ∧
      ∀ v, φ v = ⨅ n, g n v := by
  obtain ⟨D, -, hφ⟩ := h
  obtain ⟨E, hEr, hEb, hanti, hinf⟩ := D.exists_antitone_isRational ha
  exact ⟨fun n => (E n).eval, fun n => isFinFS_iff.2 ⟨E n, hEr n, hEb n, fun _ => rfl⟩, hanti,
    fun v => by rw [hφ, hinf]⟩

/-- `log |f| ∈ 𝓗(𝒳, d)` for `0 ≠ f ∈ R_d`, `d ∈ ℤ^r`. -/
theorem isFS_logSecAbs {d : Fin r → ℤ} {f : K} (hf : f ∈ X.sections d) (hf0 : f ≠ 0) :
    X.IsFS (fun i => (d i : ℚ)) fun v => X.logSecAbs v.1 d f := by
  refine ⟨FSData.single hf 0, ⟨(f, 0), Finset.mem_singleton_self _, hf0⟩, fun v => ?_⟩
  rw [FSData.eval_single, termVal_def, EReal.coe_zero, add_zero]

/-! ### The Fubini–Study system of a model (`lem:gl-fs-system`) -/

variable (X) in
/-- **`(𝒳^an, ⋆)` is a Fubini–Study system with semiample cone `C(𝒳)`** (`lem:gl-fs-system`;
BJ22 Proposition 2.19, Lemma 2.17), with `𝓗(a) = 𝓗(𝒳, a)` and `𝓗_fin(a) = 𝓗_fin(𝒳, a)`. -/
def fsSystem : FSSystemC X.an r where
  triv := X.triv
  C := X.semiampleCone
  nonneg_mem_C _ ha := X.nonneg_mem_semiampleCone ha
  IsFS := X.IsFS
  IsFinFS := X.IsFinFS
  continuous_of_isFS h := h.continuous
  apply_triv_ne_bot h := h.apply_triv_ne_bot
  apply_triv_ne_top h := h.ne_top _
  le_apply_triv h x := h.le_apply_triv x
  isFS_of_isFinFS h := h.isFS
  ne_bot_of_isFinFS h := h.ne_bot
  isFS_mono h hab := h.mono_class hab
  isFinFS_mono h hab := h.mono_class hab
  isFS_const ha c := X.isFS_const ha c
  isFinFS_const ha c := X.isFinFS_const ha c
  isFS_max hf hg := hf.max hg
  isFinFS_max hf hg := hf.max hg
  isFS_add hf hg := hf.add hg
  isFinFS_add hf hg := hf.add hg
  isFS_smul hc h := h.smul hc
  isFinFS_smul hc h := h.smul hc
  exists_antitone_isFinFS ha h := h.exists_antitone_isFinFS ha

variable (X) in
@[simp] theorem fsSystem_triv : X.fsSystem.triv = X.triv := rfl

variable (X) in
theorem fsSystem_C : X.fsSystem.C = X.semiampleCone := rfl

theorem fsSystem_isFS_iff : X.fsSystem.IsFS a φ ↔ X.IsFS a φ := Iff.rfl

theorem fsSystem_isFinFS_iff : X.fsSystem.IsFinFS a φ ↔ X.IsFinFS a φ := Iff.rfl

variable (X) in
/-- The closure of the semiample cone of the system is the model-nef cone `N(𝒳)`. -/
theorem coneClosure_fsSystem : X.fsSystem.coneClosure = X.nefCone := rfl

/-! ### Psh functions on `𝒳^an` (`def:gl-psh`) -/

variable (X) in
/-- **`θ`-psh functions on `𝒳^an`** (`def:gl-psh`, `PSH(𝒳, θ)` for `θ ∈ ℝ^r`; BJ22
Definition 4.1, see `rmk:gl-model-comparison`): usc functions `u ≢ -∞` that are limits of
decreasing nets `φ_α ∈ 𝓗(𝒳, a_α)`, `a_α → θ`, i.e. the `θ`-psh functions of `X.fsSystem`. -/
abbrev IsPSH (θ : Fin r → ℝ) (u : X.an → EReal) : Prop :=
  X.fsSystem.IsPSH θ u

variable (X) in
/-- The **psh envelope** `P_θ(φ) = sup {τ ∈ PSH(𝒳, θ) : τ ≤ φ}` (`def:gl-psh`). -/
abbrev envelope (θ : Fin r → ℝ) (φ : X.an → EReal) : X.an → EReal :=
  X.fsSystem.envelope θ φ

variable (X) in
/-- The **envelope property** `EP_𝒳(θ)` (`def:gl-psh`): `(sup_i u_i)^⋆ ∈ PSH(𝒳, θ)` for every
nonempty family `(u_i) ⊆ PSH(𝒳, θ)` bounded above. -/
abbrev HasEnvelopeProperty (θ : Fin r → ℝ) : Prop :=
  X.fsSystem.HasEnvelopeProperty θ

variable {θ θ' : Fin r → ℝ} {u u' : X.an → EReal}

/-! #### `thm:gl-fs-system-theory`(1) for `𝒳`, every class -/

/-- PSH1: `𝓗(𝒳, a) ⊆ PSH(𝒳, a)`. -/
theorem IsFS.isPSH (h : X.IsFS a φ) : X.IsPSH (fun c => (a c : ℝ)) φ :=
  FSSystemC.IsFS.isPSH (F := X.fsSystem) h

theorem IsFinFS.isPSH (h : X.IsFinFS a φ) : X.IsPSH (fun c => (a c : ℝ)) φ :=
  h.isFS.isPSH

/-- `log |f| ∈ PSH(𝒳, d)` for `0 ≠ f ∈ R_d`. -/
theorem isPSH_logSecAbs {d : Fin r → ℤ} {f : K} (hf : f ∈ X.sections d) (hf0 : f ≠ 0) :
    X.IsPSH (fun i => ((d i : ℚ) : ℝ)) fun v => X.logSecAbs v.1 d f :=
  (isFS_logSecAbs hf hf0).isPSH

/-- **The maximum principle**: `u ≤ u(⋆)`. -/
theorem IsPSH.le_apply_triv (h : X.IsPSH θ u) (v : X.an) : u v ≤ u X.triv :=
  FSSystemC.IsPSH.le_apply_triv h v

/-- A `θ`-psh function is finite at `⋆`. -/
theorem IsPSH.apply_triv_ne_bot (h : X.IsPSH θ u) : u X.triv ≠ ⊥ :=
  FSSystemC.IsPSH.apply_triv_ne_bot h

/-- `u(⋆) < +∞`. -/
theorem IsPSH.apply_triv_ne_top (h : X.IsPSH θ u) : u X.triv ≠ ⊤ :=
  FSSystemC.IsPSH.apply_triv_ne_top h

/-- **The maximum principle**: a `θ`-psh function attains its supremum at `⋆`. -/
theorem IsPSH.iSup_eq (h : X.IsPSH θ u) : ⨆ v, u v = u X.triv :=
  FSSystemC.IsPSH.iSup_eq h

/-- Maxima. -/
theorem IsPSH.max (h : X.IsPSH θ u) (h' : X.IsPSH θ u') :
    X.IsPSH θ fun v => Max.max (u v) (u' v) :=
  FSSystemC.IsPSH.max h h'

/-- Sums: `PSH(𝒳, θ) + PSH(𝒳, θ') ⊆ PSH(𝒳, θ + θ')`. -/
theorem IsPSH.add (h : X.IsPSH θ u) (h' : X.IsPSH θ' u') :
    X.IsPSH (θ + θ') fun v => u v + u' v :=
  FSSystemC.IsPSH.add h h'

/-- Real translates. -/
theorem IsPSH.add_const (h : X.IsPSH θ u) (c : ℝ) : X.IsPSH θ fun v => u v + (c : EReal) :=
  FSSystemC.IsPSH.add_const h c

/-- Positive rational multiples: `c PSH(𝒳, θ) ⊆ PSH(𝒳, c θ)`. -/
theorem IsPSH.smul_rat (h : X.IsPSH θ u) {c : ℚ} (hc : 0 < c) :
    X.IsPSH ((c : ℝ) • θ) fun v => ((c : ℝ) : EReal) * u v :=
  FSSystemC.IsPSH.smul_rat h hc

/-- Monotonicity in the class: `PSH(𝒳, θ) ⊆ PSH(𝒳, θ')` for `θ ≤ θ'`. -/
theorem IsPSH.mono_class (h : X.IsPSH θ u) (hθθ' : θ ≤ θ') : X.IsPSH θ' u :=
  FSSystemC.IsPSH.mono_class h hθθ'

/-! #### `thm:gl-fs-system-theory`(2) for `𝒳`, nef classes -/

variable (X) in
/-- Real constants are `θ`-psh for `θ ∈ N(𝒳)`. -/
theorem isPSH_const (hθ : θ ∈ X.nefCone) (c : ℝ) : X.IsPSH θ fun _ => (c : EReal) :=
  FSSystemC.isPSH_const hθ c

/-- **PSH2** for `θ₀ ∈ N(𝒳)`: if `uᵢ ∈ PSH(𝒳, θᵢ)` is a decreasing net with `θᵢ → θ₀` and
`w = infᵢ uᵢ ≢ -∞`, then `w ∈ PSH(𝒳, θ₀)`. -/
theorem isPSH_of_antitone {θ₀ : Fin r → ℝ} (hθ₀ : θ₀ ∈ X.nefCone) {ι : Type u} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] {θ : ι → Fin r → ℝ} (hθ : Tendsto θ atTop (𝓝 θ₀))
    {u : ι → X.an → EReal} (hu : ∀ i, X.IsPSH (θ i) (u i)) (hanti : ∀ v, Antitone fun i => u i v)
    {w : X.an → EReal} (hw : ∀ v, w v = ⨅ i, u i v) (hfin : ∃ v, w v ≠ ⊥) : X.IsPSH θ₀ w :=
  FSSystemC.isPSH_of_antitone hθ₀ hθ hu hanti hw hfin

/-- **PSH2** for decreasing sequences, `θ₀ ∈ N(𝒳)`. -/
theorem isPSH_of_antitone_seq {θ₀ : Fin r → ℝ} (hθ₀ : θ₀ ∈ X.nefCone) {θ : ℕ → Fin r → ℝ}
    (hθ : Tendsto θ atTop (𝓝 θ₀)) {u : ℕ → X.an → EReal} (hu : ∀ m, X.IsPSH (θ m) (u m))
    (hanti : ∀ v, Antitone fun m => u m v) {w : X.an → EReal} (hw : ∀ v, w v = ⨅ m, u m v)
    (hfin : ∃ v, w v ≠ ⊥) : X.IsPSH θ₀ w :=
  FSSystemC.isPSH_of_antitone_seq hθ₀ hθ hu hanti hw hfin

/-- Positive real multiples for `θ ∈ N(𝒳)`: `t PSH(𝒳, θ) ⊆ PSH(𝒳, t θ)`. -/
theorem IsPSH.smul (h : X.IsPSH θ u) (hθ : θ ∈ X.nefCone) {t : ℝ} (ht : 0 < t) :
    X.IsPSH (t • θ) fun v => (t : EReal) * u v :=
  FSSystemC.IsPSH.smul h hθ ht

/-- `PSH(𝒳, t θ) = t PSH(𝒳, θ)` for `θ ∈ N(𝒳)` and `t > 0`. -/
theorem isPSH_smul_iff (hθ : θ ∈ X.nefCone) {t : ℝ} (ht : 0 < t) :
    X.IsPSH (t • θ) (fun v => (t : EReal) * u v) ↔ X.IsPSH θ u :=
  FSSystemC.isPSH_smul_iff hθ ht

/-- **Regularization** for `θ ∈ N(𝒳)`: every `u ∈ PSH(𝒳, θ)` is the limit of a decreasing net
`f_α ∈ 𝓗_fin(𝒳, a_α)` with `a_α > θ` coordinatewise and `a_α → θ`. -/
theorem IsPSH.exists_isFinFS_net_gt (h : X.IsPSH θ u) (hθ : θ ∈ X.nefCone) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (a : ι → Fin r → ℚ) (f : ι → X.an → EReal), (∀ i, X.IsFinFS (a i) (f i)) ∧
        (∀ i c, θ c < a i c) ∧ Tendsto (fun i c => (a i c : ℝ)) atTop (𝓝 θ) ∧
          (∀ v, Antitone fun i => f i v) ∧ ∀ v, u v = ⨅ i, f i v :=
  FSSystemC.IsPSH.exists_isFinFS_net_gt h hθ

/-- **Regularization in a fixed class**: if `θ ∈ ℚ^r` has positive coordinates, every
`u ∈ PSH(𝒳, θ)` is the limit of a decreasing net in `𝓗_fin(𝒳, θ)`. -/
theorem IsPSH.exists_isFinFS_net_of_pos {θ : Fin r → ℚ} (hθ : ∀ c, 0 < θ c)
    (h : X.IsPSH (fun c => (θ c : ℝ)) u) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (f : ι → X.an → EReal), (∀ i, X.IsFinFS θ (f i)) ∧ (∀ v, Antitone fun i => f i v) ∧
        ∀ v, u v = ⨅ i, f i v :=
  FSSystemC.IsPSH.exists_isFinFS_net_of_pos hθ h

/-- **Countable regularization** for countable `k` and `θ ∈ N(𝒳)`: decreasing sequences
`f_m ∈ 𝓗_fin(𝒳, a_m)`, `a_m > θ`, `a_m → θ`. -/
theorem IsPSH.exists_isFinFS_seq_gt [Countable k] (h : X.IsPSH θ u) (hθ : θ ∈ X.nefCone) :
    ∃ (a : ℕ → Fin r → ℚ) (f : ℕ → X.an → EReal), (∀ m, X.IsFinFS (a m) (f m)) ∧
      (∀ m c, θ c < a m c) ∧ Tendsto (fun m c => (a m c : ℝ)) atTop (𝓝 θ) ∧
        (∀ v, Antitone fun m => f m v) ∧ ∀ v, u v = ⨅ m, f m v :=
  FSSystemC.IsPSH.exists_isFinFS_seq_gt h hθ

/-- **Countable regularization in a fixed class** for countable `k`: if `θ ∈ ℚ^r` has positive
coordinates, every `u ∈ PSH(𝒳, θ)` is the limit of a decreasing sequence in `𝓗_fin(𝒳, θ)`. -/
theorem IsPSH.exists_isFinFS_seq_of_pos [Countable k] {θ : Fin r → ℚ} (hθ : ∀ c, 0 < θ c)
    (h : X.IsPSH (fun c => (θ c : ℝ)) u) :
    ∃ f : ℕ → X.an → EReal, (∀ m, X.IsFinFS θ (f m)) ∧ (∀ v, Antitone fun m => f m v) ∧
      ∀ v, u v = ⨅ m, f m v :=
  FSSystemC.IsPSH.exists_isFinFS_seq_of_pos hθ h

/-! ### The envelope property (`lem:gl-ep-basic`) -/

/-- **`lem:gl-ep-basic`(1)**: if `θ ∈ N(𝒳)` is the limit of classes `θⱼ ≥ θ` with the envelope
property, then `θ` has the envelope property. -/
theorem HasEnvelopeProperty.of_tendsto (hθ : θ ∈ X.nefCone) {θs : ℕ → Fin r → ℝ}
    (hθs : Tendsto θs atTop (𝓝 θ)) (hle : ∀ j, θ ≤ θs j)
    (h : ∀ j, X.HasEnvelopeProperty (θs j)) : X.HasEnvelopeProperty θ :=
  FSSystemC.HasEnvelopeProperty.of_tendsto hθ hθs hle h

/-- **`lem:gl-ep-basic`(1)**, rational form: if `θ ∈ N(𝒳)` and every rational `a > θ` has the
envelope property, so has `θ`. -/
theorem hasEnvelopeProperty_of_forall_rat_gt (hθ : θ ∈ X.nefCone)
    (h : ∀ a : Fin r → ℚ, (∀ c, θ c < a c) → X.HasEnvelopeProperty fun c => (a c : ℝ)) :
    X.HasEnvelopeProperty θ :=
  FSSystemC.hasEnvelopeProperty_of_forall_rat_gt hθ h

/-- **`lem:gl-ep-basic`(2)**: for `θ ∈ N(𝒳)` and real `t > 0`, `EP_𝒳(θ) ↔ EP_𝒳(t θ)`. -/
theorem hasEnvelopeProperty_smul_iff (hθ : θ ∈ X.nefCone) {t : ℝ} (ht : 0 < t) :
    X.HasEnvelopeProperty (t • θ) ↔ X.HasEnvelopeProperty θ :=
  FSSystemC.hasEnvelopeProperty_smul_iff hθ ht

/-- **`lem:gl-ep-basic`(3)**: if `PSH(𝒳, θ) = ∅`, then `EP_𝒳(θ)` holds. -/
theorem hasEnvelopeProperty_of_forall_not_isPSH (h : ∀ u, ¬X.IsPSH θ u) :
    X.HasEnvelopeProperty θ :=
  FSSystemC.hasEnvelopeProperty_of_forall_not_isPSH h

end MultiModel

end EnvelopeProperty
