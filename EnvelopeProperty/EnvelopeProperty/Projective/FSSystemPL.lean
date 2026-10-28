/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.FSSystemEnvelope
import EnvelopeProperty.Projective.SubvarietyPSH

/-!
# PL functions, the envelope criterion and the reduction theorem in Fubini–Study systems

For a Fubini–Study system `F` of rank `r` on a compact space `(K, ⋆)`
(`EnvelopeProperty.FSSystem`, `def:pg-fs-system`), this file proves the remaining results of the
blueprint section `subsec:sg-envelopes` of `smooth-general.tex`, used in the proof of
Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX), Theorem 3.1
(`thm:smooth-EP`) for smooth projective varieties: the density of PL functions (Boucksom–Jonsson,
*Global pluripotential theory over a trivially valued field* (BJ22), `lem:FSdense`,
`thm:PLdense`), the envelope criterion (BJ addendum arXiv:2206.07183v2 `lem:contenv`, FHX
`prop:ample-envelopes`) and the reduction of the envelope property to integral classes and
nonpositive PL obstacles (FHX §3, *Reduction*, with BJ22 `lem:envppty`). The proofs are those of
the `ℙⁿ` templates `EnvelopeProperty.Projective.PLDensity` and
`EnvelopeProperty.Projective.EnvelopeCriterion`. Finally everything is specialized to the rank-one
system `ProjSubvariety.fsSystem` of a projective subvariety `X = V(I) ⊆ ℙᴹ`.

## Main definitions

* `FSSystem.IsPL F f` (`def:sg-ep`): `f = φ - ψ` with `φ ∈ 𝓗_fin(a)`, `ψ ∈ 𝓗_fin(b)`,
  `a, b ∈ ℚ^r_{≥0}`; `FSSystem.plSubmodule F`, the `ℚ`-vector space `PL(K)`.
* `ProjSubvariety.envelope X θ`, `ProjSubvariety.HasEnvelopeProperty X θ`,
  `ProjSubvariety.IsPL X`: the envelope, the envelope property and `PL(X)` for the rank-one
  system `X.fsSystem` (`def:sg-ep`, classes `θ c₁(O_X(1))`, `θ ∈ ℝ`).

## Main results

* `lem:sg-pl`(1): `FSSystem.IsPL.continuous`, `FSSystem.isPL_const`, `FSSystem.IsPL.add`,
  `FSSystem.IsPL.neg`, `FSSystem.IsPL.smul`, `FSSystem.IsPL.max`, `FSSystem.IsPL.min`,
  `FSSystem.plSubmodule`.
* `lem:sg-pl`(2): `FSSystem.exists_isPL_abs_sub_lt`, `FSSystem.dense_setOf_isPL` (lattice
  Stone–Weierstrass, `ContinuousMap.sublattice_closure_eq_top`).
* `lem:sg-pl`(3): `FSSystem.exists_isPL_gt`, `FSSystem.directedOn_isPL_gt`,
  `FSSystem.iInf_isPL_gt`, with `FSSystem.exists_isPL_gt_apply_lt`,
  `FSSystem.exists_antitone_isPL_net`, `FSSystem.le_of_forall_isPL_gt` (Urysohn's lemma).
* `prop:sg-envelope-criterion`: `FSSystem.hasEnvelopeProperty_of_forall_isPL`, and the
  equivalence `FSSystem.hasEnvelopeProperty_iff_forall_isPL` for `θ ≥ 0`.
* `thm:sg-reduction`: `FSSystem.hasEnvelopeProperty_of_forall_nat`.
* Rank one: `ProjSubvariety.envelope_add_const`, `ProjSubvariety.envelope_mul`,
  `ProjSubvariety.iInf_le_envelope`, `ProjSubvariety.HasEnvelopeProperty.of_tendsto`,
  `ProjSubvariety.hasEnvelopeProperty_of_forall_rat_gt`,
  `ProjSubvariety.envelope_eq_iSup_isFinFS`, `ProjSubvariety.isPL_iff`,
  `ProjSubvariety.hasEnvelopeProperty_of_forall_isPL`,
  `ProjSubvariety.hasEnvelopeProperty_iff_forall_isPL`,
  `ProjSubvariety.hasEnvelopeProperty_of_forall_nat`.

## The separation hypothesis

Density (`lem:sg-pl`(2),(3)), the envelope criterion and the reduction theorem assume, as in the
blueprint, that `PL(K)` separates the points of `K`, in Mathlib's form
`{f : K → ℝ | F.IsPL f}.SeparatesPoints`. For `X^an` this is `lem:sg-pl-separate`, which is not
proved here; the rank-one theorems take it as the hypothesis
`hsep : {f : X.an → ℝ | X.IsPL f}.SeparatesPoints`.

## Deviations from the blueprint

* The blueprint's standing assumption "`K` Hausdorff" is not needed: separation of points by the
  continuous PL functions makes `K` Hausdorff (`FSSystem.t2Space_of_separatesPoints`), which is
  where Urysohn's lemma needs it.
* `prop:sg-envelope-criterion` does not need `θ ≥ 0` (only its converse,
  `FSSystem.hasEnvelopeProperty_iff_forall_isPL`, does).
* `lem:sg-pl`(3) is stated for usc `h : K → [-∞, +∞)`, i.e. `h` usc with `h ≠ +∞` everywhere.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

/-- A vector `a ∈ ℚ^r` with positive coordinates has a positive integral multiple `m a ∈ ℕ^r`,
with positive coordinates (take `m` the product of the denominators). -/
theorem exists_nat_mul_rat_vec_eq_nat {r : ℕ} {a : Fin r → ℚ} (ha : ∀ c, 0 < a c) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : Fin r → ℕ, (∀ c, 0 < b c) ∧ ∀ c, (b c : ℚ) = m * a c := by
  have hm : 0 < ∏ c, (a c).den := Finset.prod_pos fun c _ => (a c).den_pos
  refine ⟨∏ c, (a c).den, hm, ?_⟩
  have key : ∀ c, ∃ z : ℕ, 0 < z ∧ (z : ℚ) = ((∏ c, (a c).den : ℕ) : ℚ) * a c := by
    intro c
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun c => (a c).den) (Finset.mem_univ c)
    have hnum : 0 < (a c).num := Rat.num_pos.2 (ha c)
    have heq : (((k * (a c).num.toNat : ℕ) : ℚ)) = ((∏ c, (a c).den : ℕ) : ℚ) * a c := by
      rw [hk]
      have h1 : (((a c).num.toNat : ℕ) : ℚ) = ((a c).num : ℚ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum.le]
      push_cast
      rw [h1, ← Rat.mul_den_eq_num]
      ring
    refine ⟨k * (a c).num.toNat, ?_, heq⟩
    have : (0 : ℚ) < ((k * (a c).num.toNat : ℕ) : ℚ) := by
      rw [heq]
      exact mul_pos (by exact_mod_cast hm) (ha c)
    exact_mod_cast this
  choose b hb hbm using key
  exact ⟨b, hb, hbm⟩

namespace FSSystem

universe u

variable {K : Type u} [TopologicalSpace K] {r : ℕ} (F : FSSystem K r)

/-! ### PL functions (`def:sg-ep`, `lem:sg-pl`(1)) -/

/-- **PL functions** of a Fubini–Study system (`def:sg-ep`; BJ22 §2): the real functions
`f = φ - ψ` with `φ ∈ 𝓗_fin(a)`, `ψ ∈ 𝓗_fin(b)` for some `a, b ∈ ℚ^r` (necessarily `≥ 0`). -/
def IsPL (f : K → ℝ) : Prop :=
  ∃ (a b : Fin r → ℚ) (φ ψ : K → EReal), F.IsFinFS a φ ∧ F.IsFinFS b ψ ∧
    ∀ x, f x = (φ x).toReal - (ψ x).toReal

variable {F} {a : Fin r → ℚ} {φ : K → EReal} {f g : K → ℝ} {θ : Fin r → ℝ}

/-- A finite Fubini–Study function is the coercion of its real part. -/
theorem IsFinFS.coe_toReal (h : F.IsFinFS a φ) (x : K) : ((φ x).toReal : EReal) = φ x :=
  EReal.coe_toReal (h.ne_top x) (h.ne_bot x)

theorem IsFinFS.continuous_toReal (h : F.IsFinFS a φ) : Continuous fun x => (φ x).toReal :=
  EReal.continuousOn_toReal.comp_continuous h.continuous fun x => by
    simp [h.ne_bot x, h.ne_top x]

/-- Finite Fubini–Study functions are PL functions. -/
theorem IsFinFS.isPL (h : F.IsFinFS a φ) : F.IsPL fun x => (φ x).toReal :=
  ⟨a, 0, φ, _, h, F.isFinFS_const le_rfl 0, fun x => by simp⟩

variable (F) in
/-- Rational constants are PL functions (`lem:sg-pl`(1)). -/
theorem isPL_const (c : ℚ) : F.IsPL fun _ => (c : ℝ) :=
  ⟨0, 0, _, _, F.isFinFS_const le_rfl c, F.isFinFS_const le_rfl 0, fun x => by simp⟩

variable (F) in
/-- The zero function is PL. -/
theorem isPL_zero : F.IsPL 0 := by
  have h := isPL_const F 0
  simp only [Rat.cast_zero] at h
  exact h

/-- PL functions are continuous (`lem:sg-pl`(1)). -/
theorem IsPL.continuous (hf : F.IsPL f) : Continuous f := by
  obtain ⟨a, b, φ, ψ, hφ, hψ, hf⟩ := hf
  rw [show f = fun x => (φ x).toReal - (ψ x).toReal from funext hf]
  exact hφ.continuous_toReal.sub hψ.continuous_toReal

/-- Sums of PL functions (`lem:sg-pl`(1), FS4). -/
theorem IsPL.add (hf : F.IsPL f) (hg : F.IsPL g) : F.IsPL fun x => f x + g x := by
  obtain ⟨a, b, φ, ψ, hφ, hψ, hf⟩ := hf
  obtain ⟨a', b', φ', ψ', hφ', hψ', hg⟩ := hg
  refine ⟨a + a', b + b', _, _, hφ.add hφ', hψ.add hψ', fun x => ?_⟩
  dsimp only
  rw [hf, hg, EReal.toReal_add (hφ.ne_top x) (hφ.ne_bot x) (hφ'.ne_top x) (hφ'.ne_bot x),
    EReal.toReal_add (hψ.ne_top x) (hψ.ne_bot x) (hψ'.ne_top x) (hψ'.ne_bot x)]
  ring

/-- Negatives of PL functions (`lem:sg-pl`(1)). -/
theorem IsPL.neg (hf : F.IsPL f) : F.IsPL fun x => -f x := by
  obtain ⟨a, b, φ, ψ, hφ, hψ, hf⟩ := hf
  exact ⟨b, a, ψ, φ, hψ, hφ, fun x => by dsimp only; rw [hf]; ring⟩

theorem IsPL.sub (hf : F.IsPL f) (hg : F.IsPL g) : F.IsPL fun x => f x - g x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem IsPL.smul_of_pos (hf : F.IsPL f) {c : ℚ} (hc : 0 < c) :
    F.IsPL fun x => (c : ℝ) * f x := by
  obtain ⟨a, b, φ, ψ, hφ, hψ, hf⟩ := hf
  refine ⟨c • a, c • b, _, _, hφ.smul hc, hψ.smul hc, fun x => ?_⟩
  dsimp only
  rw [hf, EReal.toReal_mul, EReal.toReal_mul, EReal.toReal_coe]
  ring

/-- Rational multiples of PL functions (`lem:sg-pl`(1), FS4). -/
theorem IsPL.smul (hf : F.IsPL f) (c : ℚ) : F.IsPL fun x => (c : ℝ) * f x := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have h := (hf.smul_of_pos (neg_pos.2 hc)).neg
    simpa only [Rat.cast_neg, neg_mul, neg_neg] using h
  · simpa using isPL_const F 0
  · exact hf.smul_of_pos hc

theorem IsPL.add_const (hf : F.IsPL f) (c : ℚ) : F.IsPL fun x => f x + (c : ℝ) :=
  hf.add (isPL_const F c)

/-- **Maxima of PL functions** (`lem:sg-pl`(1)):
`max(φ₁ - ψ₁, φ₂ - ψ₂) = max(φ₁ + ψ₂, φ₂ + ψ₁) - (ψ₁ + ψ₂)`, the two functions in the maximum
being moved into the class of the coordinatewise maximum by (FS2), and maxima taken by (FS3). -/
theorem IsPL.max (hf : F.IsPL f) (hg : F.IsPL g) : F.IsPL fun x => Max.max (f x) (g x) := by
  obtain ⟨a, b, φ, ψ, hφ, hψ, hf⟩ := hf
  obtain ⟨a', b', φ', ψ', hφ', hψ', hg⟩ := hg
  have h₁ := (hφ.add hψ').mono (le_sup_left : a + b' ≤ (a + b') ⊔ (a' + b))
  have h₂ := (hφ'.add hψ).mono (le_sup_right : a' + b ≤ (a + b') ⊔ (a' + b))
  refine ⟨_, _, _, _, h₁.max h₂, hψ.add hψ', fun x => ?_⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, φ x = A := ⟨_, (hφ.coe_toReal x).symm⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ψ x = B := ⟨_, (hψ.coe_toReal x).symm⟩
  obtain ⟨A', hA'⟩ : ∃ A' : ℝ, φ' x = A' := ⟨_, (hφ'.coe_toReal x).symm⟩
  obtain ⟨B', hB'⟩ : ∃ B' : ℝ, ψ' x = B' := ⟨_, (hψ'.coe_toReal x).symm⟩
  dsimp only
  rw [hf, hg, hA, hB, hA', hB', ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add,
    ← ProjBerk.ereal_coe_max, EReal.toReal_coe, EReal.toReal_coe, EReal.toReal_coe,
    EReal.toReal_coe, EReal.toReal_coe, EReal.toReal_coe, ← max_sub_sub_right]
  congr 1 <;> ring

/-- Minima of PL functions (`lem:sg-pl`(1)). -/
theorem IsPL.min (hf : F.IsPL f) (hg : F.IsPL g) : F.IsPL fun x => Min.min (f x) (g x) := by
  simpa only [max_neg_neg, neg_neg] using (hf.neg.max hg.neg).neg

variable (F) in
/-- **`PL(K)` is a `ℚ`-vector space** (`lem:sg-pl`(1)): the `ℚ`-submodule of `K → ℝ` of PL
functions. -/
def plSubmodule : Submodule ℚ (K → ℝ) where
  carrier := {f | F.IsPL f}
  add_mem' hf hg := IsPL.add hf hg
  zero_mem' := isPL_zero F
  smul_mem' c f hf := by
    have h := IsPL.smul hf c
    have e : c • f = fun x => (c : ℝ) * f x := funext fun x => by
      simp only [Pi.smul_apply, Rat.smul_def]
    show F.IsPL (c • f)
    rw [e]
    exact h

theorem mem_plSubmodule : f ∈ F.plSubmodule ↔ F.IsPL f :=
  Iff.rfl

/-- If PL functions separate the points of `K`, then `K` is Hausdorff: they are continuous. -/
theorem t2Space_of_separatesPoints (hsep : {f : K → ℝ | F.IsPL f}.SeparatesPoints) :
    T2Space K :=
  ⟨fun _ _ hxy => by
    obtain ⟨f, hf, hne⟩ := hsep hxy
    exact separated_by_continuous (show F.IsPL f from hf).continuous hne⟩

/-! ### Density of PL functions (`lem:sg-pl`(2)) -/

/-- **Density of PL functions** (`lem:sg-pl`(2); BJ22 `thm:PLdense`): if PL functions separate
the points of the compact space `K`, every continuous function on `K` is a uniform limit of PL
functions. The uniform closure `L` of the PL functions is a lattice containing the real
constants which separates points strongly (if `ψ` is PL with `ψ(x) ≠ ψ(y)`, the functions
`α ψ + β ∈ L` take arbitrary values at `x` and `y`); the lattice Stone–Weierstrass theorem gives
`closure L = C⁰(K)`. -/
theorem exists_isPL_abs_sub_lt [CompactSpace K] (hsep : {f : K → ℝ | F.IsPL f}.SeparatesPoints)
    {f : K → ℝ} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ, F.IsPL ψ ∧ ∀ x, |f x - ψ x| < ε := by
  set L : Set C(K, ℝ) := {g | ∀ ε : ℝ, 0 < ε → ∃ ψ, F.IsPL ψ ∧ ∀ x, |g x - ψ x| < ε} with hL
  -- real constants lie in `L`
  have hconst : ∀ c : ℝ, ContinuousMap.const K c ∈ L := by
    intro c ε hε
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show c - ε < c + ε by linarith)
    refine ⟨fun _ => (q : ℝ), isPL_const F q, fun x => ?_⟩
    rw [ContinuousMap.const_apply, abs_lt]
    constructor <;> linarith
  have hinf : ∀ g ∈ L, ∀ g' ∈ L, g ⊓ g' ∈ L := by
    intro g hg g' hg' ε hε
    obtain ⟨ψ, hψ, hgψ⟩ := hg ε hε
    obtain ⟨ψ', hψ', hgψ'⟩ := hg' ε hε
    refine ⟨_, hψ.min hψ', fun x => ?_⟩
    rw [ContinuousMap.inf_apply]
    exact (abs_min_sub_min_le_max _ _ _ _).trans_lt (max_lt (hgψ x) (hgψ' x))
  have hsup : ∀ g ∈ L, ∀ g' ∈ L, g ⊔ g' ∈ L := by
    intro g hg g' hg' ε hε
    obtain ⟨ψ, hψ, hgψ⟩ := hg ε hε
    obtain ⟨ψ', hψ', hgψ'⟩ := hg' ε hε
    refine ⟨_, hψ.max hψ', fun x => ?_⟩
    rw [ContinuousMap.sup_apply]
    exact (abs_max_sub_max_le_max _ _ _ _).trans_lt (max_lt (hgψ x) (hgψ' x))
  have hsep' : L.SeparatesPointsStrongly := by
    intro w x y
    by_cases hxy : x = y
    · subst hxy
      exact ⟨ContinuousMap.const _ (w x), hconst _, rfl, rfl⟩
    obtain ⟨ψ, hψ, hne⟩ := hsep hxy
    have hψ : F.IsPL ψ := hψ
    have hd : ψ x - ψ y ≠ 0 := sub_ne_zero.2 hne
    set α : ℝ := (w x - w y) / (ψ x - ψ y) with hα
    set β : ℝ := w x - α * ψ x with hβ
    refine ⟨⟨fun z => α * ψ z + β, (continuous_const.mul hψ.continuous).add continuous_const⟩,
      ?_, ?_, ?_⟩
    · intro ε hε
      obtain ⟨C, hC⟩ := exists_abs_le_of_continuous hψ.continuous
      have hC1 : 0 < |C| + 1 := by positivity
      have hδ : 0 < ε / (2 * (|C| + 1)) := by positivity
      obtain ⟨q, hq₁, hq₂⟩ :=
        exists_rat_btwn (show α - ε / (2 * (|C| + 1)) < α + ε / (2 * (|C| + 1)) by linarith)
      obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn (show β - ε / 2 < β + ε / 2 by linarith)
      refine ⟨fun z => (q : ℝ) * ψ z + (r : ℝ), (hψ.smul q).add (isPL_const F r), fun z => ?_⟩
      have hαq : |α - q| ≤ ε / (2 * (|C| + 1)) := abs_le.2 ⟨by linarith, by linarith⟩
      have hβr : |β - r| < ε / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
      have hψz : |ψ z| ≤ |C| + 1 := (hC z).trans ((le_abs_self C).trans (by linarith))
      change |α * ψ z + β - ((q : ℝ) * ψ z + (r : ℝ))| < ε
      calc |α * ψ z + β - ((q : ℝ) * ψ z + (r : ℝ))| = |(α - q) * ψ z + (β - r)| := by ring_nf
        _ ≤ |α - q| * |ψ z| + |β - r| := by
          rw [← abs_mul]; exact abs_add_le _ _
        _ < ε / (2 * (|C| + 1)) * (|C| + 1) + ε / 2 := by
          refine add_lt_add_of_le_of_lt ?_ hβr
          exact mul_le_mul hαq hψz (abs_nonneg _) hδ.le
        _ = ε := by field_simp; ring
    · change α * ψ x + β = w x
      rw [hβ]; ring
    · change α * ψ y + β = w y
      have : α * (ψ x - ψ y) = w x - w y := by rw [hα]; field_simp
      rw [hβ]; linarith
  have hclosure := ContinuousMap.sublattice_closure_eq_top L ⟨_, hconst 0⟩ hinf hsup hsep'
  have hfL : (⟨f, hf⟩ : C(K, ℝ)) ∈ closure L := by rw [hclosure]; trivial
  obtain ⟨g, hgL, hfg⟩ := Metric.mem_closure_iff.1 hfL (ε / 2) (half_pos hε)
  obtain ⟨ψ, hψ, hgψ⟩ := hgL (ε / 2) (half_pos hε)
  rw [ContinuousMap.dist_lt_iff (half_pos hε)] at hfg
  refine ⟨ψ, hψ, fun x => ?_⟩
  have h₁ : |f x - g x| < ε / 2 := by
    have := hfg x
    rwa [Real.dist_eq] at this
  calc |f x - ψ x| ≤ |f x - g x| + |g x - ψ x| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h₁ (hgψ x)
    _ = ε := add_halves ε

/-- **Density of PL functions** (`lem:sg-pl`(2)), topological form: if PL functions separate
points, they are dense in `C(K, ℝ)` for the topology of uniform convergence. -/
theorem dense_setOf_isPL [CompactSpace K] (hsep : {f : K → ℝ | F.IsPL f}.SeparatesPoints) :
    Dense {f : C(K, ℝ) | F.IsPL f} := by
  refine fun f => Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨ψ, hψ, hfψ⟩ := exists_isPL_abs_sub_lt hsep f.continuous (half_pos hε)
  refine ⟨⟨ψ, hψ.continuous⟩, hψ, ?_⟩
  refine lt_of_le_of_lt ((ContinuousMap.dist_le (half_pos hε).le).2 fun x => ?_) (half_lt_self hε)
  rw [Real.dist_eq]
  exact (hfψ x).le

/-! ### Approximation of usc functions from above (`lem:sg-pl`(3)) -/

/-- `lem:sg-pl`(3), nonemptiness: a usc function `h : K → [-∞, +∞)` on a compact `K` lies below
a PL function, indeed below a rational constant (`h` attains its maximum). -/
theorem exists_isPL_gt [CompactSpace K] {h : K → EReal} (hh : UpperSemicontinuous h)
    (htop : ∀ x, h x ≠ ⊤) : ∃ ψ, F.IsPL ψ ∧ ∀ x, h x < ψ x := by
  obtain ⟨a, -, ha⟩ := UpperSemicontinuousOn.exists_isMaxOn ⟨F.triv, mem_univ _⟩ isCompact_univ
    (hh.upperSemicontinuousOn univ)
  obtain ⟨r, hr, -⟩ := EReal.lt_iff_exists_real_btwn.1 (lt_top_iff_ne_top.2 (htop a))
  obtain ⟨q, hq⟩ := exists_rat_gt r
  refine ⟨fun _ => (q : ℝ), isPL_const F q, fun x => ?_⟩
  exact ((isMaxOn_iff.1 ha x (mem_univ x)).trans_lt hr).trans (EReal.coe_lt_coe_iff.2 hq)

/-- `lem:sg-pl`(3), directedness: the PL functions `ψ > h` form a downward directed family
(`FSSystem.IsPL.min`). -/
theorem directedOn_isPL_gt (h : K → EReal) :
    DirectedOn (· ≥ ·) {ψ : K → ℝ | F.IsPL ψ ∧ ∀ x, h x < ψ x} := by
  rintro ψ ⟨hψ, hψh⟩ ψ' ⟨hψ', hψ'h⟩
  refine ⟨fun x => Min.min (ψ x) (ψ' x), ⟨hψ.min hψ', fun x => ?_⟩, fun x => min_le_left _ _,
    fun x => min_le_right _ _⟩
  rw [ProjBerk.ereal_coe_min]
  exact lt_min (hψh x) (hψ'h x)

/-- `lem:sg-pl`(3), the infimum: if PL functions separate points, `h : K → [-∞, +∞)` is usc and
`h(x) < c`, there is a PL function `ψ > h` with `ψ(x) < c`. With reals `h(x) < r < r + 3δ < c`,
Urysohn's lemma gives a continuous `g ≥ r` with `g > h` and `g(x) = r` (equal to a large constant
on the closed set `{h ≥ r}`), and a PL function uniformly `δ`-close to `g + 2δ` works. -/
theorem exists_isPL_gt_apply_lt [CompactSpace K]
    (hsep : {f : K → ℝ | F.IsPL f}.SeparatesPoints) {h : K → EReal}
    (hh : UpperSemicontinuous h) (htop : ∀ x, h x ≠ ⊤) {x : K} {c : EReal} (hc : h x < c) :
    ∃ ψ, F.IsPL ψ ∧ (∀ w, h w < ψ w) ∧ (ψ x : EReal) < c := by
  have : T2Space K := t2Space_of_separatesPoints hsep
  obtain ⟨r₁, hr₁, hr₁c⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  obtain ⟨r, hr, hrr₁⟩ := EReal.lt_iff_exists_real_btwn.1 hr₁
  have hrr₁' : r < r₁ := EReal.coe_lt_coe_iff.1 hrr₁
  set δ : ℝ := (r₁ - r) / 3 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  -- a real upper bound `C ≥ r` of `h`
  obtain ⟨ψ₀, hψ₀, hgt₀⟩ := exists_isPL_gt (F := F) hh htop
  obtain ⟨C₀, hC₀⟩ := exists_abs_le_of_continuous hψ₀.continuous
  set C : ℝ := Max.max C₀ r with hC_def
  have hhC : ∀ w, h w < C := fun w =>
    (hgt₀ w).trans_le (EReal.coe_le_coe_iff.2 (((le_abs_self _).trans (hC₀ w)).trans
      (le_max_left _ _)))
  have hrC : r ≤ C := le_max_right _ _
  -- Urysohn's lemma for `{x}` and the closed set `G = {h ≥ r}`
  set G : Set K := {w | (r : EReal) ≤ h w} with hG_def
  have hG : IsClosed G := by
    have h₁ : G = (h ⁻¹' Iio (r : EReal))ᶜ := by
      ext w; simp [hG_def, not_lt]
    rw [h₁]
    exact (hh.isOpen_preimage _).isClosed_compl
  have hxG : Disjoint {x} G := by
    rw [disjoint_singleton_left]
    exact not_le.2 hr
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed isClosed_singleton hG hxG
  set g : K → ℝ := fun w => r + (C + 1 - r) * f w with hg_def
  have hgc : Continuous g := by fun_prop
  have hfx : f x = 0 := hf0 (mem_singleton x)
  obtain ⟨ψ, hψ, hψg⟩ := exists_isPL_abs_sub_lt hsep (f := fun w => g w + 2 * δ)
    (hgc.add continuous_const) hδ
  refine ⟨ψ, hψ, fun w => ?_, ?_⟩
  · have h₁ : g w + δ < ψ w := by have := abs_lt.1 (hψg w); linarith
    have h₂ : h w < g w := by
      by_cases hw : w ∈ G
      · have : f w = 1 := hf1 hw
        refine (hhC w).trans (EReal.coe_lt_coe_iff.2 ?_)
        rw [hg_def]; dsimp only; rw [this]; linarith
      · have h₃ : h w < r := not_le.1 hw
        refine h₃.trans_le (EReal.coe_le_coe_iff.2 ?_)
        rw [hg_def]; dsimp only
        have := (hf01 w).1
        nlinarith
    exact h₂.trans (EReal.coe_lt_coe_iff.2 (by linarith))
  · have h₁ : ψ x < g x + 3 * δ := by have := abs_lt.1 (hψg x); linarith
    have h₂ : g x + 3 * δ = r₁ := by rw [hg_def]; dsimp only; rw [hfx, hδ_def]; ring
    exact (EReal.coe_lt_coe_iff.2 (h₁.trans_eq h₂)).trans hr₁c

/-- **Approximation of usc functions from above** (`lem:sg-pl`(3); BJ addendum, proof of
`lem:contenv`): if PL functions separate points, a usc function `h : K → [-∞, +∞)` is the
pointwise infimum of the PL functions `ψ > h`. -/
theorem iInf_isPL_gt [CompactSpace K] (hsep : {f : K → ℝ | F.IsPL f}.SeparatesPoints)
    {h : K → EReal} (hh : UpperSemicontinuous h) (htop : ∀ x, h x ≠ ⊤) (x : K) :
    ⨅ (ψ : K → ℝ) (_ : F.IsPL ψ ∧ ∀ w, h w < ψ w), (ψ x : EReal) = h x := by
  refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun c hc => ?_)
    (le_iInf₂ fun ψ hψ => (hψ.2 x).le)
  obtain ⟨ψ, hψ, hgt, hlt⟩ := exists_isPL_gt_apply_lt hsep hh htop hc
  exact (iInf₂_le ψ ⟨hψ, hgt⟩).trans hlt.le

/-- `lem:sg-pl`(3) as a decreasing net: if PL functions separate points, a usc function
`h : K → [-∞, +∞)` is the limit of a decreasing net of PL functions `ψᵢ > h`, indexed by the set
of all such functions ordered by reverse pointwise order. -/
theorem exists_antitone_isPL_net [CompactSpace K]
    (hsep : {f : K → ℝ | F.IsPL f}.SeparatesPoints) {h : K → EReal}
    (hh : UpperSemicontinuous h) (htop : ∀ x, h x ≠ ⊤) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (ψ : ι → K → ℝ), (∀ i, F.IsPL (ψ i)) ∧ (∀ i w, h w < ψ i w) ∧
        (∀ w, Antitone fun i => ψ i w) ∧ ∀ w, h w = ⨅ i, (ψ i w : EReal) := by
  let ι := {ψ : K → ℝ // F.IsPL ψ ∧ ∀ w, h w < ψ w}ᵒᵈ
  have : IsDirected ι (· ≤ ·) := ⟨fun i j => ⟨OrderDual.toDual
    ⟨fun w => Min.min ((OrderDual.ofDual i).1 w) ((OrderDual.ofDual j).1 w),
      (OrderDual.ofDual i).2.1.min (OrderDual.ofDual j).2.1, fun w => by
        rw [ProjBerk.ereal_coe_min]
        exact lt_min ((OrderDual.ofDual i).2.2 w) ((OrderDual.ofDual j).2.2 w)⟩,
    fun w => min_le_left _ _, fun w => min_le_right _ _⟩⟩
  have : Nonempty ι := by
    obtain ⟨ψ, hψ⟩ := exists_isPL_gt (F := F) hh htop
    exact ⟨OrderDual.toDual ⟨ψ, hψ⟩⟩
  refine ⟨ι, inferInstance, inferInstance, inferInstance, fun i => (OrderDual.ofDual i).1,
    fun i => (OrderDual.ofDual i).2.1, fun i => (OrderDual.ofDual i).2.2,
    fun w i j hij => hij w, fun w => ?_⟩
  exact (iInf_isPL_gt hsep hh htop w).symm.trans iInf_subtype'

/-- **Comparison with usc functions** (`lem:sg-pl`(3)): if PL functions separate points and
`u ≤ ψ` for every PL function `ψ > h`, where `h : K → [-∞, +∞)` is usc, then `u ≤ h`. -/
theorem le_of_forall_isPL_gt [CompactSpace K] (hsep : {f : K → ℝ | F.IsPL f}.SeparatesPoints)
    {h u : K → EReal} (hh : UpperSemicontinuous h) (htop : ∀ x, h x ≠ ⊤)
    (hu : ∀ ψ, F.IsPL ψ → (∀ w, h w < ψ w) → ∀ x, u x ≤ ψ x) : u ≤ h :=
  fun x => (iInf_isPL_gt hsep hh htop x) ▸ le_iInf₂ fun ψ hψ => hu ψ hψ.1 hψ.2 x

/-! ### The envelope criterion (`prop:sg-envelope-criterion`) -/

/-- **Envelope property via PL obstacles** (`prop:sg-envelope-criterion`; BJ addendum
`lem:contenv`, FHX `prop:ample-envelopes`): if PL functions separate the points of the compact
space `K` and `P_θ(ψ)` is `θ`-psh for every PL function `ψ`, then `θ` has the envelope property.
For a nonempty bounded-above family `S ⊆ PSH(θ)` and `h = (sup S)^⋆`, every PL function `ψ > h`
satisfies `h ≤ P_θ(ψ) ≤ ψ` (as `P_θ(ψ)` is usc), so by `lem:sg-pl`(3) the `P_θ(ψ)` form a
decreasing net of `θ`-psh functions with limit `h`, and PSH2 (`thm:pg-psh2`(3)) applies. -/
theorem hasEnvelopeProperty_of_forall_isPL [CompactSpace K]
    (hsep : {f : K → ℝ | F.IsPL f}.SeparatesPoints)
    (hPL : ∀ φ : K → ℝ, F.IsPL φ → F.IsPSH θ (F.envelope θ fun x => (φ x : EReal))) :
    F.HasEnvelopeProperty θ := by
  intro S hSne hS hbdd
  obtain ⟨C, hC⟩ := hbdd
  have hle : ∀ u ∈ S, ∀ x, u x ≤ uscReg (fun x => ⨆ u ∈ S, u x) x := fun u hu x =>
    (le_iSup₂ (f := fun (w : K → EReal) (_ : w ∈ S) => w x) u hu).trans
      (le_uscReg (fun x => ⨆ u ∈ S, u x) x)
  set h := uscReg fun x => ⨆ u ∈ S, u x with h_def
  have hhC : ∀ x, h x ≤ C := uscReg_le_of_le (f := fun x => ⨆ u ∈ S, u x)
    (g := fun _ => (C : EReal)) continuous_const.upperSemicontinuous
    (fun x => iSup₂_le fun u hu => hC u hu x)
  have htop : ∀ x, h x ≠ ⊤ := fun x => ne_top_of_le_ne_top (EReal.coe_ne_top C) (hhC x)
  obtain ⟨ι, _, _, _, ψ, hψ, hgt, hanti, hinf⟩ :=
    exists_antitone_isPL_net hsep (upperSemicontinuous_uscReg _) htop
  -- `h ≤ P_θ(ψᵢ)` since `P_θ(ψᵢ)` is usc and dominates every member of `S`
  have hkey : ∀ i x, h x ≤ F.envelope θ (fun w => (ψ i w : EReal)) x := fun i =>
    uscReg_le_of_le (hPL _ (hψ i)).upperSemicontinuous fun x => iSup₂_le fun u hu =>
      le_envelope (hS u hu) (fun w => (hle u hu w).trans (hgt i w).le) x
  refine isPSH_of_antitone (θ := fun _ => θ) tendsto_const_nhds (fun i => hPL _ (hψ i))
    (fun x i j hij => envelope_mono (fun w => EReal.coe_le_coe_iff.2 (hanti w hij)) x)
    (fun x => le_antisymm (le_iInf fun i => hkey i x) ?_) ?_
  · exact (iInf_mono fun i => envelope_le F θ _ x).trans_eq (hinf x).symm
  · obtain ⟨u, hu⟩ := hSne
    obtain ⟨x, hx⟩ := (hS u hu).exists_ne_bot
    exact ⟨x, ne_bot_of_le_ne_bot hx (hle u hu x)⟩

/-- **The envelope criterion** (`prop:sg-envelope-criterion` with its converse): if PL functions
separate the points of the compact space `K` and `θ ≥ 0`, then `θ` has the envelope property iff
`P_θ(ψ)` is `θ`-psh for every PL function `ψ`. -/
theorem hasEnvelopeProperty_iff_forall_isPL [CompactSpace K]
    (hsep : {f : K → ℝ | F.IsPL f}.SeparatesPoints) (hθ : 0 ≤ θ) :
    F.HasEnvelopeProperty θ ↔
      ∀ φ : K → ℝ, F.IsPL φ → F.IsPSH θ (F.envelope θ fun x => (φ x : EReal)) :=
  ⟨fun h _ hφ => h.isPSH_envelope_of_continuous hθ hφ.continuous,
    hasEnvelopeProperty_of_forall_isPL hsep⟩

/-! ### Reduction to integral classes and nonpositive PL obstacles (`thm:sg-reduction`) -/

/-- **Reduction to integral classes and nonpositive PL obstacles** (`thm:sg-reduction`; FHX §3,
*Reduction*, with BJ22 `lem:envppty`): assume that PL functions separate the points of the
compact space `K` and that `P_a(φ)` is `a`-psh for every `a ∈ ℕ^r` with positive coordinates and
every PL function `φ ≤ 0`. Then every `θ ∈ ℝ^r` has the envelope property.

If `θ ≱ 0` the property is vacuous. Otherwise, by `lem:sg-envppty` it suffices to treat rational
classes `a > θ ≥ 0`, and by the envelope criterion to show `P_a(ψ) ∈ PSH(a)` for PL `ψ`. With
`m ∈ ℤ_{>0}` such that `m a ∈ ℕ^r` and a rational `c ≥ max m ψ`,
`m P_a(ψ) = P_{ma}(m ψ - c) + c` is `m a`-psh, so `P_a(ψ)` is `a`-psh. -/
theorem hasEnvelopeProperty_of_forall_nat [CompactSpace K]
    (hsep : {f : K → ℝ | F.IsPL f}.SeparatesPoints)
    (h : ∀ a : Fin r → ℕ, (∀ c, 0 < a c) → ∀ φ : K → ℝ, F.IsPL φ → (∀ x, φ x ≤ 0) →
      F.IsPSH (fun c => (a c : ℝ)) (F.envelope (fun c => (a c : ℝ)) fun x => (φ x : EReal)))
    (θ : Fin r → ℝ) : F.HasEnvelopeProperty θ := by
  by_cases hθ : 0 ≤ θ
  swap
  · exact hasEnvelopeProperty_of_not_nonneg hθ
  refine hasEnvelopeProperty_of_forall_rat_gt fun a hθa => ?_
  have ha : ∀ c, 0 < a c := fun c => by
    have h₁ := (hθ c).trans_lt (hθa c)
    simp only [Pi.zero_apply] at h₁
    exact_mod_cast h₁
  refine hasEnvelopeProperty_of_forall_isPL hsep fun ψ hψ => ?_
  obtain ⟨m, hm, b, hb, hbm⟩ := exists_nat_mul_rat_vec_eq_nat ha
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  -- a rational `c₀ > max m ψ`
  obtain ⟨C, hC⟩ := exists_abs_le_of_continuous hψ.continuous
  obtain ⟨c₀, hc₀⟩ := exists_rat_gt ((m : ℝ) * C)
  set χ : K → ℝ := fun x => (((m : ℚ) : ℝ)) * ψ x + ((-c₀ : ℚ) : ℝ) with hχ_def
  have hχ : F.IsPL χ := (hψ.smul m).add_const (-c₀)
  have hχ0 : ∀ x, χ x ≤ 0 := fun x => by
    have h₁ : ψ x ≤ C := (le_abs_self _).trans (hC x)
    have h₂ : (m : ℝ) * ψ x ≤ m * C := mul_le_mul_of_nonneg_left h₁ hm'.le
    simp only [hχ_def, Rat.cast_natCast, Rat.cast_neg]
    linarith
  have key := h b hb χ hχ hχ0
  -- the classes: `b = m • a`
  have hcls : (fun c => (b c : ℝ)) = (m : ℝ) • fun c => (a c : ℝ) := funext fun c => by
    have := hbm c
    simp only [Pi.smul_apply, smul_eq_mul]
    exact_mod_cast this
  -- the envelopes: `P_{ma}(m ψ - c₀) = m P_a(ψ) - c₀`
  have hχe : (fun x => (χ x : EReal)) =
      fun x => (fun x => ((m : ℝ) : EReal) * (ψ x : EReal)) x + ((-(c₀ : ℝ) : ℝ) : EReal) := by
    funext x
    simp only [hχ_def, Rat.cast_natCast, Rat.cast_neg, EReal.coe_add, EReal.coe_mul]
  rw [hcls, hχe, envelope_add_const, envelope_smul F _ _ hm'] at key
  have key' := key.add_const (c₀ : ℝ)
  simp only [ProjBerk.ereal_add_neg_add_coe] at key'
  exact (isPSH_smul_iff hm').1 key'

end FSSystem

/-! ### Projective subvarieties (rank one) -/

namespace ProjSubvariety

universe u

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The **psh envelope** `P_θ(φ) = sup {τ ∈ PSH(X, θ) : τ ≤ φ}` on `X^an` (`def:sg-ep` for the
system `X.fsSystem` of `lem:pg-subvariety-fs-system`, `θ ∈ ℝ`). -/
abbrev envelope (θ : ℝ) (φ : X.an → EReal) : X.an → EReal :=
  X.fsSystem.envelope (fun _ => θ) φ

/-- The **envelope property** of the class `θ c₁(O_X(1))`, `θ ∈ ℝ` (`def:sg-ep`; BJ22 §5.2). -/
abbrev HasEnvelopeProperty (θ : ℝ) : Prop :=
  X.fsSystem.HasEnvelopeProperty fun _ => θ

/-- **PL functions on `X^an`** (`def:sg-ep`, `PL(X)`): differences of finite rational
Fubini–Study functions of the system `X.fsSystem`. -/
abbrev IsPL (f : X.an → ℝ) : Prop :=
  X.fsSystem.IsPL f

variable {X} {θ : ℝ} {a : ℚ} {φ : X.an → EReal}

/-- Finite Fubini–Study functions on `X^an` are PL functions. -/
theorem IsFinFS.isPL (h : X.IsFinFS a φ) : X.IsPL fun v => (φ v).toReal :=
  FSSystem.IsFinFS.isPL (F := X.fsSystem) (a := fun _ => a) h

/-- `PL(X)` in terms of the finite Fubini–Study functions of class `O(a)` of
`def:wu-proj-functions`(1) (`ProjSubvariety.IsFiniteFS`). -/
theorem isPL_iff {f : X.an → ℝ} :
    X.IsPL f ↔ ∃ (a b : ℚ) (φ ψ : X.an → ℝ), X.IsFiniteFS a φ ∧ X.IsFiniteFS b ψ ∧
      ∀ v, f v = φ v - ψ v := by
  constructor
  · rintro ⟨a, b, φ, ψ, hφ, hψ, hf⟩
    exact ⟨a 0, b 0, _, _, IsFinFS.isFiniteFS hφ, IsFinFS.isFiniteFS hψ, hf⟩
  · rintro ⟨a, b, φ, ψ, hφ, hψ, hf⟩
    exact ⟨fun _ => a, fun _ => b, _, _, hφ.isFinFS, hψ.isFinFS, fun v => by
      simp only [EReal.toReal_coe]; exact hf v⟩

variable (X) in
/-- `P_θ(φ + c) = P_θ(φ) + c` on `X^an` (`lem:sg-env-basic`). -/
theorem envelope_add_const (θ : ℝ) (φ : X.an → EReal) (c : ℝ) :
    X.envelope θ (fun v => φ v + (c : EReal)) = fun v => X.envelope θ φ v + (c : EReal) :=
  FSSystem.envelope_add_const X.fsSystem _ φ c

variable (X) in
/-- `P_{tθ}(t φ) = t P_θ(φ)` on `X^an` for real `t > 0` (`lem:sg-env-basic`). -/
theorem envelope_mul (θ : ℝ) (φ : X.an → EReal) {t : ℝ} (ht : 0 < t) :
    X.envelope (t * θ) (fun v => (t : EReal) * φ v) = fun v => (t : EReal) * X.envelope θ φ v :=
  FSSystem.envelope_smul X.fsSystem (fun _ => θ) φ ht

variable (X) in
/-- `inf φ ≤ P_θ(φ)` on `X^an` for `θ ≥ 0` (`lem:sg-env-basic`). -/
theorem iInf_le_envelope (hθ : 0 ≤ θ) (φ : X.an → EReal) (v : X.an) :
    ⨅ w, φ w ≤ X.envelope θ φ v :=
  FSSystem.iInf_le_envelope X.fsSystem (fun _ => hθ) φ v

/-- **Approximation of classes** on `X^an` (`lem:sg-envppty`): if `θ` is the limit of a sequence
of classes `θⱼ ≥ θ` with the envelope property, then `θ` has the envelope property. -/
theorem HasEnvelopeProperty.of_tendsto {θs : ℕ → ℝ} (hθs : Tendsto θs atTop (𝓝 θ))
    (hle : ∀ j, θ ≤ θs j) (h : ∀ j, X.HasEnvelopeProperty (θs j)) : X.HasEnvelopeProperty θ :=
  FSSystem.HasEnvelopeProperty.of_tendsto (θs := fun j _ => θs j)
    (tendsto_pi_nhds.2 fun _ => hθs) (fun j _ => hle j) h

/-- `lem:sg-envppty` on `X^an` with rational classes: if every rational `a > θ` has the envelope
property, so does `θ`. -/
theorem hasEnvelopeProperty_of_forall_rat_gt
    (h : ∀ a : ℚ, θ < a → X.HasEnvelopeProperty (a : ℝ)) : X.HasEnvelopeProperty θ := by
  obtain ⟨q, -, hqθ, hq⟩ := Real.exists_seq_rat_strictAnti_tendsto θ
  exact HasEnvelopeProperty.of_tendsto hq (fun j => (hqθ j).le) fun j => h _ (hqθ j)

/-- **Fubini–Study envelopes** on `X^an` (`lem:sg-fs-envelope`): for `a ∈ ℚ_{>0}` and a lsc
obstacle `φ : X^an → (-∞, +∞]`, `P_a(φ) = sup {ψ ∈ 𝓗_fin(X, a) : ψ ≤ φ}` pointwise. -/
theorem envelope_eq_iSup_isFinFS (ha : 0 < a) (hφ : LowerSemicontinuous φ)
    (hφbot : ∀ v, φ v ≠ ⊥) (v : X.an) :
    X.envelope (a : ℝ) φ v = ⨆ (ψ : X.an → EReal) (_ : X.IsFinFS a ψ ∧ ψ ≤ φ), ψ v :=
  FSSystem.envelope_eq_iSup_isFinFS (F := X.fsSystem) (a := fun _ => a) (fun _ => ha) hφ
    hφbot v

/-- **Envelope property via PL obstacles** on `X^an` (`prop:sg-envelope-criterion`), under the
separation hypothesis `lem:sg-pl-separate`. -/
theorem hasEnvelopeProperty_of_forall_isPL (hsep : {f : X.an → ℝ | X.IsPL f}.SeparatesPoints)
    (hPL : ∀ φ : X.an → ℝ, X.IsPL φ → X.IsPSH θ (X.envelope θ fun v => (φ v : EReal))) :
    X.HasEnvelopeProperty θ :=
  FSSystem.hasEnvelopeProperty_of_forall_isPL hsep hPL

/-- **The envelope criterion** on `X^an` (`prop:sg-envelope-criterion` with its converse), under
the separation hypothesis `lem:sg-pl-separate`: for `θ ≥ 0`, `θ` has the envelope property iff
`P_θ(ψ)` is `θ`-psh for every PL function `ψ`. -/
theorem hasEnvelopeProperty_iff_forall_isPL (hsep : {f : X.an → ℝ | X.IsPL f}.SeparatesPoints)
    (hθ : 0 ≤ θ) : X.HasEnvelopeProperty θ ↔
      ∀ φ : X.an → ℝ, X.IsPL φ → X.IsPSH θ (X.envelope θ fun v => (φ v : EReal)) :=
  FSSystem.hasEnvelopeProperty_iff_forall_isPL hsep fun _ => hθ

/-- **Reduction to integral classes and nonpositive PL obstacles** on `X^an`
(`thm:sg-reduction`), under the separation hypothesis `lem:sg-pl-separate`: if `P_a(φ)` is
`a`-psh for every integer `a ≥ 1` and every PL function `φ ≤ 0`, then every `θ ∈ ℝ` has the
envelope property. -/
theorem hasEnvelopeProperty_of_forall_nat (hsep : {f : X.an → ℝ | X.IsPL f}.SeparatesPoints)
    (h : ∀ a : ℕ, 0 < a → ∀ φ : X.an → ℝ, X.IsPL φ → (∀ v, φ v ≤ 0) →
      X.IsPSH a (X.envelope a fun v => (φ v : EReal)))
    (θ : ℝ) : X.HasEnvelopeProperty θ := by
  refine FSSystem.hasEnvelopeProperty_of_forall_nat hsep (fun a ha φ hφ hφ0 => ?_) _
  have e : (fun c => (a c : ℝ)) = fun _ => ((a 0 : ℕ) : ℝ) :=
    funext fun c => by rw [Subsingleton.elim c 0]
  rw [e]
  exact h (a 0) (ha 0) φ hφ hφ0

end ProjSubvariety

end EnvelopeProperty
