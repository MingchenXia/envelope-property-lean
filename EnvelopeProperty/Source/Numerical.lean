import EnvelopeProperty.AlgGeom.NativeNumericalCurveTopology
import EnvelopeProperty.AlgGeom.NativeNumericalAmpleConeGeneration
import EnvelopeProperty.AlgGeom.NativeNumericalAmpleFamilyOpenness
import EnvelopeProperty.AlgGeom.NativeNumericalPositiveAmpleSums
import EnvelopeProperty.Berkovich.SchemeRelativeValuedPoints

/-! # Analytification, numerical classes and convergence in the ample-cone order

Let `k` be a field and `p : X ⟶ Spec k` a projective scheme. This file fixes the objects of the
source-faithful statements of Fang–Han–Xia (FHX, the paper) and
Boucksom–Jonsson (BJ22, `bj22-trivval`) on the scheme `X` itself:

* `Variety.An p`: the Berkovich analytification `X^an` over `k` with the trivial absolute value
  (BJ22 §1), i.e. the native space `Berkovich.RelativeSchemeValuedPoint 1 p` of points
  `x ∈ X` with an absolute value on `κ(x)` that is trivial on `k`;
* `N¹(X)_ℝ` is `NativeRealNumericalClasses.Space p` (the real Picard space modulo the classes of
  degree zero on every closed integral curve), with its ample cone
  `NativeRealNumericalClasses.ampleCone p` (positive combinations of ample line classes,
  BJ22's `Amp(X)`);
* `Variety.AmpleTendsto p c l θ`: convergence `c → θ` along a filter `l` **in the order of the
  ample cone**: for every ample class `η`, eventually `η ± (c_j - θ)` is ample
  (`def:var-ample-convergence`).

## Why order convergence

BJ22 (Definition 4.1, `bj22-trivval:defi:psh`) asks for `lim_i c₁(L_i) = θ` in `Num(X)`, a
finite dimensional real vector space (BJ22, conventions: "the finite dimensional `ℝ`-vector space
`Num(X)`"), in which "ample classes form a nonempty open convex cone" (same place). The finite
dimensionality of `N¹(X)_ℝ` (Néron–Severi) is not formalized. In finite dimension the sets
`{x | η ± x ∈ Amp(X)}`, `η ∈ Amp(X)`, form a basis of neighbourhoods of `0`: they are open since
`Amp(X)` is open, and they are bounded since the nef cone is closed and salient. Hence
`AmpleTendsto` *is* BJ22's convergence when `N¹(X)_ℝ` is finite dimensional; this is proved in
`EnvelopeProperty.Source.FiniteDimensionalTopology` (`Variety.ampleTendsto_iff_tendsto`). In
general it is the convergence for which BJ22's and FHX's uses of the openness of the ample cone
(FHX Lemma 2.6) hold by definition
(`AmpleTendsto.eventually_sub_mem`). The definition is intrinsic: no ample class, embedding or
line family is chosen.

## Main results

* `AmpleTendsto.tendsto`: order convergence implies convergence in the curve-weak topology of
  `N¹(X)_ℝ` (all curve degrees converge): if `η ± x ∈ Amp ⊆ Nef` then
  `|deg_C x| ≤ deg_C η`, and `η = t [A]` with `A` ample can be taken with `deg_C η` small;
* `ampleTendsto_lineFamilyMap`: on an integral `X`, coefficientwise convergence along a finite
  family of line bundles gives order convergence of the classes (from the perturbation radius of
  the ample cone along finite line families,
  `NativeRealNumericalClasses.exists_ampleCone_lineFamily_radius`);
* `AmpleTendsto.eventually_sub_mem`: if `c_j → θ` and `η` is ample, then eventually
  `θ + η - c_j` is ample;
* the algebra of limits: `ampleTendsto_const`, `AmpleTendsto.add`, `.neg`, `.sub`,
  `.const_smul`, `.comp`, `.mono_left`, `.congr'`, `.unique`.
-/

open AlgebraicGeometry CategoryTheory Filter Topology Scheme.Modules
open scoped Classical NNReal Topology

noncomputable section

universe u

namespace EnvelopeProperty.Variety

open NativeRealNumericalClasses NativeClosedCurveDegrees

section Analytification

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- The **Berkovich analytification** `X^an` of `p : X ⟶ Spec k` over the trivially valued field
`k` (BJ22 §1): points of `X` together with an absolute value on their residue field extending the
trivial absolute value of `k`, with the Berkovich topology. -/
abbrev An : Type u := Berkovich.RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p

end Analytification

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]

/-- **Convergence in `N¹(X)_ℝ`** (`def:var-ample-convergence`): `c → θ` along `l` in the order
of the ample cone, i.e. for every ample class `η`, eventually both `η + (c_j - θ)` and
`η - (c_j - θ)` are ample. When `N¹(X)_ℝ` is finite dimensional this is convergence in its
Euclidean topology (`Variety.ampleTendsto_iff_tendsto`). -/
def AmpleTendsto {J : Type*} (c : J → Space p) (l : Filter J) (θ : Space p) : Prop :=
  ∀ η ∈ ampleCone p, ∀ᶠ j in l, η + (c j - θ) ∈ ampleCone p ∧ η - (c j - θ) ∈ ampleCone p

section Basic

variable {p} {J : Type*} {c c' : J → Space p} {l : Filter J} {θ θ' : Space p}

theorem ampleTendsto_iff : AmpleTendsto p c l θ ↔ ∀ η ∈ ampleCone p,
    ∀ᶠ j in l, η + (c j - θ) ∈ ampleCone p ∧ η - (c j - θ) ∈ ampleCone p :=
  Iff.rfl

/-- A constant family converges to its value. -/
theorem ampleTendsto_const (l : Filter J) (θ : Space p) : AmpleTendsto p (fun _ => θ) l θ := by
  intro η hη
  refine Eventually.of_forall fun _ => ?_
  simp only [sub_self, add_zero, sub_zero]
  exact ⟨hη, hη⟩

theorem AmpleTendsto.mono_left {l' : Filter J} (h : AmpleTendsto p c l θ) (hl : l' ≤ l) :
    AmpleTendsto p c l' θ :=
  fun η hη => Eventually.filter_mono hl (h η hη)

theorem AmpleTendsto.comp {K : Type*} {f : K → J} {m : Filter K} (h : AmpleTendsto p c l θ)
    (hf : Tendsto f m l) : AmpleTendsto p (c ∘ f) m θ :=
  fun η hη => hf.eventually (h η hη)

theorem AmpleTendsto.congr' (h : AmpleTendsto p c l θ) (hc : c =ᶠ[l] c') :
    AmpleTendsto p c' l θ := by
  intro η hη
  filter_upwards [h η hη, hc] with j hj hj'
  rwa [← hj']

/-- Limits add. -/
theorem AmpleTendsto.add (h : AmpleTendsto p c l θ) (h' : AmpleTendsto p c' l θ') :
    AmpleTendsto p (fun j => c j + c' j) l (θ + θ') := by
  intro η hη
  have hη₂ : (2 : ℝ)⁻¹ • η ∈ ampleCone p := (ampleCone p).smul_mem (by norm_num) hη
  filter_upwards [h _ hη₂, h' _ hη₂] with j hj hj'
  have e₁ : η + (c j + c' j - (θ + θ')) =
      ((2 : ℝ)⁻¹ • η + (c j - θ)) + ((2 : ℝ)⁻¹ • η + (c' j - θ')) := by module
  have e₂ : η - (c j + c' j - (θ + θ')) =
      ((2 : ℝ)⁻¹ • η - (c j - θ)) + ((2 : ℝ)⁻¹ • η - (c' j - θ')) := by module
  rw [e₁, e₂]
  exact ⟨(ampleCone p).add_mem hj.1 hj'.1, (ampleCone p).add_mem hj.2 hj'.2⟩

theorem AmpleTendsto.neg (h : AmpleTendsto p c l θ) :
    AmpleTendsto p (fun j => -c j) l (-θ) := by
  intro η hη
  filter_upwards [h η hη] with j hj
  have e₁ : η + (-c j - -θ) = η - (c j - θ) := by abel
  have e₂ : η - (-c j - -θ) = η + (c j - θ) := by abel
  rw [e₁, e₂]
  exact ⟨hj.2, hj.1⟩

theorem AmpleTendsto.sub (h : AmpleTendsto p c l θ) (h' : AmpleTendsto p c' l θ') :
    AmpleTendsto p (fun j => c j - c' j) l (θ - θ') := by
  simpa only [sub_eq_add_neg] using h.add h'.neg

theorem AmpleTendsto.const_smul (h : AmpleTendsto p c l θ) (r : ℝ) :
    AmpleTendsto p (fun j => r • c j) l (r • θ) := by
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · have hr' : 0 < -r := neg_pos.mpr hr
    intro η hη
    filter_upwards [h _ ((ampleCone p).smul_mem (inv_pos.mpr hr') hη)] with j hj
    have h₁ := (ampleCone p).smul_mem hr' hj.1
    have h₂ := (ampleCone p).smul_mem hr' hj.2
    rw [smul_add, smul_smul, mul_inv_cancel₀ hr'.ne', one_smul] at h₁
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hr'.ne', one_smul] at h₂
    have e₁ : η + (r • c j - r • θ) = η - (-r) • (c j - θ) := by module
    have e₂ : η - (r • c j - r • θ) = η + (-r) • (c j - θ) := by module
    rw [e₁, e₂]
    exact ⟨h₂, h₁⟩
  · simpa only [zero_smul] using ampleTendsto_const l (0 : Space p)
  · intro η hη
    filter_upwards [h _ ((ampleCone p).smul_mem (inv_pos.mpr hr) hη)] with j hj
    have h₁ := (ampleCone p).smul_mem hr hj.1
    have h₂ := (ampleCone p).smul_mem hr hj.2
    rw [smul_add, smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at h₁
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at h₂
    have e₁ : η + (r • c j - r • θ) = η + r • (c j - θ) := by module
    have e₂ : η - (r • c j - r • θ) = η - r • (c j - θ) := by module
    rw [e₁, e₂]
    exact ⟨h₁, h₂⟩

/-- **The use of openness of the ample cone** (BJ22, conventions; FHX
`lem:finite-class-promotion`): if `c_j → θ` and `η` is ample, then `θ + η - c_j` is eventually
ample. -/
theorem AmpleTendsto.eventually_sub_mem (h : AmpleTendsto p c l θ) {η : Space p}
    (hη : η ∈ ampleCone p) : ∀ᶠ j in l, θ + η - c j ∈ ampleCone p := by
  filter_upwards [h η hη] with j hj
  have e : θ + η - c j = η - (c j - θ) := by abel
  rw [e]
  exact hj.2

/-- If `c_j → θ` and `η` is ample, then `c_j + η - θ` is eventually ample. -/
theorem AmpleTendsto.eventually_add_sub_mem (h : AmpleTendsto p c l θ) {η : Space p}
    (hη : η ∈ ampleCone p) : ∀ᶠ j in l, c j + η - θ ∈ ampleCone p := by
  filter_upwards [h η hη] with j hj
  have e : c j + η - θ = η + (c j - θ) := by abel
  rw [e]
  exact hj.1

/-- **Order convergence implies curve-weak convergence**: every curve degree of `c_j` tends to
that of `θ`. If `η ± x` is ample then `|deg_C x| < deg_C η`, and `η = t [A]` with `A` ample and
`t = ε / (2 deg_C A)` has `deg_C η = ε / 2`. -/
theorem AmpleTendsto.tendsto (h : AmpleTendsto p c l θ) : Tendsto c l (𝓝 θ) := by
  rw [tendsto_iff_curveDegree]
  intro C
  obtain ⟨A, hA⟩ := exists_geometric_ample_line p
  have ha : 0 < curveDegree p C (lineClass p A hA.isInvertible) :=
    curveDegree_ampleLineClass_pos p A hA C
  rw [Metric.tendsto_nhds]
  intro ε hε
  have ht : 0 < ε / (2 * curveDegree p C (lineClass p A hA.isInvertible)) :=
    div_pos hε (mul_pos two_pos ha)
  filter_upwards [h _ ((ampleCone p).smul_mem ht (ampleLineClass_mem_ampleCone p A hA))]
    with j hj
  have h₁ := curveDegree_ampleCone_pos p _ hj.1 C
  have h₂ := curveDegree_ampleCone_pos p _ hj.2 C
  rw [map_add, map_sub, (curveDegree p C).map_smul, smul_eq_mul] at h₁
  rw [map_sub, map_sub, (curveDegree p C).map_smul, smul_eq_mul] at h₂
  have hη : ε / (2 * curveDegree p C (lineClass p A hA.isInvertible)) *
      curveDegree p C (lineClass p A hA.isInvertible) = ε / 2 := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ ha.ne']
  rw [hη] at h₁ h₂
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Order limits are unique. -/
theorem AmpleTendsto.unique [l.NeBot] (h : AmpleTendsto p c l θ) (h' : AmpleTendsto p c l θ') :
    θ = θ' :=
  tendsto_nhds_unique h.tendsto h'.tendsto

end Basic

/-- **Convergence along a finite line family** (`lem:var-ample-convergence-line-family`): on an
integral `X`, if the real coefficient vectors `a_j` tend to `b`, then the classes
`∑ a_j(i) [L_i]` tend to `∑ b(i) [L_i]` in the order of the ample cone. For an ample `η`, the
ample cone contains `η + ∑ x_i [L_i]` whenever all `|x_i|` are small
(`exists_ampleCone_lineFamily_radius`); apply it to `x = ±(a_j - b)`. -/
theorem ampleTendsto_lineFamilyMap [IsIntegral X] {ι : Type*} [Fintype ι] (L : ι → X.Modules)
    (hL : ∀ i, IsInvertible (L i)) {J : Type*} {a : J → ι → ℝ} {l : Filter J} {b : ι → ℝ}
    (h : Tendsto a l (𝓝 b)) :
    AmpleTendsto p (fun j => lineFamilyMap p L hL (a j)) l (lineFamilyMap p L hL b) := by
  intro η hη
  obtain ⟨ε, hε, hrad⟩ := exists_ampleCone_lineFamily_radius p L hL η hη
  have hsmall : ∀ᶠ j in l, ∀ i, |a j i - b i| < ε := by
    refine Filter.eventually_all.2 fun i => ?_
    have hi := Metric.tendsto_nhds.1 (tendsto_pi_nhds.1 h i) ε hε
    simpa only [Real.dist_eq] using hi
  filter_upwards [hsmall] with j hj
  have h₁ := hrad (a j - b) fun i => by simpa only [Pi.sub_apply] using hj i
  have h₂ := hrad (b - a j) fun i => by rw [Pi.sub_apply, abs_sub_comm]; exact hj i
  rw [map_sub] at h₁ h₂
  have e : η - (lineFamilyMap p L hL (a j) - lineFamilyMap p L hL b) =
      η + (lineFamilyMap p L hL b - lineFamilyMap p L hL (a j)) := by abel
  rw [e]
  exact ⟨h₁, h₂⟩

end EnvelopeProperty.Variety
