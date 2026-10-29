/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietyPSH

/-!
# Local positivity (FHX Lemma 5.5), imported as a hypothesis

This file states, as the explicit `Prop`-valued hypothesis class `LocalPositivity k`, the lemma

> **FHX Lemma 5.5** (`lem:local-PL-positivity`). Let `P` be a normal projective variety and
> `L ∈ Pic(P)_ℚ` ample. Every locally `L`-convex function `φ: P^an → ℝ` belongs to `PSH(P, L)`.

of Fang–Han–Xia, *The envelope property for unibranch projective varieties*, with "locally `L`-convex" in the sense of FHX Definition 5.3
(`def:locally-L-psh`): `φ - m⁻¹ log|s|` is convex PL on `P_s^an` for **every** admissible pair
`(m, s)` for `L`. Blueprint: `wu-discharge.tex`, node `lem:wu-local-positivity`, with `PSH(P, L)` from `def:pg-subvariety-psh`. FHX prove the lemma through
Boucksom–Jonsson's test configurations (BJ22 Theorem 2.31, Definition 3.2, Lemma 4.3) and the
positivity criterion of Chambert-Loir–Ducros (CLD12), none of which is available in Mathlib.

The class is **not** an axiom: every theorem using it lists it among its hypotheses, and
`#print axioms` of such a theorem shows only the standard axioms.

## The statement in the graded model

In the graded model (blueprint
`conv:wu-bj-global`, `rmk:pg-subvariety-psh-comparison`):

* `P` is a projective subvariety `X = V(I) ⊆ ℙᴹ` (`ProjSubvariety k M`: `I ⊆ R_M = k[x₀, …, x_M]`
  a homogeneous prime not containing all `xᵢ`) whose homogeneous coordinate ring
  `S'' = R_M / I` is integrally closed ("projectively normal"; this is
  `ProjSubvariety.IsProjNormal`, and `Compactification.isIntegrallyClosed_quotient`).
  Then `P = Proj S''` is a normal projective variety and `S''_n = H⁰(P, O(n))`. The degree-zero
  part of `S''` is automatically `k`
  (`ProjSubvariety.exists_algebraMap_eq_mk_of_isHomogeneous_zero`),
  so it is not a hypothesis. `P^an` is `X.an = V(I)^an ⊆ (ℙᴹ)^an`.
* `L = O(a)` with `a ∈ ℚ_{>0}`.
* An **admissible pair** for `L` is `(m, s)` with `m ≥ 1`, `d = m a ∈ ℕ` and `s` a form of degree
  `d` with `s ∉ I` (a nonzero section of `mL = O(d)`, which is globally generated as `d ≥ 1`).
  Then `P_s^an = {|s| ≠ 0} ∩ X.an` is identified by the quotient chart `ι_s` of
  `Projective/Subvariety.lean` with `(Spec S''_{(s̄)})^an`, modelled as
  `Berk k (QuotChartAlg X.ideal s d)`, and `φ - m⁻¹ log|s|` is read on this chart
  (`ProjSubvariety.admChartFun`).
* "Convex PL on `P_s^an`" (FHX Definition 5.1(1), with `V = P`) is `IsConvexPLOn Set.univ` on
  the affine chart: a Zariski open `V₀ ⊆ P` with `W ⊆ V₀^an` may be replaced by `V₀ ∩ P_s`, and on
  an affine variety the invertible functions may be taken to be elements of the coordinate ring
  not vanishing near the point, with signed rational exponents (`Local/Defs.lean`).
* `PSH(P, L)` is `X.IsPSH a` (`def:pg-subvariety-psh`).

`ProjSubvariety.IsLocallyConvexAll X a φ` is FHX Definition 5.3 in this form, and
`LocalPositivity.isPSH_of_isLocallyConvexAll` is FHX Lemma 5.5.

## Fidelity caveats (not formalized)

1. *The model.* Every pair `(P, L)` (normal projective `P`, ample `L ∈ Pic(P)_ℚ`) is, up to
   isomorphism, a projectively normal `X ⊆ ℙᴹ` with `L = a O(1)`: for `r` sufficiently divisible
   the section ring of `rL` is a normal domain generated in degree one
   (`rmk:pg-subvariety-psh-comparison`). The identification of `X.an` with the Berkovich
   analytification has the status of that of `ProjBerk` (`def:pn-an`).
2. *Admissible pairs.* FHX allow every `m ≥ 1` such that `mL` is a (globally generated) line
   bundle; on `P` such a line bundle may exist although `m a ∉ ℕ` (e.g. `O_{ℙ¹}(1)` on a conic,
   `a = 1/2`). Restricting to the pairs with `m a ∈ ℕ` does not change the notion: these pairs
   cover `P^an`, and by the remark after FHX Definition 5.3 convexity for one admissible pair near
   each point implies it for all (in our setting this is
   `ProjSubvariety.IsLocallyConvex.isLocallyConvexAll`, `Local/PositivityReductionCharts.lean`;
   for FHX's pairs it is the same chart-change argument).
3. *The class `PSH(P, L)`.* `X.IsPSH a` restricts the approximating classes of BJ22
   Definition 4.1 to `ℝ · O(1)`, so `X.IsPSH a ⊆ PSH(P, a c₁(O(1)))` in the sense of BJ22; the
   two agree by the openness of the ample cone (Kleiman), `rmk:pg-subvariety-psh-comparison`.
   Hence the conclusion of `LocalPositivity` is, a priori, slightly stronger than FHX's; the
   class is FHX Lemma 5.5 combined with this (unformalized) comparison.

## Main definitions

* `ProjSubvariety.admChartFun X m φ s d`: the function `(φ - m⁻¹ log|s|) ∘ ι_s⁻¹` on the chart
  `(Spec S''_{(s̄)})^an`.
* `ProjSubvariety.IsLocallyConvexAll X a φ`: FHX Definition 5.3 (locally `O(a)`-convex
  functions on `X^an`, every admissible pair).
* `LocalPositivity k`: FHX Lemma 5.5, the hypothesis class.

## Main results

* `ProjSubvariety.exists_algebraMap_eq_mk_of_isHomogeneous_zero`: `S''_0 = k`.
* `ProjSubvariety.admChartFun_eq_chartFun`: for `d = m a`, `admChartFun` is `chartFun` (`m⁻¹ = a / d`).
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open ProjBerk

universe u

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- **`S''_0 = k`.** The degree-zero part of the homogeneous coordinate ring `S'' = R_M / I` of a
projective subvariety consists of the constants: a form of degree `0` is a constant polynomial.
(So the condition "`S''_0 = k`" of `conv:wu-bj-global` holds automatically in the graded
model.) -/
theorem exists_algebraMap_eq_mk_of_isHomogeneous_zero {f : MvPolynomial (Fin (M + 1)) k}
    (hf : f.IsHomogeneous 0) :
    ∃ c : k, algebraMap k (MvPolynomial (Fin (M + 1)) k ⧸ X.ideal) c =
      Ideal.Quotient.mk X.ideal f := by
  refine ⟨f.coeff 0, ?_⟩
  conv_rhs => rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.1
    ((MvPolynomial.totalDegree_zero_iff_isHomogeneous _).2 hf)]
  rfl

/-- The function `(φ - m⁻¹ log|s|) ∘ ι_s⁻¹` on the quotient chart
`(Spec S''_{(s̄)})^an = (Spec A_s / I_{(s)})^an` of a form `s` of degree `d ≥ 1`
(FHX Definition 5.3, read on the chart `P_s^an ≃ (Spec S''_{(s̄)})^an` of
`lem:wu-proj-chart`(2)). -/
def admChartFun (m : ℕ) (φ : X.an → ℝ) (s : MvPolynomial (Fin (M + 1)) k) (d : ℕ)
    (hs : s.IsHomogeneous d) (hd : 0 < d) (y : Berk k (QuotChartAlg X.ideal s d)) : EReal :=
  ((φ (X.chartInv s d hs hd y) -
    (m : ℝ)⁻¹ * Real.log ((X.chartInv s d hs hd y : ProjBerk k M).1.val s : ℝ) : ℝ) : EReal)

/-- **Locally `O(a)`-convex functions in the sense of FHX Definition 5.3** (`def:locally-L-psh`,
with `U = P^an`): for **every** admissible pair `(m, s)` for `L = O(a)` — an integer `m ≥ 1`
with `d = m a ∈ ℕ` and a form `s` of degree `d` not in `I` (a nonzero section of `mL`) — the
function `φ - m⁻¹ log|s|` is convex PL on `P_s^an`, i.e. `(φ - m⁻¹ log|s|) ∘ ι_s⁻¹` is convex PL
on the whole chart `(Spec S''_{(s̄)})^an`. (The binder `hd : 0 < d` is automatic for `a > 0`.) -/
def IsLocallyConvexAll (a : ℚ) (φ : X.an → ℝ) : Prop :=
  ∀ (m d : ℕ) (s : MvPolynomial (Fin (M + 1)) k) (hs : s.IsHomogeneous d) (hd : 0 < d),
    0 < m → (d : ℚ) = m * a → s ∉ X.ideal → IsConvexPLOn Set.univ (X.admChartFun m φ s d hs hd)

/-- For an admissible pair (`d = m a`), `φ - m⁻¹ log|s| = φ - (a / d) log|s|`: the chart function
of FHX Definition 5.3 is `chartFun` (`def:wu-proj-functions`(2)). -/
theorem admChartFun_eq_chartFun {a : ℚ} {m d : ℕ} (hm : 0 < m) (hda : (d : ℚ) = m * a)
    (φ : X.an → ℝ) {s : MvPolynomial (Fin (M + 1)) k} (hs : s.IsHomogeneous d) (hd : 0 < d) :
    X.admChartFun m φ s d hs hd = X.chartFun a φ s d hs hd := by
  funext y
  rw [admChartFun, chartFun]
  congr 3
  have hda' : (d : ℝ) = m * a := by exact_mod_cast hda
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [eq_div_iff hd', hda']
  field_simp

end ProjSubvariety

/-- **Imported: FHX Lemma 5.5** (`lem:local-PL-positivity`, blueprint `lem:wu-local-positivity`),
in the graded model. Let `P = X = V(I) ⊆ ℙᴹ` be a normal projective variety (`R_M / I` integrally
closed) and `L = O(a)`, `a ∈ ℚ_{>0}`. Every locally `L`-convex function `φ : P^an → ℝ` (FHX
Definition 5.3: `φ - m⁻¹ log|s|` is convex PL on `P_s^an` for every admissible pair `(m, s)`,
`ProjSubvariety.IsLocallyConvexAll`) belongs to `PSH(P, L)` (`X.IsPSH a`).

This is an explicit hypothesis, not an axiom; see the module docstring for the model and the
fidelity caveats (in particular, `X.IsPSH a` is a priori contained in BJ22's `PSH(P, L)`, with
equality by Kleiman's openness of the ample cone). -/
class LocalPositivity (k : Type u) [Field k] [IsAlgClosed k] : Prop where
  isPSH_of_isLocallyConvexAll : ∀ {M : ℕ} (X : ProjSubvariety k M),
    IsIntegrallyClosed (MvPolynomial (Fin (M + 1)) k ⧸ X.ideal) →
    ∀ (a : ℚ), 0 < a → ∀ φ : X.an → ℝ, X.IsLocallyConvexAll a φ →
      X.IsPSH (a : ℝ) fun v => (φ v : EReal)

end EnvelopeProperty
