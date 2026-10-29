/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.Defs

/-!
# Imported inputs for the affine theory of regularizable functions

This file records, as an explicit hypothesis, the two statements of Fang–Han–Xia,
Lemma 5.11(5) and (6) (`lem:regularizable-closure`), that the source derives from the global
pluripotential theory of Boucksom–Jonsson on a projective compactification. They are
Wu, *On the local theory of non-archimedean psh functions* (arXiv:2609.27610v1),
Lemma 3.25(2) (psh_regularization_with_growth_control) and Lemma 3.26
(approximable_on_exhausting_tropical_polytopes_implies_pshlogreg), with the corrections
recorded in the source footnotes. Their proofs (FHX Lemmas 5.9 and 5.10) use

* Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field*: the
  definition of `θ`-psh functions, PSH2 (Theorem 4.5), countable regularization in a fixed ample
  class (Corollary 12.18(iii)), and the description of PL functions by test configurations
  (Theorems 2.2, 2.31, Definition 3.2, Lemma 4.3);
* Chambert-Loir–Ducros' positivity criterion (FHX Lemma 5.5), via the residual line bundle;

none of which is available in Mathlib. Neither depends on Boucksom–Jonsson's Theorem 6.21.

The hypothesis is a `Prop`-valued class quantifying over all normal affine `k`-varieties in a
fixed universe. It is **not** an axiom: every theorem using it lists it among its hypotheses,
and `#print axioms` of such a theorem shows only the standard axioms. Discharging it requires
formalizing the projective theory above.

The statements are those of FHX Lemma 5.11(5),(6) for a normal affine variety (`A` a finitely
generated integrally closed domain over `k`). FHX's (6) is stronger than Wu's literal Lemma 3.26
(arbitrary local convex PL charts instead of a single tropicalization); the extra strength comes
from FHX Lemma 5.5. So the trust boundary is FHX Lemmas 5.5, 5.9, 5.10 together with BJ22 and
CLD12, not Wu alone. As in the sources, `k` is algebraically closed (a parameter of the class).
Countability of `k` is not needed. In (5)
only the upper bound `u_j - c g ≤ C_j` is imported (the source asserts two-sided boundedness).
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open Berk

universe u v

/-- **Imported (FHX Lemma 5.11(5),(6); Wu26 Lemmas 3.25(2), 3.26).** For every normal affine
variety `Y = Spec A` over the algebraically closed trivially valued field `k`:

* `growthControl` (5.11(5)): if `u ∈ ℛ(Y)` and `u ≤ g + C` with `g ∈ FS(Y)`, then for every
  rational `c > 1` there are `u_j ∈ FS(Y)` decreasing to `u` with `u_j - c g` bounded above;
* `localToGlobal` (5.11(6)): a function of logarithmic growth, not identically `-∞`, which on a
  neighbourhood of every compact subset is the limit of a decreasing sequence of convex PL
  functions, is regularizable. -/
class WuRegularization (k : Type u) [Field k] [IsAlgClosed k] : Prop where
  growthControl : ∀ (A : Type v) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [IsIntegrallyClosed A] (u : Berk k A → EReal)
    (g : FSData k A) (C : ℝ), IsRegularizable u → (∀ x, u x ≤ g.eval x + (C : EReal)) →
    ∀ c : ℚ, 1 < c → ∃ h : ℕ → FSData k A, (∀ x, Antitone fun j => (h j).eval x) ∧
      (∀ x, u x = ⨅ j, (h j).eval x) ∧
      ∀ j, ∃ Cj : ℝ, ∀ x, (h j).eval x ≤ ((c : ℝ) : EReal) * g.eval x + (Cj : EReal)
  localToGlobal : ∀ (A : Type v) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [IsIntegrallyClosed A] (u : Berk k A → EReal),
    (∃ x, u x ≠ ⊥) → HasLogGrowth u →
    (∀ K : Set (Berk k A), IsCompact K →
      ∃ U : Set (Berk k A), IsOpen U ∧ K ⊆ U ∧ IsDecrConvexPLLimitOn U u) →
    IsRegularizable u

end EnvelopeProperty
