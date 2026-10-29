/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumIdeals
import EnvelopeProperty.Berkovich.SpectrumBridge

/-!
# Ideal functions on bounded affine Berkovich points

In Fang–Han–Xia, §2.1 (`subsec:prelim-berkovich`), the value of an ideal is computed from
generators in the local ring at the center of a semivaluation. Independence of generators uses
that all coefficients in that ring have absolute value at most one. An arbitrary point of an
affine analytification need not have this property for its coordinate ring.

This module proves the corresponding affine foundations under the explicit hypothesis
`Berk.IsBounded x`, meaning `|a|_x ≤ 1` for every `a : A`. The intrinsic norm `idealNorm I x`
is the supremum over all elements of `I`; on bounded points it equals the maximum of any finite
set of generators. Ideal sums become maxima, products become products, and logarithms give
the formulas for local ideal functions. These are ingredients for the source's model functions;
projective centers, coherent ideal sheaf gluing, and the normalized Gauss extension are separate
constructions.

The definitions and proofs specialize the arbitrary-ring ideal calculus of
`EnvelopeProperty.Berkovich.SpectrumIdeals` through the canonical map `Berk.toSpectrum`.
The generic sum and product identities hold without boundedness; their signatures here retain
the bounded-point parameter of the existing affine API.
-/

open scoped NNReal ENNReal Topology Pointwise

open Set Topology

noncomputable section

namespace EnvelopeProperty
namespace Berk

open Berkovich

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- A point is bounded on the affine coordinate ring: all its elements have absolute value
at most one. This is the coefficient bound needed for evaluating an ideal by generators. -/
def IsBounded (x : Berk k A) : Prop := Spectrum.IsBounded x.toSpectrum

@[simp]
theorem isBounded_toSpectrum (x : Berk k A) : Spectrum.IsBounded x.toSpectrum ↔ IsBounded x :=
  Iff.rfl

theorem IsBounded.comap {B : Type*} [CommRing B] [Algebra k B] {y : Berk k B}
    (hy : IsBounded y) (φ : A →ₐ[k] B) : IsBounded (comap φ y) :=
  Spectrum.IsBounded.comap hy φ.toRingHom

/-- The intrinsic norm of an ideal, defined as the supremum of the norms of its elements.
The supremum may be infinite at an arbitrary affine analytic point. -/
def idealNorm (I : Ideal A) (x : Berk k A) : ℝ≥0∞ := Spectrum.idealNorm I x.toSpectrum

/-- The logarithmic ideal function. On bounded points it belongs to `[-∞, 0]`. -/
def idealLog (I : Ideal A) (x : Berk k A) : EReal := Spectrum.idealLog I x.toSpectrum

@[simp]
theorem idealNorm_toSpectrum (I : Ideal A) (x : Berk k A) :
    Spectrum.idealNorm I x.toSpectrum = idealNorm I x := rfl

@[simp]
theorem idealLog_toSpectrum (I : Ideal A) (x : Berk k A) :
    Spectrum.idealLog I x.toSpectrum = idealLog I x := rfl

theorem val_le_idealNorm (I : Ideal A) (x : Berk k A) {a : A} (ha : a ∈ I) :
    (x.val a : ℝ≥0∞) ≤ idealNorm I x :=
  Spectrum.val_le_idealNorm I x.toSpectrum ha

theorem idealNorm_le_iff (I : Ideal A) (x : Berk k A) (M : ℝ≥0∞) :
    idealNorm I x ≤ M ↔ ∀ a ∈ I, (x.val a : ℝ≥0∞) ≤ M :=
  Spectrum.idealNorm_le_iff I x.toSpectrum M

theorem idealNorm_mono {I J : Ideal A} (hIJ : I ≤ J) (x : Berk k A) :
    idealNorm I x ≤ idealNorm J x :=
  Spectrum.idealNorm_mono hIJ x.toSpectrum

theorem idealNorm_le_one (I : Ideal A) {x : Berk k A} (hx : IsBounded x) :
    idealNorm I x ≤ 1 :=
  Spectrum.idealNorm_le_one I hx

theorem idealLog_le_zero (I : Ideal A) {x : Berk k A} (hx : IsBounded x) :
    idealLog I x ≤ 0 :=
  Spectrum.idealLog_le_zero I hx

/-- An ideal norm vanishes exactly when the ideal is contained in the support.
This holds at every affine analytic point, without a boundedness assumption. -/
theorem idealNorm_eq_zero_iff (I : Ideal A) (x : Berk k A) :
    idealNorm I x = 0 ↔ I ≤ x.val.supp :=
  Spectrum.idealNorm_eq_zero_iff I x.toSpectrum

/-- The logarithmic ideal function equals `-∞` exactly on the ideal's vanishing locus. -/
theorem idealLog_eq_bot_iff (I : Ideal A) (x : Berk k A) :
    idealLog I x = ⊥ ↔ I ≤ x.val.supp :=
  Spectrum.idealLog_eq_bot_iff I x.toSpectrum

/-! ### Independence of generators -/

/-- A seminorm bound on a generating set extends to the ideal it generates, provided the
point is bounded on the coefficient ring. -/
theorem val_le_of_mem_span {x : Berk k A} (hx : IsBounded x) {S : Set A} {M : ℝ≥0∞}
    (hS : ∀ s ∈ S, (x.val s : ℝ≥0∞) ≤ M) {a : A} (ha : a ∈ Ideal.span S) :
    (x.val a : ℝ≥0∞) ≤ M :=
  Spectrum.val_le_of_mem_span hx hS ha

/-- The intrinsic ideal norm is the supremum of the norms of any generating set. -/
theorem idealNorm_span {x : Berk k A} (hx : IsBounded x) (S : Set A) :
    idealNorm (Ideal.span S) x = ⨆ a ∈ S, (x.val a : ℝ≥0∞) :=
  Spectrum.idealNorm_span hx S

/-- For a finite generating family the ideal norm is its maximum, including the empty family. -/
theorem idealNorm_span_finset {x : Berk k A} (hx : IsBounded x) (S : Finset A) :
    idealNorm (Ideal.span (S : Set A)) x = ((S.sup fun a => x.val a : ℝ≥0) : ℝ≥0∞) :=
  Spectrum.idealNorm_span_finset hx S

/-- Finite generating families of the same ideal give the same maximum on bounded points. -/
theorem idealNorm_span_finset_eq_of_span_eq {x : Berk k A} (hx : IsBounded x)
    (S T : Finset A) (hST : Ideal.span (S : Set A) = Ideal.span (T : Set A)) :
    S.sup (fun a => x.val a) = T.sup (fun a => x.val a) :=
  Spectrum.idealNorm_span_finset_eq_of_span_eq hx S T hST

/-! ### Pullback along affine morphisms -/

/-- Pulling back an ideal to a bounded affine point commutes with ideal evaluation. -/
theorem idealNorm_map {B : Type*} [CommRing B] [Algebra k B]
    (φ : A →ₐ[k] B) (I : Ideal A) {y : Berk k B} (hy : IsBounded y) :
    idealNorm (Ideal.map φ.toRingHom I) y = idealNorm I (comap φ y) :=
  Spectrum.idealNorm_map φ.toRingHom I hy

/-- The logarithmic pullback formula for an affine ideal function. -/
theorem idealLog_map {B : Type*} [CommRing B] [Algebra k B]
    (φ : A →ₐ[k] B) (I : Ideal A) {y : Berk k B} (hy : IsBounded y) :
    idealLog (Ideal.map φ.toRingHom I) y = idealLog I (comap φ y) :=
  Spectrum.idealLog_map φ.toRingHom I hy

/-! ### Ideal arithmetic -/

@[simp]
theorem idealNorm_bot (x : Berk k A) : idealNorm (⊥ : Ideal A) x = 0 :=
  Spectrum.idealNorm_bot x.toSpectrum

theorem idealNorm_top {x : Berk k A} (hx : IsBounded x) :
    idealNorm (⊤ : Ideal A) x = 1 :=
  Spectrum.idealNorm_top hx

/-- The norm of an ideal sum is the maximum of the two norms. -/
theorem idealNorm_sup {x : Berk k A} (hx : IsBounded x) (I J : Ideal A) :
    idealNorm (I ⊔ J) x = max (idealNorm I x) (idealNorm J x) :=
  (fun (_ : IsBounded x) => Spectrum.idealNorm_sup I J x.toSpectrum) hx

/-- The norm of an ideal product is the product of the norms. -/
theorem idealNorm_mul {x : Berk k A} (hx : IsBounded x) (I J : Ideal A) :
    idealNorm (I * J) x = idealNorm I x * idealNorm J x :=
  (fun (_ : IsBounded x) => Spectrum.idealNorm_mul I J x.toSpectrum) hx

/-- Ideal powers are evaluated by powers of the ideal norm. -/
theorem idealNorm_pow {x : Berk k A} (hx : IsBounded x) (I : Ideal A) (n : ℕ) :
    idealNorm (I ^ n) x = idealNorm I x ^ n :=
  Spectrum.idealNorm_pow hx I n

/-! ### Logarithmic model formulas -/

@[simp]
theorem idealLog_bot (x : Berk k A) : idealLog (⊥ : Ideal A) x = ⊥ :=
  Spectrum.idealLog_bot x.toSpectrum

theorem idealLog_top {x : Berk k A} (hx : IsBounded x) :
    idealLog (⊤ : Ideal A) x = 0 :=
  Spectrum.idealLog_top hx

theorem idealLog_sup {x : Berk k A} (hx : IsBounded x) (I J : Ideal A) :
    idealLog (I ⊔ J) x = max (idealLog I x) (idealLog J x) :=
  (fun (_ : IsBounded x) => Spectrum.idealLog_sup I J x.toSpectrum) hx

theorem idealLog_mul {x : Berk k A} (hx : IsBounded x) (I J : Ideal A) :
    idealLog (I * J) x = idealLog I x + idealLog J x :=
  (fun (_ : IsBounded x) => Spectrum.idealLog_mul I J x.toSpectrum) hx

theorem idealLog_pow {x : Berk k A} (hx : IsBounded x) (I : Ideal A) (n : ℕ) :
    idealLog (I ^ n) x = (n : EReal) * idealLog I x :=
  Spectrum.idealLog_pow hx I n

/-- A logarithmic ideal function is the finite maximum of the logarithms of generators. -/
theorem idealLog_span_finset {x : Berk k A} (hx : IsBounded x) (S : Finset A) :
    idealLog (Ideal.span (S : Set A)) x = S.sup (fun a => logAbs a x) :=
  Spectrum.idealLog_span_finset hx S

/-- A finitely generated ideal defines a continuous logarithmic function on the bounded locus. -/
theorem continuousOn_idealLog_of_span_eq (I : Ideal A) (S : Finset A)
    (hI : Ideal.span (S : Set A) = I) :
    ContinuousOn (idealLog (k := k) I) {x : Berk k A | IsBounded x} :=
  (Spectrum.continuousOn_idealLog_of_span_eq I S hI).comp
    continuous_toSpectrum.continuousOn (fun _ hx => hx)

end Berk
end EnvelopeProperty
