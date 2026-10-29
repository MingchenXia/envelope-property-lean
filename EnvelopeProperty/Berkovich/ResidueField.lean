/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.Basic
import EnvelopeProperty.Berkovich.ValuationCompletion
import EnvelopeProperty.Berkovich.SpectrumResidueField
import EnvelopeProperty.Berkovich.SpectrumBridge

/-!
# Completed residue fields of points of the analytification

Let `k` be a field with the trivial absolute value, `B` a commutative `k`-algebra and
`x ∈ (Spec B)^an = Berk k B`. Following Berkovich (*Spectral theory and analytic geometry over
non-Archimedean fields*, §1.2), the seminorm `|·|_x` has support a prime ideal `p_x = supp x`; it
induces an absolute value on the residue field `κ(x) = κ(p_x)` (the fraction field of `B ⧸ p_x`),
and the completion of `κ(x)` is the **completed residue field** `H(x)`. It is a complete
nonarchimedean valued field and `B → H(x)` preserves the seminorm: `‖b‖ = |b|_x`.

The constructors and proofs specialize the arbitrary-ring producers of
`EnvelopeProperty.Berkovich.SpectrumResidueField` through `Berk.toSpectrum`, preserving
the existing paper interface and its scalar-field structures.

These fields are used in FHX §5.5 (`lem:finite-flat-norm`) to describe the fibres of finite
morphisms: the points over `x` correspond to the factors of the Artinian algebra `H(x) ⊗_B A`
(see `EnvelopeProperty.Berkovich.Finite`).

## Main definitions

* `Berk.ResidueField x`: the residue field `κ(x) = κ(supp x)` (Mathlib's `Ideal.ResidueField`).
* `Berk.residueValuation x`: the valuation on `κ(x)` induced by `|·|_x`.
* `Berk.residueAbs x`: the same as an `AbsoluteValue κ(x) ℝ`.
* `Berk.H x`: the completed residue field, with instances `NormedField`, `CompleteSpace`,
  `IsUltrametricDist`, `Algebra B (H x)` and `Algebra k (H x)`.
* `Berk.toH x : B →+* H x`, with `‖toH x b‖ = |b|_x` (`Berk.norm_toH`).
* `Berk.ResidueField.map φ h`, `Berk.H.map φ h`: for a `k`-algebra map `φ : B → A` and points
  `y ∈ (Spec A)^an`, `x = φ^an(y)`, the isometric embeddings `κ(x) → κ(y)` and `H(x) → H(y)`
  compatible with `φ` (`Berk.H.map_toH`, `Berk.H.norm_map`).
-/

open scoped NNReal ENNReal Topology nonZeroDivisors

noncomputable section

namespace EnvelopeProperty

namespace Berk

open Berkovich

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]

/-! ### The residue field and its absolute value -/

/-- The residue field `κ(x)` of a point `x ∈ (Spec B)^an`: the residue field of `B` at the prime
ideal `supp x = {b | |b|_x = 0}`, i.e. the fraction field of `B ⧸ supp x`. -/
abbrev ResidueField (x : Berk k B) : Type _ :=
  Spectrum.ResidueField x.toSpectrum

theorem le_primeCompl_onQuot (x : Berk k B) :
    (B ⧸ x.val.supp)⁰ ≤ (x.val.onQuot le_rfl).supp.primeCompl :=
  Spectrum.le_primeCompl_onQuot x.toSpectrum

/-- The valuation on `κ(x)` induced by `|·|_x`: the extension of the valuation induced on
`B ⧸ supp x` to its fraction field. -/
def residueValuation (x : Berk k B) : Valuation x.ResidueField ℝ≥0 :=
  Spectrum.residueValuation x.toSpectrum

@[simp]
theorem residueValuation_algebraMap (x : Berk k B) (b : B) :
    x.residueValuation (algebraMap B x.ResidueField b) = x.val b :=
  Spectrum.residueValuation_algebraMap x.toSpectrum b

theorem residueValuation_eq_zero_iff (x : Berk k B) {z : x.ResidueField} :
    x.residueValuation z = 0 ↔ z = 0 :=
  Spectrum.residueValuation_eq_zero_iff x.toSpectrum

/-- The absolute value `κ(x) → ℝ` induced by `|·|_x`. -/
def residueAbs (x : Berk k B) : AbsoluteValue x.ResidueField ℝ :=
  Spectrum.residueAbs x.toSpectrum

@[simp]
theorem residueAbs_apply (x : Berk k B) (z : x.ResidueField) :
    x.residueAbs z = x.residueValuation z := rfl

theorem residueAbs_algebraMap (x : Berk k B) (b : B) :
    x.residueAbs (algebraMap B x.ResidueField b) = x.val b :=
  Spectrum.residueAbs_algebraMap x.toSpectrum b

theorem isNonarchimedean_residueAbs (x : Berk k B) : IsNonarchimedean x.residueAbs :=
  Spectrum.isNonarchimedean_residueAbs x.toSpectrum

/-! ### The completed residue field -/

/-- The **completed residue field** `H(x)` of a point `x ∈ (Spec B)^an` (Berkovich, §1.2): the
completion of `κ(x)` with respect to the absolute value induced by `|·|_x`. It is a complete
nonarchimedean normed field (instances `NormedField`, `CompleteSpace`, `IsUltrametricDist`); its
norm may be trivial (e.g. for the trivial valuation `x = triv`). -/
def H (x : Berk k B) : Type _ :=
  Spectrum.H x.toSpectrum

instance (x : Berk k B) : NormedField (H x) :=
  inferInstanceAs (NormedField (UniformSpace.Completion (WithAbs x.residueAbs)))

instance (x : Berk k B) : CompleteSpace (H x) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (WithAbs x.residueAbs)))

instance (x : Berk k B) : Inhabited (H x) := ⟨0⟩

/-- The embedding `κ(x) → H(x)`; it is isometric (`Berk.norm_residueToH`) with dense image
(`Berk.denseRange_residueToH`). -/
def residueToH (x : Berk k B) : x.ResidueField →+* H x :=
  Spectrum.residueToH x.toSpectrum

theorem norm_residueToH (x : Berk k B) (z : x.ResidueField) :
    ‖x.residueToH z‖ = x.residueAbs z :=
  Spectrum.norm_residueToH x.toSpectrum z

theorem denseRange_residueToH (x : Berk k B) : DenseRange x.residueToH :=
  Spectrum.denseRange_residueToH x.toSpectrum

instance (x : Berk k B) : IsUltrametricDist (WithAbs x.residueAbs) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun a b =>
    x.isNonarchimedean_residueAbs a.ofAbs b.ofAbs

instance (x : Berk k B) : IsUltrametricDist (H x) :=
  inferInstanceAs (IsUltrametricDist (UniformSpace.Completion (WithAbs x.residueAbs)))

/-- The ring homomorphism `B → H(x)` preserves the seminorm: `‖toH x b‖ = |b|_x`. -/
def toH (x : Berk k B) : B →+* H x :=
  Spectrum.toH x.toSpectrum

theorem toH_apply (x : Berk k B) (b : B) :
    x.toH b = x.residueToH (algebraMap B x.ResidueField b) := rfl

@[simp]
theorem norm_toH (x : Berk k B) (b : B) : ‖x.toH b‖ = x.val b :=
  Spectrum.norm_toH x.toSpectrum b

@[simp]
theorem nnnorm_toH (x : Berk k B) (b : B) : ‖x.toH b‖₊ = x.val b :=
  Spectrum.nnnorm_toH x.toSpectrum b

theorem toH_eq_zero_iff (x : Berk k B) {b : B} : x.toH b = 0 ↔ x.val b = 0 :=
  Spectrum.toH_eq_zero_iff x.toSpectrum

theorem ker_toH (x : Berk k B) : RingHom.ker x.toH = x.val.supp :=
  Spectrum.ker_toH x.toSpectrum

instance (x : Berk k B) : Algebra x.ResidueField (H x) := x.residueToH.toAlgebra

instance (x : Berk k B) : Algebra B (H x) := x.toH.toAlgebra

instance (x : Berk k B) : Algebra k (H x) := (x.toH.comp (algebraMap k B)).toAlgebra

theorem algebraMap_residueField_H (x : Berk k B) :
    algebraMap x.ResidueField (H x) = x.residueToH := rfl

theorem algebraMap_H (x : Berk k B) : algebraMap B (H x) = x.toH := rfl

instance (x : Berk k B) : IsScalarTower k B (H x) := IsScalarTower.of_algebraMap_eq fun _ => rfl

instance (x : Berk k B) : IsScalarTower B x.ResidueField (H x) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem norm_algebraMap_H (x : Berk k B) (b : B) : ‖algebraMap B (H x) b‖ = x.val b :=
  Spectrum.norm_algebraMap_H x.toSpectrum b

/-- The field `k` maps isometrically (for the trivial absolute value) to `H(x)`. -/
theorem norm_algebraMap_k_H (x : Berk k B) {c : k} (hc : c ≠ 0) :
    ‖algebraMap k (H x) c‖ = 1 := by
  change ‖Spectrum.toH x.toSpectrum (algebraMap k B c)‖ = 1
  rw [Spectrum.norm_toH]
  change (x.val (algebraMap k B c) : ℝ) = 1
  rw [x.val_algebraMap c hc, NNReal.coe_one]

end Berk

namespace Berk

open Berkovich

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]

/-! ### Functoriality -/

section map

variable {A : Type*} [CommRing A] [Algebra k A]

/-- The support of `φ^an(y)` is the preimage of the support of `y`. -/
theorem supp_comap (φ : B →ₐ[k] A) (y : Berk k A) :
    (comap φ y).val.supp = y.val.supp.comap (φ : B →+* A) :=
  Spectrum.supp_comap φ.toRingHom y.toSpectrum

/-- For `x = φ^an(y)`, the embedding of residue fields `κ(x) → κ(y)` induced by `φ`. -/
def ResidueField.map (φ : B →ₐ[k] A) {x : Berk k B} {y : Berk k A} (h : comap φ y = x) :
    x.ResidueField →+* y.ResidueField :=
  Spectrum.ResidueField.map φ.toRingHom (x := x.toSpectrum) (y := y.toSpectrum) (congrArg toSpectrum h)

@[simp]
theorem ResidueField.map_algebraMap (φ : B →ₐ[k] A) {x : Berk k B} {y : Berk k A}
    (h : comap φ y = x) (b : B) :
    ResidueField.map φ h (algebraMap B x.ResidueField b) = algebraMap A y.ResidueField (φ b) :=
  Spectrum.ResidueField.map_algebraMap φ.toRingHom (x := x.toSpectrum) (y := y.toSpectrum) (congrArg toSpectrum h) b

/-- The embedding `κ(x) → κ(y)` is isometric. -/
@[simp]
theorem residueValuation_map (φ : B →ₐ[k] A) {x : Berk k B} {y : Berk k A}
    (h : comap φ y = x) (z : x.ResidueField) :
    y.residueValuation (ResidueField.map φ h z) = x.residueValuation z :=
  Spectrum.residueValuation_map φ.toRingHom (x := x.toSpectrum) (y := y.toSpectrum) (congrArg toSpectrum h) z

theorem residueAbs_map (φ : B →ₐ[k] A) {x : Berk k B} {y : Berk k A}
    (h : comap φ y = x) (z : x.ResidueField) :
    y.residueAbs (ResidueField.map φ h z) = x.residueAbs z :=
  Spectrum.residueAbs_map φ.toRingHom (x := x.toSpectrum) (y := y.toSpectrum) (congrArg toSpectrum h) z

/-- The isometric embedding `κ(x) → κ(y)` on the normed fields `WithAbs`. -/
def ResidueField.withAbsMap (φ : B →ₐ[k] A) {x : Berk k B} {y : Berk k A} (h : comap φ y = x) :
    WithAbs x.residueAbs →+* WithAbs y.residueAbs :=
  Spectrum.ResidueField.withAbsMap φ.toRingHom (x := x.toSpectrum) (y := y.toSpectrum) (congrArg toSpectrum h)

theorem ResidueField.norm_withAbsMap (φ : B →ₐ[k] A) {x : Berk k B} {y : Berk k A}
    (h : comap φ y = x) (z : WithAbs x.residueAbs) : ‖ResidueField.withAbsMap φ h z‖ = ‖z‖ :=
  Spectrum.ResidueField.norm_withAbsMap φ.toRingHom (x := x.toSpectrum) (y := y.toSpectrum) (congrArg toSpectrum h) z

/-- For `x = φ^an(y)`, the isometric embedding of completed residue fields `H(x) → H(y)`
induced by `φ` (the completion of `Berk.ResidueField.map`). For `x = comap φ y` itself, use
`H.map φ rfl : H (comap φ y) →+* H y`. -/
def H.map (φ : B →ₐ[k] A) {x : Berk k B} {y : Berk k A} (h : comap φ y = x) : H x →+* H y :=
  Spectrum.H.map φ.toRingHom (x := x.toSpectrum) (y := y.toSpectrum) (congrArg toSpectrum h)

/-- The embedding `H(x) → H(y)` is isometric. -/
@[simp]
theorem H.norm_map (φ : B →ₐ[k] A) {x : Berk k B} {y : Berk k A} (h : comap φ y = x)
    (z : H x) : ‖H.map φ h z‖ = ‖z‖ :=
  Spectrum.H.norm_map φ.toRingHom (x := x.toSpectrum) (y := y.toSpectrum) (congrArg toSpectrum h) z

theorem H.map_residueToH (φ : B →ₐ[k] A) {x : Berk k B} {y : Berk k A} (h : comap φ y = x)
    (z : x.ResidueField) : H.map φ h (x.residueToH z) = y.residueToH (ResidueField.map φ h z) :=
  Spectrum.H.map_residueToH φ.toRingHom (x := x.toSpectrum) (y := y.toSpectrum) (congrArg toSpectrum h) z

/-- The square `B → H(x) → H(y)`, `B → A → H(y)` commutes. -/
@[simp]
theorem H.map_toH (φ : B →ₐ[k] A) {x : Berk k B} {y : Berk k A} (h : comap φ y = x) (b : B) :
    H.map φ h (x.toH b) = y.toH (φ b) :=
  Spectrum.H.map_toH φ.toRingHom (x := x.toSpectrum) (y := y.toSpectrum) (congrArg toSpectrum h) b

theorem H.map_comp_toH (φ : B →ₐ[k] A) {x : Berk k B} {y : Berk k A} (h : comap φ y = x) :
    (H.map φ h).comp x.toH = y.toH.comp (φ : B →+* A) :=
  Spectrum.H.map_comp_toH φ.toRingHom (x := x.toSpectrum) (y := y.toSpectrum) (congrArg toSpectrum h)

end map

end Berk

end EnvelopeProperty
