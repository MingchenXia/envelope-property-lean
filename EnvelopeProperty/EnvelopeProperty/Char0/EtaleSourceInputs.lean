/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.PrincipalizationLeafJacobians
import Hironaka.Scheme.BlowUp.CoordinateSubspace.Smooth

/-!
# Source geometry derived from actual etale coordinates

Finite generation and pure smoothness are proved from the actual coordinate
map, so the literal BP producer no longer takes them as separate inputs.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory
open scoped Classical

universe u

section Ring

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

/-- Actual etale source coordinates imply finite type over the original base ring. -/
theorem finiteType_of_etale_coordinates (z : Fin n → R)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) : Algebra.FiniteType k R := by
  let _ := (MvPolynomial.aeval (R := k) z).toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin n) k) R :=
    IsScalarTower.of_algebraMap_eq fun c => ((MvPolynomial.aeval z).commutes c).symm
  have : Algebra.Etale (MvPolynomial (Fin n) k) R := hz.toAlgebra
  exact Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType k (MvPolynomial (Fin n) k))
    (inferInstance : Algebra.FiniteType (MvPolynomial (Fin n) k) R)

/-- Actual etale source coordinates imply the original structure map is smooth of the
coordinate dimension; pure smoothness is produced rather than supplied separately. -/
theorem smoothOfRelativeDimension_of_etale_coordinates (z : Fin n → R)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  let φ := (MvPolynomial.aeval (R := k) z).toRingHom
  have : Etale (Spec.map (CommRingCat.ofHom φ)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom φ)).mpr hz
  have : SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)))) :=
    CoordinateSubspace.smoothOfRelativeDimension_Spec_map_algebraMap_mvPolynomial k n
  have hcomp : SmoothOfRelativeDimension (0 + n)
      (Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)))) := inferInstance
  have hφ : CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)) ≫
      CommRingCat.ofHom φ = CommRingCat.ofHom (algebraMap k R) := by
    ext c
    exact (MvPolynomial.aeval z).commutes c
  rw [Nat.zero_add, ← Spec.map_comp, hφ] at hcomp
  exact hcomp

end Ring

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- A literal subalgebra's finite-generation input follows from its actual etale coordinates. -/
theorem fg_of_etale_coordinates (C : Subalgebra k K) {n : ℕ} (z : Fin n → C)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) : C.FG :=
  C.fg_iff_finiteType.mpr (finiteType_of_etale_coordinates z hz)

variable [CharZero k]

/-- Actual source etale coordinates supply all smoothness and finite-generation inputs of
the actual BP literal Jacobian tree producer internally. -/
theorem exists_etaleSource_principalization_literal_leaf_jacobians
    (C : Subalgebra k K) (n : ℕ) (I : Ideal C) (hI : I ≠ ⊥)
    (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
    ∃ S : Scheme.BlowUpSequence (Spec (.of C)),
      S = Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI) ∧
      SmoothOfRelativeDimension n (S.composite ≫ f) ∧
      EtaleMonomialJacobianReesCover C S.composite n (specIdealSheaf I) z := by
  let _ := smoothOfRelativeDimension_of_etale_coordinates z hz
  exact exists_affinePrincipalization_literal_leaf_jacobians C (fg_of_etale_coordinates C z hz)
    n I hI z hz

end EnvelopeProperty.Char0
