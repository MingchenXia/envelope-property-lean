/-
Copyright (c) 2026. All rights reserved.
-/
import Hironaka.Scheme.Smooth.EtaleCoordinates
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Actual differential bases and partial derivatives from étale coordinates

The polynomial differential basis transports through the actual formally étale
base-change map. This is the same Mathlib construction used by the neighboring
`BingWangEntropy.AffineCanonicalModule` and by this project's DVR differential
basis, specialized directly to the actual coordinate ring map.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory Module
open scoped Classical

universe u

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] {n : ℕ}

/-- The actual étale coordinate ring map produces the differential basis. -/
def etaleDifferentialBasis (v : Fin n → A) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    Basis (Fin n) A (KaehlerDifferential k A) := by
  let _ := (MvPolynomial.aeval (R := k) v).toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin n) k) A :=
    IsScalarTower.of_algebraMap_eq fun c => ((MvPolynomial.aeval v).commutes c).symm
  have : Algebra.Etale (MvPolynomial (Fin n) k) A := hv.toAlgebra
  exact (KaehlerDifferential.isBaseChange_of_formallyEtale k (MvPolynomial (Fin n) k) A).basis
    (KaehlerDifferential.mvPolynomialBasis k (Fin n))

/-- Its vectors are the actual differentials of the original chart functions. -/
theorem etaleDifferentialBasis_apply (v : Fin n → A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (i : Fin n) :
    etaleDifferentialBasis v hv i = KaehlerDifferential.D k A (v i) := by
  let _ := (MvPolynomial.aeval (R := k) v).toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin n) k) A :=
    IsScalarTower.of_algebraMap_eq fun c => ((MvPolynomial.aeval v).commutes c).symm
  have : Algebra.Etale (MvPolynomial (Fin n) k) A := hv.toAlgebra
  rw [etaleDifferentialBasis, IsBaseChange.basis_apply,
    KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D]
  congr 1
  exact MvPolynomial.aeval_X v i

/-- The dual coordinate functional composed with the universal derivation is an actual partial. -/
def etalePartialDeriv (v : Fin n → A) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (j : Fin n) : Derivation k A A :=
  ((etaleDifferentialBasis v hv).coord j).compDer (KaehlerDifferential.D k A)

/-- Actual coordinate partial derivatives have the Kronecker coordinate values. -/
theorem etalePartialDeriv_apply (v : Fin n → A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (i j : Fin n) :
    etalePartialDeriv v hv j (v i) = if i = j then 1 else 0 := by
  change (etaleDifferentialBasis v hv).coord j (KaehlerDifferential.D k A (v i)) = _
  rw [← etaleDifferentialBasis_apply v hv, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

/-- A derivation is determined by its values on actual étale coordinates. -/
theorem derivation_ext_etale (v : Fin n → A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (D E : Derivation k A A)
    (h : ∀ i, D (v i) = E (v i)) : D = E := by
  have hl : D.liftKaehlerDifferential = E.liftKaehlerDifferential := by
    apply (etaleDifferentialBasis v hv).ext
    intro i
    rw [etaleDifferentialBasis_apply, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    exact h i
  ext a
  rw [← Derivation.liftKaehlerDifferential_comp_D D,
    ← Derivation.liftKaehlerDifferential_comp_D E, hl]

/-- The actual coordinate Jacobian of a family, computed with the constructed partials. -/
def etaleJacobian (v : Fin n → A) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (z : Fin n → A) : A :=
  (Matrix.of fun i j => etalePartialDeriv v hv j (z i)).det

/-- An actual étale coordinate change has unit Jacobian. -/
theorem isUnit_etaleJacobian (v : Fin n → A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (z : Fin n → A)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    IsUnit (etaleJacobian v hv z) := by
  have h := (LinearEquiv.refl A (KaehlerDifferential k A)).isUnit_det
    (etaleDifferentialBasis z hz) (etaleDifferentialBasis v hv)
  have hm : (Matrix.of fun i j => etalePartialDeriv v hv j (z i)) =
      (LinearMap.toMatrix (etaleDifferentialBasis z hz) (etaleDifferentialBasis v hv)
        (LinearEquiv.refl A (KaehlerDifferential k A))).transpose := by
    ext i j
    simp only [Matrix.of_apply, Matrix.transpose_apply, LinearMap.toMatrix_apply,
      etaleDifferentialBasis_apply]
    rfl
  rw [etaleJacobian, hm, Matrix.det_transpose]
  exact h

section Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- An actual affine scheme chart supplies its differential basis through its actual étale map. -/
def schemeEtaleDifferentialBasis (f : X ⟶ Spec (.of k)) (U : X.affineOpens)
    (v : Fin n → Γ(X, U.1)) (hv : Etale (toAffineSpace f U.1 v)) :
    letI := f.sectionsAlgebra U.1
    Basis (Fin n) Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) := by
  let _ := f.sectionsAlgebra U.1
  exact etaleDifferentialBasis v ((etale_toAffineSpace_iff f U.2 v).mp hv)

/-- The basis produced from an actual scheme chart consists of its actual coordinate differentials. -/
theorem schemeEtaleDifferentialBasis_apply (f : X ⟶ Spec (.of k)) (U : X.affineOpens)
    (v : Fin n → Γ(X, U.1)) (hv : Etale (toAffineSpace f U.1 v)) (i : Fin n) :
    letI := f.sectionsAlgebra U.1
    schemeEtaleDifferentialBasis f U v hv i = KaehlerDifferential.D k Γ(X, U.1) (v i) := by
  let _ := f.sectionsAlgebra U.1
  exact etaleDifferentialBasis_apply v ((etale_toAffineSpace_iff f U.2 v).mp hv) i

end Scheme

end EnvelopeProperty.Char0
