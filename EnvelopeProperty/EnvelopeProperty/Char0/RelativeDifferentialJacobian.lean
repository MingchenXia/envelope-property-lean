/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.EtaleDifferentials

/-!
# The relative differential determinant of actual affine algebra maps

The determinant is formed from the genuine map on Kähler differentials. Its
étale unit property and its generic nonvanishing come from actual differential
base-change isomorphisms.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open Module
open scoped Classical

variable {k R A : Type*} [CommRing k] [CommRing R] [CommRing A]
  [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A] {n : ℕ}

/-- The matrix is formed from the actual map on differentials and actual differential bases. -/
def relativeDifferentialMatrix (bR : Basis (Fin n) R (KaehlerDifferential k R))
    (bA : Basis (Fin n) A (KaehlerDifferential k A)) : Matrix (Fin n) (Fin n) A :=
  fun i j => bA.coord i (KaehlerDifferential.map k k R A (bR j))

/-- The actual affine relative differential determinant. -/
def relativeDifferentialDet (bR : Basis (Fin n) R (KaehlerDifferential k R))
    (bA : Basis (Fin n) A (KaehlerDifferential k A)) : A :=
  (relativeDifferentialMatrix bR bA).det

/-- Transport a genuine differential basis along the actual formally étale base-change map. -/
def differentialBasisBaseChange [Algebra.FormallyEtale R A]
    (bR : Basis (Fin n) R (KaehlerDifferential k R)) :
    Basis (Fin n) A (KaehlerDifferential k A) :=
  (KaehlerDifferential.isBaseChange_of_formallyEtale k R A).basis bR

/-- The transported basis consists of the actual images of the original differential vectors. -/
theorem differentialBasisBaseChange_apply [Algebra.FormallyEtale R A]
    (bR : Basis (Fin n) R (KaehlerDifferential k R)) (i : Fin n) :
    differentialBasisBaseChange (A := A) bR i = KaehlerDifferential.map k k R A (bR i) :=
  IsBaseChange.basis_apply _ _ _

/-- Formal étaleness makes the actual relative determinant a unit. -/
theorem isUnit_relativeDifferentialDet [Algebra.FormallyEtale R A]
    (bR : Basis (Fin n) R (KaehlerDifferential k R))
    (bA : Basis (Fin n) A (KaehlerDifferential k A)) :
    IsUnit (relativeDifferentialDet bR bA) := by
  have h := (LinearEquiv.refl A (KaehlerDifferential k A)).isUnit_det
    (differentialBasisBaseChange (A := A) bR) bA
  have hm : relativeDifferentialMatrix bR bA =
      LinearMap.toMatrix (differentialBasisBaseChange (A := A) bR) bA
        (LinearEquiv.refl A (KaehlerDifferential k A)) := by
    ext i j
    simp only [relativeDifferentialMatrix, LinearMap.toMatrix_apply,
      differentialBasisBaseChange_apply]
    rfl
  rw [relativeDifferentialDet, hm]
  exact h

/-- In genuine source and target étale coordinates, the differential determinant is the
literal Jacobian of the pulled-back source coordinate functions. -/
theorem relativeDifferentialDet_eq_etaleJacobian (z : Fin n → R)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) (v : Fin n → A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    relativeDifferentialDet (etaleDifferentialBasis z hz) (etaleDifferentialBasis v hv) =
      etaleJacobian v hv (fun i => algebraMap R A (z i)) := by
  have hm : relativeDifferentialMatrix (etaleDifferentialBasis z hz)
      (etaleDifferentialBasis v hv) =
      (Matrix.of fun i j => etalePartialDeriv v hv j (algebraMap R A (z i))).transpose := by
    ext i j
    simp only [relativeDifferentialMatrix, etaleDifferentialBasis_apply,
      KaehlerDifferential.map_D, Matrix.transpose_apply, Matrix.of_apply]
    rfl
  rw [relativeDifferentialDet, hm, Matrix.det_transpose]
  rfl

section Tower

variable {L : Type*} [CommRing L] [Algebra k L] [Algebra R L] [Algebra A L]
  [IsScalarTower k R L] [IsScalarTower k A L] [IsScalarTower R A L]

/-- The actual differential maps commute with the original scalar tower. -/
theorem kaehlerDifferential_map_comp_tower (z : KaehlerDifferential k R) :
    KaehlerDifferential.map k k A L (KaehlerDifferential.map k k R A z) =
      KaehlerDifferential.map k k R L z := by
  have h : ((KaehlerDifferential.map k k A L).restrictScalars R).comp
      (KaehlerDifferential.map k k R A) = KaehlerDifferential.map k k R L := by
    apply Derivation.liftKaehlerDifferential_unique
    ext r
    change KaehlerDifferential.map k k A L
      (KaehlerDifferential.map k k R A (KaehlerDifferential.D k R r)) =
        KaehlerDifferential.map k k R L (KaehlerDifferential.D k R r)
    simp only [KaehlerDifferential.map_D]
    rw [← IsScalarTower.algebraMap_apply R A L]
  exact LinearMap.congr_fun h z

/-- The actual relative determinant commutes with actual differential base change. -/
theorem relativeDifferentialDet_baseChange [Algebra.FormallyEtale A L]
    (bR : Basis (Fin n) R (KaehlerDifferential k R))
    (bA : Basis (Fin n) A (KaehlerDifferential k A)) :
    algebraMap A L (relativeDifferentialDet bR bA) =
      relativeDifferentialDet bR (differentialBasisBaseChange (A := L) bA) := by
  rw [relativeDifferentialDet, (algebraMap A L).map_det, relativeDifferentialDet]
  congr 1
  ext i j
  change algebraMap A L (bA.repr (KaehlerDifferential.map k k R A (bR j)) i) =
    ((KaehlerDifferential.isBaseChange_of_formallyEtale k A L).basis bA).repr
      (KaehlerDifferential.map k k R L (bR j)) i
  rw [← kaehlerDifferential_map_comp_tower (k := k) (R := R) (A := A) (L := L) (bR j)]
  exact ((KaehlerDifferential.isBaseChange_of_formallyEtale k A L).basis_repr_comp_apply bA _ _).symm

/-- The common formally étale target makes the actual relative determinant nonzero. -/
theorem relativeDifferentialDet_ne_zero_of_common_etale_target [Nontrivial L]
    [Algebra.FormallyEtale A L] [Algebra.FormallyEtale R L]
    (bR : Basis (Fin n) R (KaehlerDifferential k R))
    (bA : Basis (Fin n) A (KaehlerDifferential k A)) :
    relativeDifferentialDet bR bA ≠ 0 := by
  have h := isUnit_relativeDifferentialDet bR (differentialBasisBaseChange (A := L) bA)
  rw [← relativeDifferentialDet_baseChange] at h
  intro hzero
  rw [hzero, map_zero] at h
  exact h.ne_zero rfl

end Tower

/-- An actual common fraction field supplies generic nonvanishing of the actual differential
determinant; no generic-invertibility certificate is assumed. -/
theorem relativeDifferentialDet_ne_zero_of_common_fractionField (L : Type*) [Field L]
    [Algebra k L] [Algebra R L] [Algebra A L]
    [IsScalarTower k R L] [IsScalarTower k A L] [IsScalarTower R A L]
    [IsFractionRing R L] [IsFractionRing A L]
    (bR : Basis (Fin n) R (KaehlerDifferential k R))
    (bA : Basis (Fin n) A (KaehlerDifferential k A)) :
    relativeDifferentialDet bR bA ≠ 0 := by
  have : Algebra.FormallyEtale R L := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  have : Algebra.FormallyEtale A L := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  exact relativeDifferentialDet_ne_zero_of_common_etale_target (L := L) bR bA

end EnvelopeProperty.Char0
