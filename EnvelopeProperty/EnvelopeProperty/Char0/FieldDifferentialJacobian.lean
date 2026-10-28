import EnvelopeProperty.AlgGeom.Canonical.ExteriorFieldBaseChange
import EnvelopeProperty.Char0.RelativeDifferentialJacobian

/-!
# The literal original relative Jacobian under actual change of fields

Every changed-field differential basis is manufactured from the actual
pushout comparison. The entire coefficient matrix and its determinant
retain the SAME original ring-map images, with no determinant certificate.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0

open EnvelopeProperty.CanonicalGeometry
open scoped TensorProduct

universe u v

section Coefficients

variable {k L A A' : Type u} [Field k] [Field L] [CommRing A] [CommRing A']
  [Algebra k L] [Algebra k A] [Algebra k A'] [Algebra L A'] [Algebra A A']
  [IsScalarTower k L A'] [IsScalarTower k A A'] [Algebra.IsPushout k L A A']

/-- Every coordinate of every ENTIRE original differential form retains the literal coefficient image. -/
theorem fieldDifferentialBasis_repr_map {I : Type v}
    (b : Module.Basis I A (KaehlerDifferential k A)) (ω : KaehlerDifferential k A) (i : I) :
    (fieldDifferentialBasis (L := L) (A' := A') b).repr (KaehlerDifferential.map k L A A' ω) i =
      algebraMap A A' (b.repr ω i) := by
  rw [← kaehlerFieldBaseChange_one_tmul]
  change (b.baseChange A').repr
    ((KaehlerDifferential.tensorKaehlerEquiv k L A A').symm
      (KaehlerDifferential.tensorKaehlerEquiv k L A A' (1 ⊗ₜ[A] ω))) i = _
  rw [LinearEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul]
  simp only [Algebra.smul_def, mul_one]

end Coefficients

section Morphism

variable {k L R A R' A' : Type u} [Field k] [Field L]
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra k L] [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A]
  [Algebra k R'] [Algebra L R'] [Algebra R R'] [IsScalarTower k L R'] [IsScalarTower k R R']
  [Algebra k A'] [Algebra L A'] [Algebra A A'] [IsScalarTower k L A'] [IsScalarTower k A A']
  [Algebra R' A'] [IsScalarTower L R' A'] [Algebra R A']
  [IsScalarTower R R' A'] [IsScalarTower R A A']
  [Algebra.IsPushout k L R R'] [Algebra.IsPushout k L A A'] {n : ℕ}

/-- The ENTIRE actual changed-field differential matrix is the literal original entrywise coefficient image. -/
theorem relativeDifferentialMatrix_fieldBaseChange
    (bR : Module.Basis (Fin n) R (KaehlerDifferential k R))
    (bA : Module.Basis (Fin n) A (KaehlerDifferential k A)) :
    (algebraMap A A').mapMatrix (relativeDifferentialMatrix bR bA) =
      relativeDifferentialMatrix (fieldDifferentialBasis (L := L) (A' := R') bR)
        (fieldDifferentialBasis (L := L) (A' := A') bA) := by
  ext i j
  change algebraMap A A' (bA.repr (KaehlerDifferential.map k k R A (bR j)) i) =
    (fieldDifferentialBasis (L := L) (A' := A') bA).repr
      (KaehlerDifferential.map L L R' A' (fieldDifferentialBasis (L := L) (A' := R') bR j)) i
  rw [fieldDifferentialBasis_apply, kaehlerFieldBaseChange_naturality
    (k := k) (L := L) (R := R) (A := A) (R' := R') (A' := A')]
  exact (fieldDifferentialBasis_repr_map bA _ i).symm

/-- The SAME original relative Jacobian determinant retains its exact literal image when the base field changes. -/
theorem relativeDifferentialDet_fieldBaseChange
    (bR : Module.Basis (Fin n) R (KaehlerDifferential k R))
    (bA : Module.Basis (Fin n) A (KaehlerDifferential k A)) :
    algebraMap A A' (relativeDifferentialDet bR bA) =
      relativeDifferentialDet (fieldDifferentialBasis (L := L) (A' := R') bR)
        (fieldDifferentialBasis (L := L) (A' := A') bA) := by
  rw [relativeDifferentialDet, relativeDifferentialDet,
    (algebraMap A A').map_det, relativeDifferentialMatrix_fieldBaseChange
      (k := k) (L := L) (R := R) (A := A) (R' := R') (A' := A') bR bA]

end Morphism

end EnvelopeProperty.Char0
