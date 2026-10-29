import EnvelopeProperty.AlgGeom.AffineSchemeLocalDegrees
import EnvelopeProperty.AlgGeom.ResidualCurvePrincipalBalance
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Actual finite positive ORIGINAL residue degrees of projective closed points -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveClosedPointResidueDegrees
open AffineSchemeLocalDegrees FiniteClosedIdealLocalDegrees SchemeCoherentEulerIndex
variable {X : Scheme.{u}}

/-- The actual whole canonical point map's coefficients are literal original residue evaluation. -/
theorem fromSpecResidueField_appTop (x : X) :
    (X.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso (X.residueField x)).hom =
      X.Γevaluation x := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
  have hi : homOfLE (le_top : (⊤ : (Spec (X.presheaf.stalk x)).Opens) ≤ ⊤) = 𝟙 _ :=
    Subsingleton.elim _ _
  have hm := (Spec (X.presheaf.stalk x)).presheaf.map_id
    (Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens))
  simp only [hi, op_id, hm, Category.id_comp, Category.assoc,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rfl

/-- The original entire spectrum-section isomorphism preserves the SAME actual residue scalar action. -/
def sectionsResidueAlgEquiv {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) (x : X) :
    letI := structureSectionsAlgebra (X.fromSpecResidueField x ≫ p)
    letI := residueAlgebra p x
    Γ(Spec (X.residueField x), ⊤) ≃ₐ[k] X.residueField x := by
  let := structureSectionsAlgebra (X.fromSpecResidueField x ≫ p)
  let := residueAlgebra p x
  refine { (Scheme.ΓSpecIso (X.residueField x)).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro r
  change (Scheme.ΓSpecIso (X.residueField x)).hom
      ((X.fromSpecResidueField x ≫ p).appTop (baseScalar r)) =
    X.Γevaluation x (p.appTop (baseScalar r))
  have h := congrArg (fun q : Γ(X, ⊤) ⟶ X.residueField x => q (p.appTop (baseScalar r)))
    (fromSpecResidueField_appTop x)
  exact h

/-- Actual projective geometry gives finite residue degree for the SAME original closed point. -/
theorem residueField_finite {k : Type u} [Field k] (p : X ⟶ Spec (.of k))
    (hp : IsProjectiveFactorization p) (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := residueAlgebra p x
    Module.Finite k (X.residueField x) := by
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  let := structureSectionsAlgebra (X.fromSpecResidueField x ≫ p)
  let := residueAlgebra p x
  let : Module.Finite k Γ(Spec (X.residueField x), ⊤) :=
    structureSections_finite (X.fromSpecResidueField x) p hp
  exact Module.Finite.equiv (sectionsResidueAlgEquiv p x).toLinearEquiv

/-- The SAME original closed-point residue degree is genuinely positive. -/
theorem residue_finrank_pos {k : Type u} [Field k] (p : X ⟶ Spec (.of k))
    (hp : IsProjectiveFactorization p) (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := residueAlgebra p x
    0 < Module.finrank k (X.residueField x) := by
  let := residueAlgebra p x
  let := residueField_finite p hp x hx
  exact Module.finrank_pos

end EnvelopeProperty.ProjectiveClosedPointResidueDegrees

namespace EnvelopeProperty.ResidualFunctionFieldCurve
variable (k L : Type u) [Field k] [Field L] [Algebra (RatFunc k) L]
    [FiniteDimensional (RatFunc k) L]

/-- EVERY SAME original nongeneric residual-model point derives finite actual coefficient residue degree. -/
theorem point_residueField_finite (x : model k L) (hx : x ≠ genericPoint (model k L)) :
    letI := AffineSchemeLocalDegrees.residueAlgebra (baseMap k L) x
    Module.Finite k ((model k L).residueField x) :=
  ProjectiveClosedPointResidueDegrees.residueField_finite (baseMap k L)
    (structure_isProjectiveFactorization k L) x
    (CurveFiniteClosedSubschemes.isClosed_singleton (dimension_le k L) x hx)

/-- EVERY original nongeneric residual point has true strictly positive original coefficient degree. -/
theorem point_residue_finrank_pos (x : model k L) (hx : x ≠ genericPoint (model k L)) :
    letI := AffineSchemeLocalDegrees.residueAlgebra (baseMap k L) x
    0 < Module.finrank k ((model k L).residueField x) :=
  ProjectiveClosedPointResidueDegrees.residue_finrank_pos (baseMap k L)
    (structure_isProjectiveFactorization k L) x
    (CurveFiniteClosedSubschemes.isClosed_singleton (dimension_le k L) x hx)

end EnvelopeProperty.ResidualFunctionFieldCurve
