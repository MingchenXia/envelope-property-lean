import EnvelopeProperty.AlgGeom.NormalSurfaceStalk
import EnvelopeProperty.AlgGeom.SchemePointClosureCurve
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Genuine surface DVR stalks from their actual native residue degrees -/
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeSurfaceResidueDVR
variable {E : Type u} [Field E] {Y : Scheme.{u}} [IsIntegral Y]
    (b : Y ⟶ Spec (.of E)) [LocallyOfFiniteType b]

omit [IsIntegral Y] [LocallyOfFiniteType b] in
private theorem originalResidue_structure (z : Y) :
    letI := SchemePointClosureCurve.residueAlgebra z b
    Y.fromSpecResidueField z ≫ b =
      Spec.map (CommRingCat.ofHom (algebraMap E (Y.residueField z))) := by
  let := b.stalkAlgebra z
  let := SchemePointClosureCurve.residueAlgebra z b
  dsimp only [Scheme.fromSpecResidueField]
  rw [Category.assoc,SchemeStalkCoefficients.fromSpecStalk_structureMap,← Spec.map_comp]
  rfl

omit [IsIntegral Y] in
/-- The actual residue field at a closed point has genuinely finite coefficient degree. -/
theorem closedPoint_residue_finite (z : Y) (hz : IsClosed ({z} : Set Y)) :
    letI := SchemePointClosureCurve.residueAlgebra z b
    Module.Finite E (Y.residueField z) := by
  let := SchemePointClosureCurve.residueAlgebra z b
  let : IsClosedImmersion (Y.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hz
  let : LocallyOfFiniteType (Y.fromSpecResidueField z ≫ b) := inferInstance
  have hf : IsFinite (Y.fromSpecResidueField z ≫ b) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  rw [originalResidue_structure] at hf
  exact RingHom.finite_algebraMap.mp (IsFinite.SpecMap_iff _ |>.mp hf)

/-- Two actual function-field dimensions and one actual residue dimension
internally produce the genuine SAME normal original surface-stalk DVR. -/
theorem stalk_isDiscreteValuationRing (z : Y)
    (hfield : letI := b.stalkAlgebra (genericPoint Y); Algebra.trdeg E Y.functionField = 2)
    (hresidue : letI := SchemePointClosureCurve.residueAlgebra z b
      Algebra.trdeg E (Y.residueField z) = 1)
    [IsIntegrallyClosed (Y.presheaf.stalk z)] :
    IsDiscreteValuationRing (Y.presheaf.stalk z) := by
  let : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace b
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian b
  have hd : topologicalKrullDim Y = 2 :=
    SchemeFunctionFieldDimension.topologicalKrullDim_eq b 2 hfield
  have hng : z ≠ genericPoint Y := by
    intro hz
    subst z
    let := b.stalkAlgebra (genericPoint Y)
    let := SchemePointClosureCurve.residueAlgebra (genericPoint Y) b
    let e : Y.functionField ≃ₐ[E] Y.residueField (genericPoint Y) :=
      AlgEquiv.ofBijective
        { (Y.residue (genericPoint Y)).hom with commutes' := fun _ => rfl }
        ⟨(Y.residue (genericPoint Y)).hom.injective,residue_surjective⟩
    have hh := e.trdeg_eq
    rw [hfield,hresidue] at hh
    norm_num at hh
  have hnc : ¬ IsClosed ({z} : Set Y) := by
    intro hz
    let := SchemePointClosureCurve.residueAlgebra z b
    let := closedPoint_residue_finite b z hz
    have hh := trdeg_eq_zero (R := E) (A := Y.residueField z)
    rw [hresidue] at hh
    norm_num at hh
  exact NormalSurfaceStalk.stalk_isDiscreteValuationRing hd.le z hng hnc

end EnvelopeProperty.SchemeSurfaceResidueDVR
