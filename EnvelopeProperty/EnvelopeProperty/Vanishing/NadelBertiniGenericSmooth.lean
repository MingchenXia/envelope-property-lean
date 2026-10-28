import EnvelopeProperty.Vanishing.NadelBertiniGenericStalks
import Hironaka.Algebra.RegularSmooth.Stalk
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Perfect

/-! # Actual characteristic-zero generic-fibre smoothness

The perfect residue field and the regularity of the whole native fibre are
produced from the original total scheme and its actual coefficient structure.
No generic smoothness hypothesis or arbitrary auxiliary algebra is supplied.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniGenericSmooth
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X S : Scheme.{u}}

/-- The actual original base-field map to the residue field of an original point. -/
def pointScalar (p : S ⟶ Spec (.of k)) (s : S) : k →+* S.residueField s :=
  letI := p.stalkAlgebra s
  (S.residue s).hom.comp (algebraMap k (S.presheaf.stalk s))

/-- Characteristic zero is inherited through the actual structural residue map. -/
theorem residueField_charZero [CharZero k] (p : S ⟶ Spec (.of k)) (s : S) :
    CharZero (S.residueField s) :=
  charZero_of_injective_ringHom (pointScalar p s).injective

/-- Regularity of the original total scheme proves smoothness of the WHOLE actual
native generic fibre, without source integrality or dominance. -/
theorem genericFiber_smooth [CharZero k] [IsIntegral S] [IsRegular X]
    (p : S ⟶ Spec (.of k)) (f : X ⟶ S) [LocallyOfFiniteType f] :
    Smooth (f.fiberToSpecResidueField (genericPoint S)) := by
  let : CharZero (S.residueField (genericPoint S)) := residueField_charZero p _
  let : PerfectField (S.residueField (genericPoint S)) := PerfectField.ofCharZero
  let : IsRegular (f.fiber (genericPoint S)) :=
    NadelBertiniGenericStalks.genericFiber_isRegular f
  let : LocallyOfFiniteType (f.fiberToSpecResidueField (genericPoint S)) := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd _ _)
    infer_instance
  exact (Scheme.smooth_iff_isRegular (k := S.residueField (genericPoint S))
    (f.fiberToSpecResidueField (genericPoint S))).mpr inferInstance

/-- Smoothness of the original total space over the original characteristic-zero
field supplies the regularity used by the actual generic-fibre producer. -/
theorem genericFiber_smooth_of_smooth [CharZero k] [IsIntegral S]
    (p : S ⟶ Spec (.of k)) (f : X ⟶ S) [LocallyOfFiniteType f]
    (pX : X ⟶ Spec (.of k)) [Smooth pX] :
    Smooth (f.fiberToSpecResidueField (genericPoint S)) := by
  let : IsRegular X := (Scheme.smooth_iff_isRegular pX).mp inferInstance
  exact genericFiber_smooth p f

end EnvelopeProperty.Vanishing.NadelBertiniGenericSmooth
