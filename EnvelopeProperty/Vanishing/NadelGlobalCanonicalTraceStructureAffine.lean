import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverStructuralUnit
import Mathlib.RingTheory.Trace.Defs

/-! # The actual structure-sheaf trace on an original finite free affine chart

The original native affine section equivalences are reused. The actual
algebra trace is lifted through the existing quasicoherent equivalence;
no sheaf trace or matching certificate is supplied as data.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
open AlgebraicGeometry CategoryTheory Scheme.Modules
open CyclicSectionGlobalCoverStructuralUnit
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (A B : CommRingCat.{u}) [Algebra A B]

private instance unit_quasicoherent (X : Scheme.{u}) :
    (unitObj X).IsQuasicoherent := isInvertible_unit.isQuasicoherent

private instance affinePushforward_quasicoherent :
    ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (unitObj (Spec B))).IsQuasicoherent :=
  isQuasicoherent_pushforward_of_isAffineHom _

private def sourceQC :
    (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory :=
  ⟨(pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
    (unitObj (Spec B)), inferInstance⟩

private def targetQC :
    (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory :=
  ⟨unitObj (Spec A), inferInstance⟩

/-- The whole native section map is the original algebra trace, transported
by the original source and target affine section isomorphisms. -/
def affineStructureTraceSections [Module.Free A B] [Module.Finite A B] :
    (moduleSpecΓFunctor (R := A)).obj
        ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
          (unitObj (Spec B))) ⟶
      (moduleSpecΓFunctor (R := A)).obj (unitObj (Spec A)) :=
  (pushforwardSectionsEquiv (R := A) (S := B)).toModuleIso.hom ≫
    ModuleCat.ofHom (Algebra.trace A B) ≫ (unitSectionsEquiv A).toModuleIso.inv

/-- The actual original finite free affine structure trace, with its entire
native pushforward as source and its actual structure module as target. -/
def affineStructureTrace [Module.Free A B] [Module.Finite A B] :
    (pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (unitObj (Spec B)) ⟶ unitObj (Spec A) :=
  (((tildeEquiv (R := A)).inverse).preimage
    (X := sourceQC A B) (Y := targetQC A)
    (affineStructureTraceSections A B)).hom

/-- The SAME actual sheaf morphism induces the whole original native trace
on affine sections, not merely its value at the original unit. -/
theorem affineStructureTrace_sections [Module.Free A B] [Module.Finite A B] :
    (moduleSpecΓFunctor (R := A)).map (affineStructureTrace A B) =
      affineStructureTraceSections A B :=
  ((tildeEquiv (R := A)).inverse).map_preimage
    (X := sourceQC A B) (Y := targetQC A)
    (affineStructureTraceSections A B)

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
