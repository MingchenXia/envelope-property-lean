import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureAffine

/-! # Whole native coefficient normalization of the actual affine trace

The original unit and pushforward section equivalences retain every
coefficient. The structural-unit law is proved from actual Spec naturality
and the native scalar trace identity, not supplied as a certificate.
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
    [Module.Free A B] [Module.Finite A B]

/-- Every native original section has exactly its whole original algebra
trace as coefficient under the actual sheaf trace. -/
theorem affineStructureTrace_apply
    (w : (moduleSpecΓFunctor (R := A)).obj
      ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (unitObj (Spec B)))) :
    unitSectionsEquiv A
        (((moduleSpecΓFunctor (R := A)).map (affineStructureTrace A B)).hom.toFun w) =
      Algebra.trace A B (pushforwardSectionsEquiv (R := A) (S := B) w) := by
  have h := congrArg (fun q => unitSectionsEquiv A (q.hom.toFun w))
    (affineStructureTrace_sections A B)
  have hv : unitSectionsEquiv A
      ((affineStructureTraceSections A B).hom.toFun w) =
      Algebra.trace A B (pushforwardSectionsEquiv (R := A) (S := B) w) := by
    change unitSectionsEquiv A ((unitSectionsEquiv A).symm
      (Algebra.trace A B (pushforwardSectionsEquiv (R := A) (S := B) w))) = _
    exact (unitSectionsEquiv A).apply_symm_apply _
  exact h.trans hv

/-- The actual structural-unit map followed by the SAME actual trace
multiplies EVERY original base coefficient by the whole free rank. -/
theorem affineStructureTrace_structuralUnit [Nontrivial A]
    (w : (moduleSpecΓFunctor (R := A)).obj (unitObj (Spec A))) :
    unitSectionsEquiv A
      (((moduleSpecΓFunctor (R := A)).map (affineStructureTrace A B)).hom.toFun
        (((moduleSpecΓFunctor (R := A)).map
          (SheafOfModules.unitToPushforwardObjUnit
            (Spec.map (CommRingCat.ofHom (algebraMap A B))).toRingCatSheafHom)).hom.toFun w)) =
      Module.finrank A B • unitSectionsEquiv A w := by
  have hu : pushforwardSectionsEquiv (R := A) (S := B)
      (((moduleSpecΓFunctor (R := A)).map
        (SheafOfModules.unitToPushforwardObjUnit
          (Spec.map (CommRingCat.ofHom (algebraMap A B))).toRingCatSheafHom)).hom.toFun w) =
      algebraMap A B (unitSectionsEquiv A w) :=
    ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))) w
  exact (affineStructureTrace_apply A B _).trans
    ((congrArg (Algebra.trace A B) hu).trans (Algebra.trace_algebraMap (unitSectionsEquiv A w)))

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
