import EnvelopeProperty.DI.CechCupNaturality
import ModularCurves.EllipticCurve.PoleSheaf

/-! # Native tensor sections determine the original coherent tensor map

The sheafified tensor extensionality already proved for the DI cup
product is transported along the original monoidal tensor comparison.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
namespace EnvelopeProperty.SchemeTensorSectionExt
open Scheme.Modules
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory

/-- Equality on every original pure tensor determines the whole original
coherent tensor morphism, without any global generation assumption. -/
theorem tensorSection_hom_ext {X : Scheme.{u}} {M N P : X.Modules}
    {a b : M ⊗ N ⟶ P}
    (h : ∀ (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)),
      a.val.app (.op U) (ModularCurves.tensorSection M N U x y) =
        b.val.app (.op U) (ModularCurves.tensorSection M N U x y)) : a = b := by
  apply (cancel_epi (ModularCurves.monoidalTensorObjIso M N).inv).mp
  apply DI.CechAlexanderWhitneyProduct.tensorSection_hom_ext
  intro U x y
  exact h U x y

end EnvelopeProperty.SchemeTensorSectionExt
