import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Whole module transport in the original Gamma source category

The source category is the literal domain of moduleSpecGammaFunctor.
Both module objects and their equality are original parameters.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def originalGammaNativeReader
    (R : CommRingCat.{u}) (F G : (Spec (.of R)).Modules) (he : F = G)
    (w : (moduleSpecΓFunctor (R := R)).obj F) :
    (moduleSpecΓFunctor (R := R)).obj G :=
  (eqToHom he).val.app (op ⊤) w

private theorem originalGammaNativeTransport_value
    (R : CommRingCat.{u}) (F G : (Spec (.of R)).Modules) (he : F = G)
    (w : (moduleSpecΓFunctor (R := R)).obj F) :
    ((moduleSpecΓFunctor (R := R)).mapIso (eqToIso he)).hom w =
      originalGammaNativeReader R F G he w := by
  cases he
  rfl

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
