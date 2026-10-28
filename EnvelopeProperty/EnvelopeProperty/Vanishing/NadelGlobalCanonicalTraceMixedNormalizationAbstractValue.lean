import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationConstructorCore

/-! # The native composite value before specialization of its modules -/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  let name := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationConstructorCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.outerCoefficientIso
  unless (← Lean.getEnv).contains name do
    throwError "missing original composite coefficient comparison"
  Lean.Elab.Command.modifyScope fun scope =>
    { scope with openDecls :=
      Lean.OpenDecl.explicit `frozenOuterCoefficientIso name :: scope.openDecls }

private theorem originalComposite_value
    {S C P : CommRingCat.{u}}
    (α : S →+* C) (β : S →+* P) (ρ : C →+* P)
    {M : ModuleCat C} {Q N : ModuleCat P}
    (E : M ≅ (ModuleCat.restrictScalars ρ).obj Q) (T : Q ≅ N)
    (hs : β = ρ.comp α) (w : M) :
    (frozenOuterCoefficientIso α β ρ E T hs).hom w = T.hom (E.hom w) := by
  rfl

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
