import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationConstructorCore

/-! # Full original coefficient action on the restricted target itself

Restriction of scalars retains the original target-ring module action.
This formulation keeps the actual constructor's target object throughout.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  for (mod, short, original) in [
      (`EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCounit,
        `frozenNativeRingEquivSectionsIso,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeRingEquivSectionsIso),
      (`EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationConstructorCore,
        `frozenNativeOriginalConstructor_smul,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeOriginalConstructor_smul)] do
    let name := Lean.mkPrivateNameCore mod original
    unless (← Lean.getEnv).contains name do
      throwError "missing frozen original coefficient producer {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

private theorem nativeOriginalRestrictedConstructor_smul
    {K : Type u} [Field K] {S C P : CommRingCat.{u}} [Algebra K P]
    (α : S →+* C) (β : S →+* P)
    (f : Spec C ⟶ Spec (.of K)) (d : ℕ) [SmoothOfRelativeDimension d f]
    (e : C ≃+* P) (hs : β = e.toRingHom.comp α)
    (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ f = affineStructuralMap K P)
    (c : C)
    (w : (moduleSpecΓFunctor (R := C)).obj (exteriorCotangentSheaf (K := K) f d)) :
    (frozenNativeRingEquivSectionsIso (K := K) α β f d e hs he).hom (c • w) =
      e.toRingHom c •
        (frozenNativeRingEquivSectionsIso (K := K) α β f d e hs he).hom w := by
  exact frozenNativeOriginalConstructor_smul α β f d e hs he c w

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
