import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedExtendedTensorCoefficient
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationInferredAction

/-! # Every original mixed coefficient in the actual scalar extension

The generic whole tensor coefficient law is instantiated with the literal
original comparison constructor and its original ring/module arguments.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelCanonicalMixed
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

elab "originalMixedExtendedCoefficient%(" isoStx:term ", " sStx:term ", " bStx:term ", " wStx:term ")" : term => do
  let iso ← Lean.Elab.Term.elabTerm isoStx none
  let s ← Lean.Elab.Term.elabTerm sStx none
  let b ← Lean.Elab.Term.elabTerm bStx none
  let w ← Lean.Elab.Term.elabTerm wStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let iso ← Lean.instantiateMVars iso
  let s ← Lean.instantiateMVars s
  let b ← Lean.instantiateMVars b
  let w ← Lean.instantiateMVars w
  unless iso.isAppOf ``mixedExtendedSectionsIso do
    throwError "expected the original mixed scalar-extension comparison"
  let some body ← Lean.Meta.delta? iso (· == ``mixedExtendedSectionsIso) |
    throwError "could not read the original mixed scalar-extension constructor"
  let ctor := (← Lean.Meta.zetaReduce body).consumeMData
  let originalName := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceNative
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.actualTensorModuleIso
  unless ctor.isAppOf originalName && ctor.getAppArgs.size == 8 do
    throwError "unexpected original tensor comparison constructor"
  let .const _ levels := ctor.getAppFn | throwError "missing original tensor universes"
  let args := ctor.getAppArgs
  let carriers := (args.extract 0 3).map fun R =>
    Lean.mkApp (Lean.mkConst ``CommRingCat.carrier levels) R
  let rings := (args.extract 0 3).map fun R =>
    Lean.mkApp (Lean.mkConst ``CommRingCat.commRing levels) R
  let law := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedExtendedTensorCoefficient
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalWholeTensorCoefficient
  return Lean.mkAppN (Lean.mkConst law levels)
    (carriers ++ rings ++ args.extract 3 8 ++ #[s, b, w])

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

/-- Every original unit-cover tensor and every original mixed coefficient
retain their entire action through the actual mixed scalar extension.
No canonical commuting square or counit normalization is a premise. -/
theorem mixedExtendedSectionsIso_originalTensorCoefficient
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A))
    (s : UnitCover N u) (b : mixedRing x N I σ u)
    (w : mixedCanonicalModule (k := k) x N I σ u) :
    originalActionType%(originalMixedExtendedCoefficient%(
      mixedExtendedSectionsIso (k := k) x N I σ u hx hN htame, s, b, w)) :=
  originalMixedExtendedCoefficient%(
    mixedExtendedSectionsIso (k := k) x N I σ u hx hN htame, s, b, w)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
