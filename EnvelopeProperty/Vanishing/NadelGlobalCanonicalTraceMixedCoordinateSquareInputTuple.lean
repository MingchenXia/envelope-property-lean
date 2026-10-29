import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePurificationCoordinateCore

/-! # The original mixed coordinate tuple in its original input carrier

The coefficient function is unchanged. Its type is the literal last binder
of the SAME original purification coordinate theorem, before specializing
that theorem's large native canonical-section equality.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

elab "originalMixedPurificationInputTupleType%(" purStx:term ")" : term => do
  let pur ← Lean.Elab.Term.elabTerm purStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let pur ← Lean.instantiateMVars pur
  unless pur.isAppOfArity ``mixedPurificationSectionsIso 15 do
    throwError "expected the same original purification constructor"
  let .const _ levels := pur.getAppFn | throwError "missing original purification universes"
  let partialProof := Lean.mkAppN
    (Lean.mkConst ``mixedPurificationOriginalCoordinateValue levels) pur.getAppArgs
  let partialType ← Lean.Meta.whnf (← Lean.Meta.inferType partialProof)
  let .forallE _ inputType _ _ := partialType |
    throwError "missing the literal original coordinate-tuple binder"
  return inputType

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

/-- The SAME coefficient tuple, typed by the SAME original purification
coordinate theorem's input, with every original ring-map value retained. -/
def mixedNativeCanonicalSquare_purificationInputCoordinates
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    originalMixedPurificationInputTupleType%(
      mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame) :=
  fun j => (mixedRightHom x N I σ u).hom
    (algebraMap A (mixedRing x N I σ u) (x j))

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
