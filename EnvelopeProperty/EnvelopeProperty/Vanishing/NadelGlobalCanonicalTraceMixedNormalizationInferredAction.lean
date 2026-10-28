import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationRestrictedConstructor

/-! # The original constructor's coefficient law, retaining its exact instances

The proof and its type are instantiated from the same original compiled
constructor. No second canonical module or quotient-ring instance is built.
The returned term is checked by the ordinary declaration kernel.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelMixedKummer NadelCanonicalMixed NadelCanonicalMixed.Split
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def originalConstructorIn : Nat → Lean.Name → Lean.Expr → Option Lean.Expr
  | 0, _, _ => none
  | fuel + 1, name, e =>
    if e.isAppOf name then some e else
      match e with
      | .app f a => (originalConstructorIn fuel name f).orElse fun _ =>
          originalConstructorIn fuel name a
      | .mdata _ t => originalConstructorIn fuel name t
      | .proj _ _ t => originalConstructorIn fuel name t
      | _ => none

elab "originalPurificationAction%(" iso:term ", " c:term ", " w:term ")" : term => do
  let original ← Lean.Elab.Term.elabTerm iso none
  let c ← Lean.Elab.Term.elabTerm c none
  let w ← Lean.Elab.Term.elabTerm w none
  let some app := originalConstructorIn 512 ``mixedPurificationSectionsIso original |
    throwError "expected the original purification comparison"
  let some body ← Lean.Meta.delta? app (· == ``mixedPurificationSectionsIso) |
    throwError "could not read the original constructor"
  let ctor := (← Lean.Meta.zetaReduce body).consumeMData
  let expected := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCounit
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeRingEquivSectionsIso
  let .const name levels := ctor.getAppFn |
    throwError "expected original constructor constant"
  unless name == expected && ctor.getAppArgs.size == 14 do
    throwError "unexpected original constructor parameters"
  let law := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationRestrictedConstructor
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeOriginalRestrictedConstructor_smul
  let info ← Lean.getConstInfo law
  unless info.levelParams.length == levels.length do
    throwError "unexpected original constructor universes"
  return Lean.mkAppN (Lean.mkConst law levels) (ctor.getAppArgs ++ #[c, w])

elab "originalActionType%(" proof:term ")" : term => do
  let proof ← Lean.Elab.Term.elabTerm proof none
  Lean.Meta.inferType proof

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

/-- Full coefficient action of the SAME original native purification.
Its exact original target-module action and quotient instances are retained. -/
theorem mixedPurificationOriginalCoefficientAction
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A))
    (c : extendedMixedRing x N I σ u)
    (w : extendedMixedCanonicalModule (k := k) x N I σ u) :
    originalActionType%(originalPurificationAction%(
      mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame, c, w)) :=
  originalPurificationAction%(
    mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame, c, w)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
