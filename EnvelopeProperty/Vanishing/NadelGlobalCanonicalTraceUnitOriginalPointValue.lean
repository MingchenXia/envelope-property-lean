import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationInferredAction
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceNativeUnitPointValueCore
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceUnitBase

/-! # The original native unit point value before coordinate comparisons

The whole native section isomorphism and its field-transport map are taken
from the original unit-cover comparison, including their ring instances.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelCanonicalMixed
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def originalUnitPiece : Nat → (Lean.Expr → Bool) → Lean.Expr → Option Lean.Expr
  | 0, _, _ => none
  | fuel + 1, p, e =>
    if p e then some e else
      match e with
      | .app f a => (originalUnitPiece fuel p f).orElse fun _ =>
          originalUnitPiece fuel p a
      | .mdata _ t => originalUnitPiece fuel p t
      | .proj _ _ t => originalUnitPiece fuel p t
      | _ => none

elab "originalUnitPointValue%(" iso:term ", " w:term ")" : term => do
  let original ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm iso none)
  let w ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm w none)
  let some app := originalUnitPiece 512 (·.isAppOf ``unitBaseSectionsIso) original |
    throwError "expected original whole unit-cover comparison"
  let some body ← Lean.Meta.delta? app (· == ``unitBaseSectionsIso) |
    throwError "could not read original unit-cover constructor"
  let body ← Lean.Meta.zetaReduce body
  let some E := originalUnitPiece 512 (·.isAppOf ``nativeSectionsIso) body |
    throwError "missing original native unit-cover isomorphism"
  let some T := originalUnitPiece 512 (fun t =>
      t.isAppOf ``Functor.mapIso && t.getAppArgs.size == 8 &&
        t.getAppArgs[4]!.isAppOf ``moduleSpecΓFunctor) body |
    throwError "missing original unit-cover field transport"
  let tt ← Lean.Meta.whnf (← Lean.Meta.inferType T)
  unless tt.isAppOf ``Iso do
    throwError "expected original native transport isomorphism"
  let ta := tt.getAppArgs
  let Q := ta[ta.size - 1]!
  let thom ← Lean.Meta.mkAppM ``Iso.hom #[T]
  let law := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceNativeUnitPointValueCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeUnit_postcompose_point
  let .const _ levels := E.getAppFn | throwError "missing original universes"
  return Lean.mkAppN (Lean.mkConst law levels) (E.getAppArgs ++ #[Q, thom, w])

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (u : Fin q → Aˣ)

/-- The original unit-cover comparison evaluates its actual adjunction unit
as the original native canonical pullback followed by its target-linear field transport. This private probe has no coordinate/counit completion credit. -/
private theorem unitBaseOriginalPointValue
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A))
    (w : (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
      (exteriorCotangentSheaf (affineStructuralMap k (CommRingCat.of A)) n)) :
    originalActionType%(originalUnitPointValue%(
      unitBaseSectionsIso (k := k) x N u hx hN htame, w)) :=
  originalUnitPointValue%(unitBaseSectionsIso (k := k) x N u hx hN htame, w)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
