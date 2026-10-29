import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceUnitOriginalPointValue
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGammaNativeTransportCore

/-! # The original unit differential in its whole native target carrier

All ring and module data are extracted from the original native point law.
The ordinary readback is cached before specializing to the original cover.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def originalUnitGammaReaderPiece : Nat → (Lean.Expr → Bool) → Lean.Expr → Option Lean.Expr
  | 0, _, _ => none
  | fuel + 1, p, e =>
    if p e then some e else
      match e with
      | .app f a => (originalUnitGammaReaderPiece fuel p f).orElse fun _ =>
          originalUnitGammaReaderPiece fuel p a
      | .mdata _ t => originalUnitGammaReaderPiece fuel p t
      | .proj _ _ t => originalUnitGammaReaderPiece fuel p t
      | _ => none

elab "originalUnitGammaReaderValue%(" isoStx:term ", " wStx:term ")" : term => do
  let iso ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm isoStx none)
  let w ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm wStx none)
  unless iso.isAppOf ``unitBaseSectionsIso do throwError "expected original unit comparison"
  let .const _ levels := iso.getAppFn | throwError "missing original universes"
  let valueName := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceUnitOriginalPointValue
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.unitBaseOriginalPointValue
  let hv := Lean.mkAppN (Lean.mkConst valueName levels) (iso.getAppArgs ++ #[w])
  let vt ← Lean.Meta.whnf (← Lean.Meta.inferType hv)
  unless vt.isAppOfArity ``Eq 3 do throwError "expected original point equality"
  let va := vt.getAppArgs
  let rhs ← Lean.Meta.zetaReduce (← Lean.instantiateMVars va[2]!)
  let .app _ nativeValue := rhs.consumeMData | throwError "missing original native input value"
  let some T := originalUnitGammaReaderPiece 1024 (fun t =>
      t.isAppOf ``Functor.mapIso && t.getAppArgs.size == 8 &&
        t.getAppArgs[4]!.isAppOf ``moduleSpecΓFunctor) rhs |
    throwError "missing original Gamma field transport"
  let ta := T.getAppArgs
  let moduleIso := ta[7]!
  unless moduleIso.isAppOf ``eqToIso do throwError "expected original module equality"
  let readbackName := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGammaNativeTransportCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalGammaNativeTransport_value
  let hr := Lean.mkAppN (Lean.mkConst readbackName levels)
    #[ta[4]!.getAppArgs[0]!, ta[5]!, ta[6]!, moduleIso.getAppArgs.back!, nativeValue]
  let rt ← Lean.Meta.whnf (← Lean.Meta.inferType hr)
  unless rt.isAppOfArity ``Eq 3 do throwError "expected original native target readback"
  let .const _ eqLevels := vt.getAppFn | throwError "missing equality universes"
  let ra := rt.getAppArgs
  return Lean.mkAppN (Lean.mkConst ``Eq.trans eqLevels)
    #[va[0]!, va[1]!, va[2]!, ra[2]!, hv, hr]

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (u : Fin q → Aˣ)

/-- The same original Unit comparison is read through the whole original
Gamma transport, retaining both original module objects and their equality. -/
private theorem unitBaseOriginalGammaReaderValue
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A))
    (w : (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
      (exteriorCotangentSheaf (affineStructuralMap k (CommRingCat.of A)) n)) :
    originalActionType%(originalUnitGammaReaderValue%(
      unitBaseSectionsIso (k := k) x N u hx hN htame, w)) :=
  originalUnitGammaReaderValue%(unitBaseSectionsIso (k := k) x N u hx hN htame, w)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
