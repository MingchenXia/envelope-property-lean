import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceUnitOriginalGammaReaderValue

/-! # The actual original native unit differential value

The actual Gamma reader theorem and its original native-domain function are retained.
Only the original native differential's checked value is substituted.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def gammaDifferentialValuePart : Nat → (Lean.Expr → Bool) → Lean.Expr → Option Lean.Expr
  | 0, _, _ => none
  | fuel + 1, p, e =>
    if p e then some e else
      match e with
      | .app f a => (gammaDifferentialValuePart fuel p f).orElse fun _ => gammaDifferentialValuePart fuel p a
      | .mdata _ t => gammaDifferentialValuePart fuel p t
      | .proj _ _ t => gammaDifferentialValuePart fuel p t
      | _ => none

elab "originalUnitGammaDifferentialValue%(" isoStx:term ", " wStx:term ")" : term => do
  let iso ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm isoStx none)
  let w ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm wStx none)
  unless iso.isAppOf ``unitBaseSectionsIso do throwError "expected the original unit comparison"
  let .const _ levels := iso.getAppFn | throwError "missing original unit universes"
  let pointName := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceUnitOriginalGammaReaderValue
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.unitBaseOriginalGammaReaderValue
  let hp := Lean.mkAppN (Lean.mkConst pointName levels) (iso.getAppArgs ++ #[w])
  let pt ← Lean.Meta.whnf (← Lean.Meta.inferType hp)
  unless pt.isAppOfArity ``Eq 3 do throwError "expected original point equality"
  let pa := pt.getAppArgs
  let rhs ← Lean.Meta.zetaReduce (← Lean.instantiateMVars pa[2]!)
  let .app targetFn _ := rhs.consumeMData | throwError "missing original target point function"
  let some delta := gammaDifferentialValuePart 512 (·.isAppOf ``nativeCanonicalPullbackMap) rhs |
    throwError "missing original native differential"
  let hd := Lean.mkAppN (Lean.mkConst ``nativeCanonicalPullbackMap_apply levels)
    (delta.getAppArgs ++ #[w])
  let dt ← Lean.Meta.whnf (← Lean.Meta.inferType hd)
  unless dt.isAppOfArity ``Eq 3 do throwError "expected original native differential equality"
  let .const _ [v] := pt.getAppFn | throwError "missing original point equality universe"
  let .const _ [s] := dt.getAppFn | throwError "missing original differential equality universe"
  let da := dt.getAppArgs
  let lifted := Lean.mkAppN (Lean.mkConst ``congrArg [s,v])
    #[da[0]!, pa[0]!, da[1]!, da[2]!, targetFn, hd]
  let lt ← Lean.Meta.whnf (← Lean.Meta.inferType lifted)
  let la := lt.getAppArgs
  return Lean.mkAppN (Lean.mkConst ``Eq.trans [v])
    #[pa[0]!, pa[1]!, pa[2]!, la[2]!, hp, lifted]

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (u : Fin q → Aˣ)

/-- Private actual differential readback; no target coordinate normalization
or counit/trace completion is asserted. -/
private theorem unitBaseOriginalGammaDifferentialValue
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A))
    (w : (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
      (exteriorCotangentSheaf (affineStructuralMap k (CommRingCat.of A)) n)) :
    originalActionType%(originalUnitGammaDifferentialValue%(
      unitBaseSectionsIso (k := k) x N u hx hN htame, w)) :=
  originalUnitGammaDifferentialValue%(
    unitBaseSectionsIso (k := k) x N u hx hN htame, w)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
