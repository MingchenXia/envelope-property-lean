import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePurificationGammaReaderValue

/-! # The same original purification differential through its native Gamma reader

The actual all-section composite reader and the original native-equivalence
value law are composed. The exact original reader, coefficient restriction,
whole differential and module equality are read from those two checked terms.
No second sheaf, coefficient action or field triangle is constructed.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelMixedKummer NadelCanonicalMixed NadelCanonicalMixed.Split
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def purificationGammaDifferentialPiece : Nat → (Lean.Expr → Bool) → Lean.Expr → Option Lean.Expr
  | 0, _, _ => none
  | fuel + 1, p, e =>
    if p e then some e else
      match e with
      | .app f a => (purificationGammaDifferentialPiece fuel p f).orElse fun _ =>
          purificationGammaDifferentialPiece fuel p a
      | .mdata _ t => purificationGammaDifferentialPiece fuel p t
      | .proj _ _ t => purificationGammaDifferentialPiece fuel p t
      | _ => none

elab "originalPurificationGammaDifferentialValue%(" isoStx:term ", " wStx:term ")" : term => do
  let original ← Lean.Elab.Term.elabTerm isoStx none
  let w ← Lean.Elab.Term.elabTerm wStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let original ← Lean.instantiateMVars original
  let w ← Lean.instantiateMVars w
  unless original.isAppOf ``mixedPurificationSectionsIso && original.getAppArgs.size == 15 do
    throwError "expected the same original purification comparison"
  let .const _ levels := original.getAppFn | throwError "missing original universes"
  let readerLaw := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePurificationGammaReaderValue
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedPurificationOriginalGammaReaderValue
  let hReader := Lean.mkAppN (Lean.mkConst readerLaw levels) (original.getAppArgs ++ #[w])
  let readerType ← Lean.Meta.whnf (← Lean.Meta.inferType hReader)
  unless readerType.isAppOfArity ``Eq 3 do throwError "expected original composite-reader equality"
  let readerArgs := readerType.getAppArgs
  let readerRight ← Lean.Meta.zetaReduce (← Lean.instantiateMVars readerArgs[2]!)
  let .app readerFn nativeValuePlain := readerRight.consumeMData |
    throwError "missing the original Gamma reader value"
  unless nativeValuePlain.isAppOf ``ModuleRestrictionCarrier.toUnderlying &&
      nativeValuePlain.getAppArgs.size == 5 do
    throwError "expected the same original coefficient-restriction reader"
  let toPlain := nativeValuePlain.appFn!
  let some body ← Lean.Meta.delta? original (· == ``mixedPurificationSectionsIso) |
    throwError "could not read the original purification constructor"
  let ctor := (← Lean.Meta.zetaReduce body).consumeMData
  let ctorName := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCounit
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeRingEquivSectionsIso
  unless ctor.isAppOf ctorName && ctor.getAppArgs.size == 14 do
    throwError "expected the same original fourteen-argument purification constructor"
  let some ctorBody ← Lean.Meta.delta? ctor (· == ctorName) |
    throwError "could not read the original native equivalence"
  let ctorBody ← Lean.Meta.zetaReduce ctorBody
  let some E := purificationGammaDifferentialPiece 512 (·.isAppOf ``nativeEquivSectionsIso) ctorBody |
    throwError "missing the same original native equivalence"
  let hDifferential := Lean.mkAppN (Lean.mkConst ``nativeEquivSectionsIso_apply levels)
    (E.getAppArgs ++ #[w])
  let differentialType ← Lean.Meta.whnf (← Lean.Meta.inferType hDifferential)
  unless differentialType.isAppOfArity ``Eq 3 do
    throwError "expected original native differential value equality"
  let differentialArgs := differentialType.getAppArgs
  let .const _ [dLevel] := differentialType.getAppFn | throwError "missing differential equality universe"
  let .const _ [rLevel] := readerType.getAppFn | throwError "missing reader equality universe"
  let fn := Lean.mkLambda `w Lean.BinderInfo.default differentialArgs[0]!
    (Lean.mkApp readerFn (Lean.mkApp toPlain (Lean.mkBVar 0)))
  let mapped := Lean.mkAppN (Lean.mkConst ``congrArg [dLevel, rLevel])
    #[differentialArgs[0]!, readerArgs[0]!, differentialArgs[1]!, differentialArgs[2]!, fn, hDifferential]
  let mappedType ← Lean.Meta.whnf (← Lean.Meta.inferType mapped)
  unless mappedType.isAppOfArity ``Eq 3 do throwError "expected original mapped differential equality"
  let mappedArgs := mappedType.getAppArgs
  let readerEndpoint ← Lean.Meta.zetaReduce (← Lean.instantiateMVars readerArgs[2]!)
  let mappedEndpoint ← Lean.Meta.zetaReduce (← Lean.instantiateMVars mappedArgs[1]!)
  unless readerEndpoint.headBeta.consumeMData == mappedEndpoint.headBeta.consumeMData do
    throwError "the original Gamma reader and differential endpoints are not the same beta/zeta term"
  let proof := Lean.mkAppN (Lean.mkConst ``Eq.trans [rLevel])
    #[readerArgs[0]!, readerArgs[1]!, readerArgs[2]!, mappedArgs[2]!, hReader, mapped]
  let proof ← Lean.instantiateMVars proof
  if proof.hasMVar then throwError "unresolved metavariable in same original purification differential"
  return proof

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

/-- Every original native section is carried by the same original whole
canonical differential and then its literal original Gamma reader. -/
private theorem mixedPurificationOriginalGammaDifferentialValue
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A))
    (w : extendedMixedCanonicalModule (k := k) x N I σ u) :
    originalActionType%(originalPurificationGammaDifferentialValue%(
      mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame, w)) :=
  originalPurificationGammaDifferentialValue%(
    mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame, w)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
