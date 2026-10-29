import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationSections
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationInferredAction

/-! # The original mixed extension on its actual scalar-extension unit

The actual whole tensor formula is used on its original adjunction unit.
All module and ring data are read from the original comparison.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def originalMixedExtendedUnitPiece : Nat → (Lean.Expr → Bool) → Lean.Expr → Option Lean.Expr
  | 0, _, _ => none
  | fuel + 1, p, e =>
    if p e then some e else
      match e with
      | .app f a => (originalMixedExtendedUnitPiece fuel p f).orElse fun _ =>
          originalMixedExtendedUnitPiece fuel p a
      | .mdata _ t => originalMixedExtendedUnitPiece fuel p t
      | .proj _ _ t => originalMixedExtendedUnitPiece fuel p t
      | _ => none

elab "originalMixedExtendedUnitValue%(" isoStx:term ", " wStx:term ")" : term => do
  let iso ← Lean.Elab.Term.elabTerm isoStx none
  let w ← Lean.Elab.Term.elabTerm wStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let iso ← Lean.instantiateMVars iso
  let w ← Lean.instantiateMVars w
  unless iso.isAppOf ``mixedExtendedSectionsIso do throwError "expected original mixed extension"
  let .const _ levels := iso.getAppFn | throwError "missing original extension universes"
  let [level] := levels | throwError "unexpected original universe count"
  let it ← Lean.Meta.whnf (← Lean.Meta.inferType iso)
  unless it.isAppOf ``Iso do throwError "expected original comparison isomorphism"
  let ia := it.getAppArgs
  let source := ia[ia.size - 2]!
  unless source.isAppOf ``Functor.obj do throwError "expected original extended module"
  let sourceModule := source.getAppArgs.back!
  let some ext := originalMixedExtendedUnitPiece 1024
      (·.isAppOf ``ModuleCat.extendScalars) source |
    throwError "missing original scalar-extension functor"
  unless ext.getAppArgs.size == 5 do
    throwError "unexpected original scalar-extension prefix {ext.getAppArgs.size}"
  let unitLaw := ``ModuleCat.extendRestrictScalarsAdj_unit_app_apply
  let unitInfo ← Lean.getConstInfo unitLaw
  let hu := Lean.mkAppN (Lean.mkConst unitLaw (unitInfo.levelParams.map (fun _ => level)))
    (ext.getAppArgs ++ #[sourceModule, w])
  let ut ← Lean.Meta.whnf (← Lean.Meta.inferType hu)
  unless ut.isAppOfArity ``Eq 3 do throwError "expected original adjunction-unit value"
  let ua := ut.getAppArgs
  let tensorValue := ua[2]!.consumeMData
  unless tensorValue.isAppOf ``TensorProduct.tmul do throwError "expected original pure tensor"
  let tensorArgs := tensorValue.getAppArgs
  let s := tensorArgs[tensorArgs.size - 2]!
  let hs := Lean.mkAppN (Lean.mkConst ``mixedExtendedSectionsIso_tmul levels)
    (iso.getAppArgs ++ #[s, w])
  let st ← Lean.Meta.whnf (← Lean.Meta.inferType hs)
  unless st.isAppOfArity ``Eq 3 do throwError "expected original whole tensor value"
  let sa := st.getAppArgs
  let .app nativeFn _ := sa[1]!.consumeMData | throwError "missing original comparison value function"
  let .const _ [sourceLevel] := ut.getAppFn | throwError "missing source equality universe"
  let .const _ [targetLevel] := st.getAppFn | throwError "missing target equality universe"
  let hc := Lean.mkAppN (Lean.mkConst ``congrArg [sourceLevel, targetLevel])
    #[ua[0]!, sa[0]!, ua[1]!, ua[2]!, nativeFn, hu]
  return Lean.mkAppN (Lean.mkConst ``Eq.trans [targetLevel])
    #[sa[0]!, Lean.mkApp nativeFn ua[1]!, sa[1]!, sa[2]!, hc, hs]

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

/-- The original mixed scalar-extension comparison on every original native
source section, presented by its actual adjunction unit. This is a prefix of
the mixed E-square, not a commutation or counit normalization conclusion. -/
private theorem mixedExtendedSectionsIso_originalUnitValue
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A))
    (w : mixedCanonicalModuleOverBase (k := k) x N I σ u) :
    originalActionType%(originalMixedExtendedUnitValue%(
      mixedExtendedSectionsIso (k := k) x N I σ u hx hN htame, w)) :=
  originalMixedExtendedUnitValue%(
    mixedExtendedSectionsIso (k := k) x N I σ u hx hN htame, w)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
