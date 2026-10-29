import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedExtendedOriginalUnitValue
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationPullback

/-! # The original mixed differential followed by the actual whole extension

Adjunction-unit naturality is used on the original native differential.
The already checked original mixed extension supplies its whole-section value.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def mixedNativeExtendedPointPiece : Nat → (Lean.Expr → Bool) → Lean.Expr → Option Lean.Expr
  | 0, _, _ => none
  | fuel + 1, p, e =>
    if p e then some e else
      match e with
      | .app f a => (mixedNativeExtendedPointPiece fuel p f).orElse fun _ =>
          mixedNativeExtendedPointPiece fuel p a
      | .mdata _ t => mixedNativeExtendedPointPiece fuel p t
      | .proj _ _ t => mixedNativeExtendedPointPiece fuel p t
      | _ => none

private def originalModuleValueFn (f : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let linear ← Lean.Meta.mkAppM ``ModuleCat.Hom.hom #[f]
  Lean.Meta.mkAppM ``DFunLike.coe #[linear]

elab "originalMixedNativeExtendedPoint%(" fStx:term ", " isoStx:term ", " wStx:term ")" : term => do
  let f ← Lean.Elab.Term.elabTerm fStx none
  let iso ← Lean.Elab.Term.elabTerm isoStx none
  let w ← Lean.Elab.Term.elabTerm wStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let f ← Lean.instantiateMVars f
  let iso ← Lean.instantiateMVars iso
  let w ← Lean.instantiateMVars w
  unless iso.isAppOf ``mixedExtendedSectionsIso do throwError "expected original whole extension"
  let .const _ levels := iso.getAppFn | throwError "missing original universes"
  let [level] := levels | throwError "unexpected original universe count"
  let fw := Lean.mkApp (← originalModuleValueFn f) w
  let valueName := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedExtendedOriginalUnitValue
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedExtendedSectionsIso_originalUnitValue
  let hv := Lean.mkAppN (Lean.mkConst valueName levels) (iso.getAppArgs ++ #[fw])
  let vt ← Lean.Meta.whnf (← Lean.Meta.inferType hv)
  unless vt.isAppOfArity ``Eq 3 do throwError "expected original whole unit value"
  let va := vt.getAppArgs
  let .app nativeFn _ := va[1]!.consumeMData | throwError "missing original extension function"
  let it ← Lean.Meta.whnf (← Lean.Meta.inferType iso)
  let ia := it.getAppArgs
  let source := ia[ia.size - 2]!
  let some ext := mixedNativeExtendedPointPiece 1024
      (·.isAppOf ``ModuleCat.extendScalars) source |
    throwError "missing original scalar extension"
  unless ext.getAppArgs.size == 5 do throwError "unexpected original scalar-extension data"
  let adjName := ``ModuleCat.extendRestrictScalarsAdj
  let adjInfo ← Lean.getConstInfo adjName
  let adj := Lean.mkAppN (Lean.mkConst adjName (adjInfo.levelParams.map (fun _ => level))) ext.getAppArgs
  let unit ← Lean.Meta.mkAppM ``Adjunction.unit #[adj]
  let naturality ← Lean.Meta.mkAppM ``NatTrans.naturality #[unit, f]
  let nt ← Lean.Meta.whnf (← Lean.Meta.inferType naturality)
  unless nt.isAppOfArity ``Eq 3 do throwError "expected original adjunction naturality"
  let na := nt.getAppArgs
  let eval ← Lean.Meta.withLocalDeclD `originalArrow na[0]! fun h => do
    let value := Lean.mkApp (← originalModuleValueFn h) w
    Lean.Meta.mkLambdaFVars #[h] value
  let reversed ← Lean.Meta.mkAppM ``Eq.symm #[naturality]
  let point ← Lean.Meta.mkAppM ``congrArg #[eval, reversed]
  let lifted ← Lean.Meta.mkAppM ``congrArg #[nativeFn, point]
  let lt ← Lean.Meta.whnf (← Lean.Meta.inferType lifted)
  let la := lt.getAppArgs
  let .const _ targetLevels := vt.getAppFn | throwError "missing target equality universe"
  return Lean.mkAppN (Lean.mkConst ``Eq.trans targetLevels)
    #[va[0]!, la[1]!, la[2]!, va[2]!, lifted, hv]

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

/-- Every original base native section enters the actual left mixed extension
through the original adjunction-unit naturality. This is before purification. -/
private theorem mixedNativeExtended_originalPointValue
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A))
    (w : (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
      (exteriorCotangentSheaf (affineStructuralMap k (CommRingCat.of A)) n)) :
    originalActionType%(originalMixedNativeExtendedPoint%(
      mixedNativeCanonicalPullback (k := k) x N I σ u hx,
      mixedExtendedSectionsIso (k := k) x N I σ u hx hN htame, w)) :=
  originalMixedNativeExtendedPoint%(
    mixedNativeCanonicalPullback (k := k) x N I σ u hx,
    mixedExtendedSectionsIso (k := k) x N I σ u hx hN htame, w)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
