import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceUnitOriginalGammaDifferentialValue
import EnvelopeProperty.AlgGeom.Canonical.NativeCoordinateImageGammaDomain

/-! # The original unit comparison on native coordinate forms

The source coordinate identity is used inside the original native source
carrier. The target-linear differential retains its original whole data.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def unitOriginalNativeCoordinatePiece : Nat → (Lean.Expr → Bool) → Lean.Expr → Option Lean.Expr
  | 0, _, _ => none
  | fuel + 1, p, e =>
    if p e then some e else
      match e with
      | .app f a => (unitOriginalNativeCoordinatePiece fuel p f).orElse fun _ => unitOriginalNativeCoordinatePiece fuel p a
      | .mdata _ t => unitOriginalNativeCoordinatePiece fuel p t
      | .proj _ _ t => unitOriginalNativeCoordinatePiece fuel p t
      | _ => none

elab "unitOriginalNativeCoordinateProof%(" isoStx:term ", " fieldStx:term ", " zStx:term ")" : term => do
  let iso ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm isoStx none)
  let z ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm zStx none)
  let fieldEq ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm fieldStx none)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let fieldEq ← Lean.instantiateMVars fieldEq
  unless iso.isAppOf ``unitBaseSectionsIso do throwError "expected original unit comparison"
  let some body ← Lean.Meta.delta? iso (· == ``unitBaseSectionsIso) |
    throwError "could not read original unit comparison"
  let body ← Lean.Meta.zetaReduce body
  let some E := unitOriginalNativeCoordinatePiece 1024 (·.isAppOf ``nativeSectionsIso) body |
    throwError "missing original native unit comparison"
  unless E.getAppArgs.size == 9 do throwError "unexpected original native constructor"
  let ea := E.getAppArgs
  let f := ea[4]!.consumeMData
  unless f.isAppOf ``affineStructuralMap && f.getAppArgs.size == 4 do
    throwError "expected original affine source structure"
  let fa := f.getAppArgs
  let .const _ levels := E.getAppFn | throwError "missing original universes"
  let sourceName := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineNaturality
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeCanonicalCoordinateSection_eq
  let hs := Lean.mkAppN (Lean.mkConst sourceName levels)
    #[fa[0]!, fa[1]!, fa[2]!, fa[3]!, ea[6]!, z]
  let st ← Lean.Meta.whnf (← Lean.Meta.inferType hs)
  unless st.isAppOfArity ``Eq 3 do throwError "expected original native source identity"
  let sa := st.getAppArgs
  let pointName := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceUnitOriginalGammaDifferentialValue
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.unitBaseOriginalGammaDifferentialValue
  let hp := Lean.mkAppN (Lean.mkConst pointName levels) (iso.getAppArgs ++ #[sa[2]!])
  let pt ← Lean.Meta.whnf (← Lean.Meta.inferType hp)
  unless pt.isAppOfArity ``Eq 3 do throwError "expected original unit point identity"
  let pa := pt.getAppArgs
  let lhs ← Lean.Meta.zetaReduce (← Lean.instantiateMVars pa[1]!)
  let .app outerFn unitValue := lhs.consumeMData | throwError "missing original outer value"
  let .app unitFn _ := unitValue.consumeMData | throwError "missing original adjunction unit"
  let fn ← Lean.Meta.withLocalDeclD `originalSource sa[0]! fun w =>
    Lean.Meta.mkLambdaFVars #[w] (Lean.mkApp outerFn (Lean.mkApp unitFn w))
  let .const _ [sourceLevel] := st.getAppFn | throwError "missing source equality universe"
  let .const _ [targetLevel] := pt.getAppFn | throwError "missing target equality universe"
  let hc := Lean.mkAppN (Lean.mkConst ``congrArg [sourceLevel, targetLevel])
    #[sa[0]!, pa[0]!, sa[1]!, sa[2]!, fn, hs]
  let hsNative := Lean.mkAppN (Lean.mkConst ``Eq.trans [targetLevel])
    #[pa[0]!, Lean.mkApp fn sa[1]!, pa[1]!, pa[2]!, hc, hp]
  let some T := unitOriginalNativeCoordinatePiece 1024 (fun t =>
      t.isAppOf ``Functor.mapIso && t.getAppArgs.size == 8 &&
        t.getAppArgs[4]!.isAppOf ``moduleSpecΓFunctor) body |
    throwError "missing original whole Gamma field transport"
  let ta := T.getAppArgs
  let gamma := ta[4]!
  unless gamma.getAppArgs.size == 1 do throwError "expected original bundled Gamma ring"
  let targetRing := gamma.getAppArgs[0]!
  let targetModule := ta[6]!
  let some targetStructure := unitOriginalNativeCoordinatePiece 1024
      (·.isAppOf ``affineStructuralMap) targetModule |
    throwError "missing original target field structure"
  unless targetStructure.getAppArgs.size == 4 do throwError "unexpected original target structure"
  let algKT := targetStructure.getAppArgs[3]!
  let image := Lean.mkAppN
    (Lean.mkConst ``CanonicalGeometry.NativeCoordinateImageGammaDomain.transported_sourceCoordinate levels)
    #[ea[0]!, ea[1]!, ea[2]!, targetRing, algKT, ea[4]!, ea[5]!, fieldEq, ea[6]!, z]
  let it ← Lean.Meta.whnf (← Lean.Meta.inferType image)
  unless it.isAppOfArity ``Eq 3 do throwError "expected checked original native target coordinate image"
  let ia := it.getAppArgs
  let stNative ← Lean.Meta.whnf (← Lean.Meta.inferType hsNative)
  let sn := stNative.getAppArgs
  return Lean.mkAppN (Lean.mkConst ``Eq.trans [targetLevel])
    #[sn[0]!, sn[1]!, sn[2]!, ia[2]!, hsNative, image]


variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (u : Fin q → Aˣ)

/-- The original native unit receives the coordinate form through its
same original source representative, before target coordinate comparison. -/
theorem unitBaseOriginalNativeCoordinateValue
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) (z : Fin n → A) :
    originalActionType%(unitOriginalNativeCoordinateProof%(
      unitBaseSectionsIso (k := k) x N u hx hN htame, unitBaseStructure (k := k) (A := A) N u, z)) :=
  unitOriginalNativeCoordinateProof%(unitBaseSectionsIso (k := k) x N u hx hN htame, unitBaseStructure (k := k) (A := A) N u, z)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
