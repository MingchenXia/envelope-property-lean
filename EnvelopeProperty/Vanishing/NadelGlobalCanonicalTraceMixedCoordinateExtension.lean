import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNativeExtendedPointValue
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRawAffineCanonicalCoordinateImage
import EnvelopeProperty.AlgGeom.Canonical.ModuleSpecGammaCarrier

/-! # The original mixed extension on the actual base coordinate generator

The actual mixed native pullback, its actual scalar-extension comparison,
and the raw coefficient-map coordinate theorem are composed. The target
keeps its original composite field structure; no target algebra is chosen.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalCoefficientOne_smul
    (S C : CommRingCat.{u}) (α : S →+* C) (M : ModuleCat.{u} C) (v : M) :
    α 1 • v = v := by
  rw [map_one, one_smul]

private def mixedExtendedCoordinatePiece : Nat → (Lean.Expr → Bool) → Lean.Expr → Option Lean.Expr
  | 0, _, _ => none
  | fuel + 1, p, e =>
    if p e then some e else
      match e with
      | .app f a => (mixedExtendedCoordinatePiece fuel p f).orElse fun _ => mixedExtendedCoordinatePiece fuel p a
      | .mdata _ t => mixedExtendedCoordinatePiece fuel p t
      | .proj _ _ t => mixedExtendedCoordinatePiece fuel p t
      | _ => none

private def mixedExtendedCoordinateProof
    (extStx mixedStx coordinateStx : Lean.Syntax) : Lean.Elab.Term.TermElabM Lean.Expr := do
  let ext ← Lean.Elab.Term.elabTerm extStx none
  let mixed ← Lean.Elab.Term.elabTerm mixedStx none
  let coordinate ← Lean.Elab.Term.elabTerm coordinateStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let ext ← Lean.instantiateMVars ext
  let mixed ← Lean.instantiateMVars mixed
  let coordinate ← Lean.instantiateMVars coordinate
  unless ext.isAppOf ``mixedExtendedSectionsIso && mixed.isAppOf ``mixedNativeCanonicalPullback do
    throwError "expected the original mixed extension and actual differential"
  let .const _ levels := ext.getAppFn | throwError "missing original mixed universes"
  let eqData (h : Lean.Expr) : Lean.MetaM (Lean.Expr × Array Lean.Expr) := do
    let t ← Lean.Meta.whnf (← Lean.instantiateMVars (← Lean.Meta.inferType h))
    unless t.isAppOfArity ``Eq 3 do throwError "expected an original coordinate equality"
    pure (t, t.getAppArgs)
  let sourceName := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNativeExtendedPointValue
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeExtended_originalPointValue
  let hSource := Lean.mkAppN (Lean.mkConst sourceName levels) (ext.getAppArgs ++ #[coordinate])
  let (st, sa) ← eqData hSource
  let hDifferential := Lean.mkAppN (Lean.mkConst ``mixedNativeCanonicalPullback_coordinate levels)
    mixed.getAppArgs
  let (dt, da) ← eqData hDifferential
  let sourceValue ← Lean.Meta.zetaReduce sa[2]!
  let .app scaledFn rawPoint := sourceValue.headBeta.consumeMData |
    throwError "missing original unit tensor coefficient"
  let rawPoint ← Lean.Meta.zetaReduce rawPoint
  let .app rawFn _ := rawPoint.headBeta.consumeMData |
    throwError "missing original middle differential value (constructor {rawPoint.ctorName}, head {rawPoint.getAppFn.constName?})"
  let some morphism := mixedExtendedCoordinatePiece 1024
      (·.isAppOf ``exteriorCotangentSheafMorphism) rawFn |
    throwError "missing original middle sheaf differential"
  let mo := morphism.getAppArgs
  unless mo.size == 7 && mo[5]!.isAppOfArity ``Spec.map 3 do
    throwError "unexpected original middle differential parameters"
  let ringMap := mo[5]!.getAppArgs
  let sourceRing := ringMap[0]!
  let targetRing := ringMap[1]!
  let phi := ringMap[2]!
  unless da[2]!.isAppOf ``affineCanonicalCoordinateSection do
    throwError "missing the original mixed target coordinate"
  let ca := da[2]!.getAppArgs
  unless ca.size == 6 do throwError "unexpected original affine coordinate parameters"
  let some extBody ← Lean.Meta.delta? ext (· == ``mixedExtendedSectionsIso) |
    throwError "could not read the original mixed tensor comparison"
  let ctor := (← Lean.Meta.zetaReduce extBody).consumeMData
  let ctorName := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceNative
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.actualTensorModuleIso
  unless ctor.isAppOf ctorName && ctor.getAppArgs.size == 8 do
    throwError "unexpected original whole tensor comparison"
  let actualM := ctor.getAppArgs[6]!
  let some moduleBody ← Lean.Meta.delta? actualM (· == ``extendedMixedCanonicalModule) |
    throwError "could not read the original whole target module"
  let moduleBody := (← Lean.Meta.zetaReduce moduleBody).consumeMData
  unless moduleBody.isAppOf ``CategoryTheory.Functor.obj && moduleBody.getAppArgs.size == 6 do
    throwError "missing the original native Gamma target"
  let mb := moduleBody.getAppArgs
  unless mb[4]!.isAppOf ``moduleSpecΓFunctor do throwError "missing the original Gamma functor"
  let originalTargetRing := mb[4]!.getAppArgs[0]!
  let targetModule := mb[5]!
  let sourceModule := Lean.mkAppN (Lean.mkConst ``exteriorCotangentSheaf levels)
    #[mo[2]!, mo[0]!, mo[1]!, mo[4]!, mo[6]!]
  let toRaw := Lean.mkAppN (Lean.mkConst ``ModuleSpecGammaCarrier.toRaw levels)
    #[sourceRing, sourceModule]
  let toNative := Lean.mkAppN (Lean.mkConst ``ModuleSpecGammaCarrier.toNative levels)
    #[originalTargetRing, targetModule]
  let sourceFn ← Lean.Meta.withLocalDeclD `originalNativeSource da[0]! fun v =>
    Lean.Meta.mkLambdaFVars #[v]
      (Lean.mkApp scaledFn (Lean.mkApp toNative (Lean.mkApp rawFn (Lean.mkApp toRaw v))))
  let .const _ [sLevel] := st.getAppFn | throwError "missing original extension equality universe"
  let .const _ [dLevel] := dt.getAppFn | throwError "missing original mixed equality universe"
  let mappedDifferential := Lean.mkAppN (Lean.mkConst ``congrArg [dLevel, sLevel])
    #[da[0]!, sa[0]!, da[1]!, da[2]!, sourceFn, hDifferential]
  let rawName := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRawAffineCanonicalCoordinateImage
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalRawAffineCanonicalCoordinateImage
  let hRaw := Lean.mkAppN (Lean.mkConst rawName levels)
    #[ca[0]!, ca[1]!, sourceRing, targetRing, ca[3]!, phi, mo[6]!, ca[5]!]
  let (rt, ra) ← eqData hRaw
  let targetFn ← Lean.Meta.withLocalDeclD `originalRawTarget ra[0]! fun v =>
    Lean.Meta.mkLambdaFVars #[v] (Lean.mkApp scaledFn (Lean.mkApp toNative v))
  let .const _ [rLevel] := rt.getAppFn | throwError "missing original raw equality universe"
  let mappedRaw := Lean.mkAppN (Lean.mkConst ``congrArg [rLevel, sLevel])
    #[ra[0]!, sa[0]!, ra[1]!, ra[2]!, targetFn, hRaw]
  let some alpha := mixedExtendedCoordinatePiece 1024
      (·.isAppOf ``Algebra.TensorProduct.includeLeftRingHom) scaledFn |
    throwError "missing the original unit-cover coefficient map"
  let nativeCoordinate := Lean.mkApp toNative ra[2]!
  let oneName := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCoordinateExtension
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalCoefficientOne_smul
  let hOne := Lean.mkAppN (Lean.mkConst oneName levels)
    #[ctor.getAppArgs[1]!, originalTargetRing, alpha, actualM, nativeCoordinate]
  let transProof (p q : Lean.Expr) : Lean.MetaM Lean.Expr := do
    let (pt, pa) ← eqData p
    let (_, qa) ← eqData q
    let .const _ eqLevels := pt.getAppFn | throwError "missing original equality universe"
    pure (Lean.mkAppN (Lean.mkConst ``Eq.trans eqLevels)
      #[pa[0]!, pa[1]!, pa[2]!, qa[2]!, p, q])
  let mut proof := hSource
  for h in [mappedDifferential, mappedRaw, hOne] do
    proof ← transProof proof h
  let finalProof ← Lean.instantiateMVars proof
  if finalProof.hasMVar then throwError "unresolved metavariable in original mixed coordinate proof"
  pure finalProof

elab "mixedExtendedCoordinateProof%(" e:term ", " d:term ", " w:term ")" : term =>
  mixedExtendedCoordinateProof e d w

elab "mixedExtendedCoordinateType%(" e:term ", " d:term ", " w:term ")" : term => do
  Lean.instantiateMVars (← Lean.Meta.inferType (← mixedExtendedCoordinateProof e d w))

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

/-- The exact coordinate source of the original purification is produced
from the actual base generator through the original mixed extension. -/
theorem mixedNativeExtended_originalCoordinateValue
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    mixedExtendedCoordinateType%(
      mixedExtendedSectionsIso (k := k) x N I σ u hx hN htame,
      mixedNativeCanonicalPullback (k := k) x N I σ u hx,
      affineCanonicalCoordinateSection k (.of A) n x) :=
  mixedExtendedCoordinateProof%(
    mixedExtendedSectionsIso (k := k) x N I σ u hx hN htame,
    mixedNativeCanonicalPullback (k := k) x N I σ u hx,
    affineCanonicalCoordinateSection k (.of A) n x)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
