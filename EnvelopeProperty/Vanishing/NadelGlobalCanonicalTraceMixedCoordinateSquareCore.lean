import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCoordinateSquareCarrierCore
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCoordinateExtension
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNativeSquareMaps
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceUnitOriginalNativeCoordinateValue
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePurificationCoordinateCore
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedSchemeSquare
import EnvelopeProperty.AlgGeom.Canonical.ModuleRestrictionCarrier

/-! # The original mixed square on its actual coordinate generator

The existing original coordinate values are joined using the produced ring
square. The coordinate generator then detects equality of the entire maps.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelCanonicalMixed NadelCanonicalMixed.Split
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def coordinateSquareEqData (h : Lean.Expr) : Lean.MetaM (Array Lean.Expr) := do
  let t ← Lean.Meta.whnf (← Lean.Meta.inferType h)
  unless t.isAppOfArity ``Eq 3 do throwError "expected an original coordinate equality"
  pure t.getAppArgs

private def coordinateSquareTrans (p q : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let a ← coordinateSquareEqData p
  let b ← coordinateSquareEqData q
  let t ← Lean.Meta.whnf (← Lean.Meta.inferType p)
  let .const _ levels := t.getAppFn | throwError "missing original equality universes"
  pure <| Lean.mkAppN (Lean.mkConst ``Eq.trans levels) #[a[0]!, a[1]!, a[2]!, b[2]!, p, q]

private def coordinateSquareCongr
    (fn p target : Lean.Expr) (targetLevel : Lean.Level) : Lean.MetaM Lean.Expr := do
  let t ← Lean.Meta.whnf (← Lean.Meta.inferType p)
  unless t.isAppOfArity ``Eq 3 do throwError "expected the original coordinate congruence source"
  let .const _ [sourceLevel] := t.getAppFn | throwError "missing coordinate congruence universe"
  let a := t.getAppArgs
  pure <| Lean.mkAppN (Lean.mkConst ``congrArg [sourceLevel, targetLevel])
    #[a[0]!, target, a[1]!, a[2]!, fn, p]

private def coordinateSquarePiece : Nat → (Lean.Expr → Bool) → Lean.Expr → Option Lean.Expr
  | 0, _, _ => none
  | fuel + 1, p, e =>
    if p e then some e else
      match e with
      | .app f a => (coordinateSquarePiece fuel p f).orElse fun _ => coordinateSquarePiece fuel p a
      | .mdata _ t => coordinateSquarePiece fuel p t
      | .proj _ _ t => coordinateSquarePiece fuel p t
      | .lam _ _ t _ => coordinateSquarePiece fuel p t
      | _ => none

/-- Retain the original transport witness in a DATA reader.  Ordinary local
let bindings make the already proved witness application atomic; the Lean
DATA preprocessor can therefore keep that exact witness instead of building
a new specialized proof with the entire canonical sheaf in its indices. -/
private partial def coordinateSquareShareWitnessArgs
    (reader witness : Lean.Expr) (remaining : List Lean.Expr)
    (args : Array Lean.Expr) : Lean.MetaM Lean.Expr := do
  match remaining with
  | [] =>
    let shared := Lean.mkAppN witness.getAppFn args
    pure <| reader.replace fun e => if e == witness then some shared else none
  | arg :: rest =>
    if arg.isAtomic then
      coordinateSquareShareWitnessArgs reader witness rest (args.push arg)
    else
      Lean.Meta.withLetDecl `originalTransportArgument (← Lean.Meta.inferType arg) arg fun value => do
        let body ← coordinateSquareShareWitnessArgs reader witness rest (args.push value)
        Lean.Meta.mkLetFVars #[value] body (generalizeNondepLet := false)

private def coordinateSquareShareOriginalWitness (reader : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let name := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCounit
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeRingEquivSectionsIso._proof_1
  let some witness := coordinateSquarePiece 2048 (·.isAppOf name) reader |
    throwError "missing the original purification transport witness"
  if witness.hasLooseBVars then
    throwError "the original purification transport witness depends on the section binder"
  unless ← Lean.Meta.isProof witness do
    throwError "the original purification transport witness is not a proof"
  coordinateSquareShareWitnessArgs reader witness witness.getAppArgs.toList #[]

private def coordinateSquareValueFn (f : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let linear ← Lean.Meta.mkAppM ``ModuleCat.Hom.hom #[f]
  Lean.Meta.mkAppM ``DFunLike.coe #[linear]

elab "originalMixedCoordinateSquarePiece%(" stage:num ", " extStx:term ", " purStx:term ", " unitStx:term ", " pureStx:term ", " zStx:term ", " ringStx:term ")" : term => do
  let stage := stage.getNat
  let ext ← Lean.Elab.Term.elabTerm extStx none
  let pur ← Lean.Elab.Term.elabTerm purStx none
  let unit ← Lean.Elab.Term.elabTerm unitStx none
  let pureMap ← Lean.Elab.Term.elabTerm pureStx none
  let z ← Lean.Elab.Term.elabTerm zStx none
  let ringSquare ← Lean.Elab.Term.elabTerm ringStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let ext ← Lean.instantiateMVars ext
  let pur ← Lean.instantiateMVars pur
  let unit ← Lean.instantiateMVars unit
  let pureMap ← Lean.instantiateMVars pureMap
  let z ← Lean.instantiateMVars z
  let ringSquare ← Lean.instantiateMVars ringSquare
  let .const _ levels := ext.getAppFn | throwError "missing original coordinate universes"

  let he := Lean.mkAppN (Lean.mkConst ``mixedNativeExtended_originalCoordinateValue levels) ext.getAppArgs
  let ea ← coordinateSquareEqData he

  let hp := Lean.mkAppN (Lean.mkConst ``mixedPurificationOriginalCoordinateValue levels)
    (pur.getAppArgs ++ #[z])
  let pa ← coordinateSquareEqData hp
  if stage == 39 then
    let proof := Lean.mkAppN
      (Lean.mkConst
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_purification_input_coordinate_typed levels)
      ext.getAppArgs

    return proof
  let purificationLeft := pa[1]!.consumeMData
  unless purificationLeft.isAppOfArity ``ModuleRestrictionCarrier.toUnderlying 5 do
    throwError "missing the original purification target carrier reader"
  let purificationToNative := purificationLeft.appFn!
  -- The accepted S-source equality is retargeted BEFORE the original
  -- P-reader.  The checked original coordinate theorem is then consumed
  -- directly; no proposition is transported through a reader DATA alias.
  if stage == 40 || stage == 41 || stage == 42 then
    let originalValue := purificationLeft.appArg!.consumeMData
    let .app originalOuterFn originalCoordinate := originalValue |
      throwError "missing the original purification input value"
    let outerFnType ← Lean.Meta.whnf (← Lean.Meta.inferType originalOuterFn)
    let .forallE _ originalSource _ _ := outerFnType |
      throwError "missing the original purification S-source binder"
    let input := Lean.mkAppN
      (Lean.mkConst
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_restrictedInputValue levels)
      ext.getAppArgs
    let sourceSort ← Lean.Meta.whnf (← Lean.Meta.inferType originalSource)
    unless sourceSort.isSort do throwError "missing the original S-source universe"
    if stage == 40 then
      return Lean.mkAppN (Lean.mkConst ``Eq [sourceSort.sortLevel!])
        #[originalSource, input, originalCoordinate]
    if stage == 41 then
      return Lean.mkAppN
        (Lean.mkConst
          `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_restricted_input_eq_coordinate levels)
        ext.getAppArgs
    let sourceProof := Lean.mkAppN
      (Lean.mkConst
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_restricted_input_original_coordinate levels)
      ext.getAppArgs
    let originalReader ← Lean.Meta.withLocalDeclD `originalSourceSection originalSource fun w =>
      Lean.Meta.mkLambdaFVars #[w]
        (Lean.mkApp purificationToNative (Lean.mkApp originalOuterFn w))
    let checkedCoordinate := Lean.mkAppN
      (Lean.mkConst
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_purification_input_coordinate_typed levels)
      ext.getAppArgs
    return Lean.mkAppN (Lean.mkConst ``originalCoordinate_map_trans [sourceSort.sortLevel!])
      #[originalSource, pa[0]!, originalReader, input, originalCoordinate, pa[2]!,
        sourceProof, checkedCoordinate]
  let some extBody ← Lean.Meta.delta? ext (· == ``mixedExtendedSectionsIso) |
    throwError "missing original extension constructor"
  let ec := (← Lean.Meta.zetaReduce extBody).consumeMData.getAppArgs
  unless ec.size == 8 do throwError "unexpected original extension constructor"
  let some purBody ← Lean.Meta.delta? pur (· == ``mixedPurificationSectionsIso) |
    throwError "missing original purification constructor"
  let pc := (← Lean.Meta.zetaReduce purBody).consumeMData.getAppArgs
  unless pc.size == 14 do throwError "unexpected original purification constructor"
  let toNative := Lean.mkAppN (Lean.mkConst ``ModuleRestrictionCarrier.toUnderlying levels)
    #[pc[2]!, pc[3]!, pc[6]!, ec[6]!]
  -- Abstract the ENTIRE checked original value. Its outermost function is
  -- the P-carrier reader, not the C-to-P purification comparison.
  let readLaw := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePurificationGammaDifferentialValue
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedPurificationOriginalGammaDifferentialValue
  let purNativeFn ← Lean.Meta.withLocalDeclD `originalExtendedCoordinate ea[0]! fun v => do
    let hRead := Lean.mkAppN (Lean.mkConst readLaw levels)
      (pur.getAppArgs ++ #[Lean.mkApp toNative v])
    let r ← coordinateSquareEqData hRead
    Lean.Meta.mkLambdaFVars #[v] r[1]!
  let pt ← Lean.Meta.whnf (← Lean.Meta.inferType hp)
  let .const _ [targetLevel] := pt.getAppFn | throwError "missing original pure target universe"

  if stage == 0 then
    let proof ← coordinateSquareCongr purNativeFn he pa[0]! targetLevel

    return proof
  if stage == 10 then
    let liftedExt := Lean.mkAppN
      (Lean.mkConst
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_left_congr_coordinate levels)
      ext.getAppArgs
    let readback := Lean.mkAppN
      (Lean.mkConst
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_source_carrier_coordinate levels)
      ext.getAppArgs
    let proof ← coordinateSquareTrans liftedExt readback

    return proof
  if stage == 6 || stage == 7 || stage == 8 || stage == 9 || stage == 11 || stage == 12 then
    let nativeCoordinate := ea[2]!.consumeMData
    unless nativeCoordinate.isAppOfArity ``ModuleSpecGammaCarrier.toNative 3 do
      throwError "missing the original extension native-coordinate carrier"
    let nc := nativeCoordinate.getAppArgs
    let nativeType ← Lean.Meta.inferType (Lean.mkApp toNative ea[2]!)
    let nativeReader ← Lean.Meta.withLocalDeclD `originalNativeCoordinate nativeType fun w => do
      let hRead := Lean.mkAppN (Lean.mkConst readLaw levels) (pur.getAppArgs ++ #[w])
      let r ← coordinateSquareEqData hRead
      Lean.Meta.mkLambdaFVars #[w] r[1]!
    if stage == 6 then
      let proof := Lean.mkAppN (Lean.mkConst ``originalRestricted_readback levels)
        #[pc[2]!, pc[3]!, pc[6]!, ec[6]!, pa[0]!, nativeReader, ea[2]!]

      return proof
    if stage == 11 then
      let proof := Lean.mkAppN (Lean.mkConst ``originalRawNative_readback levels)
        #[nc[0]!, nc[1]!, pa[0]!, nativeReader, nc[2]!]

      return proof
    let purificationValue := purificationLeft.appArg!.consumeMData
    let .app _ originalRawCoordinate := purificationValue |
      throwError "missing the original raw purification source coordinate"
    let rawWedgeName := Lean.mkPrivateNameCore
      `EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore
      `EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore.rawWedge
    unless nc[2]!.isAppOf rawWedgeName && originalRawCoordinate.isAppOf rawWedgeName do
      throwError "expected the two same original raw-wedge constructors"
    let sourceSort ← Lean.Meta.whnf (← Lean.Meta.inferType nativeType)
    unless sourceSort.isSort do throwError "missing the original native source universe"
    let sourceLevel := sourceSort.sortLevel!
    if stage == 7 then

      return Lean.mkAppN (Lean.mkConst ``Eq [sourceLevel])
        #[nativeType, nc[2]!, originalRawCoordinate]
    if stage == 8 then

      return Lean.mkAppN (Lean.mkConst ``Eq.refl [sourceLevel]) #[nativeType, nc[2]!]
    let rawEquality := Lean.mkAppN
      (Lean.mkConst
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_source_raw_coordinate levels)
      ext.getAppArgs
    if stage == 12 then
      let sourceMap ← coordinateSquareCongr toNative he nativeType sourceLevel
      let identity := Lean.mkLambda `originalNativeSource Lean.BinderInfo.default nativeType (Lean.mkBVar 0)
      let restriction := Lean.mkAppN (Lean.mkConst ``originalRestricted_readback levels)
        #[pc[2]!, pc[3]!, pc[6]!, ec[6]!, nativeType, identity, ea[2]!]
      let raw := Lean.mkAppN (Lean.mkConst ``originalRawNative_readback levels)
        #[nc[0]!, nc[1]!, nativeType, identity, nc[2]!]
      let sourceEqData ← coordinateSquareEqData sourceMap
      let restrictionEqData ← coordinateSquareEqData restriction
      let rawEqData ← coordinateSquareEqData raw
      let coordinateEqData ← coordinateSquareEqData rawEquality
      let proof := Lean.mkAppN (Lean.mkConst ``originalCoordinate_four_step [sourceLevel])
        #[nativeType, sourceEqData[1]!, sourceEqData[2]!, restrictionEqData[2]!,
          rawEqData[2]!, coordinateEqData[2]!,
          sourceMap, restriction, raw, rawEquality]

      return proof
    let proof ← coordinateSquareCongr nativeReader rawEquality pa[0]! targetLevel

    return proof
  if stage == 16 || stage == 17 || (19 <= stage && stage <= 36) then
    let source := Lean.mkAppN
      (Lean.mkConst
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_source_point_coordinate levels)
      ext.getAppArgs
    let sourceData ← coordinateSquareEqData source
    let outerName := Lean.mkPrivateNameCore
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationConstructorCore
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.outerCoefficientIso
    let some actualOuter := coordinateSquarePiece 1024 (·.isAppOf outerName) purificationLeft |
      throwError "missing the same original outer coefficient constructor"
    let outerArgs := actualOuter.getAppArgs
    unless outerArgs.size == 12 do throwError "unexpected original outer coefficient constructor"
    let purificationValue := purificationLeft.appArg!.consumeMData
    let .app actualOuterFn _ := purificationValue |
      throwError "missing the actual original outer hom value"
    let actualFromNative := Lean.mkAppN
      (Lean.mkConst ``ModuleRestrictionCarrier.fromUnderlying levels)
      #[outerArgs[0]!, outerArgs[1]!, outerArgs[3]!, outerArgs[6]!]
    let fromType ← Lean.Meta.whnf (← Lean.Meta.inferType actualFromNative)
    let .forallE _ actualNativeDomain _ _ := fromType |
      throwError "missing the actual original native source domain"
    if stage == 16 then
      let sourceSort ← Lean.Meta.whnf (← Lean.Meta.inferType actualNativeDomain)
      unless sourceSort.isSort do throwError "missing actual original native source universe"

      return Lean.mkAppN (Lean.mkConst ``Eq [sourceSort.sortLevel!])
        #[actualNativeDomain, sourceData[1]!, sourceData[2]!]
    if stage == 17 then

      return source
    let alignedSource := Lean.mkAppN
      (Lean.mkConst
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_source_point_aligned_coordinate levels)
      ext.getAppArgs
    let helperPrefix := Lean.mkAppN (Lean.mkConst ``originalRestrictedCoordinate_finish levels)
      #[outerArgs[0]!, outerArgs[1]!]
    let alphaBinder ← Lean.Meta.whnf (← Lean.Meta.inferType helperPrefix)
    let .forallE _ expectedAlphaType _ _ := alphaBinder |
      throwError "missing original coefficient-map interface"
    if stage == 19 then

      return expectedAlphaType
    if stage == 20 then

      return outerArgs[3]!
    let nativeAlpha := Lean.mkAppN
      (Lean.mkConst
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_coefficientMap levels)
      ext.getAppArgs
    if stage == 21 || stage == 23 then

      return actualNativeDomain
    if stage == 22 then

      return sourceData[1]!
    if stage == 24 then

      return sourceData[2]!
    if stage == 27 || stage == 28 then
      let nativeInput := Lean.mkAppN
        (Lean.mkConst
          `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_inputValue levels)
        ext.getAppArgs
      let nativeCoordinate := Lean.mkAppN
        (Lean.mkConst
          `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_coordinateValue levels)
        ext.getAppArgs
      if stage == 28 then

        return alignedSource
      let sourceSort ← Lean.Meta.whnf (← Lean.Meta.inferType actualNativeDomain)
      unless sourceSort.isSort do throwError "missing exact native source-value universe"

      return Lean.mkAppN (Lean.mkConst ``Eq [sourceSort.sortLevel!])
        #[actualNativeDomain, nativeInput, nativeCoordinate]
    let helperToReader := Lean.mkAppN (Lean.mkConst ``originalRestrictedCoordinate_finish levels)
      #[outerArgs[0]!, outerArgs[1]!, nativeAlpha, outerArgs[6]!, pa[0]!]
    let readerBinder ← Lean.Meta.whnf (← Lean.Meta.inferType helperToReader)
    let .forallE _ expectedReaderType _ _ := readerBinder |
      throwError "missing exact original restricted reader interface"
    if stage == 25 then

      return expectedReaderType
    let outerFnType ← Lean.Meta.whnf (← Lean.Meta.inferType actualOuterFn)
    let .forallE _ actualRestrictedDomain _ _ := outerFnType |
      throwError "missing the actual original restricted source domain"
    let restrictedReader ← Lean.Meta.withLocalDeclD `originalRestrictedCoordinate actualRestrictedDomain fun w =>
      Lean.Meta.mkLambdaFVars #[w] (Lean.mkApp purificationToNative (Lean.mkApp actualOuterFn w))
    if stage == 26 then

      return ← coordinateSquareShareOriginalWitness restrictedReader
    let nativeInput := Lean.mkAppN
      (Lean.mkConst
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_inputValue levels)
      ext.getAppArgs
    let nativeReader := Lean.mkAppN
      (Lean.mkConst
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_restrictedReader levels)
      ext.getAppArgs
    let readerType ← Lean.Meta.whnf (← Lean.Meta.inferType nativeReader)
    let .forallE _ readerSource _ _ := readerType | throwError "missing the exact original S-reader source"
    let readerSourceSort ← Lean.Meta.whnf (← Lean.Meta.inferType readerSource)
    unless readerSourceSort.isSort do throwError "missing the exact S-source universe"
    let readerSourceLevel := readerSourceSort.sortLevel!
    let nativeFrom := Lean.mkAppN
      (Lean.mkConst ``ModuleRestrictionCarrier.fromUnderlying levels)
      #[outerArgs[0]!, outerArgs[1]!, nativeAlpha, outerArgs[6]!]
    if stage == 31 || stage == 33 then

      return readerSource
    if stage == 32 then

      return Lean.mkApp nativeFrom nativeInput
    if stage == 34 then

      return purificationValue.appArg!
    let restrictedInput := Lean.mkAppN
      (Lean.mkConst
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_restrictedInputValue levels)
      ext.getAppArgs
    let restrictedCoordinate := Lean.mkAppN
      (Lean.mkConst
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_restrictedCoordinateValue levels)
      ext.getAppArgs
    if stage == 35 then

      return Lean.mkAppN (Lean.mkConst ``Eq [readerSourceLevel])
        #[readerSource, restrictedInput, restrictedCoordinate]
    if stage == 36 then
      let nativeEquality := Lean.mkAppN
        (Lean.mkConst
          `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_native_input_eq_coordinate levels)
        ext.getAppArgs
      let proof ← coordinateSquareCongr nativeFrom nativeEquality readerSource readerSourceLevel

      return proof
    if stage == 29 || stage == 30 then
      if stage == 30 then

        return hp

      return Lean.mkAppN (Lean.mkConst ``Eq [targetLevel])
        #[pa[0]!, Lean.mkApp nativeReader restrictedCoordinate, pa[2]!]
    throwError "unsupported coordinate source stage"
  let hu := Lean.mkAppN (Lean.mkConst ``unitBaseOriginalNativeCoordinateValue levels)
    (unit.getAppArgs ++ #[ext.getAppArgs[7]!])
  let ua ← coordinateSquareEqData hu
  unless ua[2]!.isAppOfArity ``affineCanonicalCoordinateSection 6 do
    throwError "missing the original unit target coordinate section"
  let some pureBody ← Lean.Meta.delta? pureMap (· == ``pureNativeCanonicalPullback) |
    throwError "could not read original pure differential"
  let pureBody ← Lean.Meta.zetaReduce pureBody
  unless pureBody.isAppOf ``affineAlgebraCanonicalPullbackMap do
    throwError "unexpected original pure differential constructor"
  let hd := Lean.mkAppN (Lean.mkConst ``affineAlgebraCanonicalPullbackMap_coordinate_wedge levels)
    (pureBody.getAppArgs ++ #[ua[2]!.getAppArgs[5]!])
  let da ← coordinateSquareEqData hd
  let dt ← Lean.Meta.whnf (← Lean.Meta.inferType hd)
  let .const _ [rightLevel] := dt.getAppFn | throwError "missing original right target universe"
  let pureFn ← coordinateSquareValueFn pureMap
  let unitNativeFn := Lean.mkLambda `originalUnitCoordinate Lean.BinderInfo.default ua[0]!
    (Lean.mkApp pureFn (Lean.mkBVar 0))

  if stage == 2 then
    let proof ← coordinateSquareCongr unitNativeFn hu da[0]! rightLevel

    return proof
  let liftedUnit := Lean.mkAppN
    (Lean.mkConst
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_unit_congr_coordinate levels)
    ext.getAppArgs
  let rightRestricted ← coordinateSquareTrans liftedUnit hd
  -- Read the original pure path through the SAME target-carrier reader
  -- already present in the checked purification value.
  if stage == 3 then
    let proof ← coordinateSquareCongr purificationToNative rightRestricted pa[0]! targetLevel

    return proof
  let left := Lean.mkAppN
    (Lean.mkConst
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_left_coordinate levels)
    ext.getAppArgs
  let right := Lean.mkAppN
    (Lean.mkConst
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_right_coordinate levels)
    ext.getAppArgs
  let rightData ← coordinateSquareEqData right
  let rightReader := rightData[2]!.consumeMData
  unless rightReader.isAppOfArity ``ModuleRestrictionCarrier.toUnderlying 5 do
    throwError "missing the original pure target restriction identity"
  let targetReaderArgs := rightReader.getAppArgs
  let rightNativeCoordinate := targetReaderArgs[4]!
  if stage == 43 then
    let identity := Lean.mkLambda `originalPureTarget Lean.BinderInfo.default rightData[0]!
      (Lean.mkBVar 0)
    return Lean.mkAppN (Lean.mkConst ``originalRestricted_readback levels)
      #[targetReaderArgs[0]!, targetReaderArgs[1]!, targetReaderArgs[2]!,
        targetReaderArgs[3]!, rightData[0]!, identity, rightNativeCoordinate]
  let la ← coordinateSquareEqData left
  let raRestricted ← coordinateSquareEqData rightRestricted
  unless la[2]!.isAppOfArity ``affineCanonicalCoordinateSection 6 &&
      raRestricted[2]!.isAppOfArity ``affineCanonicalCoordinateSection 6 do
    throwError "missing the two original pure target coordinate wedges"
  let rt ← Lean.Meta.whnf (← Lean.Meta.inferType ringSquare)
  unless rt.isAppOfArity ``Eq 3 do throwError "missing the proved original ring square"
  let originalX := ext.getAppArgs[7]!
  let xType ← Lean.Meta.whnf (← Lean.Meta.inferType originalX)
  let .forallE _ index _ _ := xType | throwError "missing original coordinate index type"

  let tuple ← Lean.Meta.withLocalDeclD `j index fun j => do
    let h ← Lean.Meta.mkAppM ``RingHom.congr_fun #[ringSquare, Lean.mkApp originalX j]
    Lean.Meta.mkLambdaFVars #[j] h
  let tupleEq ← Lean.Meta.mkAppM ``funext #[tuple]
  unless rightNativeCoordinate.isAppOfArity ``affineCanonicalCoordinateSection 6 do
    throwError "missing the same original native pure coordinate value"
  let originalCoordinateFn := la[2]!.appFn!
  let coordinateFnType ← Lean.Meta.whnf (← Lean.Meta.inferType originalCoordinateFn)
  let .forallE _ coordinateTupleType _ _ := coordinateFnType |
    throwError "missing the original target coordinate-tuple domain"
  let leftTuple := la[2]!.appArg!
  let rightTuple := rightNativeCoordinate.appArg!
  let tupleSort ← Lean.Meta.whnf (← Lean.Meta.inferType coordinateTupleType)
  unless tupleSort.isSort do throwError "missing the original coordinate-tuple universe"
  if stage == 44 then
    return Lean.mkAppN (Lean.mkConst ``Eq [tupleSort.sortLevel!])
      #[coordinateTupleType, leftTuple, rightTuple]
  if stage == 45 then
    return tupleEq
  let originalRightCoordinate := Lean.mkApp originalCoordinateFn rightTuple
  if stage == 47 then
    return Lean.mkAppN (Lean.mkConst ``Eq [targetLevel])
      #[la[0]!, originalRightCoordinate, rightNativeCoordinate]
  if stage == 48 then
    return Lean.mkAppN (Lean.mkConst ``Eq.refl [targetLevel])
      #[la[0]!, originalRightCoordinate]
  if stage == 4 then
    let typedTupleLaw := Lean.mkAppN
      (Lean.mkConst
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_original_target_tuple levels)
      ext.getAppArgs
    let proof ← coordinateSquareCongr originalCoordinateFn typedTupleLaw la[0]! targetLevel
    return proof
  let wedgeEq := Lean.mkAppN
    (Lean.mkConst
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_wedge_coordinate levels)
    ext.getAppArgs
  let first ← coordinateSquareTrans left wedgeEq
  let aliasReadback := Lean.mkAppN
    (Lean.mkConst
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_original_right_coordinate levels)
    ext.getAppArgs
  let afterAlias ← coordinateSquareTrans first aliasReadback
  let targetReadback := Lean.mkAppN
    (Lean.mkConst
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedNativeCanonicalSquare_right_target_readback levels)
    ext.getAppArgs
  let targetReversed ← Lean.Meta.mkAppM ``Eq.symm #[targetReadback]
  let afterTarget ← coordinateSquareTrans afterAlias targetReversed
  let reversed ← Lean.Meta.mkAppM ``Eq.symm #[right]
  let proof ← Lean.instantiateMVars (← coordinateSquareTrans afterTarget reversed)
  if proof.hasMVar then throwError "unresolved metavariable in the original mixed coordinate square"

  return proof


end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
