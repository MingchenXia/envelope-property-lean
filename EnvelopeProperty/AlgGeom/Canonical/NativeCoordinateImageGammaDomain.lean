import EnvelopeProperty.AlgGeom.Canonical.NativeCoordinateImage
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGammaNativeTransportCore

/-! # Coordinate images in the original Gamma source category

This representation-specific producer reapplies the checked original square
and target coordinate laws with the square target explicitly the literal
source category of the same original Gamma functor. The original bundled
rings, their ring structures, entire coefficient map and field triangle are
retained. No coordinate naturality is reproved and no algebra data is replaced.
-/
noncomputable section
namespace EnvelopeProperty.CanonicalGeometry.NativeCoordinateImageGammaDomain
open AlgebraicGeometry CategoryTheory Opposite
open EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  for (source, short, original) in [
      (`EnvelopeProperty.AlgGeom.Canonical.NativeCoordinateImage,
        `checkedNativeImageProof,
        `EnvelopeProperty.CanonicalGeometry.NativeCoordinateImage.nativeCoordinateImageProof),
      (`EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGammaNativeTransportCore,
        `originalGammaNativeReader,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalGammaNativeReader),
      (`EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineNaturality,
        `originalAffineCoordinateImage,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeAffineCoordinateImage),
      (`EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineNaturality,
        `originalCanonicalCoordinateSection,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeCanonicalCoordinateSection_eq),
      (`EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore,
        `originalSquareCoordinateImage,
        `EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore.originalSquareCoordinateImage)] do
    let name := Lean.mkPrivateNameCore source original
    unless (← Lean.getEnv).contains name do throwError "missing original checked Gamma coordinate component"
    Lean.Elab.Command.modifyScope fun scope =>
      {scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls}

-- This is the original Mathlib carrier-instance spelling used by the native
-- target coordinate law. Its compiled body is exactly the original ring field;
-- retain its original universe and argument rather than resynthesizing data.
run_cmd do
  let ci ← Lean.getConstInfo ``CommRingCat.instCommRingObjForgetRingHomCarrier
  let some body := ci.value? | throwError "missing the original compiled carrier instance"
  let .lam _ _ b _ := body | throwError "unexpected original carrier instance binder"
  unless b.isAppOfArity ``CommRingCat.commRing 1 && b.appArg! == Lean.mkBVar 0 &&
      ci.levelParams.length == 1 &&
      b.getAppFn == Lean.mkConst ``CommRingCat.commRing (ci.levelParams.map Lean.Level.param) do
    throwError "the carrier instance does not retain the same original ring field and universe"

private def originalGammaCarrier
    (R : CommRingCat.{u}) (M : (Spec (.of R)).Modules)
    (w : M.val.obj (op ⊤)) : (moduleSpecΓFunctor (R := R)).obj M := w

private theorem reader_toNative_hom
    (R : CommRingCat.{u}) (F G : (Spec (.of R)).Modules) (he : F = G)
    (w : (moduleSpecΓFunctor (R := R)).obj F) :
    originalGammaNativeReader R F G he w =
      originalGammaCarrier R G
        (((eqToHom he).val.app (op ⊤)).hom.toFun w) := by
  cases R
  cases he
  rfl

private def originalCastPiece : Nat → Lean.Expr → Option Lean.Expr
  | 0, _ => none
  | fuel + 1, e =>
    if e.isAppOfArity ``eqToHom 5 then some e else
      match e with
      | .app f a => (originalCastPiece fuel f).orElse fun _ => originalCastPiece fuel a
      | .mdata _ t => originalCastPiece fuel t
      | .proj _ _ t => originalCastPiece fuel t
      | _ => none

private def gammaDomainImageProof
    (ringStx rawStx targetStx mapStx : Lean.Syntax) : Lean.Elab.Term.TermElabM Lean.Expr := do
  let image ← checkedNativeImageProof rawStx targetStx mapStx
  let ring ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm ringStx none)
  unless image.isAppOfArity ``Eq.trans 6 do throwError "expected the checked original native image composition"
  let mapped := image.getAppArgs[4]!
  unless mapped.isAppOfArity ``congrArg 6 do throwError "expected the same original raw-to-native map"
  let raw := mapped.getAppArgs.back!
  let rawType ← Lean.instantiateMVars (← Lean.Meta.inferType raw)
  unless rawType.isAppOfArity ``Eq 3 do throwError "expected the same original square equality"
  let rawLeft := rawType.getAppArgs[1]!
  let some cast := originalCastPiece 512 rawLeft | throwError "missing the same original field-square module equality"
  let ca := cast.getAppArgs
  let point := rawLeft.appArg!
  let .const _ levels := raw.getAppFn | throwError "missing the original square universe"
  let nativePoint := point
  let reader := Lean.mkAppN (Lean.mkConst ``reader_toNative_hom levels)
    #[ring, ca[2]!, ca[3]!, ca[4]!, nativePoint]
  let readerType ← Lean.instantiateMVars (← Lean.Meta.inferType reader)
  let imageType ← Lean.instantiateMVars (← Lean.Meta.inferType image)
  unless readerType.isAppOfArity ``Eq 3 && imageType.isAppOfArity ``Eq 3 do
    throwError "expected the original Gamma reader and image equalities"
  let .const _ imageLevels := imageType.getAppFn | throwError "missing the original native equality universe"
  let a := readerType.getAppArgs
  let b := imageType.getAppArgs
  let proof := Lean.mkAppN (Lean.mkConst ``Eq.trans imageLevels)
    #[b[0]!, a[1]!, a[2]!, b[2]!, reader, image]
  if proof.hasMVar then throwError "unresolved metavariable in the original Gamma coordinate image"
  let proposition ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
  unless proposition.isAppOfArity ``Eq 3 && (← Lean.Meta.isProp proposition) do
    throwError "expected an ordinary original Gamma coordinate equality"
  return proof

elab "gammaDomainImageProof%(" ring:term ", " raw:term ", " target:term ", " map:term ")" : term =>
  gammaDomainImageProof ring raw target map
elab "gammaDomainImageType%(" ring:term ", " raw:term ", " target:term ", " map:term ")" : term => do
  return ← Lean.instantiateMVars (← Lean.Meta.inferType (← gammaDomainImageProof ring raw target map))

/-- The same whole coordinate image in the literal domain of the original
Gamma functor, with the ordinary proof fixing its own equality type. -/
theorem transported_sourceCoordinate {K : Type u} [Field K]
    (R T : CommRingCat.{u}) [Algebra K T]
    (f : Spec R ⟶ Spec (.of K)) (φ : R ⟶ T)
    (he : Spec.map φ ≫ f = affineStructuralMap K T)
    (d : ℕ) (z : Fin d → R) :
    gammaDomainImageType%(
      T,
      (originalSquareCoordinateImage (K := K) (X := Spec R)
        (Y := Spec (@CommRingCat.of T (CommRingCat.instCommRingObjForgetRingHomCarrier (R := T))))
        f (Spec.map φ) (affineStructuralMap K T) he d
        (fun j => affineCoordinateMap R (op ⊤) (z j))
        (fun j => affineCoordinateMap T (op ⊤) (φ.hom (z j)))
        (fun j => originalAffineCoordinateImage R T φ (z j))),
      (originalCanonicalCoordinateSection K T d (fun j => φ.hom (z j))),
      (originalGammaCarrier T
        (exteriorCotangentSheaf (X := Spec (@CommRingCat.of T (CommRingCat.instCommRingObjForgetRingHomCarrier (R := T))))
          (affineStructuralMap K T) d))) :=
  gammaDomainImageProof%(
      T,
      (originalSquareCoordinateImage (K := K) (X := Spec R)
        (Y := Spec (@CommRingCat.of T (CommRingCat.instCommRingObjForgetRingHomCarrier (R := T))))
        f (Spec.map φ) (affineStructuralMap K T) he d
        (fun j => affineCoordinateMap R (op ⊤) (z j))
        (fun j => affineCoordinateMap T (op ⊤) (φ.hom (z j)))
        (fun j => originalAffineCoordinateImage R T φ (z j))),
      (originalCanonicalCoordinateSection K T d (fun j => φ.hom (z j))),
      (originalGammaCarrier T
        (exteriorCotangentSheaf (X := Spec (@CommRingCat.of T (CommRingCat.instCommRingObjForgetRingHomCarrier (R := T))))
          (affineStructuralMap K T) d)))

end EnvelopeProperty.CanonicalGeometry.NativeCoordinateImageGammaDomain
