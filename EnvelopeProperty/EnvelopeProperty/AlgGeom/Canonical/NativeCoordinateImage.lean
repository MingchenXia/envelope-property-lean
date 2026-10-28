import EnvelopeProperty.AlgGeom.Canonical.NativeCoordinateSection
import EnvelopeProperty.AlgGeom.Canonical.ModuleSpecGammaCarrier
import EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore

/-! # Original ordinary coordinates in the native target Gamma carrier

The original bundled rings, entire coefficient morphism and field triangle
are retained. Coordinates are ordinary elements of the original source ring;
their original Gamma representatives are constructed internally. No source
algebra structure, smoothness or incoming coordinate-image certificate is used.
-/
noncomputable section
namespace EnvelopeProperty.CanonicalGeometry.NativeCoordinateImage
open AlgebraicGeometry CategoryTheory Opposite
open EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  for (source, short, original) in [
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
    unless (← Lean.getEnv).contains name do throwError "missing checked original coordinate law"
    Lean.Elab.Command.modifyScope fun scope =>
      {scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls}

/-- The original ordinary source coordinates in their same native Gamma module. -/
def sourceCoordinate {K : Type u} [Field K] (R : CommRingCat.{u})
    (f : Spec R ⟶ Spec (.of K)) (d : ℕ) (z : Fin d → R) :
    (moduleSpecΓFunctor (R := R)).obj (exteriorCotangentSheaf f d) :=
  NativeCoordinateSection.ofGammaCoordinates R f d
    (fun j => affineCoordinateMap R (op ⊤) (z j))

private def nativeCoordinateImageProof
    (rawStx targetStx mapStx : Lean.Syntax) : Lean.Elab.Term.TermElabM Lean.Expr := do
  let raw ← Lean.Elab.Term.elabTerm rawStx none
  let target ← Lean.Elab.Term.elabTerm targetStx none
  let nativeMap ← Lean.Elab.Term.elabTerm mapStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let raw ← Lean.instantiateMVars raw
  let target ← Lean.instantiateMVars target
  let nativeMap ← Lean.instantiateMVars nativeMap
  let rawType ← Lean.instantiateMVars (← Lean.Meta.inferType raw)
  let nativeType ← Lean.instantiateMVars (← Lean.Meta.inferType target)
  unless rawType.isAppOfArity ``Eq 3 && nativeType.isAppOfArity ``Eq 3 do
    throwError "expected the checked original raw/native coordinate equalities"
  let .const _ rawLevels := rawType.getAppFn | throwError "missing raw equality universe"
  let .const _ nativeLevels := nativeType.getAppFn | throwError "missing native equality universe"
  unless rawLevels.length == 1 && nativeLevels.length == 1 do
    throwError "unexpected equality universe arity"
  let a := rawType.getAppArgs
  let b := nativeType.getAppArgs
  let mapped := Lean.mkAppN
    (Lean.mkConst ``congrArg [rawLevels.head!, nativeLevels.head!])
    #[a[0]!, b[0]!, a[1]!, a[2]!, nativeMap, raw]
  let reversed := Lean.mkAppN (Lean.mkConst ``Eq.symm nativeLevels)
    #[b[0]!, b[1]!, b[2]!, target]
  let proof := Lean.mkAppN (Lean.mkConst ``Eq.trans nativeLevels)
    #[b[0]!, Lean.mkApp nativeMap a[1]!, Lean.mkApp nativeMap a[2]!, b[1]!, mapped, reversed]
  if proof.hasMVar then throwError "unresolved metavariable in original native coordinate proof"
  let proposition ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
  unless ← Lean.Meta.isProp proposition do throwError "the original native image is not Prop"
  let propositionSort ← Lean.Meta.inferType proposition
  unless propositionSort.consumeMData == Lean.mkSort Lean.Level.zero do
    throwError "the original proposition must have sort zero"
  unless proposition.isAppOfArity ``Eq 3 do throwError "the original image is not an explicit equality"
  return proof

elab "nativeCoordinateImageProof%(" raw:term ", " target:term ", " map:term ")" : term =>
  nativeCoordinateImageProof raw target map

elab "nativeCoordinateImageType%(" raw:term ", " target:term ", " map:term ")" : term => do
  let proof ← nativeCoordinateImageProof raw target map
  return ← Lean.instantiateMVars (← Lean.Meta.inferType proof)

/-- The original native target coordinate image, retaining the entire original
coefficient map and field triangle. The ordinary proof fixes its own type. -/
theorem transported_sourceCoordinate {K : Type u} [Field K]
    (R T : CommRingCat.{u}) [Algebra K T]
    (f : Spec R ⟶ Spec (.of K)) (φ : R ⟶ T)
    (he : Spec.map φ ≫ f = affineStructuralMap K T)
    (d : ℕ) (z : Fin d → R) :
    nativeCoordinateImageType%(
      (originalSquareCoordinateImage (K := K) (X := Spec R) (Y := Spec T)
        f (Spec.map φ) (affineStructuralMap K T) he d
        (fun j => affineCoordinateMap R (op ⊤) (z j))
        (fun j => affineCoordinateMap T (op ⊤) (φ.hom (z j)))
        (fun j => originalAffineCoordinateImage R T φ (z j))),
      (originalCanonicalCoordinateSection K T d (fun j => φ.hom (z j))),
      (ModuleSpecGammaCarrier.toNative T (exteriorCotangentSheaf (affineStructuralMap K T) d))) :=
  nativeCoordinateImageProof%(
    (originalSquareCoordinateImage (K := K) (X := Spec R) (Y := Spec T)
      f (Spec.map φ) (affineStructuralMap K T) he d
      (fun j => affineCoordinateMap R (op ⊤) (z j))
      (fun j => affineCoordinateMap T (op ⊤) (φ.hom (z j)))
      (fun j => originalAffineCoordinateImage R T φ (z j))),
    (originalCanonicalCoordinateSection K T d (fun j => φ.hom (z j))),
    (ModuleSpecGammaCarrier.toNative T (exteriorCotangentSheaf (affineStructuralMap K T) d)))

end EnvelopeProperty.CanonicalGeometry.NativeCoordinateImage
