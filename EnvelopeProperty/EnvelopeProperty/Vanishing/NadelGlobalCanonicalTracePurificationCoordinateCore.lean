import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePurificationGammaDifferentialValue
import EnvelopeProperty.AlgGeom.Canonical.NativeCoordinateImageGammaDomain
import EnvelopeProperty.AlgGeom.Canonical.ModuleRestrictionCarrier

/-! # Coordinate values of the same original whole purification

The original constructor, its literal Gamma transport and every original
non-propositional parameter are retained. The generic native coordinate
image is a proved producer; no raw-coordinate proof is reconstructed here.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry
open NadelMixedKummer NadelCanonicalMixed NadelCanonicalMixed.Split
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def purificationCoordinateTrans (p q : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let tp ← Lean.Meta.whnf (← Lean.Meta.inferType p)
  let tq ← Lean.Meta.whnf (← Lean.Meta.inferType q)
  unless tp.isAppOfArity ``Eq 3 && tq.isAppOfArity ``Eq 3 do
    throwError "expected checked original coordinate equalities"
  let .const _ levels := tp.getAppFn | throwError "missing equality universes"
  let ap := tp.getAppArgs
  let aq := tq.getAppArgs
  return Lean.mkAppN (Lean.mkConst ``Eq.trans levels)
    #[ap[0]!, ap[1]!, ap[2]!, aq[2]!, p, q]

private def findOriginalCoordinatePart : Nat → (Lean.Expr → Bool) → Lean.Expr → Option Lean.Expr
  | 0, _, _ => none
  | fuel + 1, p, e =>
    if p e then some e else
      match e with
      | .app f a => (findOriginalCoordinatePart fuel p f).orElse fun _ =>
          findOriginalCoordinatePart fuel p a
      | .mdata _ t => findOriginalCoordinatePart fuel p t
      | .proj _ _ t => findOriginalCoordinatePart fuel p t
      | _ => none

elab "actualPurificationCoordinateProof%(" isoStx:term ", " zStx:term ")" : term => do
  let original ← Lean.Elab.Term.elabTerm isoStx none
  let z ← Lean.Elab.Term.elabTerm zStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let original ← Lean.instantiateMVars original
  let z ← Lean.instantiateMVars z
  unless original.isAppOf ``mixedPurificationSectionsIso && original.getAppArgs.size == 15 do
    throwError "expected the same original fifteen-argument purification comparison"
  let some body ← Lean.Meta.delta? original (· == ``mixedPurificationSectionsIso) |
    throwError "could not read original purification"
  let ctor := (← Lean.Meta.zetaReduce body).consumeMData
  let ctorName := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCounit
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeRingEquivSectionsIso
  unless ctor.isAppOf ctorName && ctor.getAppArgs.size == 14 do
    throwError "unexpected original fourteen-argument purification constructor"
  let ca := ctor.getAppArgs
  let .const _ levels := ctor.getAppFn | throwError "missing original universes"
  let heType ← Lean.Meta.whnf (← Lean.Meta.inferType ca[13]!)
  unless heType.isAppOfArity ``Eq 3 do throwError "missing original field triangle"
  let compositeArgs := heType.getAppArgs[1]!.getAppArgs
  unless compositeArgs.size >= 2 do throwError "missing original geometric composite"
  let g := compositeArgs[compositeArgs.size - 2]!
  unless g.isAppOfArity ``Spec.map 3 do throwError "expected the original whole spectrum map"
  let phi := g.getAppArgs[2]!
  let hImage := Lean.mkAppN
    (Lean.mkConst ``NativeCoordinateImageGammaDomain.transported_sourceCoordinate levels)
    #[ca[0]!, ca[1]!, ca[3]!, ca[4]!, ca[5]!, ca[8]!, phi, ca[13]!, ca[9]!, z]
  let imageType ← Lean.Meta.whnf (← Lean.Meta.inferType hImage)
  unless imageType.isAppOfArity ``Eq 3 do throwError "expected the checked original Gamma coordinate image"
  let reader := imageType.getAppArgs[1]!.consumeMData
  let readerName := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGammaNativeTransportCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalGammaNativeReader
  unless reader.isAppOfArity readerName 5 do
    throwError "missing the same original whole Gamma coordinate reader"
  let differentialPoint := reader.appArg!.consumeMData
  unless differentialPoint.isApp &&
      (findOriginalCoordinatePart 512 (·.isAppOf ``exteriorCotangentSheafMorphism)
        differentialPoint.appFn!).isSome do
    throwError "missing the same original whole raw coordinate differential point"
  -- Use the SAME raw source coordinate value already exposed by the checked
  -- image producer, rather than rebuilding an equivalent source presentation.
  let w := differentialPoint.appArg!
  let readLaw := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePurificationGammaDifferentialValue
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedPurificationOriginalGammaDifferentialValue
  let hRead := Lean.mkAppN (Lean.mkConst readLaw levels)
    (original.getAppArgs ++ #[w])
  let proof ← Lean.instantiateMVars (← purificationCoordinateTrans hRead hImage)
  if proof.hasMVar then throwError "unresolved metavariable in original actual coordinate proof"
  let proposition ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
  unless proposition.isAppOfArity ``Eq 3 && !proposition.hasMVar do
    throwError "the original actual proof has no complete equality proposition"
  return proof

-- The theorem type is inferred from exactly the same ordinary proof
-- factory used by its body. No proposition or proof is stored as data.
elab "actualPurificationCoordinateType%(" proofStx:term ")" : term => do
  let proof ← Lean.Elab.Term.elabTerm proofStx none
  let proposition ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
  if proposition.hasMVar then throwError "unresolved metavariable in original coordinate proposition"
  unless proposition.isAppOfArity ``Eq 3 do
    throwError "the original coordinate proof did not expose its actual equality"
  let kind ← Lean.Meta.whnf (← Lean.Meta.inferType proposition)
  unless kind.isSort && kind.sortLevel!.isZero do
    throwError "the original coordinate equality is not a proposition"
  return proposition

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

/-- Every original coordinate wedge has its original purification image,
with the same original coefficient and field structures throughout. -/
theorem mixedPurificationOriginalCoordinateValue
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A))
    (z : Fin n → extendedMixedRing x N I σ u) :
    actualPurificationCoordinateType%(actualPurificationCoordinateProof%(
      mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame, z)) :=
  actualPurificationCoordinateProof%(
    mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame, z)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
