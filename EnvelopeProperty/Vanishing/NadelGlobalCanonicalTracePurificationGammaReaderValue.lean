import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationNativeValue
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGammaNativeTransportCore
import EnvelopeProperty.AlgGeom.Canonical.ModuleRestrictionCarrier

/-! # The original purification value through its same native Gamma reader

Every module, map and coefficient action is read from the same original
constructor. Only the original abstract composite value and the checked
exact-domain Gamma transport reader are instantiated. No coordinate or
normalization certificate is an input.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelMixedKummer NadelCanonicalMixed NadelCanonicalMixed.Split
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


run_cmd
  for (source, short, original) in [
      (`EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationConstructorCore,
        `originalPurificationOuterCoefficientIso,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.outerCoefficientIso),
      (`EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGammaNativeTransportCore,
        `originalPurificationGammaNativeReader,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalGammaNativeReader),
      (`EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGammaNativeTransportCore,
        `originalPurificationGammaNativeTransport_value,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalGammaNativeTransport_value)] do
    let name := Lean.mkPrivateNameCore source original
    unless (← Lean.getEnv).contains name do throwError "missing original purification reader component"
    Lean.Elab.Command.modifyScope fun scope =>
      {scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls}

/-- The original composite and its same Gamma reader, before specialization of
any ring, module or scalar-action presentation. -/
private theorem originalPurificationCompositeGammaReader_value
    (S C P : CommRingCat.{u})
    (α : S →+* C) (β : S →+* P) (ρ : C →+* P)
    (M : ModuleCat C) (F G : (Spec (.of P)).Modules)
    (E : M ≅ (ModuleCat.restrictScalars ρ).obj ((moduleSpecΓFunctor (R := P)).obj F))
    (he : F = G) (hs : β = ρ.comp α) (w : M) :
    ModuleRestrictionCarrier.toUnderlying S P β ((moduleSpecΓFunctor (R := P)).obj G)
      ((originalPurificationOuterCoefficientIso α β ρ E
        ((moduleSpecΓFunctor (R := P)).mapIso (eqToIso he)) hs).hom w) =
    originalPurificationGammaNativeReader P F G he
      (ModuleRestrictionCarrier.toUnderlying C P ρ ((moduleSpecΓFunctor (R := P)).obj F)
        (E.hom w)) := by
  exact originalPurificationGammaNativeTransport_value P F G he
    (ModuleRestrictionCarrier.toUnderlying C P ρ ((moduleSpecΓFunctor (R := P)).obj F)
      (E.hom w))

private def purificationReaderPiece : Nat → (Lean.Expr → Bool) → Lean.Expr → Option Lean.Expr
  | 0, _, _ => none
  | fuel + 1, p, e =>
    if p e then some e else
      match e with
      | .app f a => (purificationReaderPiece fuel p f).orElse fun _ => purificationReaderPiece fuel p a
      | .mdata _ t => purificationReaderPiece fuel p t
      | .proj _ _ t => purificationReaderPiece fuel p t
      | _ => none

elab "originalPurificationGammaReaderValue%(" isoStx:term ", " wStx:term ")" : term => do
  let original ← Lean.Elab.Term.elabTerm isoStx none
  let w ← Lean.Elab.Term.elabTerm wStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let original ← Lean.instantiateMVars original
  let w ← Lean.instantiateMVars w
  unless original.isAppOf ``mixedPurificationSectionsIso && original.getAppArgs.size == 15 do
    throwError "expected the same original purification comparison"
  let some body ← Lean.Meta.delta? original (· == ``mixedPurificationSectionsIso) |
    throwError "could not read original purification"
  let ctor := (← Lean.Meta.zetaReduce body).consumeMData
  let ctorName := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCounit
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeRingEquivSectionsIso
  unless ctor.isAppOf ctorName && ctor.getAppArgs.size == 14 do
    throwError "unexpected original fourteen-argument purification constructor"
  let ca := ctor.getAppArgs
  let some cb ← Lean.Meta.delta? ctor (· == ctorName) |
    throwError "could not read original purification composite"
  let cb ← Lean.Meta.zetaReduce cb
  let some E := purificationReaderPiece 512 (·.isAppOf ``nativeEquivSectionsIso) cb |
    throwError "missing the original native equivalence"
  let some T := purificationReaderPiece 512 (fun t =>
      t.isAppOf ``Functor.mapIso && t.getAppArgs.size == 8 &&
        t.getAppArgs[4]!.isAppOf ``moduleSpecΓFunctor) cb |
    throwError "missing the original Gamma transport"
  let some rho := purificationReaderPiece 512 (·.isAppOf ``RingEquiv.toRingHom) cb |
    throwError "missing the original purification coefficient map"
  let et ← Lean.Meta.whnf (← Lean.Meta.inferType E)
  let tt ← Lean.Meta.whnf (← Lean.Meta.inferType T)
  unless et.isAppOf ``Iso && tt.isAppOf ``Iso do
    throwError "missing the original module isomorphism types"
  let ea := et.getAppArgs
  let M := ea[ea.size - 2]!
  let ta := T.getAppArgs
  let ga := ta[4]!.getAppArgs
  unless ga.size == 1 do throwError "unexpected original Gamma ring arguments"
  let moduleIso := ta[7]!
  unless moduleIso.isAppOf ``eqToIso do throwError "expected original whole module equality"
  let .const _ levels := E.getAppFn | throwError "missing original universes"
  let law := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePurificationGammaReaderValue
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalPurificationCompositeGammaReader_value
  let proof := Lean.mkAppN (Lean.mkConst law levels)
    #[ca[2]!, ca[3]!, ga[0]!, ca[6]!, ca[7]!, rho,
      M, ta[5]!, ta[6]!, E, moduleIso.getAppArgs.back!, ca[12]!, w]
  let proof ← Lean.instantiateMVars proof
  if proof.hasMVar then throwError "unresolved metavariable in same original purification reader"
  return proof

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

/-- Every original native section is evaluated through its original
coefficient composite and the same exact-domain Gamma transport reader. -/
private theorem mixedPurificationOriginalGammaReaderValue
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A))
    (w : extendedMixedCanonicalModule (k := k) x N I σ u) :
    originalActionType%(originalPurificationGammaReaderValue%(
      mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame, w)) :=
  originalPurificationGammaReaderValue%(
    mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame, w)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
