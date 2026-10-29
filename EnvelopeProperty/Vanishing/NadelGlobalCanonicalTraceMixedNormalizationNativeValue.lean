import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationInferredAction
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationAbstractValue

/-! # Native values of the literal original purification composite

The original constructor's own E and T are read, not rebuilt. Its underlying
restriction-of-scalars composite is evaluated on every original section.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelMixedKummer NadelCanonicalMixed NadelCanonicalMixed.Split
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def findOriginalPiece : Nat → (Lean.Expr → Bool) → Lean.Expr → Option Lean.Expr
  | 0, _, _ => none
  | fuel + 1, p, e =>
    if p e then some e else
      match e with
      | .app f a => (findOriginalPiece fuel p f).orElse fun _ =>
          findOriginalPiece fuel p a
      | .mdata _ t => findOriginalPiece fuel p t
      | .proj _ _ t => findOriginalPiece fuel p t
      | _ => none

elab "originalPurificationNativeValue%(" iso:term ", " w:term ")" : term => do
  let original ← Lean.Elab.Term.elabTerm iso none
  let w ← Lean.Elab.Term.elabTerm w none
  let some app := findOriginalPiece 512 (·.isAppOf ``mixedPurificationSectionsIso) original |
    throwError "expected the same original purification comparison"
  let some body ← Lean.Meta.delta? app (· == ``mixedPurificationSectionsIso) |
    throwError "could not read the same original purification"
  let ctor := (← Lean.Meta.zetaReduce body).consumeMData
  let name := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCounit
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeRingEquivSectionsIso
  unless ctor.isAppOf name && ctor.getAppArgs.size == 14 do
    throwError "unexpected original constructor"
  let args := ctor.getAppArgs
  let some cbody ← Lean.Meta.delta? ctor (· == name) |
    throwError "could not read the original native composite"
  let cbody ← Lean.Meta.zetaReduce cbody
  let some E := findOriginalPiece 512 (·.isAppOf ``nativeEquivSectionsIso) cbody |
    throwError "missing original native equivalence"
  let some T := findOriginalPiece 512 (fun t =>
      t.isAppOf ``Functor.mapIso && t.getAppArgs.size == 8 &&
        t.getAppArgs[4]!.isAppOf ``moduleSpecΓFunctor) cbody |
    throwError "missing original native field-transport comparison"
  let some ρ := findOriginalPiece 512 (·.isAppOf ``RingEquiv.toRingHom) cbody |
    throwError "missing original literal purification ring map"
  let et ← Lean.Meta.whnf (← Lean.Meta.inferType E)
  let tt ← Lean.Meta.whnf (← Lean.Meta.inferType T)
  unless et.isAppOf ``Iso && tt.isAppOf ``Iso do
    throwError "expected original module isomorphisms"
  let ea := et.getAppArgs
  let ta := tt.getAppArgs
  let M := ea[ea.size - 2]!
  let Q := ta[ta.size - 2]!
  let NN := ta[ta.size - 1]!
  let abstractLaw := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationAbstractValue
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalComposite_value
  let h₁ ← Lean.Meta.mkAppOptM abstractLaw
    #[some args[2]!, some args[3]!, some args[4]!,
      some args[6]!, some args[7]!, some ρ, some M, some Q, some NN,
      some E, some T, some args[12]!, some w]
  let .const _ levels := E.getAppFn | throwError "missing native equivalence universes"
  let hE := Lean.mkAppN (Lean.mkConst ``nativeEquivSectionsIso_apply levels)
    (E.getAppArgs ++ #[w])
  let thom ← Lean.Meta.mkAppM ``Iso.hom #[T]
  let linear ← Lean.Meta.mkAppM ``ModuleCat.Hom.hom #[thom]
  let fn ← Lean.Meta.mkAppM ``DFunLike.coe #[linear]
  let h₂ ← Lean.Meta.mkAppM ``congrArg #[fn, hE]
  let t₁ ← Lean.Meta.whnf (← Lean.Meta.inferType h₁)
  let t₂ ← Lean.Meta.whnf (← Lean.Meta.inferType h₂)
  unless t₁.isAppOfArity ``Eq 3 && t₂.isAppOfArity ``Eq 3 do
    throwError "expected the two original native value equalities"
  let .const _ eqLevels := t₁.getAppFn | throwError "missing equality universes"
  let a₁ := t₁.getAppArgs
  let a₂ := t₂.getAppArgs
  return Lean.mkAppN (Lean.mkConst ``Eq.trans eqLevels)
    #[a₁[0]!, a₁[1]!, a₁[2]!, a₂[2]!, h₁, h₂]

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

/-- Every native section is evaluated through the original purification's
literal restriction/equivalence/field-transport composite. -/
theorem mixedPurificationOriginalNativeValue
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A))
    (w : extendedMixedCanonicalModule (k := k) x N I σ u) :
    originalActionType%(originalPurificationNativeValue%(
      mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame, w)) :=
  originalPurificationNativeValue%(
    mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame, w)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
