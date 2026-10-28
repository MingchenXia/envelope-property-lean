import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationPullback
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCounit
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePureNormalization

/-! # The two actual native maps in the original mixed square

The left map uses exactly the comparisons in the original extended counit.
The right map uses the original pure differential on the same pure quotient.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelCanonicalMixed NadelCanonicalMixed.Split
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

elab "nativeMixedMapType%(" mapStx:term ")" : term => do
  let map ← Lean.Elab.Term.elabTerm mapStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  Lean.instantiateMVars (← Lean.Meta.inferType map)

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

/-- The original mixed native pullback followed by the SAME two original
comparisons used in `mixedExtendedCounit`. -/
def originalMixedNativeSquareLeft
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :=
  (ModuleCat.extendScalars (R := CommRingCat.of A)
    (S := CommRingCat.of (UnitCover N u)) (algebraMap A (UnitCover N u))).map
      (mixedNativeCanonicalPullback (k := k) x N I σ u hx) ≫
    ((mixedExtendedSectionsIso (k := k) x N I σ u hx hN htame).hom ≫
      (mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame).hom)

/-- The original unit comparison followed by the original whole pure
native differential. All coordinate data are produced from the original chart. -/
def originalMixedNativeSquareRight
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :=
  (unitBaseSectionsIso (k := k) x N u hx hN htame).hom ≫
    pureNativeCanonicalPullback N I σ (unitCoordinateMap (k := k) x N u)
      (unitCoordinateMap_etale x N u hx hN htame)

/-- The original pure path in the exact original target of the mixed path.
This declaration changes no field structure or coefficient action. -/
def originalMixedNativeSquareRightAligned
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    nativeMixedMapType%(originalMixedNativeSquareLeft (k := k) x N I σ u hx hN htame) :=
  originalMixedNativeSquareRight (k := k) x N I σ u hx hN htame

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
