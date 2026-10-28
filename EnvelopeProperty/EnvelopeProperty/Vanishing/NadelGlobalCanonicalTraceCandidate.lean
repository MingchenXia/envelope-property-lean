import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCounit
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRetraction

/-! # The actual original mixed canonical candidate

This constructs the original A-linear map from the internally produced
extended mixed counit and the actual normalized coefficient trace.  Its
intrinsic differential normalization and overlap comparison are separate
remaining proof obligations, not inputs to this constructor.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelCanonicalMixed
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k A : Type u} [Field k] [CharZero k] [CommRing A] [Algebra k A] [Nontrivial A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

/-- The actual original mixed A-linear candidate: original scalar-extension
unit, SAME internally constructed mixed extended map, then the SAME produced
coefficient trace tensor identity.  No matching or compatibility input occurs. -/
def mixedCanonicalCandidate
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    mixedCanonicalModuleOverBase (k := k) x N I σ u ⟶
      (moduleSpecΓFunctor (R := .of A)).obj
        (exteriorCotangentSheaf (affineStructuralMap k (.of A)) n) := by
  let φ := algebraMap A (UnitCover N u)
  let M := mixedCanonicalModuleOverBase (k := k) x N I σ u
  let Q := (moduleSpecΓFunctor (R := .of A)).obj
    (exteriorCotangentSheaf (affineStructuralMap k (.of A)) n)
  exact (ModuleCat.extendRestrictScalarsAdj φ).unit.app M ≫
    (ModuleCat.restrictScalars φ).map (mixedExtendedCounit x N I σ u hx hN htame) ≫
      unitCoverSectionsRetraction (k := k) N u hN Q

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
