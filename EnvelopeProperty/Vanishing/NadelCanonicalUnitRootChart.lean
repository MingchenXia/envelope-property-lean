import EnvelopeProperty.Vanishing.NadelCanonicalUnitRoot

/-! # Canonical trace from actual original étale coordinate charts -/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelCanonicalUnitRoot

open CategoryTheory ModuleCat CanonicalGeometry NadelFiniteDuality

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}
    (a : MvPolynomial (Fin n) R →ₐ[R] A) (ha : a.toRingHom.FormallyEtale)

/-- The original coordinate morphism internally produces its true Kähler differential basis. -/
def chartDifferentialBasis : Module.Basis (Fin n) A (KaehlerDifferential R A) := by
  let : Algebra (MvPolynomial (Fin n) R) A := a.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial (Fin n) R) A :=
    IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  let : Algebra.FormallyEtale (MvPolynomial (Fin n) R) A := ha
  exact polynomialEtaleDifferentialBasis R A n

/-- The internally produced frame consists of the actual original coordinate differentials. -/
theorem chartDifferentialBasis_apply (j : Fin n) :
    chartDifferentialBasis R A a ha j =
      KaehlerDifferential.D R A (a (MvPolynomial.X j)) := by
  let : Algebra (MvPolynomial (Fin n) R) A := a.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial (Fin n) R) A :=
    IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  let : Algebra.FormallyEtale (MvPolynomial (Fin n) R) A := ha
  exact polynomialEtaleDifferentialBasis_apply R A n j

variable [Nontrivial A] (m : ℕ) (u : Aˣ) (hN : IsUnit ((m + 1 : ℕ) : A))

/-- Actual original coordinate data produce whole unit-root canonical duality with no Omega-model input. -/
def chartCanonicalIso :
    ModuleCat.of (Root m (u : A)) (rootCanonicalModule R A m u n) ≅
      (coextendScalars (rootStructure A m u)).obj
        (ModuleCat.of A (affineCanonicalModule R A n)) :=
  canonicalIso R A m u (chartDifferentialBasis R A a ha) hN

/-- Actual original coordinate data produce the entire native canonical trace. -/
def chartCanonicalCounit :
    (restrictScalars (rootStructure A m u)).obj
        (ModuleCat.of (Root m (u : A)) (rootCanonicalModule R A m u n)) ⟶
      ModuleCat.of A (affineCanonicalModule R A n) :=
  canonicalCounit R A m u (chartDifferentialBasis R A a ha) hN

/-- The internally produced whole chart trace satisfies the intrinsic normalization on every actual top form. -/
theorem chartCanonicalCounit_pulled_topform (c : Root m (u : A))
    (w : affineCanonicalModule R A n) :
    chartCanonicalCounit R A a ha m u hN (c • canonicalPullback R A m u n w) =
      Algebra.trace A (Root m (u : A)) c • w :=
  canonicalCounit_pulled_topform R A m u (chartDifferentialBasis R A a ha) hN c w

/-- Two actual étale coordinate systems on the same original algebra produce the same whole canonical trace. -/
theorem chartCanonicalCounit_independent
    (a' : MvPolynomial (Fin n) R →ₐ[R] A) (ha' : a'.toRingHom.FormallyEtale) :
    chartCanonicalCounit R A a' ha' m u hN = chartCanonicalCounit R A a ha m u hN :=
  canonicalCounit_frame_independent R A m u
    (chartDifferentialBasis R A a ha) hN (chartDifferentialBasis R A a' ha')

end EnvelopeProperty.Vanishing.NadelCanonicalUnitRoot
