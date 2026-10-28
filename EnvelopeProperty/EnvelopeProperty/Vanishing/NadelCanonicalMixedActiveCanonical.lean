import EnvelopeProperty.Vanishing.NadelCanonicalMixedActiveDual

/-! # Actual original canonical duality of the whole active-coordinate quotient -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split

open CategoryTheory ModuleCat CanonicalGeometry NadelKummerCanonicalTrace NadelKummerCanonicalBaseChange
variable {k R : Type u} [CommRing k] [Nontrivial k] [CommRing R] [Algebra k R] {n q : ℕ}
    (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n) (hN : ∀ i, 0 < N i)
    (a : MvPolynomial (Fin n) k →ₐ[k] R) (ha : a.toRingHom.FormallyEtale)
local notation "d" => coordinateExponent N I σ
local notation "x" => originalCoordinates a
local notation "A₀" => ActiveRing N I (pureCoefficient x I σ)

/-- Genuine original coordinate geometry and the proved whole active finite dual give actual canonical duality. -/
def activeCanonicalIso : ModuleCat.of A₀ (affineCanonicalModule k A₀ n) ≅
    (coextendScalars (algebraMap R A₀)).obj (ModuleCat.of R (affineCanonicalModule k R n)) :=
  (affineCanonicalTrivialization (activeDifferentialBasis N I σ hN a ha)).toModuleIso ≪≫
    activeDualizingIso N I σ hN a ≪≫
      (coextendScalars (algebraMap R A₀)).mapIso
        (affineCanonicalTrivialization (baseDifferentialBasis a ha)).symm.toModuleIso

/-- The whole actual canonical functional retains the original native coefficient formula on every true top form. -/
theorem activeCanonicalIso_apply (w : affineCanonicalModule k A₀ n) (c : A₀) :
    (activeCanonicalIso N I σ hN a ha).hom w c =
      powerBaseChangeCoefficient k d R a.toRingHom
        (activeToPower N I σ hN a (c * affineCanonicalTrivialization (activeDifferentialBasis N I σ hN a ha) w)) •
          affineCanonicalGenerator (baseDifferentialBasis a ha) := by
  change (affineCanonicalTrivialization (baseDifferentialBasis a ha)).symm
    (activeDualizingMap N I σ hN a
      (affineCanonicalTrivialization (activeDifferentialBasis N I σ hN a ha) w) c) = _
  rw [activeDualizingMap_apply]
  exact (affineCanonical_eq_smul_generator (baseDifferentialBasis a ha)
    ((affineCanonicalTrivialization (baseDifferentialBasis a ha)).symm
      (powerBaseChangeCoefficient k d R a.toRingHom
        (activeToPower N I σ hN a (c * affineCanonicalTrivialization (activeDifferentialBasis N I σ hN a ha) w))))).trans
      (by rw [LinearEquiv.apply_symm_apply])

/-- The true original canonical counit is the actual native restriction/coextension counit. -/
def activeCanonicalCounit :
    (restrictScalars (algebraMap R A₀)).obj (ModuleCat.of A₀ (affineCanonicalModule k A₀ n)) ⟶
      ModuleCat.of R (affineCanonicalModule k R n) :=
  (restrictScalars (algebraMap R A₀)).map (activeCanonicalIso N I σ hN a ha).hom ≫
    (restrictCoextendScalarsAdj (algebraMap R A₀)).counit.app
      (ModuleCat.of R (affineCanonicalModule k R n))

/-- The whole original active canonical trace has its actual coefficient formula on every genuine frame multiple. -/
theorem activeCanonicalCounit_generator (c : A₀) :
    activeCanonicalCounit N I σ hN a ha
      (c • affineCanonicalGenerator (activeDifferentialBasis N I σ hN a ha)) =
        powerBaseChangeCoefficient k d R a.toRingHom (activeToPower N I σ hN a c) •
          affineCanonicalGenerator (baseDifferentialBasis a ha) := by
  change (activeCanonicalIso N I σ hN a ha).hom
    (c • affineCanonicalGenerator (activeDifferentialBasis N I σ hN a ha)) (1 : A₀) = _
  rw [activeCanonicalIso_apply, map_smul, affineCanonicalTrivialization_generator,
    smul_eq_mul, mul_one, one_mul]

end EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split
