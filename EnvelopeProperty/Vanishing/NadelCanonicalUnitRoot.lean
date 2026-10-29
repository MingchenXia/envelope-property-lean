import EnvelopeProperty.Vanishing.NadelCanonicalUnitRootDifferentials

/-! # Actual canonical trace on the whole tame unit-root cover -/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelCanonicalUnitRoot

open CategoryTheory ModuleCat CanonicalGeometry NadelFiniteDuality

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]
    (m : ℕ) (u : Aˣ) {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (hN : IsUnit ((m + 1 : ℕ) : A))

/-- The actual native top differential module is the coextension of the original base top module. -/
def canonicalIso :
    ModuleCat.of (Root m (u : A)) (rootCanonicalModule R A m u n) ≅
      (coextendScalars (rootStructure A m u)).obj
        (ModuleCat.of A (affineCanonicalModule R A n)) :=
  (affineCanonicalTrivialization (rootDifferentialBasis R A m u b hN)).toModuleIso ≪≫
    traceDualizingIso m u hN ≪≫
      (coextendScalars (rootStructure A m u)).mapIso
        (affineCanonicalTrivialization b).symm.toModuleIso

/-- The whole canonical isomorphism has its true native trace-functional formula. -/
theorem canonicalIso_apply (w : rootCanonicalModule R A m u n) (c : Root m (u : A)) :
    (canonicalIso R A m u b hN).hom w c =
      Algebra.trace A (Root m (u : A))
        (c * affineCanonicalTrivialization (rootDifferentialBasis R A m u b hN) w) •
          affineCanonicalGenerator b := by
  change (affineCanonicalTrivialization b).symm
    (traceDualizingEquiv m u hN
      (affineCanonicalTrivialization (rootDifferentialBasis R A m u b hN) w) c) = _
  rw [traceDualizingEquiv_apply]
  exact (affineCanonical_eq_smul_generator b
    ((affineCanonicalTrivialization b).symm
      (Algebra.trace A (Root m (u : A))
        (c * affineCanonicalTrivialization (rootDifferentialBasis R A m u b hN) w)))).trans
    (by rw [LinearEquiv.apply_symm_apply])

/-- The canonical trace is the actual native restriction/coextension counit. -/
def canonicalCounit :
    (restrictScalars (rootStructure A m u)).obj
        (ModuleCat.of (Root m (u : A)) (rootCanonicalModule R A m u n)) ⟶
      ModuleCat.of A (affineCanonicalModule R A n) :=
  (restrictScalars (rootStructure A m u)).map (canonicalIso R A m u b hN).hom ≫
    (restrictCoextendScalarsAdj (rootStructure A m u)).counit.app
      (ModuleCat.of A (affineCanonicalModule R A n))

/-- The native counit is the actual whole-algebra trace on every coefficient of the true top frame. -/
theorem canonicalCounit_generator (c : Root m (u : A)) :
    canonicalCounit R A m u b hN
      (c • affineCanonicalGenerator (rootDifferentialBasis R A m u b hN)) =
        Algebra.trace A (Root m (u : A)) c • affineCanonicalGenerator b := by
  change (canonicalIso R A m u b hN).hom
    (c • affineCanonicalGenerator (rootDifferentialBasis R A m u b hN)) (1 : Root m (u : A)) = _
  rw [canonicalIso_apply, map_smul, affineCanonicalTrivialization_generator,
    smul_eq_mul, mul_one, one_mul]

/-- Every original base top form satisfies the intrinsic trace normalization under true differential pullback. -/
theorem canonicalCounit_pulled_topform (c : Root m (u : A))
    (w : affineCanonicalModule R A n) :
    canonicalCounit R A m u b hN (c • canonicalPullback R A m u n w) =
      Algebra.trace A (Root m (u : A)) c • w := by
  conv_lhs => rw [affineCanonical_eq_smul_generator b w]
  rw [map_smulₛₗ, canonicalPullback_generator R A m u b hN, smul_smul,
    canonicalCounit_generator]
  change Algebra.trace A (Root m (u : A))
    (c * algebraMap A (Root m (u : A)) (affineCanonicalTrivialization b w)) • _ = _
  rw [mul_comm, ← Algebra.smul_def, map_smul]
  rw [smul_eq_mul, mul_comm, ← smul_smul, ← affineCanonical_eq_smul_generator b w]

/-- The whole actual counit is uniquely determined by intrinsic normalization on all actual base top forms. -/
theorem canonicalCounit_unique
    (l : (restrictScalars (rootStructure A m u)).obj
        (ModuleCat.of (Root m (u : A)) (rootCanonicalModule R A m u n)) ⟶
      ModuleCat.of A (affineCanonicalModule R A n))
    (hl : ∀ (c : Root m (u : A)) (w : affineCanonicalModule R A n),
      l (c • canonicalPullback R A m u n w) =
        Algebra.trace A (Root m (u : A)) c • w) :
    l = canonicalCounit R A m u b hN := by
  ext w
  rw [affineCanonical_eq_smul_generator (rootDifferentialBasis R A m u b hN) w]
  rw [← canonicalPullback_generator R A m u b hN,
    hl, canonicalCounit_pulled_topform]

/-- Changing the genuine base differential frame preserves the entire native canonical trace. -/
theorem canonicalCounit_frame_independent
    (b' : Module.Basis (Fin n) A (KaehlerDifferential R A)) :
    canonicalCounit R A m u b' hN = canonicalCounit R A m u b hN :=
  canonicalCounit_unique R A m u b hN _
    (canonicalCounit_pulled_topform R A m u b' hN)

end EnvelopeProperty.Vanishing.NadelCanonicalUnitRoot
