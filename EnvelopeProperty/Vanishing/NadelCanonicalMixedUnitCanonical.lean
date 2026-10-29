import EnvelopeProperty.Vanishing.NadelCanonicalMixedUnitTrace
import EnvelopeProperty.Vanishing.NadelCanonicalEtaleBaseChange
import EnvelopeProperty.Vanishing.NadelCanonicalUnitRootChart

/-! # Genuine original top differentials and native canonical trace on ALL tame coefficient-root factors -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed

open CategoryTheory ModuleCat CanonicalGeometry NadelCanonicalBaseChange
open scoped TensorProduct

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Nontrivial R]
    {q n : ℕ} (N : Fin q → ℕ) (u : Fin q → Rˣ)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : R))
    (b : Module.Basis (Fin n) R (KaehlerDifferential k R))

/-- Original etale Kähler base change constructs the actual whole-cover differential frame. -/
def unitCoverDifferentialBasis :
    Module.Basis (Fin n) (UnitCover N u) (KaehlerDifferential k (UnitCover N u)) := by
  let : Algebra.Etale R (UnitCover N u) := unitCover_etale N u hN htame
  exact affineDifferentialBasisOfFormallyEtale b

/-- Native exterior base change constructs the actual Omega isomorphism on the WHOLE coefficient cover. -/
def unitCoverCanonicalTensorEquiv :
    UnitCover N u ⊗[R] affineCanonicalModule k R n ≃ₗ[UnitCover N u]
      affineCanonicalModule k (UnitCover N u) n := by
  let : Algebra.Etale R (UnitCover N u) := unitCover_etale N u hN htame
  exact etaleTopEquiv b

omit [Nontrivial R] in
/-- The true original exterior differential pullback retains its genuine whole-cover frame. -/
theorem unitCoverTopPullback_generator :
    topPullback (R := k) (A := R) (B := UnitCover N u) n (affineCanonicalGenerator b) =
      affineCanonicalGenerator (unitCoverDifferentialBasis N u hN htame b) := by
  let : Algebra.Etale R (UnitCover N u) := unitCover_etale N u hN htame
  exact topPullback_generator b

/-- The entire original variable-degree tame cover has actual top differential canonical duality. -/
def unitCoverCanonicalIso :
    ModuleCat.of (UnitCover N u) (affineCanonicalModule k (UnitCover N u) n) ≅
      (coextendScalars (algebraMap R (UnitCover N u))).obj
        (ModuleCat.of R (affineCanonicalModule k R n)) :=
  (affineCanonicalTrivialization (unitCoverDifferentialBasis N u hN htame b)).toModuleIso ≪≫
    unitCoverTraceIso N u hN htame ≪≫
      (coextendScalars (algebraMap R (UnitCover N u))).mapIso
        (affineCanonicalTrivialization b).symm.toModuleIso

/-- The whole actual canonical functional is native trace of every original coefficient product. -/
theorem unitCoverCanonicalIso_apply (w : affineCanonicalModule k (UnitCover N u) n)
    (c : UnitCover N u) :
    (unitCoverCanonicalIso N u hN htame b).hom w c =
      Algebra.trace R (UnitCover N u)
        (c * affineCanonicalTrivialization (unitCoverDifferentialBasis N u hN htame b) w) •
          affineCanonicalGenerator b := by
  change (affineCanonicalTrivialization b).symm
    (unitCoverTraceMap N u
      (affineCanonicalTrivialization (unitCoverDifferentialBasis N u hN htame b) w) c) = _
  rw [unitCoverTraceMap_apply]
  exact (affineCanonical_eq_smul_generator b
    ((affineCanonicalTrivialization b).symm
      (Algebra.trace R (UnitCover N u)
        (c * affineCanonicalTrivialization (unitCoverDifferentialBasis N u hN htame b) w)))).trans
      (by rw [LinearEquiv.apply_symm_apply])

/-- The actual native canonical counit on the WHOLE original simultaneous tame coefficient cover. -/
def unitCoverCanonicalCounit :
    (restrictScalars (algebraMap R (UnitCover N u))).obj
        (ModuleCat.of (UnitCover N u) (affineCanonicalModule k (UnitCover N u) n)) ⟶
      ModuleCat.of R (affineCanonicalModule k R n) :=
  (restrictScalars (algebraMap R (UnitCover N u))).map (unitCoverCanonicalIso N u hN htame b).hom ≫
    (restrictCoextendScalarsAdj (algebraMap R (UnitCover N u))).counit.app
      (ModuleCat.of R (affineCanonicalModule k R n))

/-- The actual whole native counit is trace on each coefficient of the genuine differential frame. -/
theorem unitCoverCanonicalCounit_generator (c : UnitCover N u) :
    unitCoverCanonicalCounit N u hN htame b
      (c • affineCanonicalGenerator (unitCoverDifferentialBasis N u hN htame b)) =
        Algebra.trace R (UnitCover N u) c • affineCanonicalGenerator b := by
  change (unitCoverCanonicalIso N u hN htame b).hom
    (c • affineCanonicalGenerator (unitCoverDifferentialBasis N u hN htame b)) (1 : UnitCover N u) = _
  rw [unitCoverCanonicalIso_apply, map_smul, affineCanonicalTrivialization_generator,
    smul_eq_mul, mul_one, one_mul]

/-- Every original base top form has the actual intrinsic trace normalization, on all original unit-root factors. -/
theorem unitCoverCanonicalCounit_pulled_topform (c : UnitCover N u) (w : affineCanonicalModule k R n) :
    unitCoverCanonicalCounit N u hN htame b (c • topPullback (R := k) (A := R) (B := UnitCover N u) n w) =
      Algebra.trace R (UnitCover N u) c • w := by
  conv_lhs => rw [affineCanonical_eq_smul_generator b w]
  rw [map_smulₛₗ, unitCoverTopPullback_generator N u hN htame b, smul_smul,
    unitCoverCanonicalCounit_generator]
  rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul,
    mul_comm, ← smul_smul, ← affineCanonical_eq_smul_generator b w]

/-- Whole actual canonical trace is independent of the original genuine base differential frame. -/
theorem unitCoverCanonicalCounit_frame_independent
    (b' : Module.Basis (Fin n) R (KaehlerDifferential k R)) :
    unitCoverCanonicalCounit N u hN htame b' = unitCoverCanonicalCounit N u hN htame b := by
  ext w
  rw [affineCanonical_eq_smul_generator (unitCoverDifferentialBasis N u hN htame b) w]
  rw [← unitCoverTopPullback_generator N u hN htame b,
    unitCoverCanonicalCounit_pulled_topform, unitCoverCanonicalCounit_pulled_topform]

/-- Genuine original etale coordinates produce the entire canonical duality internally, without an Omega-frame premise. -/
def chartUnitCoverCanonicalIso (a : MvPolynomial (Fin n) k →ₐ[k] R) (ha : a.toRingHom.FormallyEtale) :
    ModuleCat.of (UnitCover N u) (affineCanonicalModule k (UnitCover N u) n) ≅
      (coextendScalars (algebraMap R (UnitCover N u))).obj
        (ModuleCat.of R (affineCanonicalModule k R n)) :=
  unitCoverCanonicalIso N u hN htame (NadelCanonicalUnitRoot.chartDifferentialBasis k R a ha)

end EnvelopeProperty.Vanishing.NadelCanonicalMixed
