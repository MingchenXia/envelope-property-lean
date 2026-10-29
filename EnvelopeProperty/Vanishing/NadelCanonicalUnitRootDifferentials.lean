import EnvelopeProperty.Vanishing.NadelCanonicalUnitRootDual
import EnvelopeProperty.Vanishing.NadelCanonicalEtaleBaseChange

/-! # Actual original top differential modules on the entire tame root algebra -/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelCanonicalUnitRoot

open CategoryTheory ModuleCat CanonicalGeometry NadelFiniteDuality NadelCanonicalBaseChange
open scoped TensorProduct

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (m : ℕ) (u : Aˣ)

/-- The original root coefficient homomorphism, fixed before any further scalar structure. -/
def rootStructure : A →+* Root m (u : A) := algebraMap A (Root m (u : A))

/-- The actual original small coefficient map on the entire root algebra. -/
def rootConstants : R →+* Root m (u : A) :=
  (rootStructure A m u).comp (algebraMap R A)

/-- The actual R-algebra structure obtained from the original whole coefficient tower. -/
@[instance_reducible]
def rootRAlgebra : Algebra R (Root m (u : A)) := inferInstance

/-- The native small-ring action is exactly the original coefficient tower. -/
theorem rootRAlgebra_map :
    @algebraMap R (Root m (u : A)) _ _ (rootRAlgebra R A m u) =
      rootConstants R A m u := rfl

/-- The actual target canonical module is a native top exterior Kähler module. -/
abbrev rootCanonicalModule (n : ℕ) :=
  letI := rootRAlgebra R A m u
  affineCanonicalModule R (Root m (u : A)) n

/-- The true original exterior Kähler pullback to the whole unit-root source. -/
def canonicalPullback (n : ℕ) :
    affineCanonicalModule R A n →ₛₗ[rootStructure A m u] rootCanonicalModule R A m u n := by
  let := rootRAlgebra R A m u
  let : IsScalarTower R A (Root m (u : A)) := inferInstance
  exact topPullback n

/-- The actual base differential frame transports to a genuine native frame on the whole root algebra. -/
def rootDifferentialBasis {n : ℕ} (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (hN : IsUnit ((m + 1 : ℕ) : A)) :
    letI := rootRAlgebra R A m u
    Module.Basis (Fin n) (Root m (u : A)) (KaehlerDifferential R (Root m (u : A))) := by
  let := rootRAlgebra R A m u
  let : IsScalarTower R A (Root m (u : A)) := inferInstance
  let : Algebra.Etale A (Root m (u : A)) := root_etale m u hN
  exact affineDifferentialBasisOfFormallyEtale b

/-- The actual unit-root Omega comparison is produced by genuine native étale and exterior base change. -/
def canonicalTensorIso {n : ℕ} (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (hN : IsUnit ((m + 1 : ℕ) : A)) :
    Root m (u : A) ⊗[A] affineCanonicalModule R A n ≃ₗ[Root m (u : A)]
      rootCanonicalModule R A m u n := by
  let := rootRAlgebra R A m u
  let : IsScalarTower R A (Root m (u : A)) := inferInstance
  let : Algebra.Etale A (Root m (u : A)) := root_etale m u hN
  exact etaleTopEquiv b

/-- The actual canonical pullback preserves the true original top differential frame. -/
theorem canonicalPullback_generator {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A)) (hN : IsUnit ((m + 1 : ℕ) : A)) :
    canonicalPullback R A m u n (affineCanonicalGenerator b) =
      affineCanonicalGenerator (rootDifferentialBasis R A m u b hN) := by
  let := rootRAlgebra R A m u
  let : IsScalarTower R A (Root m (u : A)) := inferInstance
  let : Algebra.Etale A (Root m (u : A)) := root_etale m u hN
  exact topPullback_generator b

/-- The actual whole unit-root tensor comparison retains the same true top differential frame. -/
theorem canonicalTensorIso_generator {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A)) (hN : IsUnit ((m + 1 : ℕ) : A)) :
    canonicalTensorIso R A m u b hN (1 ⊗ₜ[A] affineCanonicalGenerator b) =
      affineCanonicalGenerator (rootDifferentialBasis R A m u b hN) := by
  let := rootRAlgebra R A m u
  let : IsScalarTower R A (Root m (u : A)) := inferInstance
  let : Algebra.Etale A (Root m (u : A)) := root_etale m u hN
  exact etaleTopEquiv_generator b

end EnvelopeProperty.Vanishing.NadelCanonicalUnitRoot
