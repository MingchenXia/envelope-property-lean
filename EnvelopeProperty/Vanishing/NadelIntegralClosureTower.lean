import EnvelopeProperty.Vanishing.NadelIntegralClosureCandidate

/-! # The SAME raw integral algebra and candidate retain the WHOLE normalization

The raw action is constructed from the actual original A-algebra map into B.
No scalar matching, integral-closure equality or normalization iso is an input.
-/
noncomputable section
open scoped TensorProduct
universe u v w z
namespace EnvelopeProperty.Vanishing.NadelIntegralClosureTower
open NadelIntegralClosureCandidate

/-- Integrality transitivity identifies ALL original elements of the two whole
closures. Subrings are used since their original scalar bases are different. -/
theorem integralClosure_subrings_eq (A : Type u) [CommRing A]
    (R : Type w) [CommRing R] [Algebra A R] [Algebra.IsIntegral A R]
    (E : Type z) [CommRing E] [Algebra A E] [Algebra R E] [IsScalarTower A R E] :
    (integralClosure A E).toSubring = (integralClosure R E).toSubring := by
  ext x
  change IsIntegral A x ↔ IsIntegral R x
  exact ⟨fun hx => hx.tower_top, fun hx => isIntegral_trans (R := A) x hx⟩

variable (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
  {R : Type w} [CommRing R] [Algebra A R] (rawMap : R →ₐ[A] B)
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The ACTUAL original raw-to-candidate map defines the actual raw action on B. -/
@[instance_reducible] def rawCandidateAlgebra : Algebra R B := rawMap.toRingHom.toAlgebra

/-- The ACTUAL original raw generic action is the composite with the WHOLE
original candidate generic map, not a matching certificate. -/
@[instance_reducible] def rawGenericAlgebra : Algebra R (genericAlgebra A B) :=
  ((genericMap A B).comp rawMap).toRingHom.toAlgebra

/-- Every original raw element retains its actual whole generic image. -/
theorem rawGeneric_algebraMap (r : R) :
    letI := rawGenericAlgebra A B rawMap
    algebraMap R (genericAlgebra A B) r = (1 : FractionRing A) ⊗ₜ[A] rawMap r := rfl

private theorem rawBaseScalarTower :
    letI := rawGenericAlgebra A B rawMap
    IsScalarTower A R (genericAlgebra A B) := by
  let := rawGenericAlgebra A B rawMap
  apply IsScalarTower.of_algebraMap_eq'
  ext a
  exact (((genericMap A B).comp rawMap).commutes a).symm

private theorem rawCandidateScalarTower :
    letI := rawCandidateAlgebra A B rawMap
    letI := rawGenericAlgebra A B rawMap
    IsScalarTower R B (genericAlgebra A B) := by
  let := rawCandidateAlgebra A B rawMap
  let := rawGenericAlgebra A B rawMap
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The ACTUAL original raw integral algebra and original base have exactly the
same WHOLE closure subring in the SAME original generic algebra. -/
theorem integralClosure_subring_eq_raw [Algebra.IsIntegral A R] :
    letI := rawGenericAlgebra A B rawMap
    (integralClosure A (genericAlgebra A B)).toSubring =
      (integralClosure R (genericAlgebra A B)).toSubring := by
  let := rawGenericAlgebra A B rawMap
  let := rawBaseScalarTower A B rawMap
  exact integralClosure_subrings_eq A R (genericAlgebra A B)

/-- Genuine native integral closure of the SAME raw algebra, with all actual
raw scalar actions constructed internally from its original A-algebra map. -/
theorem isIntegralClosure_raw [Module.Finite A B] [Module.Flat A B] [Algebra.IsIntegral A R]
    (hlocal : ∀ (p : Ideal B) [p.IsMaximal], IsIntegrallyClosed (Localization.AtPrime p)) :
    letI := rawCandidateAlgebra A B rawMap
    letI := rawGenericAlgebra A B rawMap
    IsIntegralClosure B R (genericAlgebra A B) := by
  let := rawCandidateAlgebra A B rawMap
  let := rawGenericAlgebra A B rawMap
  let := rawBaseScalarTower A B rawMap
  let := NadelIntegralClosureCandidate.isIntegralClosure A B hlocal
  exact IsIntegralClosure.tower_top (R := A)

/-- The ACTUAL normalization isomorphism over the original raw algebra, retaining
all components and the original raw-to-candidate action. -/
def rawNormalizationEquiv [Module.Finite A B] [Module.Flat A B] [Algebra.IsIntegral A R]
    (hlocal : ∀ (p : Ideal B) [p.IsMaximal], IsIntegrallyClosed (Localization.AtPrime p)) :
    letI := rawCandidateAlgebra A B rawMap
    letI := rawGenericAlgebra A B rawMap
    B ≃ₐ[R] integralClosure R (genericAlgebra A B) := by
  letI := rawCandidateAlgebra A B rawMap
  letI := rawGenericAlgebra A B rawMap
  letI := rawCandidateScalarTower A B rawMap
  letI := isIntegralClosure_raw A B rawMap hlocal
  exact IsIntegralClosure.equiv R B (genericAlgebra A B) (integralClosure R (genericAlgebra A B))

/-- The raw normalization retains EVERY original element's WHOLE original
canonical image, without selecting any component. -/
theorem rawNormalizationEquiv_val [Module.Finite A B] [Module.Flat A B] [Algebra.IsIntegral A R]
    (hlocal : ∀ (p : Ideal B) [p.IsMaximal], IsIntegrallyClosed (Localization.AtPrime p)) (b : B) :
    letI := rawCandidateAlgebra A B rawMap
    letI := rawGenericAlgebra A B rawMap
    (rawNormalizationEquiv A B rawMap hlocal b : genericAlgebra A B) =
      (1 : FractionRing A) ⊗ₜ[A] b := by
  let := rawCandidateAlgebra A B rawMap
  let := rawGenericAlgebra A B rawMap
  let := rawCandidateScalarTower A B rawMap
  let := isIntegralClosure_raw A B rawMap hlocal
  exact IsIntegralClosure.algebraMap_equiv R B (genericAlgebra A B)
    (integralClosure R (genericAlgebra A B)) b

end EnvelopeProperty.Vanishing.NadelIntegralClosureTower
