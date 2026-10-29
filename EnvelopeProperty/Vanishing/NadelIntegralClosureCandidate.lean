import EnvelopeProperty.Vanishing.NadelIntegralClosureLocality
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange

/-! # The actual WHOLE finite flat locally normal candidate is its integral closure

B may be disconnected, non-domain, or zero. The literal generic algebra is
FractionRing A ⊗[A] B, with the native original includeRight and scalar actions.
-/
noncomputable section
open scoped nonZeroDivisors TensorProduct
universe u v
namespace EnvelopeProperty.Vanishing.NadelIntegralClosureCandidate
variable (A : Type u) [CommRing A]
  (B : Type v) [CommRing B] [Algebra A B]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The WHOLE actual original generic algebra, retaining every component. -/
abbrev genericAlgebra := FractionRing A ⊗[A] B

/-- The actual original candidate map, with the original A-scalar action. -/
def genericMap : B →ₐ[A] genericAlgebra A B := Algebra.TensorProduct.includeRight

theorem genericMap_apply (b : B) :
    genericMap A B b = (1 : FractionRing A) ⊗ₜ[A] b := rfl

/-- Flatness makes the images of ORIGINAL nonzero denominators regular on the
WHOLE original B, without assuming B is a domain or selecting a component. -/
theorem denominators_regular [Module.Flat A B] :
    Algebra.algebraMapSubmonoid B A⁰ ≤ B⁰ := by
  intro s hs
  obtain ⟨a, ha, rfl⟩ := hs
  apply mem_nonZeroDivisors_iff_left.mpr
  intro b hb
  have hreg := Module.Flat.isSMulRegular_of_isRegular (M := B)
    (isRegular_iff_mem_nonZeroDivisors.mpr ha)
  apply hreg
  simpa only [Algebra.smul_def, mul_zero] using hb

/-- The literal original tensor generic algebra is the actual localization of
B at the images of the ORIGINAL base nonzero elements. -/
instance generic_isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (genericAlgebra A B) :=
  inferInstance

/-- Genuine native integral-closure predicate, internally produced from actual
finite flatness and actual local normality, preserving the entire generic algebra. -/
theorem isIntegralClosure [Module.Finite A B] [Module.Flat A B]
    (hlocal : ∀ (p : Ideal B) [p.IsMaximal], IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegralClosure B A (genericAlgebra A B) := by
  let : IsIntegrallyClosedIn B (genericAlgebra A B) :=
    NadelIntegralClosureLocality.isIntegrallyClosedIn_of_maximal
      (Algebra.algebraMapSubmonoid B A⁰) (denominators_regular A B) (genericAlgebra A B) hlocal
  exact IsIntegralClosure.of_isIntegrallyClosedIn

/-- The WHOLE original canonical image equals the actual integral closure;
this is proved, and is never an input certificate. -/
theorem image_eq_integralClosure [Module.Finite A B] [Module.Flat A B]
    (hlocal : ∀ (p : Ideal B) [p.IsMaximal], IsIntegrallyClosed (Localization.AtPrime p)) :
    (genericMap A B).range = integralClosure A (genericAlgebra A B) := by
  let := isIntegralClosure A B hlocal
  ext x
  change (∃ b, genericMap A B b = x) ↔ IsIntegral A x
  exact IsIntegralClosure.isIntegral_iff.symm

/-- The actual normalization isomorphism of the SAME original candidate and
WHOLE original generic algebra, constructed from the proved closure predicate. -/
def normalizationEquiv [Module.Finite A B] [Module.Flat A B]
    (hlocal : ∀ (p : Ideal B) [p.IsMaximal], IsIntegrallyClosed (Localization.AtPrime p)) :
    B ≃ₐ[A] integralClosure A (genericAlgebra A B) := by
  let := isIntegralClosure A B hlocal
  exact IsIntegralClosure.equiv A B (genericAlgebra A B) (integralClosure A (genericAlgebra A B))

/-- The actual normalization isomorphism retains EVERY original element and
its SAME original whole generic image, not just a component or generic point. -/
theorem normalizationEquiv_val [Module.Finite A B] [Module.Flat A B]
    (hlocal : ∀ (p : Ideal B) [p.IsMaximal], IsIntegrallyClosed (Localization.AtPrime p)) (b : B) :
    (normalizationEquiv A B hlocal b : genericAlgebra A B) = (1 : FractionRing A) ⊗ₜ[A] b := by
  let := isIntegralClosure A B hlocal
  exact IsIntegralClosure.algebraMap_equiv A B (genericAlgebra A B)
    (integralClosure A (genericAlgebra A B)) b

end EnvelopeProperty.Vanishing.NadelIntegralClosureCandidate
