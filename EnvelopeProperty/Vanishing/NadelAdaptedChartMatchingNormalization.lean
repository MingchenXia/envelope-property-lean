import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingTensor
import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingFinite
import EnvelopeProperty.Vanishing.NadelIntegralClosureTower

/-! # The WHOLE original raw generic normalization, with its actual ratio model

The proved actual whole generic map transports the separately proved genuine
integral-closure criterion. No normalization isomorphism or closure equality
is an input. The entire original raw generic tensor algebra is retained.
-/

noncomputable section
open scoped TensorProduct
universe u
namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.MultiRatio
open NadelMixedKummer NadelIntegralClosureCandidate NadelIntegralClosureTower
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {R : Type u} [CommRing R] [IsDomain R] {q : ℕ}
  (N : Fin q → ℕ) (c b : Fin q → R) (H : Fin q → Fin q)
  (hH : ∀ i, H (H i) = H i) (hN : ∀ i, N (H i) = N i)
  (hb : ∀ i, b (H i) = c (H i))
  (hc : ∀ i, i ≠ H i → c i = c (H i) * b i)
  (hpositive : ∀ i, 0 < N i) (hne : ∀ i, c (H i) ≠ 0)

/-- The actual WHOLE generic comparison is over the SAME original raw
algebra, using the proved triangle on EVERY original raw element. -/
def genericRawAlgEquiv :
    let _ := rawGenericAlgebra R (Ring N b) (rawAlgHom N c b H hN hb hc)
    FractionRing R ⊗[R] Ring N c ≃ₐ[Ring N c] FractionRing R ⊗[R] Ring N b := by
  let := rawGenericAlgebra R (Ring N b) (rawAlgHom N c b H hN hb hc)
  exact {
    toRingEquiv := (genericTensorAlgEquiv N c b H hH hN hb hc hpositive hne).toRingEquiv
    commutes' := fun z => genericTensorAlgEquiv_includeRight N c b H hH hN hb hc hpositive hne z }

/-- The ACTUAL whole ratio model IS the normalization of the SAME original
raw algebra inside its literal WHOLE original generic tensor algebra.
Local normality is the native actual-ring property consumed by the independently
proved whole non-domain criterion, with no global domain assumption on the model. -/
def normalizationEquiv
    (hlocal : ∀ (p : Ideal (Ring N b)) [p.IsMaximal], IsIntegrallyClosed (Localization.AtPrime p)) :
    let _ := rawCandidateAlgebra R (Ring N b) (rawAlgHom N c b H hN hb hc)
    Ring N b ≃ₐ[Ring N c] integralClosure (Ring N c) (FractionRing R ⊗[R] Ring N c) := by
  let := rawCandidateAlgebra R (Ring N b) (rawAlgHom N c b H hN hb hc)
  let := rawGenericAlgebra R (Ring N b) (rawAlgHom N c b H hN hb hc)
  have : Module.Finite R (Ring N c) := VaryingFinite.finite N c hpositive
  have : Algebra.IsIntegral R (Ring N c) := inferInstance
  have : Module.Finite R (Ring N b) := VaryingFinite.finite N b hpositive
  have : Module.Flat R (Ring N b) := VaryingFinite.flat N b hpositive
  exact (rawNormalizationEquiv R (Ring N b) (rawAlgHom N c b H hN hb hc) hlocal).trans
    (genericRawAlgEquiv N c b H hH hN hb hc hpositive hne).mapIntegralClosure.symm

end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.MultiRatio
