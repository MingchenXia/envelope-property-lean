import EnvelopeProperty.Berkovich.SpectrumFinite
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # The actual completed residue field of the norm point of a complete field -/

open scoped NNReal Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.Spectrum
variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- The genuine original field norm regarded as a point of its entire spectrum. -/
def normPoint : Spectrum K := ⟨NormedField.valuation⟩

/-- The actual canonical coefficient map is an isometry. -/
theorem normPoint_toH_isometry : Isometry (toH (normPoint K)) :=
  AddMonoidHomClass.isometry_of_norm _ (fun a => norm_toH (normPoint K) a)

/-- Its original field image is dense in the true completed residue field. -/
theorem normPoint_toH_denseRange : DenseRange (toH (normPoint K)) := by
  have hmax : (normPoint K).val.supp.IsMaximal := inferInstance
  let := hmax
  have hsurj := Ideal.algebraMap_residueField_surjective (normPoint K).val.supp
  have hr : Set.range (toH (normPoint K)) = Set.range (residueToH (normPoint K)) :=
    hsurj.range_comp (residueToH (normPoint K))
  change Dense (Set.range (toH (normPoint K)))
  rw [hr]
  exact denseRange_residueToH _

/-- Completeness makes the same canonical original coefficient map onto. -/
theorem normPoint_toH_bijective [CompleteSpace K] :
    Function.Bijective (toH (normPoint K)) := by
  have hi := normPoint_toH_isometry K
  refine ⟨hi.injective, ?_⟩
  intro z
  have hz := normPoint_toH_denseRange K z
  rw [hi.isClosedEmbedding.isClosed_range.closure_eq] at hz
  exact hz

/-- The actual completed residue field of a complete normed field is the same coefficient field. -/
def normPointEquiv [CompleteSpace K] : K ≃ₐ[K] H (normPoint K) :=
  AlgEquiv.ofBijective (Algebra.ofId K (H (normPoint K))) (normPoint_toH_bijective K)

/-- This actual comparison is exactly the original canonical coefficient map. -/
theorem normPointEquiv_apply [CompleteSpace K] (a : K) :
    normPointEquiv K a = toH (normPoint K) a := rfl

end EnvelopeProperty.Berkovich.Spectrum
