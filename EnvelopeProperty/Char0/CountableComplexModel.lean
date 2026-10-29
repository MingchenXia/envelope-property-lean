import EnvelopeProperty.Char0.Embedding
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.Data.Countable.Small

/-! # Actual countable-field complex embeddings and universe-zero tensor models

Only the actual countable coefficient field embeds into C. The original
arbitrary field need not embed. The actual model algebra is shrunk by its
countability, retaining its whole algebra/ideal through the canonical actual
isomorphism. The literal complex tensor is Type0 even if the base field is not.
-/

noncomputable section
open scoped TensorProduct
namespace EnvelopeProperty.Char0.CountableComplexModel
universe u v

/-- The actual countable characteristic-zero coefficient field embeds into C,
using its actual countable algebraic closure and the established embedding. -/
theorem nonempty_complex_embedding (F : Type u) [Field F] [CharZero F] [Countable F] :
    Nonempty (F →+* ℂ) := by
  let : Countable (AlgebraicClosure F) := Cardinal.mk_le_aleph0_iff.mp
    ((Algebra.IsAlgebraic.cardinalMk_le_max F (AlgebraicClosure F)).trans
      (max_le (Cardinal.mk_le_aleph0_iff.mpr inferInstance) le_rfl))
  obtain ⟨ι⟩ := EnvelopeProperty.nonempty_ringHom_complex (AlgebraicClosure F)
  exact ⟨ι.comp (algebraMap F (AlgebraicClosure F))⟩

variable (F : Type u) [Field F] (A₀ : Type v) [CommRing A₀] [Algebra F A₀] [Countable A₀]

/-- The actual original countable model algebra in universe ZERO. -/
abbrev smallModel : Type := Shrink.{0} A₀

/-- The whole actual F-algebra shrinking isomorphism back to the original model. -/
def smallModelEquiv : smallModel A₀ ≃ₐ[F] A₀ := Shrink.algEquiv.{0} F A₀

/-- Actual original smoothness transports to the SAME universe-zero model. -/
theorem smallModel_smooth [Algebra.Smooth F A₀] : Algebra.Smooth F (smallModel A₀) :=
  Algebra.Smooth.of_equiv (smallModelEquiv F A₀).symm

variable [Algebra F ℂ]

/-- The actual complex algebra equivalence preserves the SAME entire model,
with a literal universe-zero source and no smallness assumption on F. -/
def complexTensorEquiv :
    (ℂ ⊗[F] smallModel A₀) ≃ₐ[ℂ] (ℂ ⊗[F] A₀) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : ℂ ≃ₐ[ℂ] ℂ) (smallModelEquiv F A₀)

/-- EVERY whole original pure tensor retains its literal original coefficient. -/
theorem complexTensorEquiv_tmul (c : ℂ) (a : smallModel A₀) :
    complexTensorEquiv F A₀ (c ⊗ₜ[F] a) = c ⊗ₜ[F] smallModelEquiv F A₀ a := rfl

/-- The LITERAL universe-zero complex model is actually smooth, internally
transported from the SAME original coefficient model. -/
theorem complexTensor_smooth [Algebra.Smooth F A₀] :
    Algebra.Smooth ℂ (ℂ ⊗[F] smallModel A₀) := by
  let : Algebra.Smooth F (smallModel A₀) := smallModel_smooth F A₀
  infer_instance

/-- The WHOLE original ideal is preserved by the actual shrinking/tensor square,
including every original ideal generator and arbitrary coefficient combination. -/
theorem map_complexTensor_smallIdeal (I : Ideal A₀) :
    ((I.comap (smallModelEquiv F A₀).toRingHom).map
      (Algebra.TensorProduct.includeRight (R := F) (A := ℂ)).toRingHom).map
        (complexTensorEquiv F A₀).toRingHom =
      I.map (Algebra.TensorProduct.includeRight (R := F) (A := ℂ)).toRingHom := by
  rw [Ideal.map_map]
  have h : (complexTensorEquiv F A₀).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := F) (A := ℂ)).toRingHom =
      (Algebra.TensorProduct.includeRight (R := F) (A := ℂ)).toRingHom.comp
        (smallModelEquiv F A₀).toRingHom := by
    ext a
    rfl
  rw [h, ← Ideal.map_map, Ideal.map_comap_of_surjective (smallModelEquiv F A₀).toRingHom
    (smallModelEquiv F A₀).surjective]

end EnvelopeProperty.Char0.CountableComplexModel
