import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.AffineBlowUp.Chart
/-! # The entire original finite ratio family generates the whole native Rees chart -/
noncomputable section
open AlgebraicGeometry
universe u v
namespace EnvelopeProperty.Vanishing.NadelNefBigReesRatios

theorem adjoin_ratios_eq_top {A : Type u} [CommRing A] (I : Ideal A)
    {ι : Type v} (g : ι → I) (hspan : Ideal.span (Set.range (fun i => (g i : A))) = I) (a : I) :
    Algebra.adjoin A (Set.range (fun i => affineBlowUpAlgebra.ratio I a (g i))) = ⊤ := by
  apply Subalgebra.map_injective (f := (affineBlowUpAlgebra I a).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  have hset : ((affineBlowUpAlgebra I a).val ''
      Set.range (fun i => affineBlowUpAlgebra.ratio I a (g i))) =
      (fun x => Localization.mk x ⟨(a : A), Submonoid.mem_powers (a : A)⟩) ''
        Set.range (fun i => (g i : A)) := by
    ext z
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨g i, ⟨i, rfl⟩, by change _ = awayFrac _ 1 _; rw [awayFrac_one]⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨affineBlowUpAlgebra.ratio I a (g i), ⟨i, rfl⟩, by change awayFrac _ 1 _ = _; rw [awayFrac_one]⟩
  rw [hset]
  exact (congrArg (fun J : Ideal A => affineBlowUpAlgebra J (a : A)) hspan.symm).trans
    (affineBlowUpAlgebra_span_eq_adjoin (Set.range (fun i => (g i : A))) (a : A)) |>.symm
end EnvelopeProperty.Vanishing.NadelNefBigReesRatios
