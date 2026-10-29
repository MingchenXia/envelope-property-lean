/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeRelativeValuedPoints

open scoped NNReal Topology
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace EnvelopeProperty.Berkovich.SchemeValuedPoint
variable {A : Type*} [CommRing A]

/-- A genuine original local section has one whole original-ring fraction formula on a true principal neighborhood. -/
theorem exists_section_fraction_near (V : (Spec (CommRingCat.of A)).Opens)
    (a : Γ(Spec (CommRingCat.of A), V)) (x : SchemeValuedPoint (Spec (CommRingCat.of A)))
    (hx : x.point ∈ V) :
    ∃ b h : A, x.point ∈ PrimeSpectrum.basicOpen h ∧
      ∃ i : PrimeSpectrum.basicOpen h ≤ V,
        ∀ (y : SchemeValuedPoint (Spec (CommRingCat.of A))) (hy : y.point ∈ PrimeSpectrum.basicOpen h),
          eval y V (i hy) a = ValuedPoint.eval (toValuedPoint y) b / ValuedPoint.eval (toValuedPoint y) h := by
  obtain ⟨h, hxh, i, b, hs⟩ := StructureSheaf.exists_const V a x.point hx
  refine ⟨b, h, hxh, i, ?_⟩
  intro y hy
  have he := ofValuedPoint_eval_of_const (toValuedPoint y) V a b h i hs hy
  simpa only [ofValuedPoint_toValuedPoint] using he

/-- If the original section is a genuine unit, the TRUE local fraction numerator and denominator never vanish on the whole principal neighborhood. -/
theorem exists_unit_fraction_near (V : (Spec (CommRingCat.of A)).Opens)
    (a : Γ(Spec (CommRingCat.of A), V)ˣ) (x : SchemeValuedPoint (Spec (CommRingCat.of A)))
    (hx : x.point ∈ V) :
    ∃ b h : A, x.point ∈ PrimeSpectrum.basicOpen h ∧
      ∃ i : PrimeSpectrum.basicOpen h ≤ V,
        ∀ (y : SchemeValuedPoint (Spec (CommRingCat.of A))) (hy : y.point ∈ PrimeSpectrum.basicOpen h),
          eval y V (i hy) (a : Γ(Spec (CommRingCat.of A), V)) =
              ValuedPoint.eval (toValuedPoint y) b / ValuedPoint.eval (toValuedPoint y) h ∧
            ValuedPoint.eval (toValuedPoint y) b ≠ 0 ∧ ValuedPoint.eval (toValuedPoint y) h ≠ 0 := by
  obtain ⟨b, h, hxh, i, he⟩ := exists_section_fraction_near V (a : Γ(Spec (CommRingCat.of A), V)) x hx
  refine ⟨b, h, hxh, i, ?_⟩
  intro y hy
  have hn : eval y V (i hy) (a : Γ(Spec (CommRingCat.of A), V)) ≠ 0 := by
    intro hz
    have hz' := (eval_eq_zero_iff y V (i hy) (a : Γ(Spec (CommRingCat.of A), V))).mp hz
    rw [(Spec (CommRingCat.of A)).basicOpen_of_isUnit a.isUnit] at hz'
    exact hz' (i hy)
  refine ⟨he y hy, ?_, ?_⟩
  · intro hb
    exact hn (by rw [he y hy, hb, zero_div])
  · intro hh
    exact hn (by rw [he y hy, hh, div_zero])

end EnvelopeProperty.Berkovich.SchemeValuedPoint
