import EnvelopeProperty.Vanishing.NadelNefBigExceptionalProjectiveCharts
import EnvelopeProperty.Vanishing.NadelNefBigAffineMapSpectrum
import EnvelopeProperty.Vanishing.NadelNefBigReesRatios
import EnvelopeProperty.Alterations.Geometry.FiniteProjectiveAffineClosed

noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelNefBigExceptionalProjectiveTuple
open NadelNefBigExceptionalGenerators NadelNefBigExceptionalFrames NadelNefBigExceptionalProjectiveCharts
open GeneratedLineProjectiveAffineMap SchemeGeneratedLineCoefficients
open Alterations.Geometry.FiniteProjective
variable {A : Type u} [CommRing A] (I : Ideal A) {ι : Type u} [Fintype ι]
    (g : ι → I) (hspan : Ideal.span (Set.range (fun i => (g i : A))) = I)

private instance : Fintype (generatingSections I g hspan).I := (inferInstance : Fintype ι)
private instance pullbackIndexFintype {X Y : Scheme.{u}} {M : X.Modules} (f : Y ⟶ X)
    (G : M.GeneratingSections) [Fintype G.I] :
    Fintype (ClosedProjectiveGlobalGeneration.pullback_generatingSections f G).I :=
  (inferInstance : Fintype G.I)

omit [Fintype ι] in
private theorem coefficient_spec (a : I) (i : ι) :
    (Scheme.ΓSpecIso (.of (affineBlowUpAlgebra I a))).hom.hom
      (coefficient (ClosedProjectiveGlobalGeneration.pullback_generatingSections (affineBlowUp.chart I a)
        (generatingSections I g hspan)) (chartFrame I a) i) = affineBlowUpAlgebra.ratio I a (g i) :=
  (congrArg (Scheme.ΓSpecIso (.of (affineBlowUpAlgebra I a))).hom.hom
    (coefficient_chartFrame I g hspan a i)).trans
      ((Scheme.ΓSpecIso (.of (affineBlowUpAlgebra I a))).inv_hom_id_apply _)

include hspan in
theorem span_padded_ratios (a : I) :
    Ideal.span (Set.range (paddedCoefficients (fun i => affineBlowUpAlgebra.ratio I a (g i)))) = ⊤ := by
  let K := ClosedProjectiveGlobalGeneration.pullback_generatingSections (affineBlowUp.chart I a)
    (generatingSections I g hspan)
  have h := congrArg (Ideal.map (Scheme.ΓSpecIso (.of (affineBlowUpAlgebra I a))).hom.hom)
    (span_coefficients_eq_top K (chartFrame I a))
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
  have h' : Ideal.span (Set.range (fun i : ι =>
      (Scheme.ΓSpecIso (.of (affineBlowUpAlgebra I a))).hom.hom
        (coefficient K (chartFrame I a) i))) = ⊤ := h
  have hc : (fun i : ι => (Scheme.ΓSpecIso (.of (affineBlowUpAlgebra I a))).hom.hom
      (coefficient K (chartFrame I a) i)) = fun i => affineBlowUpAlgebra.ratio I a (g i) :=
    funext (coefficient_spec I g hspan a)
  rw [hc] at h'
  exact span_paddedCoefficients_eq_top _ h'

theorem on_chart_tuple (a : I) :
    affineBlowUp.chart I a ≫ projectiveMap I g hspan =
      affineTupleMap (algebraMap A (affineBlowUpAlgebra I a))
        (paddedCoefficients (fun i => affineBlowUpAlgebra.ratio I a (g i)))
        (span_padded_ratios I g hspan a) := by
  let K := ClosedProjectiveGlobalGeneration.pullback_generatingSections (affineBlowUp.chart I a)
    (generatingSections I g hspan)
  have h0 := on_chart I g hspan a
  have h1 := congrArg (fun p => affineMap p K (chartFrame I a)) (affineBlowUp.chart_π I a)
  have h2 := NadelNefBigAffineMapSpectrum.affineMap_spec (algebraMap A (affineBlowUpAlgebra I a))
    K (chartFrame I a)
  apply h0.trans (h1.trans (h2.trans ?_))
  apply affineTupleMap_congr rfl
  exact congrArg paddedCoefficients (funext (coefficient_spec I g hspan a))

include hspan in
private theorem adjoin_padded_ratios (a : I) :
    Algebra.adjoin A (Set.range (paddedCoefficients (fun i => affineBlowUpAlgebra.ratio I a (g i)))) = ⊤ := by
  apply le_antisymm le_top
  rw [← NadelNefBigReesRatios.adjoin_ratios_eq_top I g hspan a]
  apply Algebra.adjoin_mono
  rintro x ⟨i, rfl⟩
  refine ⟨((Fintype.equivFin ι) i).succ, ?_⟩
  simp only [paddedCoefficients, Fin.cases_succ, Equiv.symm_apply_apply]

theorem chart_isImmersion (i : ι) :
    IsImmersion (affineBlowUp.chart I (g i) ≫ projectiveMap I g hspan) := by
  rw [on_chart_tuple]
  apply affineTupleMap_isImmersion _ _ _ ((Fintype.equivFin ι) i).succ
  · simp only [paddedCoefficients, Fin.cases_succ, Equiv.symm_apply_apply]
    apply Subtype.ext
    change awayFrac (g i : A) 1 (g i : A) = 1
    rw [awayFrac_one]
    exact Localization.mk_self ⟨(g i : A), Submonoid.mem_powers _⟩
  · have halg : (algebraMap A (affineBlowUpAlgebra I (g i))).toAlgebra =
        (inferInstance : Algebra A (affineBlowUpAlgebra I (g i))) := toAlgebra_algebraMap
    exact halg.symm ▸ adjoin_padded_ratios I g hspan (g i)
end EnvelopeProperty.Vanishing.NadelNefBigExceptionalProjectiveTuple
