/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.ReesChart
import EnvelopeProperty.Berkovich.Blowup
import EnvelopeProperty.Projective.NormalizedSpectrum

/-!
# Actual normalized projective seminorms constructed from original Rees charts

Original centre ratios define the genuine affine projective chart map.
The actual normalized inverse chart gives a normalized graded seminorm,
retaining whole coefficient values and annihilating the whole actual Rees
presentation kernel. No lift or whole-point comparison is assumed.
-/

open scoped NNReal Topology
open MvPolynomial EnvelopeProperty.Berkovich
noncomputable section
namespace EnvelopeProperty.ReesPresentation
variable {A : Type*} [CommRing A] [IsDomain A] {n : ℕ}
    (s : Finset A) (g : Fin (n + 1) → A) (hs : ∀ m, g m ∈ s) (l : Fin (n + 1))

/-- The whole original homogeneous polynomial evaluates in the actual
fraction-adjoin ring at its original centre ratios. -/
def fcPaperPolynomialDehom : MvPolynomial (Fin (n + 1)) A →ₐ[A] blowupChart s (g l) :=
  aeval fun m => chartFrac s (g l) (hs m)

/-- The true affine projective ratio coordinates evaluate at the original
fraction elements, with the actual inherited coefficient action. -/
def fcPaperCoordinateDehom : ProjBerk.CoordinateRing A l →ₐ[A] blowupChart s (g l) :=
  aeval fun m : ProjBerk.ChartIndex l => chartFrac s (g l) (hs m.1)

/-- The selected nonzero original ratio supplies the entire actual
polynomial dehomogenization triangle. -/
theorem fcPaperCoordinateDehom_comp (hl : g l ≠ 0) :
    (fcPaperCoordinateDehom s g hs l).comp (ProjBerk.coordinateDehom l) =
      fcPaperPolynomialDehom s g hs l := by
  ext m
  simp only [AlgHom.comp_apply, ProjBerk.coordinateDehom, aeval_X]
  by_cases hm : m = l
  · subst m
    simp only [ProjBerk.coordinateDehomCoord_self, map_one,
      fcPaperPolynomialDehom, aeval_X, chartFrac_self (hs l) hl]
  · simp only [ProjBerk.coordinateDehomCoord, dif_neg hm,
      fcPaperCoordinateDehom, fcPaperPolynomialDehom, aeval_X]

/-- The actual coordinate-chart bound equals the exact maximum of all
original Rees ratios, including the selected ratio one. -/
theorem fcPaperCoordinateDehom_chartBound (hl : g l ≠ 0)
    (w : Spectrum (blowupChart s (g l))) :
    NormalizedProjectiveSpectrum.chartBound l
      (Spectrum.comap (fcPaperCoordinateDehom s g hs l).toRingHom w) =
        Finset.univ.sup (fun m => w.val (chartFrac s (g l) (hs m))) := by
  rw [NormalizedProjectiveSpectrum.chartBound_eq_sup_dehom]
  apply Finset.sup_congr rfl
  intro m _
  change w.val (fcPaperCoordinateDehom s g hs l (ProjBerk.coordinateDehomCoord l m)) = _
  have he := AlgHom.congr_fun (fcPaperCoordinateDehom_comp s g hs l hl) (X m)
  simpa only [AlgHom.comp_apply, ProjBerk.coordinateDehom, fcPaperPolynomialDehom,
    aeval_X] using congrArg w.val he

/-- The existing genuine normalized inverse coordinate chart constructs the
whole actual projective seminorm from every original paper chart seminorm. -/
def fcPaperNormalizedPoint (w : Spectrum (blowupChart s (g l))) : NormalizedProjectiveSpectrum A n :=
  NormalizedProjectiveSpectrum.coordinateChartInversePoint l
    (Spectrum.comap (fcPaperCoordinateDehom s g hs l).toRingHom w)

/-- Every actual homogeneous polynomial value is the actual whole chart
value divided by the original finite coordinate maximum to its true degree. -/
theorem fcPaperNormalizedPoint_val (hl : g l ≠ 0)
    (w : Spectrum (blowupChart s (g l))) {b : ℕ} {Q : MvPolynomial (Fin (n + 1)) A}
    (hQ : Q.IsHomogeneous b) :
    (fcPaperNormalizedPoint s g hs l w).1.val Q =
      w.val (fcPaperPolynomialDehom s g hs l Q) /
        (Finset.univ.sup (fun m => w.val (chartFrac s (g l) (hs m)))) ^ b := by
  have he := NormalizedProjectiveSpectrum.rawChartPoint_val_homogeneousComponent l
    (Spectrum.comap (fcPaperCoordinateDehom s g hs l).toRingHom w) Q b
  rw [homogeneousComponent_eq_self hQ] at he
  change (fcPaperNormalizedPoint s g hs l w).1.val Q = _ at he
  rw [he, NormalizedProjectiveSpectrum.chartRadius,
    fcPaperCoordinateDehom_chartBound s g hs l hl]
  have hp := AlgHom.congr_fun (fcPaperCoordinateDehom_comp s g hs l hl) Q
  change w.val ((fcPaperCoordinateDehom s g hs l).comp (ProjBerk.coordinateDehom l) Q) * _ = _
  rw [hp, div_eq_mul_inv, inv_pow]

/-- The whole coefficient seminorm is retained exactly by the constructed
normalized projective point. -/
theorem fcPaperNormalizedPoint_val_C (w : Spectrum (blowupChart s (g l))) (a : A) :
    (fcPaperNormalizedPoint s g hs l w).1.val (C a) =
      w.val (algebraMap A (blowupChart s (g l)) a) := by
  change (NormalizedProjectiveSpectrum.rawChartPoint l _).val (C a) = _
  rw [NormalizedProjectiveSpectrum.rawChartPoint_val_C]
  change w.val (fcPaperCoordinateDehom s g hs l (C a)) = _
  rw [← algebraMap_eq, AlgHom.commutes]

/-- Every homogeneous original chart polynomial follows its actual
fraction-field ratio evaluation, preserving the whole numerator. -/
theorem fcPaperPolynomialDehom_coe {b : ℕ} {Q : MvPolynomial (Fin (n + 1)) A}
    (hQ : Q.IsHomogeneous b) :
    (fcPaperPolynomialDehom s g hs l Q : FractionRing A) =
      algebraMap A (FractionRing A) (aeval g Q) /
        (algebraMap A (FractionRing A) (g l)) ^ b := by
  have hmap : (blowupChart s (g l)).val.comp (fcPaperPolynomialDehom s g hs l) =
      aeval (ReesChart.ratios g l) := by
    ext m
    simp only [AlgHom.comp_apply, fcPaperPolynomialDehom, aeval_X]
    rfl
  exact (AlgHom.congr_fun hmap Q).trans (ReesChart.aeval_ratios g l hQ)

/-- The actual whole original presentation kernel vanishes in the actual
fraction chart, by its true homogeneous coefficient formula. -/
theorem fcPaperPolynomialDehom_eq_zero_of_mem_kernel
    {Q : MvPolynomial (Fin (n + 1)) A} (hQ : Q ∈ kernel g) :
    fcPaperPolynomialDehom s g hs l Q = 0 := by
  rw [← sum_homogeneousComponent Q, map_sum]
  apply Finset.sum_eq_zero
  intro b _
  apply Subtype.ext
  rw [fcPaperPolynomialDehom_coe s g hs l (homogeneousComponent_isHomogeneous b Q)]
  have hc := congrArg (fun P => Polynomial.coeff P b) hQ
  change (presentation g Q).coeff b = (0 : Polynomial A).coeff b at hc
  rw [presentation_coeff, Polynomial.coeff_zero] at hc
  rw [hc, map_zero, zero_div]
  rfl

/-- The constructed normalized point annihilates the entire actual
original Rees presentation kernel, with no assumed point lift. -/
theorem fcPaperNormalizedPoint_kernel (hl : g l ≠ 0)
    (w : Spectrum (blowupChart s (g l))) {Q : MvPolynomial (Fin (n + 1)) A}
    (hQ : Q ∈ kernel g) :
    (fcPaperNormalizedPoint s g hs l w).1.val Q = 0 := by
  rw [(fcPaperNormalizedPoint s g hs l w).isGraded Q]
  apply Finset.sup_eq_zero.2
  intro b _
  rw [fcPaperNormalizedPoint_val s g hs l hl w (homogeneousComponent_isHomogeneous b Q),
    fcPaperPolynomialDehom_eq_zero_of_mem_kernel s g hs l
      (homogeneousComponent_mem_kernel g hQ b), map_zero, zero_div]

end EnvelopeProperty.ReesPresentation
