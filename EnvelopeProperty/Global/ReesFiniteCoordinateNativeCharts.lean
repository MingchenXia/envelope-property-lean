/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.ReesFiniteCoordinateCharts
import EnvelopeProperty.Global.ReesNormalizedChart

/-!
# Whole original Rees-chart and native projective-chart triangles

The actual homogeneous localization maps retain every original fraction.
Their exact ring triangle gives the whole genuine scheme-chart triangle
used to match the native Rees map with normalized paper chart points.
-/

open scoped Classical NNReal
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open EnvelopeProperty.Berkovich
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ReesPresentation
variable {A : Type u} [CommRing A] [IsDomain A] {n : ℕ} (g : Fin (n + 1) → A)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private local instance projectiveChartAlgebra (l : Fin (n + 1)) :
    Algebra A (ProjBerk.HomogeneousChartRing A l) := ProjBerk.homogeneousChartAlgebra l
private local instance reesChartAlgebra (l : Fin (n + 1)) :
    Algebra A (ReesChart.Chart g l) := ReesChart.chartAlgebra g l

omit [CommRing A] [IsDomain A] in
/-- The original finite family belongs to its literal finite set, with no
extra generation witness. -/
theorem fcFinite_mem_generatorSet (m : Fin (n + 1)) : g m ∈ Finset.univ.image g :=
  Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩

/-- The original entire projective homogeneous chart fraction maps to the
same actual centre fraction on both genuine chart-ring routes. -/
theorem fcFinitePaperHomogeneousChartRing_triangle (l : Fin (n + 1)) (hl : g l ≠ 0) :
    (fcFiniteChartEquiv g l hl).toRingHom.comp
      (Away.map (GradedQuotient.gradedMk
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (homogeneousKernel g).toIdeal)
          (MvPolynomial.X l)) =
    (fcPaperCoordinateDehom (Finset.univ.image g) g (fcFinite_mem_generatorSet g) l).toRingHom.comp
      (ProjBerk.homogeneousChartEquiv (R := A) l).toRingHom := by
  apply RingHom.ext
  intro z
  obtain ⟨d, F, hF, rfl⟩ := Away.mk_surjective (ProjBerk.ProjectiveGrading A n)
    (MvPolynomial.isHomogeneous_X A l) z
  change fcFiniteChartEquiv g l hl
      (Away.map (GradedQuotient.gradedMk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
        (homogeneousKernel g).toIdeal) (MvPolynomial.X l)
          (Away.mk (ProjBerk.ProjectiveGrading A n) (MvPolynomial.isHomogeneous_X A l) d F hF)) =
    fcPaperCoordinateDehom (Finset.univ.image g) g (fcFinite_mem_generatorSet g) l
      (ProjBerk.homogeneousChartDehom l
        (Away.mk (ProjBerk.ProjectiveGrading A n) (MvPolynomial.isHomogeneous_X A l) d F hF))
  rw [Away.map_mk, ProjBerk.homogeneousChartDehom_mk]
  apply Subtype.ext
  have hq : Ideal.Quotient.mk (kernel g) F ∈ ReesChart.grading g (d • (1 : ℕ)) :=
    (GradedQuotient.gradedMk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
      (kernel g)).map_mem hF
  change ReesChart.toFractionRing g l hl
    (Away.mk (ReesChart.grading g) (ReesChart.generator_mem g l) d
      (Ideal.Quotient.mk (kernel g) F) hq) = _
  rw [ReesChart.toFractionRing_mk, quotientEvaluation_mk]
  have he := AlgHom.congr_fun
    (fcPaperCoordinateDehom_comp (Finset.univ.image g) g (fcFinite_mem_generatorSet g) l hl) F
  calc
    _ = (fcPaperPolynomialDehom (Finset.univ.image g) g (fcFinite_mem_generatorSet g) l F :
        FractionRing A) :=
      (fcPaperPolynomialDehom_coe (Finset.univ.image g) g (fcFinite_mem_generatorSet g) l
        (show F.IsHomogeneous d from by
          change F.IsHomogeneous (d • (1 : ℕ)) at hF
          simpa only [smul_eq_mul, mul_one] using hF)).symm
    _ = _ := congrArg (fun z : blowupChart (Finset.univ.image g) (g l) => (z : FractionRing A)) he.symm

/-- The whole actual fraction-chart immersion into the same native Rees
scheme commutes with the genuine polynomial projective coordinate chart. -/
theorem fcFinitePaperChartImmersion_comp_immersion (l : Fin (n + 1)) (hl : g l ≠ 0) :
    fcFinitePaperChartImmersion g l hl ≫ fcFiniteImmersion g =
      Spec.map (CommRingCat.ofHom
        (fcPaperCoordinateDehom (Finset.univ.image g) g (fcFinite_mem_generatorSet g) l).toRingHom) ≫
        ProjBerk.nativeCoordinateInclusion l := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A
  let J := homogeneousKernel g
  have hsq := (GradedQuotient.isPullback_awayMap 𝒜 J
    (show 0 < (1 : ℕ) by decide) (MvPolynomial.isHomogeneous_X A l)).w
  rw [fcFinitePaperChartImmersion, Category.assoc]
  rw [show fcFiniteChartImmersion g l ≫ fcFiniteImmersion g =
    Spec.map (CommRingCat.ofHom (Away.map (GradedQuotient.gradedMk 𝒜 J.toIdeal)
      (MvPolynomial.X l))) ≫ Proj.awayι 𝒜 (MvPolynomial.X l)
      (MvPolynomial.isHomogeneous_X A l) (by decide) from hsq.symm]
  change Spec.map (CommRingCat.ofHom (fcFiniteChartEquiv g l hl).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (Away.map (GradedQuotient.gradedMk 𝒜 J.toIdeal)
      (MvPolynomial.X l))) ≫ _) = _
  change _ = Spec.map (CommRingCat.ofHom
    (fcPaperCoordinateDehom (Finset.univ.image g) g (fcFinite_mem_generatorSet g) l).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (ProjBerk.homogeneousChartEquiv (R := A) l).toRingHom) ≫
        (ProjBerk.nativeHomogeneousChartSchemeIso l).inv) ≫ (ProjBerk.nativeCoordinateOpen l).ι
  rw [ProjBerk.nativeHomogeneousChartSchemeIso_eq, Category.assoc]
  erw [Proj.basicOpenIsoSpec_inv_ι]
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ) ≫
    Proj.awayι 𝒜 (MvPolynomial.X l) (MvPolynomial.isHomogeneous_X A l) (by decide))
    (fcFinitePaperHomogeneousChartRing_triangle g l hl)

end EnvelopeProperty.ReesPresentation
