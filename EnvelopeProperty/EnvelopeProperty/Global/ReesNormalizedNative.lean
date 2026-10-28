/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.ReesPresentation
import EnvelopeProperty.Projective.NativeModelIdeals
import EnvelopeProperty.Projective.HomogeneousQuotient
import EnvelopeProperty.Projective.NativeProper
import EnvelopeProperty.Projective.NativeClosed

/-!
# Actual native Rees points and the entire original normalized kernel locus

The true closed quotient-Proj immersion and its actual scheme image
identify native prescribed-base points with normalized graded seminorms
annihilating the whole original Rees presentation kernel. No old-model
comparison or image-identification certificate is an input.
-/

open scoped NNReal Topology
open CategoryTheory AlgebraicGeometry EnvelopeProperty.Berkovich
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ReesPresentation
variable {A : Type u} [CommRing A] {n : ℕ} (g : Fin (n + 1) → A)
    (v : Valuation A ℝ≥0)

/-- The actual finite-index original Rees quotient scheme. This direct
Proj definition retains arbitrary coefficient-ring universes although the
finite coordinate index type itself lives in Type 0. -/
abbrev fcFiniteScheme :=
  Proj (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
    (homogeneousKernel g).toIdeal)

/-- The genuine original finite-index quotient-Proj immersion. -/
def fcFiniteImmersion : fcFiniteScheme g ⟶ ProjBerk.NativeProjectiveScheme A n :=
  GradedQuotient.quotientSchemeMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
    (homogeneousKernel g)

/-- The actual original finite-index quotient immersion is closed. -/
instance fcFiniteImmersion_isClosedImmersion : IsClosedImmersion (fcFiniteImmersion g) := by
  unfold fcFiniteImmersion
  infer_instance

/-- The actual finite-index Rees scheme retains the entire original
coefficient-scheme projection. -/
def fcFiniteProjection : fcFiniteScheme g ⟶ Spec (CommRingCat.of A) :=
  fcFiniteImmersion g ≫ ProjBerk.nativeStructureMap

/-- The genuine finite projective presentation derives properness of the
actual original Rees projection without a domain or nonzero-generator input. -/
instance fcFiniteProjection_isProper : IsProper (fcFiniteProjection g) := by
  let : IsProper (ProjBerk.nativeStructureMap (R := A) (n := n)) :=
    ProjBerk.nativeStructureMap_isProper
  unfold fcFiniteProjection
  infer_instance

/-- The actual closed-projective support locus is exactly the entire
original Rees polynomial kernel zero locus, without taking a radical. -/
theorem fc_normalizedClosedLocus_immersion :
    ProjBerk.normalizedClosedLocus v (fcFiniteImmersion g) =
      {w : RelativeNormalizedProjectiveSpectrum v n | ∀ Q ∈ kernel g, w.1.1.val Q = 0} := by
  ext w
  change NormalizedProjectiveSpectrum.nativeSupport w.1 ∈ Set.range
      (GradedQuotient.quotientSchemeMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
        (homogeneousKernel g)) ↔ _
  rw [GradedQuotient.range_quotientSchemeMap]
  rfl

/-- The genuine original Rees scheme's entire native prescribed-base space
is the true normalized homogeneous kernel locus, including topology. -/
def fcNativeNormalizedHomeomorph :
    RelativeSchemeValuedPoint v (fcFiniteProjection g) ≃ₜ
      {w : RelativeNormalizedProjectiveSpectrum v n // ∀ Q ∈ kernel g, w.1.1.val Q = 0} :=
  (ProjBerk.nativeClosedProjectiveHomeomorph v (fcFiniteImmersion g)).trans
    (Homeomorph.setCongr (fc_normalizedClosedLocus_immersion g v))

/-- The constructed homeomorphism retains the entire native image point
under the original actual closed projective Rees immersion. -/
theorem fcNativeNormalizedHomeomorph_apply
    (x : RelativeSchemeValuedPoint v (fcFiniteProjection g)) :
    RelativeNormalizedProjectiveSpectrum.nativeHomeomorph v (fcNativeNormalizedHomeomorph g v x).1 =
      RelativeSchemeValuedPoint.map (fcFiniteImmersion g) rfl x :=
  ProjBerk.nativeClosedProjectiveHomeomorph_apply v (fcFiniteImmersion g) x

end EnvelopeProperty.ReesPresentation
