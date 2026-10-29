/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.FiniteCurveNormalization
import EnvelopeProperty.Berkovich.SchemeIdealPullback
import EnvelopeProperty.Berkovich.SchemeModelIdealPullback
import EnvelopeProperty.Berkovich.SchemeModelNoetherian
import EnvelopeProperty.Berkovich.SchemeIntegralImage

/-!
# Actual finite affine normalization and original ideal pullback

The true integral-closure ring constructs a literal Spec normalization map,
finite and surjective over a finite-type perfect-field curve algebra. The real
coefficient curve map is finite and flat under genuine principal-domain and
injectivity hypotheses. Actual original affine ideal data pull back as whole
ideal images, and the entire stalk-image law is retained.

The optional norm/log corollaries concern a GIVEN proper bounded coefficient
model f: Spec(B) to Spec(R), not idealNorm over all coefficients of a valued
field curve. They do not construct the paper's field-curve model, and generally
do not supply points with a prescribed nontrivial field valuation. Original
ideal data are preserved. No normalized smoothness, arbitrary model existence,
analytic potential comparison or continuation theorem is claimed.
-/

open scoped NNReal ENNReal Topology
open Topology CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace EnvelopeProperty.CurveNormalization
variable {A B : Type u} [CommRing A] [CommRing B]

/-- The actual affine normalization scheme from the original curve fraction field. -/
abbrev scheme (B : Type u) [CommRing B] : Scheme.{u} := Spec (CommRingCat.of (Ring B))

/-- The actual original normalization projection, retaining every curve coefficient. -/
def projection (B : Type u) [CommRing B] : scheme B ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (inclusion B))

/-- The true normalization's original coefficient-curve morphism. -/
def curveProjection (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    scheme B ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (coefficientMap A B))

/-- Entire normalization/base-curve morphisms commute with the original curve map. -/
theorem projection_coefficientMap [Algebra A B] :
    projection B ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = curveProjection A B := by
  dsimp only [projection, curveProjection]
  rw [← Spec.map_comp]
  rfl

/-- The true affine normalization projection is finite by perfect-field finite normalization. -/
theorem projection_isFinite (F : Type u) [Field F] [PerfectField F] [IsDomain B]
    [Algebra F B] [Algebra.FiniteType F B] : IsFinite (projection B) :=
  (IsFinite.SpecMap_iff _).mpr (finite_inclusion F B)

/-- The actual original coefficient-curve projection remains finite after normalization. -/
theorem curveProjection_isFinite (F : Type u) [Field F] [PerfectField F] [IsDomain B]
    [Algebra A B] [Module.Finite A B] [Algebra F B] [Algebra.FiniteType F B] :
    IsFinite (curveProjection A B) := (IsFinite.SpecMap_iff _).mpr (finite_coefficientMap F A B)

/-- Genuine injectivity of the original base map gives an actual finite flat normalization map to the principal-domain curve. -/
theorem curveProjection_flat (F : Type u) [Field F] [PerfectField F] [IsDomain A]
    [IsPrincipalIdealRing A] [IsDomain B] [Algebra A B] [Module.Finite A B]
    [Algebra F B] [Algebra.FiniteType F B] (hAB : Function.Injective (algebraMap A B)) :
    AlgebraicGeometry.Flat (curveProjection A B) := Flat.SpecMap_iff.mpr (flat_coefficientMap F A B hAB)

/-- The actual normalization projection is surjective on genuine scheme points. -/
theorem projection_surjective [IsDomain B] : Function.Surjective (projection B) := by
  exact (show (inclusion B).IsIntegral from algebraMap_isIntegral_iff.mpr inferInstance).comap_surjective (inclusion_injective B)

/-- The original affine ideal datum constructed from every actual curve-ring element. -/
def idealSheaf (B : Type u) [CommRing B] (J : Ideal B) : (Spec (CommRingCat.of B)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (J.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)

/-- Actual geometric pullback along normalization extends the entire original ideal without radical replacement. -/
theorem idealSheaf_projection_comap (J : Ideal B) :
    (idealSheaf B J).comap (projection B) = idealSheaf (Ring B) (J.map (inclusion B)) := by
  apply Scheme.IdealSheafData.ext_of_isAffine (X := scheme B)
  rw [Scheme.IdealSheafData.comap_ideal_top_of_isAffine_native]
  simp only [idealSheaf, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map]
  congr 1
  change (projection B).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom =
    (Scheme.ΓSpecIso (CommRingCat.of (Ring B))).inv.hom.comp (inclusion B)
  change ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (projection B).appTop).hom =
    ((CommRingCat.ofHom (inclusion B)) ≫ (Scheme.ΓSpecIso (CommRingCat.of (Ring B))).inv).hom
  exact congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (inclusion B))).symm

/-- The actual ideal stalk pullback is the original full stalk-map image at every normalization point. -/
theorem stalkIdeal_projection_comap (I : (Spec (CommRingCat.of B)).IdealSheafData) (x : scheme B) :
    (I.comap (projection B)).stalkIdeal x =
      (I.stalkIdeal (projection B x)).map ((projection B).stalkMap x).hom :=
  I.paperStalkIdeal_comap (projection B) x

/-- Actual finite normalization preserves the original intrinsic model ideal norm over a bounded proper coefficient model. -/
theorem modelIdealNorm_projection_comap (F R : Type u) [Field F] [PerfectField F]
    [CommRing R] [IsDomain B] [Algebra F B] [Algebra.FiniteType F B]
    {v : Valuation R ℝ≥0} (f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    [IsProper f] (I : (Spec (CommRingCat.of B)).IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : Berkovich.RelativeSchemeValuedPoint v (projection B ≫ f)) :
    letI := projection_isFinite (B := B) F
    Berkovich.RelativeSchemeValuedPoint.modelIdealNorm (I.comap (projection B)) hb y =
      Berkovich.RelativeSchemeValuedPoint.modelIdealNorm I hb
        (Berkovich.RelativeSchemeValuedPoint.map (projection B) rfl y) := by
  let := projection_isFinite (B := B) F
  exact Berkovich.RelativeSchemeValuedPoint.modelIdealNorm_comap I (projection B) rfl hb y

/-- True logarithmic model ideal pullback through normalization retains zero and negative infinity. -/
theorem modelIdealLog_projection_comap (F R : Type u) [Field F] [PerfectField F]
    [CommRing R] [IsDomain B] [Algebra F B] [Algebra.FiniteType F B]
    {v : Valuation R ℝ≥0} (f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    [IsProper f] (I : (Spec (CommRingCat.of B)).IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : Berkovich.RelativeSchemeValuedPoint v (projection B ≫ f)) :
    letI := projection_isFinite (B := B) F
    Berkovich.RelativeSchemeValuedPoint.modelIdealLog (I.comap (projection B)) hb y =
      Berkovich.RelativeSchemeValuedPoint.modelIdealLog I hb
        (Berkovich.RelativeSchemeValuedPoint.map (projection B) rfl y) :=
  congrArg ENNReal.log (modelIdealNorm_projection_comap F R f I hb y)

end EnvelopeProperty.CurveNormalization
