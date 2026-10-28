/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.HomogeneousChart
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import EnvelopeProperty.Berkovich.SchemeRelativeAtlas

/-!
# Native prescribed-base coordinate charts of actual polynomial Proj

The structure morphism is the actual Mathlib Proj degree-zero morphism followed
by the constant-polynomial ring map. The genuine coordinate scheme charts commute
with this original base morphism. Their true native valued-point chart homeomorphisms
preserve every affine polynomial through the actual local section-ring comparison.

The coefficient ring and prescribed real seminorm are arbitrary. No coefficient bound,
field, completion, assumed chart certificate or unrelated coefficient action is needed.
A global normalized graded model comparison and analytic structure sheaf are separate.
-/

open scoped Classical NNReal Topology
open MvPolynomial AlgebraicGeometry CategoryTheory Opposite
open EnvelopeProperty.Berkovich
noncomputable section
namespace EnvelopeProperty.ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type*} [CommRing R] {n : ℕ}
private local instance nativeHomogeneousChartBaseAlgebra (j : Fin (n + 1)) :
    Algebra R (HomogeneousChartRing R j) := homogeneousChartAlgebra j

/-- The true structure morphism of polynomial Proj to its original coefficient scheme. -/
def nativeStructureMap : NativeProjectiveScheme R n ⟶ Spec (CommRingCat.of R) :=
  AlgebraicGeometry.Proj.toSpecZero (ProjectiveGrading R n) ≫
    Spec.map (CommRingCat.ofHom (homogeneousCoefficientZero R n))

set_option backward.isDefEq.respectTransparency false in
/-- The constructed chart morphism is the canonical Mathlib homogeneous-fraction chart. -/
theorem nativeHomogeneousChartSchemeIso_hom_eq (j : Fin (n + 1)) :
    (nativeHomogeneousChartSchemeIso (R := R) j).hom =
      AlgebraicGeometry.Proj.basicOpenToSpec (ProjectiveGrading R n) (MvPolynomial.X j) := by
  apply Scheme.fullyFaithfulForgetToLocallyRingedSpace.map_injective
  change ProjectiveSpectrum.Proj.toSpec (ProjectiveGrading R n) (MvPolynomial.X j) = _
  symm
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [AlgebraicGeometry.Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Equality with the actual canonical Mathlib Proj coordinate-chart isomorphism. -/
theorem nativeHomogeneousChartSchemeIso_eq (j : Fin (n + 1)) :
    nativeHomogeneousChartSchemeIso (R := R) j =
      AlgebraicGeometry.Proj.basicOpenIsoSpec (ProjectiveGrading R n) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j) (by decide : 0 < (1 : ℕ)) := by
  apply Iso.ext
  exact nativeHomogeneousChartSchemeIso_hom_eq j

set_option backward.isDefEq.respectTransparency false in
/-- The full homogeneous localization chart commutes with the original coefficient morphism. -/
theorem nativeHomogeneousChart_over_base (j : Fin (n + 1)) :
    (nativeHomogeneousChartSchemeIso (R := R) j).inv ≫
      (nativeCoordinateOpen j).ι ≫ nativeStructureMap =
        Spec.map (CommRingCat.ofHom (homogeneousChartCoefficients (R := R) j)) := by
  rw [nativeHomogeneousChartSchemeIso_eq, nativeStructureMap, ← Category.assoc,
    ← Category.assoc]
  erw [AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι,
    AlgebraicGeometry.Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The full affine coordinate chart commutes with the original coefficient morphism. -/
theorem nativeCoordinateChart_over_base (j : Fin (n + 1)) :
    (nativeCoordinateSchemeIso (R := R) j).inv ≫
      (nativeCoordinateOpen j).ι ≫ nativeStructureMap =
        Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R j))) := by
  change (Spec.map (CommRingCat.ofHom (homogeneousChartEquiv (R := R) j).toRingHom) ≫
    (nativeHomogeneousChartSchemeIso j).inv) ≫ _ ≫ _ = _
  rw [Category.assoc, nativeHomogeneousChart_over_base, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (homogeneousChartEquiv (R := R) j).commutes r

/-- The actual affine coordinate chart inclusion into the native polynomial Proj scheme. -/
def nativeCoordinateInclusion (j : Fin (n + 1)) :
    Spec (CommRingCat.of (CoordinateRing R j)) ⟶ NativeProjectiveScheme R n :=
  (nativeCoordinateSchemeIso j).inv ≫ (nativeCoordinateOpen j).ι

/-- The genuine coordinate chart inclusion is an actual scheme open immersion. -/
theorem nativeCoordinateInclusion_isOpenImmersion (j : Fin (n + 1)) :
    IsOpenImmersion (nativeCoordinateInclusion (R := R) j) := by
  unfold nativeCoordinateInclusion
  infer_instance

private local instance nativeCoordinateInclusion_openImmersion (j : Fin (n + 1)) :
    IsOpenImmersion (nativeCoordinateInclusion (R := R) j) :=
  nativeCoordinateInclusion_isOpenImmersion j

/-- Its scheme image is exactly the genuine coordinate open. -/
theorem nativeCoordinateInclusion_opensRange (j : Fin (n + 1)) :
    (nativeCoordinateInclusion (R := R) j).opensRange = nativeCoordinateOpen j :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (nativeCoordinateOpen j).opensRange_ι

/-- Actual native coordinate points over a prescribed whole base point form the relative spectrum. -/
def nativeCoordinateSpectrumHomeomorph (v : Valuation R ℝ≥0) (j : Fin (n + 1)) :
    {y : RelativeSchemeValuedPoint v (nativeStructureMap (R := R) (n := n)) //
      y.1.point ∈ nativeCoordinateOpen (R := R) j} ≃ₜ RelativeSpectrum v (CoordinateRing R j) :=
  ((RelativeSchemeValuedPoint.affineSpectrumHomeomorph (v := v)).symm.trans
    ((RelativeSchemeValuedPoint.openImmersionHomeomorph (v := v)
      (nativeCoordinateInclusion j) (nativeCoordinateChart_over_base j)).trans
        (Homeomorph.setCongr (by rw [nativeCoordinateInclusion_opensRange])))).symm

/-- The inverse chart gives the whole original native point through the genuine scheme inclusion. -/
@[simp]
theorem nativeCoordinateSpectrumHomeomorph_symm_coe (v : Valuation R ℝ≥0)
    (j : Fin (n + 1)) (x : RelativeSpectrum v (CoordinateRing R j)) :
    ((nativeCoordinateSpectrumHomeomorph v j).symm x).1.1 =
      SchemeValuedPoint.map (nativeCoordinateInclusion j)
        (SchemeValuedPoint.spectrumHomeomorph.symm x.1) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The fraction comparison equals the actual global-section pullback of the whole coordinate chart. -/
theorem nativeCoordinateSectionsIso_eq (j : Fin (n + 1)) :
    nativeCoordinateSectionsIso (R := R) j =
      (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing R j))).symm.trans
        ((Scheme.Γ.mapIso (nativeCoordinateSchemeIso (R := R) j).op).trans
          (nativeCoordinateOpen (R := R) j).topIso) := by
  apply Iso.ext
  change _ = (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing R j))).inv ≫
    (Spec.map (CommRingCat.ofHom (homogeneousChartEquiv (R := R) j).symm.toRingHom)).appTop ≫
      (nativeHomogeneousChartSchemeIso j).hom.appTop ≫ (nativeCoordinateOpen j).topIso.hom
  erw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The true section-ring comparison cancels with the inverse coordinate-chart pullback. -/
theorem nativeCoordinateSectionsIso_cancel (j : Fin (n + 1)) :
    (nativeCoordinateSectionsIso (R := R) j).hom ≫
      (nativeCoordinateOpen j).topIso.inv ≫ (nativeCoordinateSchemeIso j).inv.appTop =
        (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing R j))).inv := by
  rw [nativeCoordinateSectionsIso_eq]
  change ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing R j))).inv ≫
    (Scheme.Γ.mapIso (nativeCoordinateSchemeIso (R := R) j).op).hom ≫
      (nativeCoordinateOpen j).topIso.hom) ≫ (nativeCoordinateOpen j).topIso.inv ≫
        (Scheme.Γ.mapIso (nativeCoordinateSchemeIso (R := R) j).op).inv = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse native chart preserves the value of every affine polynomial as a genuine local section. -/
theorem nativeCoordinateSpectrumHomeomorph_symm_val (v : Valuation R ℝ≥0)
    (j : Fin (n + 1)) (x : RelativeSpectrum v (CoordinateRing R j)) (a : CoordinateRing R j) :
    x.1.val a = SchemeValuedPoint.eval
      ((nativeCoordinateSpectrumHomeomorph v j).symm x).1.1 (nativeCoordinateOpen j)
      ((nativeCoordinateSpectrumHomeomorph v j).symm x).2
      ((nativeCoordinateSectionsIso (R := R) j).hom a) := by
  simp only [nativeCoordinateSpectrumHomeomorph_symm_coe, nativeCoordinateInclusion,
    SchemeValuedPoint.map_comp, SchemeValuedPoint.eval_map_ι_topIso,
    SchemeValuedPoint.evalTop_map]
  have hs := congrArg (fun f => f a) (nativeCoordinateSectionsIso_cancel (R := R) j)
  change (nativeCoordinateSchemeIso j).inv.appTop
    ((nativeCoordinateOpen j).topIso.inv ((nativeCoordinateSectionsIso j).hom a)) =
      (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing R j))).inv a at hs
  erw [hs]
  have h := SchemeValuedPoint.spectrumHomeomorph_val_apply
    (SchemeValuedPoint.spectrumHomeomorph.symm x.1) a
  rw [Homeomorph.apply_symm_apply] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Every affine polynomial is evaluated through the actual native homogeneous-fraction section. -/
theorem nativeCoordinateSpectrumHomeomorph_val_apply (v : Valuation R ℝ≥0)
    (j : Fin (n + 1))
    (y : {y : RelativeSchemeValuedPoint v (nativeStructureMap (R := R) (n := n)) //
      y.1.point ∈ nativeCoordinateOpen (R := R) j}) (a : CoordinateRing R j) :
    (nativeCoordinateSpectrumHomeomorph v j y).1.val a =
      SchemeValuedPoint.eval y.1.1 (nativeCoordinateOpen j) y.2
        ((nativeCoordinateSectionsIso (R := R) j).hom a) := by
  have h := nativeCoordinateSpectrumHomeomorph_symm_val v j
    (nativeCoordinateSpectrumHomeomorph v j y) a
  rwa [Homeomorph.symm_apply_apply] at h

end EnvelopeProperty.ProjBerk
