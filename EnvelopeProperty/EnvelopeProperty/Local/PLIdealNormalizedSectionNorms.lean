import EnvelopeProperty.Local.PLIdealNormalizedGlobalGeneration
import EnvelopeProperty.Berkovich.SchemeLineSectionNormPullback
import EnvelopeProperty.Projective.HomogeneousSectionModelNorms

/-! # Original homogeneous section norms on the SAME normalized simultaneous model -/
open scoped Classical Polynomial NNReal ENNReal
open CategoryTheory AlgebraicGeometry Opposite Limits
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)

/-- The SAME actual normalized model's original polynomial projective projection. -/
def normalizedSimultaneousPolynomialProjection :
    X.normalizedSimultaneousIdealBlowup I J hfin ⟶ NativeProjectiveScheme k[X] M :=
  (X.normalizedSimultaneousIdealBlowupProjection I J hfin ≫
    X.simultaneousIdealBlowupProjection I J) ≫ X.nativeProductPolynomialInclusion

/-- The literal original composite preserves the SAME actual polynomial base. -/
theorem normalizedSimultaneousPolynomialProjection_over_base :
    X.normalizedSimultaneousPolynomialProjection I J hfin ≫ nativeStructureMap =
      X.normalizedSimultaneousIdealBlowupStructure I J hfin := by
  dsimp only [normalizedSimultaneousPolynomialProjection, nativeProductPolynomialInclusion]
  simp only [Category.assoc, nativePolynomialLineProductIso_inv_over_base]
  rfl

/-- The ACTUAL original polynomial projection preserves the ENTIRE original
normalized Gauss point, including its original residue valuation. -/
theorem map_normalizedSimultaneousPolynomialProjection_gauss
    (hX : X.IsProjNormal) (w : X.an) :
    RelativeSchemeValuedPoint.map (X.normalizedSimultaneousPolynomialProjection I J hfin)
      (X.normalizedSimultaneousPolynomialProjection_over_base I J hfin)
      (X.normalizedSimultaneousGaussPoint I J hfin hX w) =
      RelativeNormalizedProjectiveSpectrum.nativeHomeomorph _ (gaussModelPoint w.1) := by
  apply Subtype.ext
  have hν := congrArg Subtype.val (X.map_normalizedSimultaneousGaussPoint I J hfin hX w)
  have hμ := congrArg Subtype.val (X.map_simultaneousIdealBlowupGaussPoint I J w
    (hfin w).1 (hfin w).2)
  have hι := congrArg Subtype.val (X.map_nativeProductGaussPoint w)
  have he := congrArg Subtype.val (nativePolynomialLineProductPoint_inverse (gaussModelPoint w.1))
  change SchemeValuedPoint.map _ _ = _ at hν hμ hι he
  change SchemeValuedPoint.map _ _ = _
  dsimp only [normalizedSimultaneousPolynomialProjection, nativeProductPolynomialInclusion]
  simp only [SchemeValuedPoint.map_comp]
  rw [hν, hμ, hι]
  exact he

private local instance normalizedSectionProper :
    IsProper (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
  X.normalizedSimultaneousIdealBlowupStructure_isProper I J hfin
private local instance polynomialProjectiveSectionProper :
    IsProper (nativeStructureMap (R := k[X]) (n := M)) := nativeStructureMap_isProper

/-- Actual proper-model norm of the SAME original pulled homogeneous section,
on the SAME original normalized model and its TRUE original Gauss lift. -/
def normalizedSimultaneousHomogeneousSectionNorm (hX : X.IsProjNormal)
    (j : Fin (M+1)) (d : ℕ) (F : MvPolynomial (Fin (M+1)) k) (hF : F.IsHomogeneous d)
    (w : X.an) : ℝ≥0 :=
  modelLineNorm gaussModelCoefficient_le_one (X.normalizedSimultaneousGaussPoint I J hfin hX w)
    ((MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible (R := k[X]) j d).pullback
      (X.normalizedSimultaneousPolynomialProjection I J hfin))
    (fibreSection (X.normalizedSimultaneousGaussPoint I J hfin hX w)
      (SchemeLineSectionEvaluation.pullbackSectionHom
        (X.normalizedSimultaneousPolynomialProjection I J hfin)
        (ProjectiveHomogeneousSections.sectionHom j d (MvPolynomial.map Polynomial.C F)
          (hF.map Polynomial.C))))

/-- The TRUE normalized-model section norm is EXACTLY the ORIGINAL full
homogeneous form value at the ORIGINAL original variety point, including zero. -/
theorem normalizedSimultaneousHomogeneousSectionNorm_eq_val (hX : X.IsProjNormal)
    (j : Fin (M+1)) (d : ℕ) (F : MvPolynomial (Fin (M+1)) k) (hF : F.IsHomogeneous d)
    (w : X.an) :
    X.normalizedSimultaneousHomogeneousSectionNorm I J hfin hX j d F hF w = w.1.1.val F := by
  let g := X.normalizedSimultaneousPolynomialProjection I J hfin
  have hg := X.normalizedSimultaneousPolynomialProjection_over_base I J hfin
  have h := modelLineNorm_pullbackSection_eq_overBase (RingHom.id k[X]) (fun _ => rfl) g
    (by simpa only [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id] using hg)
    gaussModelCoefficient_le_one gaussModelCoefficient_le_one
    (X.normalizedSimultaneousGaussPoint I J hfin hX w)
    (MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible (R := k[X]) j d)
    (ProjectiveHomogeneousSections.sectionHom j d (MvPolynomial.map Polynomial.C F)
      (hF.map Polynomial.C))
  rw [mapOverBase_id g hg, X.map_normalizedSimultaneousPolynomialProjection_gauss I J hfin hX w] at h
  change X.normalizedSimultaneousHomogeneousSectionNorm I J hfin hX j d F hF w = _ at h
  rw [RelativeNormalizedProjectiveSpectrum.homogeneousSection_modelLineNorm] at h
  refine h.trans ?_
  have hs := swap_modelMonomial (k := k) (n := M) F 1 0
  simp only [modelMonomial, pow_one, pow_zero, MvPolynomial.C_1, mul_one] at hs
  rw [gaussModelPoint_val_apply, hs, gaussExt_val_C]

end EnvelopeProperty.ProjSubvariety
