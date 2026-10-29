import EnvelopeProperty.Projective.SubvarietyMultiplierConeGeneratorsEvaluation
import EnvelopeProperty.Projective.SubvarietyMultiplierOriginalGenerationCore
import EnvelopeProperty.AlgGeom.InvertibleBaseIdealPullback

/-! # Actual lifted homogeneous families recover the entire original scheme ideal -/

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierConeGeneratorsSheaf
open ProjBerk Scheme.Modules ModularCurves InvertibleSheafBaseIdeal
open InvertibleSectionFamilyImage MultiplierConeGeneratorsEvaluation
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The actual homogeneous ideal spanned by precisely the given original forms. -/
def homogeneousFamilyIdeal {ι : Type u}
    (F : ι → MvPolynomial (Fin (n + 1)) R) (e : ℕ) (hF : ∀ a, (F a).IsHomogeneous e) :
    HomogeneousIdeal (ProjectiveGrading R n) := by
  refine ⟨Ideal.span (Set.range F), ?_⟩
  apply Ideal.homogeneous_span
  rintro _ ⟨a, rfl⟩
  exact ⟨e, hF a⟩

private theorem iSup_span_range {ι A : Type u} [CommRing A] (c : ι → A) :
    (⨆ a, Ideal.span ({c a} : Set A)) = Ideal.span (Set.range c) := by
  apply le_antisymm
  · apply iSup_le
    intro a
    apply Ideal.span_le.mpr
    rintro _ ⟨rfl⟩
    exact Ideal.subset_span ⟨a, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact Ideal.mem_iSup_of_mem (R := A) a (Ideal.mem_span_singleton_self _)

/-- The actual whole quotient-kernel ideal sheaf of the homogeneous span is
exactly the supremum of the SAME original homogeneous section ideals. -/
theorem homogeneousFamilyIdeal_sheaf_eq_iSup {ι : Type u}
    (j : Fin (n + 1)) (F : ι → MvPolynomial (Fin (n + 1)) R)
    (e : ℕ) (hF : ∀ a, (F a).IsHomogeneous e) :
    GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) (homogeneousFamilyIdeal F e hF) =
      ⨆ a, sectionIdeal (coordinateHyperplanePoleSheafPower_isInvertible (R := R) j e)
        (ProjectiveHomogeneousSections.homogeneousSection j e (F a) (hF a)) := by
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun j : Fin (n + 1) => ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩)
    iSup_nativeCoordinateOpen_eq_top
  intro k
  let U : (NativeProjectiveScheme R n).affineOpens :=
    ⟨nativeCoordinateOpen k, nativeCoordinateOpen_isAffine k⟩
  let c : ι → Γ(NativeProjectiveScheme R n, U.1) := fun a =>
    (nativeCoordinateSectionsIso (R := R) k).hom (coordinateDehom k (F a))
  have hs : (⨆ a, sectionIdeal (coordinateHyperplanePoleSheafPower_isInvertible (R := R) j e)
      (ProjectiveHomogeneousSections.homogeneousSection j e (F a) (hF a))).ideal U =
      Ideal.span (Set.range c) := by
    calc
      _ = ⨆ a, (sectionIdeal (coordinateHyperplanePoleSheafPower_isInvertible (R := R) j e)
          (ProjectiveHomogeneousSections.homogeneousSection j e (F a) (hF a))).ideal U := by
        rw [Scheme.IdealSheafData.ideal_iSup, iSup_apply]
      _ = ⨆ a, Ideal.span ({c a} : Set Γ(NativeProjectiveScheme R n, U.1)) :=
        iSup_congr fun a => MultiplierOriginalGenerationCore.homogeneousSection_sectionIdeal
          k j e (F a) (hF a)
      _ = Ideal.span (Set.range c) := iSup_span_range c
  refine Eq.trans ?_ hs.symm
  rw [Char0.EnvelopeGradedBaseIdealsCore.quotientIdealSheaf_coordinateIdeal]
  change ((Ideal.span (Set.range F)).map (coordinateDehom k).toRingHom).map
    (nativeCoordinateSectionsIso (R := R) k).hom.hom = _
  rw [Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
  rfl

/-- Actual homogeneous representatives of the SAME included original
sections give an equality of ENTIRE original comap ideals. The representation
equalities are consumed here; the final producer constructs them by the proved
fixed polynomial-lift theorem rather than supplying a matching certificate. -/
theorem homogeneousFamilyIdeal_comap_eq {Y : Scheme.{u}}
    (μ : Y ⟶ NativeProjectiveScheme R n) (j : Fin (n + 1)) (e : ℕ)
    (K : Y.IdealSheafData)
    (G : (K.toModules ⊗ (Scheme.Modules.pullback μ).obj
      (coordinateHyperplanePoleSheafPower (R := R) j e)).GeneratingSections)
    (F : G.I → MvPolynomial (Fin (n + 1)) R) (hF : ∀ a, (F a).IsHomogeneous e)
    (hlift : ∀ a, affinePullbackUnitTop μ _
      (ProjectiveHomogeneousSections.homogeneousSection j e (F a) (hF a)) =
      includedSection K _ G a) :
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n)
      (homogeneousFamilyIdeal F e hF)).comap μ = K := by
  let L := coordinateHyperplanePoleSheafPower (R := R) j e
  let hL := coordinateHyperplanePoleSheafPower_isInvertible (R := R) j e
  let hP := hL.pullback μ
  let _ := freeTensorDual_isQuasicoherent hP G.I
  calc
    _ = (⨆ a, sectionIdeal hL
        (ProjectiveHomogeneousSections.homogeneousSection j e (F a) (hF a))).comap μ :=
      congrArg (fun J : (NativeProjectiveScheme R n).IdealSheafData => J.comap μ)
        (homogeneousFamilyIdeal_sheaf_eq_iSup j F e hF)
    _ = ⨆ a, (sectionIdeal hL
        (ProjectiveHomogeneousSections.homogeneousSection j e (F a) (hF a))).comap μ :=
      (Scheme.IdealSheafData.map_gc μ).l_iSup
    _ = ⨆ a, sectionIdeal hP (includedSection K _ G a) :=
      iSup_congr fun a => (InvertibleBaseIdealPullback.sectionIdeal_comap μ hL _).trans
        (congrArg (sectionIdeal hP) (hlift a))
    _ = QuasicoherentImageIdeal.imageIdeal _
        (familyEvaluation hP (includedSection K _ G)) :=
      (familyEvaluation_imageIdeal hP (includedSection K _ G)).symm
    _ = K := includedEvaluation_imageIdeal K _ hP G

end EnvelopeProperty.ProjSubvariety.MultiplierConeGeneratorsSheaf
