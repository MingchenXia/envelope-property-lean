import EnvelopeProperty.Projective.SubvarietyMultiplierConeGeneratorsSheaf
import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsSaturation
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroPolynomial
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroCoefficients

/-! # Actual original polynomial spans satisfy both genuine cone ideal bounds -/

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory MvPolynomial
open scoped Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierConeGeneratorsAlgebra
open ProjBerk Scheme.Modules MultiplierBaseIdeals
open MultiplierConeGeneratorsEvaluation MultiplierConeGeneratorsSheaf
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- A finite genuine homogeneous representative family of the SAME included
original generators supplies the exact bounded-polynomial-generator property.
The whole image equality is proved from the actual original generating family;
it is not a hypothesis, and individual t-components are never assumed in B. -/
theorem hasBoundedPolynomialConeGenerators_of_lifts
    (K : (familyScheme X).IdealSheafData) (e : ℕ)
    (G : (K.toModules ⊗ (Scheme.Modules.pullback (familyInclusion X)).obj
      (coordinateHyperplanePoleSheafPower (R := Polynomial k) (0 : Fin (M + 1)) e)).GeneratingSections)
    (hG : G.IsFiniteType)
    (F : G.I → MvPolynomial (Fin (M + 1)) k[X]) (hF : ∀ a, (F a).IsHomogeneous e)
    (hlift : ∀ a, affinePullbackUnitTop (familyInclusion X) _
      (ProjectiveHomogeneousSections.homogeneousSection (0 : Fin (M + 1)) e (F a) (hF a)) =
      includedSection K _ G a) :
    X.HasBoundedPolynomialConeGenerators (coneIdeal X K) e := by
  classical
  let : G.IsFiniteType := hG
  let : Fintype G.I := Fintype.ofFinite G.I
  let J := homogeneousFamilyIdeal F e hF
  have hJ : (GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M) J).comap
      (familyInclusion X) = K :=
    homogeneousFamilyIdeal_comap_eq (familyInclusion X) (0 : Fin (M + 1)) e K G F hF hlift
  have hJle : J ≤ homogeneousConeRepresentative X K :=
    homogeneousIdeal_le_nativeRepresentative J (K.map (familyInclusion X))
      (Scheme.IdealSheafData.le_map_iff_comap_le.mpr hJ.le)
  have hlo : J.toIdeal.map (parameterConeQuotient X).toRingHom ≤ coneIdeal X K :=
    Ideal.map_mono (show J.toIdeal ≤ (homogeneousConeRepresentative X K).toIdeal from hJle)
  have hsat : coneIdeal X K ≤ X.saturation (J.toIdeal.map (parameterConeQuotient X).toRingHom) :=
    map_cone_le_saturation_of_family_comap_le X (homogeneousConeRepresentative X K) J
      (by rw [homogeneousConeRepresentative_comap, hJ])
  let P : G.I → (MvPolynomial (Fin (M + 1)) k)[X] := fun a => parameterEquiv.symm (F a)
  let S : Finset (MvPolynomial (Fin (M + 1)) k)[X] := Finset.univ.image P
  have hspan : (Ideal.span (S : Set _)).map X.coneMk =
      J.toIdeal.map (parameterConeQuotient X).toRingHom := by
    change (Ideal.span (S : Set _)).map X.coneMk =
      (Ideal.span (Set.range F)).map (parameterConeQuotient X).toRingHom
    rw [Ideal.map_span, Ideal.map_span]
    congr 1
    apply Set.ext
    intro z
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨a, _ha, hpa⟩ := Finset.mem_image.mp hp
      subst p
      exact ⟨F a, ⟨a, rfl⟩, rfl⟩
    · rintro ⟨f, ⟨a, rfl⟩, rfl⟩
      refine ⟨P a, ?_, rfl⟩
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
  refine ⟨S, ?_, ?_, ?_⟩
  · intro p hp l
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨e, le_rfl, parameterEquiv_symm_coeff_isHomogeneous (hF a) l⟩
  · rw [hspan]
    exact hlo
  · rw [hspan]
    exact hsat

end EnvelopeProperty.ProjSubvariety.MultiplierConeGeneratorsAlgebra
