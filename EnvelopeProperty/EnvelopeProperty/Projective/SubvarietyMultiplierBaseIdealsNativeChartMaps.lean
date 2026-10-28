import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsNativeCharts
import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsParameterChartMaps

/-! # The ENTIRE original family inclusion, coefficient and ideal chart diagrams -/

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
open ProjBerk Berkovich Char0.EnvelopeGradedBaseIdealsSectionAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem appLE_of_hom_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by subst g; rfl

private theorem sectionAlgEquivOfIso_apply {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (e : X ≅ Y) (pX : X ⟶ Spec (.of R)) (pY : Y ⟶ Spec (.of R))
    (w : e.hom ≫ pY = pX) (U : Y.Opens) (s : Γ(Y, U)) :
    sectionAlgEquivOfIso e pX pY w U s = (e.hom.app U).hom s := rfl

private theorem sectionAlgEquivOfIso_symm_app {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (e : X ≅ Y) (pX : X ⟶ Spec (.of R)) (pY : Y ⟶ Spec (.of R))
    (w : e.hom ≫ pY = pX) (U : Y.Opens) (s : Γ(Y, U)) :
    letI := pY.sectionsAlgebra U
    letI := pX.sectionsAlgebra (e.hom ⁻¹ᵁ U)
    (sectionAlgEquivOfIso e pX pY w U).symm ((e.hom.app U).hom s) = s := by
  let := pY.sectionsAlgebra U
  let := pX.sectionsAlgebra (e.hom ⁻¹ᵁ U)
  rw [← sectionAlgEquivOfIso_apply e pX pY w U s]
  exact AlgEquiv.symm_apply_apply _ s

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The genuine SAME original coordinate section pulled along the ORIGINAL
whole inclusion to the SAME actual original family affine open. -/
def familyCoordinateSection (j : Fin (M + 1)) (F : CoordinateRing k[X] j) :
    Γ(familyScheme X, familyChartOpen X j) :=
  ((familyInclusion X).appLE (nativeCoordinateOpen j) (familyChartOpen X j)
    (familyChartOpen_eq X j).le).hom ((nativeCoordinateSectionsIso (R := k[X]) j).hom.hom F)

/-- The ENTIRE original coefficient map is the actual inclusion triangle
on fixed whole opens, with no implicit change of section support. -/
theorem familyCoordinateSection_eq_transport (j : Fin (M + 1)) (F : CoordinateRing k[X] j) :
    familyCoordinateSection X j F =
      ((familyCutIso X).hom.app (familyCutChartOpen X j)).hom
        (((familyCutIdeal X).subschemeι.app (nativeCoordinateOpen j)).hom
          ((nativeCoordinateSectionsIso (R := k[X]) j).hom.hom F)) := by
  have he := appLE_of_hom_eq (familyCutIso_inclusion X) (nativeCoordinateOpen j)
    (familyChartOpen X j) (le_refl _) (familyChartOpen_eq X j).le
  have hc : ((familyCutIso X).hom ≫ (familyCutIdeal X).subschemeι).appLE
      (nativeCoordinateOpen j) (familyChartOpen X j) (le_refl _) =
      (familyCutIdeal X).subschemeι.app (nativeCoordinateOpen j) ≫
        (familyCutIso X).hom.app (familyCutChartOpen X j) := by
    rw [Scheme.Hom.comp_appLE]
    exact congrArg (fun f => (familyCutIdeal X).subschemeι.app (nativeCoordinateOpen j) ≫ f)
      (Scheme.Hom.appLE_eq_app (familyCutIso X).hom)
  exact congrArg (fun f => f.hom ((nativeCoordinateSectionsIso (R := k[X]) j).hom.hom F))
    (he.symm.trans hc)

/-- The actual whole family coordinate equivalence sends its original
inclusion section to EXACTLY the same original quotient class. -/
theorem familyChartCoordinateAlgEquiv_coordinateSection (j : Fin (M + 1))
    (F : CoordinateRing k[X] j) :
    familyChartCoordinateAlgEquiv X j (familyCoordinateSection X j F) =
      Ideal.Quotient.mk ((familyHomogeneousIdeal X).toIdeal.map (coordinateDehom j).toRingHom) F := by
  let := (familyCutProjection X).sectionsAlgebra (familyCutChartOpen X j)
  let := (familyProjection X).sectionsAlgebra ((familyCutIso X).hom ⁻¹ᵁ familyCutChartOpen X j)
  rw [familyCoordinateSection_eq_transport]
  change nativeQuotientCoordinateSectionsEquiv (familyHomogeneousIdeal X) j
    ((sectionAlgEquivOfIso (familyCutIso X) (familyProjection X) (familyCutProjection X)
      (familyCutIso_projection X) (familyCutChartOpen X j)).symm
        (((familyCutIso X).hom.app (familyCutChartOpen X j)).hom
          (((familyCutIdeal X).subschemeι.app (nativeCoordinateOpen j)).hom
            ((nativeCoordinateSectionsIso (R := k[X]) j).hom.hom F)))) = _
  rw [sectionAlgEquivOfIso_symm_app]
  exact nativeQuotientCoordinateSectionsEquiv_pullback (familyHomogeneousIdeal X) j F

/-- The same actual absolute-field chart equivalence retains the complete
original quotient-coordinate image. -/
theorem familyChartSectionsEquiv_coordinateSection (j : Fin (M + 1))
    (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal)
    (F : CoordinateRing k[X] j) :
    familyChartSectionsEquiv X j hj (familyCoordinateSection X j F) =
      familyCoordinateQuotientEquiv X j hj (Ideal.Quotient.mk _ F) := by
  change familyCoordinateQuotientEquiv X j hj
    (familyChartCoordinateAlgEquiv X j (familyCoordinateSection X j F)) = _
  rw [familyChartCoordinateAlgEquiv_coordinateSection]

/-- Every ORIGINAL whole polynomial, including its original parameter,
has EXACTLY its same old dehomogenized value in the actual original chart. -/
theorem familyChartSectionsEquiv_parameterDehom (j : Fin (M + 1))
    (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal)
    (g : (MvPolynomial (Fin (M + 1)) k)[X]) :
    familyChartSectionsEquiv X j hj
      (familyCoordinateSection X j (coordinateDehom j (parameterEquiv g))) =
      g.map (X.quotDehom j).toRingHom :=
  (familyChartSectionsEquiv_coordinateSection X j hj _).trans
    (familyCoordinateQuotientEquiv_parameterDehom X j hj g)

/-- Actual representative membership gives membership of its SAME original
inclusion section in the ENTIRE original ideal on this whole affine open. -/
theorem familyCoordinateSection_mem_of_representative (K : (familyScheme X).IdealSheafData)
    (j : Fin (M + 1)) (F : MvPolynomial (Fin (M + 1)) k[X])
    (hF : F ∈ homogeneousConeRepresentative X K) :
    familyCoordinateSection X j (coordinateDehom j F) ∈ K.ideal (familyChartAffineOpen X j) := by
  let U := familyChartAffineOpen X j
  let V : (NativeProjectiveScheme k[X] M).affineOpens :=
    ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩
  have hi : (nativeCoordinateSectionsIso (R := k[X]) j).hom.hom (coordinateDehom j F) ∈
      (K.map (familyInclusion X)).ideal V :=
    nativeHomogeneousRepresentative_dehom_le (K.map (familyInclusion X)) j
      (Ideal.mem_map_of_mem (coordinateDehom j).toRingHom hF)
  have hm : familyCoordinateSection X j (coordinateDehom j F) ∈
      ((K.map (familyInclusion X)).comap (familyInclusion X)).ideal U := by
    rw [Scheme.IdealSheafData.comap_ideal_of_affine_opens _ _ U V (familyChartOpen_eq X j).le]
    exact Ideal.mem_map_of_mem _ hi
  rw [Scheme.IdealSheafData.comap_map_of_isClosedImmersion] at hm
  exact hm

/-- The inverse of the SAME actual field-algebra chart equivalence takes
every original representative polynomial's old dehomogenization into K. -/
theorem familyChartSectionsEquiv_symm_dehom_mem (K : (familyScheme X).IdealSheafData)
    (j : Fin (M + 1)) (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal)
    (F : MvPolynomial (Fin (M + 1)) k[X]) (hF : F ∈ homogeneousConeRepresentative X K) :
    letI := (familyAbsoluteStructure X).sectionsAlgebra (familyChartOpen X j)
    (familyChartSectionsEquiv X j hj).symm
      (((parameterEquiv (k := k) (M := M)).symm F).map (X.quotDehom j).toRingHom) ∈
      K.ideal (familyChartAffineOpen X j) := by
  let := (familyAbsoluteStructure X).sectionsAlgebra (familyChartOpen X j)
  have h := familyChartSectionsEquiv_parameterDehom X j hj ((parameterEquiv (k := k) (M := M)).symm F)
  simp only [AlgEquiv.apply_symm_apply] at h
  rw [← h, AlgEquiv.symm_apply_apply]
  exact familyCoordinateSection_mem_of_representative X K j F hF

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
