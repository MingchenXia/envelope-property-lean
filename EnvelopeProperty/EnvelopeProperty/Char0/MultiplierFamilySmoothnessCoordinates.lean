import EnvelopeProperty.Char0.MultiplierFamilySmoothness

/-! # The SAME whole original native chart maps preserve every old homogeneous coordinate -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
universe u
namespace EnvelopeProperty.Char0.MultiplierFamilySmoothness
open ProjBerk Berkovich
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The actual coordinate quotient comparison retains EVERY original homogeneous numerator and its actual degree. -/
theorem coordinateQuotientEquiv_mk_homogeneous (j : Fin (M + 1))
    (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal)
    {d : ℕ} {F : MvPolynomial (Fin (M + 1)) k} (hF : F.IsHomogeneous d) :
    coordinateQuotientEquiv X j hj
      (Ideal.Quotient.mk (X.ideal.map (coordinateDehom j).toRingHom) (coordinateDehom j F)) =
      quotChartMk X.ideal (MvPolynomial.X j) 1 d F := by
  apply (coordinateQuotientEquiv X j hj).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  change Ideal.Quotient.mk _ (coordinateDehom j F) =
    Ideal.Quotient.mk _ (chartCoordinateEquiv j (chartMk (MvPolynomial.X j) 1 d F))
  rw [chartCoordinateEquiv_chartMk j hF]

/-- The WHOLE genuine original native inclusion transports every homogeneous dehomogenized
coordinate to its SAME original old quotient-chart fraction, with no coordinate matching input. -/
theorem nativeChartSectionsEquiv_pullback_homogeneous (j : Fin (M + 1))
    (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal)
    {d : ℕ} {F : MvPolynomial (Fin (M + 1)) k} (hF : F.IsHomogeneous d) :
    nativeChartSectionsEquiv X j hj
      ((X.nativeInclusion.app (nativeCoordinateOpen j)).hom
        ((nativeCoordinateSectionsIso j).hom.hom (coordinateDehom j F))) =
      quotChartMk X.ideal (MvPolynomial.X j) 1 d F := by
  change coordinateQuotientEquiv X j hj
    (nativeChartCoordinateSectionsEquiv X j
      ((X.nativeInclusion.app (nativeCoordinateOpen j)).hom
        ((nativeCoordinateSectionsIso j).hom.hom (coordinateDehom j F)))) = _
  rw [nativeChartCoordinateSectionsEquiv_pullback, coordinateQuotientEquiv_mk_homogeneous X j hj hF]

/-- The SAME original field coefficient map is retained by the actual whole native chart comparison. -/
theorem nativeChartSectionsEquiv_coefficients (j : Fin (M + 1))
    (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal) (c : k) :
    nativeChartSectionsEquiv X j hj
      (SchemeValuedPoint.sectionBaseMap X.nativeStructure (nativeChartOpen X j) c) =
      algebraMap k (QuotChartAlg X.ideal (MvPolynomial.X j) 1) c := by
  let : Algebra k Γ(X.NativeScheme, nativeChartOpen X j) := nativeChartAlgebra X j
  exact (nativeChartSectionsEquiv X j hj).commutes c

/-- The actual WHOLE original parameter family is the genuine product of the SAME original native variety and parameter line. -/
def familyPullbackIso : ProjSubvariety.MultiplierBaseIdeals.familyScheme X ≅
    CategoryTheory.Limits.pullback X.nativeStructure
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) :=
  familyProductIso X ≪≫ X.nativeProductModelIso

/-- Its original parameter projection is the SAME actual family projection. -/
theorem familyPullbackIso_projection :
    (familyPullbackIso X).hom ≫ CategoryTheory.Limits.pullback.snd X.nativeStructure
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) =
      ProjSubvariety.MultiplierBaseIdeals.familyProjection X := by
  rw [familyPullbackIso, Iso.trans_hom, Category.assoc, X.nativeProductModelIso_over_base,
    familyProductIso_projection]

/-- The actual first projection to the ORIGINAL native variety, constructed internally. -/
def familyToOriginal : ProjSubvariety.MultiplierBaseIdeals.familyScheme X ⟶ X.NativeScheme :=
  (familyPullbackIso X).hom ≫ CategoryTheory.Limits.pullback.fst X.nativeStructure
    (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))

/-- BOTH original scalar actions satisfy their genuine whole-product field triangle. -/
theorem familyToOriginal_structure :
    familyToOriginal X ≫ X.nativeStructure = familyAbsoluteStructure X := by
  rw [familyToOriginal, Category.assoc, CategoryTheory.Limits.pullback.condition,
    ← Category.assoc, familyPullbackIso_projection]
  rfl

end EnvelopeProperty.Char0.MultiplierFamilySmoothness
