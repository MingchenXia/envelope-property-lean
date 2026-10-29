import EnvelopeProperty.Projective.IdealBaseChange
import EnvelopeProperty.AlgGeom.CartierAdmissibleModulePullback
import EnvelopeProperty.AlgGeom.MorphismKernelIdealModuleComparison
import ModularCurves.EllipticCurve.ProjectiveSpaceTwist

/-! # Actual coordinate hyperplane ideal modules under arbitrary coefficient change -/
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousIdeal
open EnvelopeProperty.ProjBerk
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjectiveCoordinateIdealBaseChange
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}
private local instance closedHyperplane (j : Fin (n+1)) :
    IsClosedImmersion (coordinateHyperplaneι (R := R) j) := coordinateHyperplaneι_isClosedImmersion j

private theorem localEquation_eq_nativeCoordinate (i j : Fin (n+1)) :
    coordinateHyperplaneLocalEquation (R := R) i j =
      (nativeCoordinateSectionsIso (R := R) i).hom.hom (coordinateDehom i (MvPolynomial.X j)) := by
  rw [coordinateDehom,MvPolynomial.aeval_X]
  by_cases hji : j = i
  · subst j
    rw [coordinateHyperplaneLocalEquation_self,coordinateDehomCoord_self,map_one]
  · rw [coordinateHyperplaneLocalEquation_of_ne i j hji]
    simp only [coordinateDehomCoord,dif_neg hji]
    change (Proj.basicOpenIsoAway (ProjectiveGrading R n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) one_pos).hom.hom (awayVar R i ⟨j,hji⟩) =
      (nativeHomogeneousChartSectionsIso (R := R) i).hom.hom
        (homogeneousChartRatioHom i (MvPolynomial.X ⟨j,hji⟩))
    rw [nativeHomogeneousChartSectionsIso_hom]
    simp only [homogeneousChartRatioHom,MvPolynomial.aeval_X]
    rfl

/-- The actual original coordinate hyperplane kernel is the SAME whole original
homogeneous quotient ideal sheaf, with its original coordinate generator. -/
theorem coordinateHyperplane_ker_eq_quotientIdealSheaf (j : Fin (n+1)) :
    (coordinateHyperplaneι (R := R) j).ker =
      GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) (coordinateHyperplaneIdeal j) := by
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun i : Fin (n+1) => ⟨nativeCoordinateOpen i,nativeCoordinateOpen_isAffine i⟩)
    iSup_nativeCoordinateOpen_eq_top
  intro i
  let e := (nativeCoordinateSectionsIso (R := R) i).hom.hom
  have heb : Function.Bijective e :=
    ConcreteCategory.bijective_of_isIso (nativeCoordinateSectionsIso (R := R) i).hom
  apply Ideal.comap_injective_of_surjective e heb.surjective
  rw [homogeneousQuotient_coordinateSectionIdeal,coordinateHyperplaneIdeal_toIdeal,
    Ideal.map_span,Set.image_singleton]
  change ((Scheme.Hom.ker (coordinateHyperplaneι j)).ideal
    ⟨coordinateOpen i,coordinateOpen_isAffineOpen i⟩).comap e = _
  rw [coordinateHyperplaneLocalEquation_span,localEquation_eq_nativeCoordinate]
  change (Ideal.span {e (coordinateDehom i (MvPolynomial.X j))}).comap e = _
  rw [← Set.image_singleton,← Ideal.map_span,Ideal.comap_map_of_bijective e heb]
  rfl

/-- The SAME original coordinate homogeneous ideal commutes with ANY original
coefficient-ring map, without injectivity or flatness. -/
theorem coordinateHyperplaneIdeal_map (φ : R →+* S) (j : Fin (n+1)) :
    (coordinateHyperplaneIdeal (R := R) j).map (coefficientGradedMap φ) =
      coordinateHyperplaneIdeal (R := S) j := by
  apply HomogeneousIdeal.toIdeal_injective
  change (Ideal.span {MvPolynomial.X j}).map (MvPolynomial.map φ) = Ideal.span {MvPolynomial.X j}
  rw [Ideal.map_span,Set.image_singleton,MvPolynomial.map_X]

/-- The geometric coordinate-hyperplane ideal is genuinely Cartier over EVERY
commutative coefficient ring, including nonreduced rings. -/
theorem coordinateHyperplane_ker_isInvertible (j : Fin (n+1)) :
    (coordinateHyperplaneι (R := R) j).ker.IsInvertible := by
  intro x
  have hx : x ∈ ⨆ i : Fin (n+1), coordinateOpen (R := R) i := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨⟨coordinateOpen i,coordinateOpen_isAffineOpen i⟩,hi,
    coordinateHyperplaneLocalEquation i j,coordinateHyperplaneLocalEquation_mem_nonZeroDivisors i j,
    coordinateHyperplaneLocalEquation_span i j⟩

/-- The WHOLE genuine coordinate-hyperplane geometric ideal comap is exactly
the SAME original coordinate ideal over the new coefficient ring. -/
theorem coordinateHyperplane_ker_comap (φ : R →+* S) (j : Fin (n+1)) :
    ((coordinateHyperplaneι (R := R) j).ker).comap (nativeCoefficientMap φ) =
      (coordinateHyperplaneι (R := S) j).ker := by
  rw [coordinateHyperplane_ker_eq_quotientIdealSheaf,
    homogeneousQuotientIdealSheaf_comap_coefficientMap,coordinateHyperplaneIdeal_map,
    coordinateHyperplane_ker_eq_quotientIdealSheaf]

/-- The true whole ORIGINAL native coordinate ideal module commutes with ANY
coefficient-ring change. This is the canonical actual Cartier comparison,
not an assumed frame or base-change isomorphism. -/
def coordinateIdealPullbackIso (φ : R →+* S) (j : Fin (n+1)) :
    (Scheme.Modules.pullback (nativeCoefficientMap φ)).obj
      (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j)) ≅
        ModularCurves.idealModule (coordinateHyperplaneι (R := S) j) := by
  let f := nativeCoefficientMap (n := n) φ
  let D := (coordinateHyperplaneι (R := R) j).ker
  have hD : D.IsInvertible := coordinateHyperplane_ker_isInvertible j
  have hf : (D.comap f).IsInvertible := by
    rw [show D.comap f = (coordinateHyperplaneι (R := S) j).ker from coordinateHyperplane_ker_comap φ j]
    exact coordinateHyperplane_ker_isInvertible j
  letI : IsIso (D.toModulesComapPullbackMap f) :=
    hD.toModulesComapPullbackMap_isIso_of_isInvertible_comap f hf
  exact (Scheme.Modules.pullback f).mapIso
      (MorphismKernelIdealModuleComparison.kernelIdealModuleIso (coordinateHyperplaneι (R := R) j)).symm ≪≫
    asIso (D.toModulesComapPullbackMap f) ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.toModules (coordinateHyperplane_ker_comap φ j)) ≪≫
    MorphismKernelIdealModuleComparison.kernelIdealModuleIso (coordinateHyperplaneι (R := S) j)

end EnvelopeProperty.ProjectiveCoordinateIdealBaseChange
