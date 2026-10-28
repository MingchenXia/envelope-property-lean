import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsNativeChartMaps

/-! # The ENTIRE original obstacle scheme ideal has EXACTLY its SAME old affine chart image -/

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
open ProjBerk Char0.EnvelopeGradedBaseIdealsCore
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The WHOLE original obstacle ideal on the SAME actual affine family chart,
transported by the SAME field-linear section equivalence, is EXACTLY the
original obstacle ideal mapped by the original old dehomogenization.
No chart-ideal or ring-map comparison certificate is an input. -/
theorem schemeIdeal_chart_map (d : ℕ) (φ : X.an → ℝ) (q : ℕ)
    (j : Fin (M + 1)) (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal) :
    letI := (familyAbsoluteStructure X).sectionsAlgebra (familyChartOpen X j)
    ((schemeIdeal X d φ q).ideal (familyChartAffineOpen X j)).map
      (familyChartSectionsEquiv X j hj).toRingHom =
      (X.obstacleIdeal d φ q).map (Polynomial.mapRingHom (X.quotDehom j).toRingHom) := by
  let := (familyAbsoluteStructure X).sectionsAlgebra (familyChartOpen X j)
  let U := familyChartAffineOpen X j
  let V : (NativeProjectiveScheme k[X] M).affineOpens :=
    ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩
  let a := (familyInclusion X).appLE V.1 U.1 (familyChartOpen_eq X j).le
  let r := (nativeCoordinateSectionsIso (R := k[X]) j).hom.hom
  let e := familyChartSectionsEquiv X j hj
  let ψ : (MvPolynomial (Fin (M + 1)) k)[X] →+* Γ(familyScheme X, U.1) :=
    a.hom.comp (r.comp ((coordinateDehom j).toRingHom.comp
      (parameterEquiv (k := k) (M := M)).toRingHom))
  have hm : e.toRingHom.comp ψ = Polynomial.mapRingHom (X.quotDehom j).toRingHom := by
    apply RingHom.ext
    intro g
    exact familyChartSectionsEquiv_parameterDehom X j hj g
  have hc : (schemeIdeal X d φ q).ideal U = ((ambientSchemeIdeal X d φ q).ideal V).map a.hom :=
    Scheme.IdealSheafData.comap_ideal_of_affine_opens (ambientSchemeIdeal X d φ q)
      (familyInclusion X) U V (familyChartOpen_eq X j).le
  have hp : (ambientSchemeIdeal X d φ q).ideal V =
      ((parameterObstacleIdeal X d φ q).map (coordinateDehom j).toRingHom).map r :=
    quotientIdealSheaf_coordinateIdeal (homogeneousObstacleIdeal X d φ q) j
  calc
    ((schemeIdeal X d φ q).ideal U).map e.toRingHom =
        (((ambientSchemeIdeal X d φ q).ideal V).map a.hom).map e.toRingHom :=
      congrArg (Ideal.map e.toRingHom) hc
    _ = ((((parameterObstacleIdeal X d φ q).map (coordinateDehom j).toRingHom).map r).map a.hom).map
        e.toRingHom := congrArg (fun I => (I.map a.hom).map e.toRingHom) hp
    _ = (X.obstacleIdeal d φ q).map (e.toRingHom.comp ψ) := by
      unfold parameterObstacleIdeal
      simp only [Ideal.map_map]
      rfl
    _ = (X.obstacleIdeal d φ q).map (Polynomial.mapRingHom (X.quotDehom j).toRingHom) :=
      congrArg (Ideal.map (I := X.obstacleIdeal d φ q)) hm

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
