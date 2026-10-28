import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingProduct
import DeJongAlterations.Geometry.BlowupDivisor
import EnvelopeProperty.AlgGeom.GeneratedTupleTwistSections
import EnvelopeProperty.AlgGeom.CartierInvertibleSheaves
import EnvelopeProperty.AlgGeom.SchemeSectionPreservingGluing
import EnvelopeProperty.AlgGeom.HironakaDeJongBlowupComparison

/-! # The actual homogeneous tautological line of the original ideal blowup -/

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open DeJongAlterations
open DeJongAlterations.Geometry
open DeJongAlterations.Geometry.ProjectiveIdeal
open DeJongAlterations.Geometry.BlowupProjectiveEmbedding
open DeJongAlterations.Algebra.ReesPresentation

universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] {m : ℕ}

private theorem variable_mem (i : Fin (m+1)) :
    MvPolynomial.X i ∈ projectiveSpaceGrading R m (1 : ℕ) :=
  MvPolynomial.isHomogeneous_X R i

private theorem variable_mem_once (i : Fin (m+1)) :
    MvPolynomial.X i ∈ projectiveSpaceGrading R m ((1 : ℕ) • (1 : ℕ)) := by
  simpa only [one_smul] using variable_mem (R := R) i

private theorem homogeneousCoordinate_typed (i j : Fin (m+1)) :
    homogeneousChartRatioHom (R := R) i (coordinateDehomCoord i j) =
      Away.mk (projectiveSpaceGrading R m) (variable_mem (R := R) i) 1
        (MvPolynomial.X j) (variable_mem_once (R := R) j) :=
  DeJongAlterations.Algebra.Segre.homogeneousChartRatioHom_coordinate i j

private theorem coordinateInclusion_typed (i : Fin (m+1)) :
    DeJongAlterations.Geometry.Segre.coordinateChartInclusion (R := R) i =
      Spec.map (homogeneousChartEquiv (R := R) i).toRingEquiv.toCommRingCatIso.hom ≫
        Proj.awayι (projectiveSpaceGrading R m) (MvPolynomial.X i)
          (variable_mem (R := R) i) (by decide : 0 < (1 : ℕ)) :=
  DeJongAlterations.Geometry.Segre.coordinateChartInclusion_eq i

private def generatorGradedMap (r : R →+* A) (I : Ideal A)
    (g : Fin (m+1) → A) (hspan : Ideal.span (Set.range g) = I) :
    projectiveSpaceGrading R m →+*ᵍ reesGrading I :=
  (generatorPolynomialMap I g hspan).toGradedRingHom.comp (polynomialCoefficientMap r m)

private theorem generatorGradedMap_X (r : R →+* A) (I : Ideal A)
    (g : Fin (m+1) → A) (hspan : Ideal.span (Set.range g) = I) (i : Fin (m+1)) :
    generatorGradedMap r I g hspan (MvPolynomial.X i) =
      reesDegreeOne I (g i) (generator_mem I g hspan i) := by
  change reesPolynomialEval I g _ (MvPolynomial.map r (MvPolynomial.X i)) = _
  rw [MvPolynomial.map_X, reesPolynomialEval, MvPolynomial.aeval_X]

private theorem generatorGradedMap_irrelevant (r : R →+* A) (I : Ideal A)
    (g : Fin (m+1) → A) (hspan : Ideal.span (Set.range g) = I) :
    HomogeneousIdeal.irrelevant (reesGrading I) ≤
      (HomogeneousIdeal.irrelevant (projectiveSpaceGrading R m)).map
        (generatorGradedMap r I g hspan) :=
  HomogeneousIdeal.irrelevant_le_map_comp (polynomialCoefficientMap_irrelevant r m)
    (ProjClosedImmersion.irrelevant_le_map_of_surjective _
      (generatorPolynomialMap_surjective I g hspan))

private theorem affineProjectiveMap_graded (r : R →+* A) (I : Ideal A)
    (g : Fin (m+1) → A) (hspan : Ideal.span (Set.range g) = I) :
    affineProjectiveMap r I g hspan =
      Proj.map (generatorGradedMap r I g hspan)
        (generatorGradedMap_irrelevant r I g hspan) := by
  unfold generatorGradedMap
  rw [Proj.map_comp]
  rfl

variable [IsDomain A]

private def fractionHomAt (I : Ideal A) (g : A) (hg : g ∈ I) (hg0 : g ≠ 0)
    (b : reesAlgebra I) (hb : b = reesDegreeOne I g hg) :
    Away (reesGrading I) b →+* affineBlowupFractionChart I g := by
  subst b
  exact (reesChartFractionEquiv I g hg hg0).toAlgHom.toRingHom

private theorem fractionHomAt_generator (I : Ideal A) (g : A) (hg : g ∈ I)
    (hg0 : g ≠ 0) (b : reesAlgebra I) (hb : b = reesDegreeOne I g hg)
    (hbd : b ∈ reesGrading I 1) (a : A) (ha : a ∈ I) :
    fractionHomAt I g hg hg0 b hb
      (Away.mk (reesGrading I) hbd 1 (reesDegreeOne I a ha)
        (by simpa using reesDegreeOne_mem I a ha)) =
      affineBlowupChartRatio I g a ha := by
  subst b
  apply Subtype.ext
  exact reesChartFractionEquiv_generator I g hg hg0 a ha

private theorem chartInclusionAt (I : Ideal A) (g : A) (hg : g ∈ I) (hg0 : g ≠ 0)
    (b : reesAlgebra I) (hb : b = reesDegreeOne I g hg)
    (hbd : b ∈ reesGrading I 1) :
    affineBlowupChartInclusion I g hg hg0 =
      Spec.map (CommRingCat.ofHom (fractionHomAt I g hg hg0 b hb)) ≫
        Proj.awayι (reesGrading I) b hbd (by decide : 0 < (1 : ℕ)) := by
  subst b
  rfl

omit [IsDomain A] in
private theorem coordinateNonAssocSemiringParent_eq (i : Fin (m+1)) :
    @Semiring.toNonAssocSemiring (CoordinateRing R i)
        (inferInstance : Semiring (CoordinateRing R i)) =
      (inferInstance : NonAssocSemiring (CoordinateRing R i)) := by
  rfl

private theorem fractionNonAssocSemiringParent_eq (I : Ideal A) (g : A) :
    @Semiring.toNonAssocSemiring (affineBlowupFractionChart I g)
        (inferInstance : Semiring (affineBlowupFractionChart I g)) =
      (inferInstance : NonAssocSemiring (affineBlowupFractionChart I g)) := by
  rfl

private def reparentHom {B C : Type u}
    {sB tB : NonAssocSemiring B} {sC tC : NonAssocSemiring C}
    (hB : sB = tB) (hC : sC = tC) (f : @RingHom B C sB sC) :
    @RingHom B C tB tC := by
  subst tB
  subst tC
  exact f

private theorem reparentHom_apply {B C : Type u}
    {sB tB : NonAssocSemiring B} {sC tC : NonAssocSemiring C}
    (hB : sB = tB) (hC : sC = tC) (f : @RingHom B C sB sC) (x : B) :
    reparentHom hB hC f x = f x := by
  subst tB
  subst tC
  rfl

omit [IsDomain A] in
private theorem reesFraction_congr (I : Ideal A) (b : reesAlgebra I)
    (hb : b ∈ reesGrading I (1 : ℕ)) (x y : reesAlgebra I)
    (hx : x ∈ reesGrading I ((1 : ℕ) • (1 : ℕ)))
    (hy : y ∈ reesGrading I ((1 : ℕ) • (1 : ℕ))) (hxy : x = y) :
    Away.mk (reesGrading I) hb 1 x hx = Away.mk (reesGrading I) hb 1 y hy := by
  subst y
  rfl

omit [IsDomain A] in
private theorem coordinate_composition {S : Type u} (I : Ideal A)
    (G : projectiveSpaceGrading R m →+*ᵍ reesGrading I) (i j : Fin (m+1))
    (e : Away (reesGrading I) (G (MvPolynomial.X i)) → S)
    (a : reesAlgebra I) (ha : a ∈ reesGrading I ((1 : ℕ) • (1 : ℕ)))
    (hXa : G (MvPolynomial.X j) = a) (x : S)
    (hEv : e (Away.mk (reesGrading I) (G.map_mem (variable_mem (R := R) i)) 1 a ha) = x) :
    e (Away.map G (MvPolynomial.X i)
      (homogeneousChartRatioHom i (coordinateDehomCoord i j))) = x := by
  have h₁ := congrArg (fun z => e (Away.map G (MvPolynomial.X i) z))
    (homogeneousCoordinate_typed (R := R) i j)
  have h₂ := congrArg e
    (Away.map_mk G (MvPolynomial.X i) (variable_mem (R := R) i) 1
      (MvPolynomial.X j) (variable_mem_once (R := R) j))
  have h₃ := congrArg e (reesFraction_congr I (G (MvPolynomial.X i))
    (G.map_mem (variable_mem (R := R) i)) (G (MvPolynomial.X j)) a
    (G.map_mem (variable_mem_once (R := R) j)) ha hXa)
  exact h₁.trans (h₂.trans (h₃.trans hEv))

omit [IsDomain A] in
private def coordinateRingMap {S : Type u} [Semiring S] (I : Ideal A)
    (G : projectiveSpaceGrading R m →+*ᵍ reesGrading I) (i : Fin (m+1))
    (e : Away (reesGrading I) (G (MvPolynomial.X i)) →+* S) :
    @RingHom (CoordinateRing R i) S
      (@Semiring.toNonAssocSemiring (CoordinateRing R i) inferInstance)
      (@Semiring.toNonAssocSemiring S inferInstance) where
  toFun z := e (Away.map G (MvPolynomial.X i) (homogeneousChartRatioHom i z))
  map_zero' := by simp only [map_zero]
  map_one' := by simp only [map_one]
  map_add' x y := by simp only [map_add]
  map_mul' x y := by simp only [map_mul]

omit [IsDomain A] in
private theorem coordinateRingMap_coordinate {S : Type u} [Semiring S] (I : Ideal A)
    (G : projectiveSpaceGrading R m →+*ᵍ reesGrading I) (i j : Fin (m+1))
    (e : Away (reesGrading I) (G (MvPolynomial.X i)) →+* S)
    (a : reesAlgebra I) (ha : a ∈ reesGrading I ((1 : ℕ) • (1 : ℕ)))
    (hXa : G (MvPolynomial.X j) = a) (x : S)
    (hEv : e (Away.mk (reesGrading I) (G.map_mem (variable_mem (R := R) i)) 1 a ha) = x) :
    coordinateRingMap I G i e (coordinateDehomCoord i j) = x := by
  exact coordinate_composition I G i j (fun z => e z) a ha hXa x hEv


private def generatorChartRingMap (r : R →+* A) (I : Ideal A)
    (g : Fin (m+1) → A) (hspan : Ideal.span (Set.range g) = I)
    (i : Fin (m+1)) (hi : g i ≠ 0) :
    CoordinateRing R i →+* affineBlowupFractionChart I (g i) :=
  reparentHom (coordinateNonAssocSemiringParent_eq (R := R) i)
    (fractionNonAssocSemiringParent_eq I (g i))
    (coordinateRingMap I (generatorGradedMap r I g hspan) i
      (fractionHomAt I (g i) (generator_mem I g hspan i) hi
        (generatorGradedMap r I g hspan (MvPolynomial.X i))
        (generatorGradedMap_X r I g hspan i)))

private theorem generatorChartRingMap_coordinate (r : R →+* A) (I : Ideal A)
    (g : Fin (m+1) → A) (hspan : Ideal.span (Set.range g) = I)
    (i : Fin (m+1)) (hi : g i ≠ 0) (j : Fin (m+1)) :
    generatorChartRingMap r I g hspan i hi (coordinateDehomCoord i j) =
      affineBlowupChartRatio I (g i) (g j) (generator_mem I g hspan j) := by
  let G := generatorGradedMap r I g hspan
  let e := fractionHomAt I (g i) (generator_mem I g hspan i) hi
    (G (MvPolynomial.X i)) (generatorGradedMap_X r I g hspan i)
  have h₄ := fractionHomAt_generator I (g i) (generator_mem I g hspan i) hi
    (G (MvPolynomial.X i)) (generatorGradedMap_X r I g hspan i)
    (G.map_mem (variable_mem (R := R) i))
    (g j) (generator_mem I g hspan j)
  have h := coordinateRingMap_coordinate I G i j e
    (reesDegreeOne I (g j) (generator_mem I g hspan j))
    (by simpa only [one_smul] using reesDegreeOne_mem I (g j) (generator_mem I g hspan j))
    (generatorGradedMap_X r I g hspan j) _ h₄
  exact (reparentHom_apply (coordinateNonAssocSemiringParent_eq (R := R) i)
    (fractionNonAssocSemiringParent_eq I (g i)) (coordinateRingMap I G i e)
    (coordinateDehomCoord i j)).trans h


private theorem affineProjectiveMap_homogeneousChart (r : R →+* A) (I : Ideal A)
    (g : Fin (m+1) → A) (hspan : Ideal.span (Set.range g) = I)
    (i : Fin (m+1)) (hi : g i ≠ 0) :
    affineBlowupChartInclusion I (g i) (generator_mem I g hspan i) hi ≫
        affineProjectiveMap r I g hspan =
      Spec.map (CommRingCat.ofHom
        ((fractionHomAt I (g i) (generator_mem I g hspan i) hi
          (generatorGradedMap r I g hspan (MvPolynomial.X i))
          (generatorGradedMap_X r I g hspan i)).comp
            (Away.map (generatorGradedMap r I g hspan) (MvPolynomial.X i)))) ≫
        Proj.awayι (projectiveSpaceGrading R m) (MvPolynomial.X i)
          (variable_mem (R := R) i) (by decide : 0 < (1 : ℕ)) := by
  let G := generatorGradedMap r I g hspan
  let hG := generatorGradedMap_irrelevant r I g hspan
  let e := fractionHomAt I (g i) (generator_mem I g hspan i) hi
    (G (MvPolynomial.X i)) (generatorGradedMap_X r I g hspan i)
  let u := Spec.map (CommRingCat.ofHom e)
  let a := Proj.awayι (reesGrading I) (G (MvPolynomial.X i))
    (G.map_mem (variable_mem (R := R) i)) (by decide : 0 < (1 : ℕ))
  let q := Proj.map G hG
  let v := Spec.map (CommRingCat.ofHom (Away.map G (MvPolynomial.X i)))
  let c := Proj.awayι (projectiveSpaceGrading R m) (MvPolynomial.X i)
    (variable_mem (R := R) i) (by decide : 0 < (1 : ℕ))
  have hs : affineBlowupChartInclusion I (g i) (generator_mem I g hspan i) hi ≫
      affineProjectiveMap r I g hspan = (u ≫ a) ≫ q :=
    congrArg₂ (fun (f : Spec (.of (affineBlowupFractionChart I (g i))) ⟶ affineBlowup I)
      (j : affineBlowup I ⟶ projectiveSpace R m) => f ≫ j)
      (chartInclusionAt I (g i) (generator_mem I g hspan i) hi
        (G (MvPolynomial.X i)) (generatorGradedMap_X r I g hspan i)
        (G.map_mem (variable_mem (R := R) i))) (affineProjectiveMap_graded r I g hspan)
  have hm : a ≫ q = v ≫ c :=
    Proj.awayι_comp_map G hG (by decide : 0 < (1 : ℕ)) (MvPolynomial.X i)
      (variable_mem (R := R) i)
  have hu : u ≫ v = Spec.map (CommRingCat.ofHom
      (e.comp (Away.map G (MvPolynomial.X i)))) :=
    (Spec.map_comp (CommRingCat.ofHom (Away.map G (MvPolynomial.X i)))
      (CommRingCat.ofHom e)).symm
  exact hs.trans ((Category.assoc u a q).trans
    ((congrArg (fun f => u ≫ f) hm).trans
      ((Category.assoc u v c).symm.trans (congrArg (fun f => f ≫ c) hu))))

private theorem affineProjectiveMap_coordinateChart (r : R →+* A) (I : Ideal A)
    (g : Fin (m+1) → A) (hspan : Ideal.span (Set.range g) = I)
    (i : Fin (m+1)) (hi : g i ≠ 0) :
    affineBlowupChartInclusion I (g i) (generator_mem I g hspan i) hi ≫
        affineProjectiveMap r I g hspan =
      Spec.map (CommRingCat.ofHom (generatorChartRingMap r I g hspan i hi)) ≫
        DeJongAlterations.Geometry.Segre.coordinateChartInclusion i := by
  let e := fractionHomAt I (g i) (generator_mem I g hspan i) hi
    (generatorGradedMap r I g hspan (MvPolynomial.X i)) (generatorGradedMap_X r I g hspan i)
  let φ := e.comp (Away.map (generatorGradedMap r I g hspan) (MvPolynomial.X i))
  let θ := generatorChartRingMap r I g hspan i hi
  let E := homogeneousChartEquiv (R := R) i
  let c := Proj.awayι (projectiveSpaceGrading R m) (MvPolynomial.X i)
    (variable_mem (R := R) i) (by decide : 0 < (1 : ℕ))
  have hRing : θ.comp E.toRingHom = φ := by
    apply RingHom.ext
    intro z
    change e (Away.map (generatorGradedMap r I g hspan) (MvPolynomial.X i)
      (homogeneousChartRatioHom i (homogeneousChartEquiv i z))) =
        e (Away.map (generatorGradedMap r I g hspan) (MvPolynomial.X i) z)
    exact congrArg (fun t => e (Away.map (generatorGradedMap r I g hspan) (MvPolynomial.X i) t))
      (E.symm_apply_apply z)
  have hMap : Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom θ) ≫ Spec.map E.toRingEquiv.toCommRingCatIso.hom := by
    have hCat : E.toRingEquiv.toCommRingCatIso.hom ≫ CommRingCat.ofHom θ =
        CommRingCat.ofHom φ := by
      apply CommRingCat.hom_ext
      exact hRing
    exact (congrArg Spec.map hCat).symm.trans (Spec.map_comp _ _)
  have hInc := congrArg (fun f => Spec.map (CommRingCat.ofHom θ) ≫ f)
    (coordinateInclusion_typed (R := R) i)
  exact (affineProjectiveMap_homogeneousChart r I g hspan i hi).trans
    ((congrArg (fun f => f ≫ c) hMap).trans
      ((Category.assoc _ _ _).trans hInc.symm))

private theorem generatorChartRingMap_C (r : R →+* A) (I : Ideal A)
    (g : Fin (m+1) → A) (hspan : Ideal.span (Set.range g) = I)
    (i : Fin (m+1)) (hi : g i ≠ 0) (c : R) :
    generatorChartRingMap r I g hspan i hi (MvPolynomial.C c) =
      algebraMap A (affineBlowupFractionChart I (g i)) (r c) := by
  have h : (affineBlowupChartInclusion I (g i) (generator_mem I g hspan i) hi ≫
      affineProjectiveMap r I g hspan) ≫ projectiveSpaceStructure R m =
      Spec.map (CommRingCat.ofHom
        ((algebraMap A (affineBlowupFractionChart I (g i))).comp r)) := by
    rw [Category.assoc, affineProjectiveMap_structure, ← Category.assoc,
      affineBlowupChartInclusion_structure, ← Spec.map_comp]
    rfl
  rw [affineProjectiveMap_coordinateChart r I g hspan i hi, Category.assoc,
    DeJongAlterations.Geometry.Segre.coordinateChartInclusion_structure,
    ← Spec.map_comp] at h
  have hh := Spec.map_injective h
  exact congrArg (fun q : CommRingCat.of R ⟶
    CommRingCat.of (affineBlowupFractionChart I (g i)) => q.hom c) hh

private theorem generatorChartRingMap_eq_eval (r : R →+* A) (I : Ideal A)
    (g : Fin (m+1) → A) (hspan : Ideal.span (Set.range g) = I)
    (i : Fin (m+1)) (hi : g i ≠ 0) :
    generatorChartRingMap r I g hspan i hi =
      MvPolynomial.eval₂Hom ((algebraMap A (affineBlowupFractionChart I (g i))).comp r)
        (fun j : ChartIndex i =>
          affineBlowupChartRatio I (g i) (g j.1) (generator_mem I g hspan j.1)) := by
  classical
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [generatorChartRingMap_C, MvPolynomial.eval₂Hom_C]
    rfl
  · intro j
    rw [MvPolynomial.eval₂Hom_X']
    simpa only [coordinateDehomCoord, dif_neg j.2] using
      generatorChartRingMap_coordinate r I g hspan i hi j.1

/-- The SAME original specified-generator Rees morphism retains its entire
original chart-ring evaluation at the actual ideal ratios, with original coefficients. -/
theorem affineGeneratorChartReadback (r : R →+* A) (I : Ideal A)
    (g : Fin (m+1) → A) (hspan : Ideal.span (Set.range g) = I)
    (i : Fin (m+1)) (hi : g i ≠ 0) :
    affineBlowupChartInclusion I (g i) (generator_mem I g hspan i) hi ≫
        affineProjectiveMap r I g hspan =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.eval₂Hom ((algebraMap A (affineBlowupFractionChart I (g i))).comp r)
          (fun j : ChartIndex i =>
            affineBlowupChartRatio I (g i) (g j.1) (generator_mem I g hspan j.1)))) ≫
        DeJongAlterations.Geometry.Segre.coordinateChartInclusion i := by
  rw [affineProjectiveMap_coordinateChart r I g hspan i hi, generatorChartRingMap_eq_eval]

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
