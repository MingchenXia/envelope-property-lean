import EnvelopeProperty.ComplexGeometry.Schemes.PolynomialProjectiveCanonical
import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAnalyticSeparation
import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAnalyticClosedEmbedding
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Actual analytic compactness of native complex polynomial Proj

Literal normalized coordinates produce genuine points of the native Proj
scheme. Its genuine affine ratio charts will identify these points locally,
and a continuous surjection from a genuine finite-dimensional unit sphere
will prove analytic compactness.
-/

open CategoryTheory AlgebraicGeometry Algebra
open scoped Topology

set_option backward.isDefEq.respectTransparency false

namespace ComplexSchemes

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual native projective coordinate chart as an actual complex affine chart. -/
def polynomialProjComplexAffineChart (n : ℕ) (i : Fin (n + 1)) :
    ComplexAffineChart (polynomialProj ℂ n) :=
  ⟨.of (polynomialProjCoordinateRing ℂ n i), polynomialProjCoordinateImmersion ℂ n i,
    inferInstance⟩

/-- Literal affine ratios of a complex homogeneous coordinate vector. -/
def polynomialProjVectorRatios (n : ℕ) (i : Fin (n + 1)) (z : Fin (n + 1) → ℂ) : Fin n → ℂ :=
  fun a => z (i.succAbove a) / z i

/-- The actual native affine ring is evaluated through its proved literal dehomogenization. -/
def polynomialProjVectorChartAlgebraPoint (n : ℕ) (i : Fin (n + 1))
    (z : Fin (n + 1) → ℂ) : ComplexAlgebraPoint (polynomialProjCoordinateRing ℂ n i) :=
  (MvPolynomial.aeval (polynomialProjVectorRatios n i z)).comp
    (polynomialProjCoordinateEquiv ℂ n i).toAlgHom

/-- The same actual evaluator respects the inherited native structural complex algebra. -/
def polynomialProjVectorChartInheritedPoint (n : ℕ) (i : Fin (n + 1))
    (z : Fin (n + 1) → ℂ) :
    let := affinePointFieldAlgebra
      ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
    ComplexAlgebraPoint (polynomialProjComplexAffineChart n i).ring := by
  let := affinePointFieldAlgebra
    ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
  refine { (polynomialProjVectorChartAlgebraPoint n i z).toRingHom with commutes' := ?_ }
  intro c
  change (polynomialProjVectorChartAlgebraPoint n i z)
    ((Spec.preimage (polynomialProjCoordinateImmersion ℂ n i ≫ polynomialProjStructureMap ℂ n)).hom c) = c
  rw [polynomialProjCoordinateImmersion_structure]
  change (polynomialProjVectorChartAlgebraPoint n i z)
    ((Spec.preimage (Spec.map (CommRingCat.ofHom (algebraMap ℂ
      (polynomialProjCoordinateRing ℂ n i))))).hom c) = c
  rw [Spec.preimage_map]
  exact (polynomialProjVectorChartAlgebraPoint n i z).commutes c

/-- The literal vector ratio point is an actual global complex scheme point of native polynomial Proj. -/
def polynomialProjVectorChartPoint (n : ℕ) (i : Fin (n + 1))
    (z : Fin (n + 1) → ℂ) : SchemeComplexPoint (polynomialProjStructureMap ℂ n) := by
  let := affinePointFieldAlgebra
    ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
  let := affineSchemePointTopologyOfStructure
    ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
  exact complexAffineChartPointMap (polynomialProjStructureMap ℂ n) (polynomialProjComplexAffineChart n i)
    ((affineSchemePointHomeomorphOfStructure _).symm (polynomialProjVectorChartInheritedPoint n i z))

/-- This actual projective point has its literal native Spec morphism followed by the native coordinate immersion. -/
theorem polynomialProjVectorChartPoint_val (n : ℕ) (i : Fin (n + 1))
    (z : Fin (n + 1) → ℂ) :
    (polynomialProjVectorChartPoint n i z).val =
      Spec.map (CommRingCat.ofHom (polynomialProjVectorChartAlgebraPoint n i z).toRingHom) ≫
        polynomialProjCoordinateImmersion ℂ n i := by
  let := affinePointFieldAlgebra
    ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
  let := affineSchemePointTopologyOfStructure
    ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
  change ((affineSchemePointHomeomorphOfStructure _).symm
    (polynomialProjVectorChartInheritedPoint n i z)).val ≫ _ = _
  rw [affineSchemePointHomeomorphOfStructure_symm_val]
  rfl

/-- Actual coordinate fractions evaluate at the literal normalized coordinates. -/
theorem polynomialProjVectorChartAlgebraPoint_ratio (n : ℕ) (i j : Fin (n + 1))
    (z : Fin (n + 1) → ℂ) (hi : z i ≠ 0) :
    polynomialProjVectorChartAlgebraPoint n i z (polynomialProjCoordinateRatio ℂ n i j) = z j / z i := by
  refine Fin.succAboveCases i ?_ (fun a => ?_) j
  · rw [polynomialProjCoordinateRatio_self, map_one, div_self hi]
  · change MvPolynomial.aeval (polynomialProjVectorRatios n i z)
      (polynomialProjCoordinateDehomogenization ℂ n i
        (polynomialProjCoordinateRatio ℂ n i (i.succAbove a))) = _
    rw [polynomialProjCoordinateDehomogenization_ratio, MvPolynomial.aeval_X]
    rfl

/-- Substitution and literal ratio evaluation normalize all homogeneous coordinates by their actual denominator. -/
theorem polynomialProjVectorChartAlgebraPoint_dehomogenization (n : ℕ) (i : Fin (n + 1))
    (z : Fin (n + 1) → ℂ) (hi : z i ≠ 0) (p : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial.eval (polynomialProjVectorRatios n i z)
      (polynomialProjDehomogenization ℂ n i p) =
        MvPolynomial.eval (fun j => (z i)⁻¹ * z j) p := by
  have h : (MvPolynomial.aeval (polynomialProjVectorRatios n i z)).comp
      (polynomialProjDehomogenization ℂ n i) =
        MvPolynomial.aeval (fun j => (z i)⁻¹ * z j) := by
    apply MvPolynomial.algHom_ext
    intro j
    refine Fin.succAboveCases i ?_ (fun a => ?_) j
    · simp [polynomialProjDehomogenization, polynomialProjDehomogenizationVariable_self, hi]
    · simp [polynomialProjDehomogenization, polynomialProjDehomogenizationVariable_succAbove,
        polynomialProjVectorRatios, div_eq_mul_inv, mul_comm]
  simpa only [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval] using AlgHom.congr_fun h p

/-- Every positive-degree homogeneous equation vanishes at the actual projective point exactly when it vanishes on the vector. -/
theorem polynomialProjVectorChartPoint_mem_homogeneous_positive (n : ℕ)
    (i : Fin (n + 1)) (z : Fin (n + 1) → ℂ) (hi : z i ≠ 0)
    (d : ℕ) (hd : 0 < d) (p : MvPolynomial (Fin (n + 1)) ℂ)
    (hp : p.IsHomogeneous d) :
    p ∈ (schemeComplexPointImage (polynomialProjStructureMap ℂ n)
      (polynomialProjVectorChartPoint n i z)).asHomogeneousIdeal ↔ MvPolynomial.eval z p = 0 := by
  let G := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ
  let e := polynomialProjVectorChartAlgebraPoint n i z
  have hk : (Spec.map (CommRingCat.ofHom e.toRingHom) default).asIdeal = RingHom.ker e.toRingHom := by
    have hdefault : (default : Spec (.of ℂ)) = (⊥ : PrimeSpectrum ℂ) := Subsingleton.elim _ _
    rw [hdefault]
    rfl
  have hopen : schemeComplexPointImage (polynomialProjStructureMap ℂ n)
      (polynomialProjVectorChartPoint n i z) ∈ Proj.basicOpen G p ↔
      e (HomogeneousLocalization.Away.isLocalizationElem
        (MvPolynomial.isHomogeneous_X ℂ i) hp) ≠ 0 := by
    unfold schemeComplexPointImage
    rw [polynomialProjVectorChartPoint_val, Scheme.Hom.comp_apply]
    change (Spec.map (CommRingCat.ofHom e.toRingHom) default) ∈
      polynomialProjCoordinateImmersion ℂ n i ⁻¹ᵁ Proj.basicOpen G p ↔ _
    rw [polynomialProjCoordinateImmersion,
      Proj.awayι_preimage_basicOpen G (MvPolynomial.isHomogeneous_X ℂ i) (by decide) hp hd]
    rw [PrimeSpectrum.mem_basicOpen, hk]
    rfl
  have heval : e (HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X ℂ i) hp) = (z i)⁻¹ ^ d * MvPolynomial.eval z p := by
    have helem : HomogeneousLocalization.Away.isLocalizationElem
        (MvPolynomial.isHomogeneous_X ℂ i) hp =
          HomogeneousLocalization.Away.mk G (MvPolynomial.isHomogeneous_X ℂ i) d p
            (by simpa [G] using hp) := by
      apply HomogeneousLocalization.val_injective
      simp only [HomogeneousLocalization.Away.isLocalizationElem,
        HomogeneousLocalization.Away.val_mk, pow_one]
    rw [helem]
    change MvPolynomial.eval (polynomialProjVectorRatios n i z)
      (polynomialProjCoordinateDehomogenization ℂ n i
        (HomogeneousLocalization.Away.mk G (MvPolynomial.isHomogeneous_X ℂ i) d
          p (by simpa [G] using hp))) = _
    rw [polynomialProjCoordinateDehomogenization_mk ℂ n i d p hp,
      polynomialProjVectorChartAlgebraPoint_dehomogenization n i z hi]
    exact homogeneousPolynomial_eval₂_scaled hp (RingHom.id ℂ) z (z i)⁻¹
  have hmul : e (HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X ℂ i) hp) = 0 ↔ MvPolynomial.eval z p = 0 := by
    rw [heval, mul_eq_zero, or_iff_right (pow_ne_zero _ (inv_ne_zero hi))]
  simpa only [Proj.mem_basicOpen, not_not] using
    (not_congr hopen).trans (by simpa only [not_not] using hmul)

/-- Every homogeneous equation has its actual vector vanishing condition, including degree zero. -/
theorem polynomialProjVectorChartPoint_mem_homogeneous (n : ℕ)
    (i : Fin (n + 1)) (z : Fin (n + 1) → ℂ) (hi : z i ≠ 0)
    (d : ℕ) (p : MvPolynomial (Fin (n + 1)) ℂ) (hp : p.IsHomogeneous d) :
    p ∈ (schemeComplexPointImage (polynomialProjStructureMap ℂ n)
      (polynomialProjVectorChartPoint n i z)).asHomogeneousIdeal ↔ MvPolynomial.eval z p = 0 := by
  cases d with
  | succ d =>
    exact polynomialProjVectorChartPoint_mem_homogeneous_positive n i z hi _
      (Nat.succ_pos _) p hp
  | zero =>
    let x := schemeComplexPointImage (polynomialProjStructureMap ℂ n)
      (polynomialProjVectorChartPoint n i z)
    have hXi : MvPolynomial.X i ∉ x.asHomogeneousIdeal := by
      rw [polynomialProjVectorChartPoint_mem_homogeneous_positive n i z hi 1 (by decide)
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i), MvPolynomial.eval_X]
      exact hi
    have hprod : (p * MvPolynomial.X i).IsHomogeneous 1 := by
      simpa using hp.mul (MvPolynomial.isHomogeneous_X ℂ i)
    have hmem : p ∈ x.asHomogeneousIdeal ↔ p * MvPolynomial.X i ∈ x.asHomogeneousIdeal :=
      ⟨fun hp => Ideal.mul_mem_right _ _ hp,
        fun h => (x.isPrime.mem_or_mem h).resolve_right hXi⟩
    rw [hmem, polynomialProjVectorChartPoint_mem_homogeneous_positive n i z hi 1 (by decide)
      (p * MvPolynomial.X i) hprod, map_mul, MvPolynomial.eval_X,
      mul_eq_zero, or_iff_left hi]

/-- Different nonzero coordinates define the same genuine global native projective scheme point. -/
theorem polynomialProjVectorChartPoint_eq (n : ℕ) (i j : Fin (n + 1))
    (z : Fin (n + 1) → ℂ) (hi : z i ≠ 0) (hj : z j ≠ 0) :
    polynomialProjVectorChartPoint n i z = polynomialProjVectorChartPoint n j z := by
  apply schemeComplexPointImage_injective (polynomialProjStructureMap ℂ n)
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d p hp
  exact (polynomialProjVectorChartPoint_mem_homogeneous n i z hi d p hp).trans
    (polynomialProjVectorChartPoint_mem_homogeneous n j z hj d p hp).symm

/-- Scaling a literal nonzero vector does not change any actual ratio point. -/
theorem polynomialProjVectorChartPoint_smul (n : ℕ) (i : Fin (n + 1))
    (z : Fin (n + 1) → ℂ) (c : ℂ) (hc : c ≠ 0) :
    polynomialProjVectorChartPoint n i (c • z) = polynomialProjVectorChartPoint n i z := by
  have hr : polynomialProjVectorRatios n i (c • z) = polynomialProjVectorRatios n i z := by
    funext a
    exact mul_div_mul_left _ _ hc
  apply Subtype.ext
  rw [polynomialProjVectorChartPoint_val, polynomialProjVectorChartPoint_val]
  have he : polynomialProjVectorChartAlgebraPoint n i (c • z) =
      polynomialProjVectorChartAlgebraPoint n i z := by
    unfold polynomialProjVectorChartAlgebraPoint
    rw [hr]
  rw [he]

/-- A literal nonzero vector has an actual nonzero coordinate. -/
theorem polynomialProjVector_exists_nonzero_coordinate (n : ℕ)
    (z : Fin (n + 1) → ℂ) (hz : z ≠ 0) : ∃ i, z i ≠ 0 := by
  by_contra! h
  exact hz (funext h)

/-- The native projective point of an actual nonzero vector, choosing an actual nonzero-coordinate chart. -/
def polynomialProjNonzeroVectorPoint (n : ℕ) (z : {z : Fin (n + 1) → ℂ // z ≠ 0}) :
    SchemeComplexPoint (polynomialProjStructureMap ℂ n) :=
  polynomialProjVectorChartPoint n
    (polynomialProjVector_exists_nonzero_coordinate n z.val z.property).choose z.val

/-- Near any actual nonzero coordinate the global native vector-point map is its genuine ratio-chart formula. -/
theorem polynomialProjNonzeroVectorPoint_eq_chart (n : ℕ)
    (z : {z : Fin (n + 1) → ℂ // z ≠ 0}) (i : Fin (n + 1)) (hi : z.val i ≠ 0) :
    polynomialProjNonzeroVectorPoint n z = polynomialProjVectorChartPoint n i z.val :=
  polynomialProjVectorChartPoint_eq n _ i z.val
    (polynomialProjVector_exists_nonzero_coordinate n z.val z.property).choose_spec hi

/-- On its genuine nonvanishing-coordinate domain, the literal projective ratio-chart formula is continuous. -/
theorem polynomialProjVectorChartPoint_continuousOn (n : ℕ) (i : Fin (n + 1)) :
    let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    ContinuousOn (polynomialProjVectorChartPoint n i) {z | z i ≠ 0} := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  let := affinePointFieldAlgebra
    ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
  let := affineSchemePointTopologyOfStructure
    ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hr : Continuous (fun z : {z : Fin (n + 1) → ℂ // z i ≠ 0} =>
      polynomialProjVectorRatios n i z.val) := by
    apply continuous_pi_iff.mpr
    intro a
    exact ((continuous_apply (i.succAbove a)).comp continuous_subtype_val).div
      ((continuous_apply i).comp continuous_subtype_val) (fun z => z.property)
  have he : Continuous (fun z : {z : Fin (n + 1) → ℂ // z i ≠ 0} =>
      polynomialProjVectorChartInheritedPoint n i z.val) := by
    apply (continuous_complexPoint_iff _).mpr
    intro a
    change Continuous (fun z : {z : Fin (n + 1) → ℂ // z i ≠ 0} =>
      MvPolynomial.eval (polynomialProjVectorRatios n i z.val)
        (polynomialProjCoordinateDehomogenization ℂ n i a))
    exact (complexPolynomial_continuous (polynomialProjCoordinateDehomogenization ℂ n i a)).comp hr
  exact (complexAffineChartPointMap_continuous (polynomialProjStructureMap ℂ n)
    (polynomialProjComplexAffineChart n i)).comp
      ((affineSchemePointHomeomorphOfStructure _).symm.continuous.comp he)

/-- The native projective point map from actual nonzero homogeneous vectors is continuous. -/
theorem polynomialProjNonzeroVectorPoint_continuous (n : ℕ) :
    let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    Continuous (polynomialProjNonzeroVectorPoint n) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨i, hi⟩ := polynomialProjVector_exists_nonzero_coordinate n z.val z.property
  have hopen : IsOpen {v : Fin (n + 1) → ℂ | v i ≠ 0} :=
    isOpen_ne_fun (continuous_apply i) continuous_const
  have hchart := (polynomialProjVectorChartPoint_continuousOn n i).continuousAt
    (hopen.mem_nhds hi)
  have hcomp : ContinuousAt (fun v : {v : Fin (n + 1) → ℂ // v ≠ 0} =>
      polynomialProjVectorChartPoint n i v.val) z := hchart.comp continuous_subtype_val.continuousAt
  apply hcomp.congr
  filter_upwards [hopen.preimage continuous_subtype_val |>.mem_nhds hi] with v hv
  exact (polynomialProjNonzeroVectorPoint_eq_chart n v i hv).symm

/-- Every actual affine chart algebra point supplies a literal homogeneous vector with coordinate one. -/
def polynomialProjAlgebraPointVector (n : ℕ) (i : Fin (n + 1))
    (a : ComplexAlgebraPoint (polynomialProjCoordinateRing ℂ n i)) : Fin (n + 1) → ℂ :=
  Fin.insertNth i 1 (fun t => a (polynomialProjCoordinateRatio ℂ n i (i.succAbove t)))

/-- The distinguished coordinate of the actual affine-point vector is exactly one. -/
theorem polynomialProjAlgebraPointVector_self (n : ℕ) (i : Fin (n + 1))
    (a : ComplexAlgebraPoint (polynomialProjCoordinateRing ℂ n i)) :
    polynomialProjAlgebraPointVector n i a i = 1 := by
  simp [polynomialProjAlgebraPointVector]

/-- Actual vector ratio evaluations recover the entire actual affine algebra point. -/
theorem polynomialProjAlgebraPointVector_chartAlgebraPoint (n : ℕ) (i : Fin (n + 1))
    (a : ComplexAlgebraPoint (polynomialProjCoordinateRing ℂ n i)) :
    polynomialProjVectorChartAlgebraPoint n i (polynomialProjAlgebraPointVector n i a) = a := by
  have h : a.comp (polynomialProjRatioMap ℂ n i) =
      MvPolynomial.aeval (polynomialProjVectorRatios n i (polynomialProjAlgebraPointVector n i a)) := by
    apply MvPolynomial.algHom_ext
    intro t
    simp [polynomialProjRatioMap, polynomialProjVectorRatios, polynomialProjAlgebraPointVector]
  apply AlgHom.ext
  intro b
  have hval := AlgHom.congr_fun h (polynomialProjCoordinateDehomogenization ℂ n i b)
  change MvPolynomial.aeval
    (polynomialProjVectorRatios n i (polynomialProjAlgebraPointVector n i a))
      (polynomialProjCoordinateDehomogenization ℂ n i b) = a b
  simpa only [AlgHom.comp_apply, polynomialProjRatioMap_coordinateDehomogenization] using hval.symm

/-- Every genuine complex point of native polynomial Proj is represented by an actual nonzero vector. -/
theorem polynomialProjNonzeroVectorPoint_surjective (n : ℕ) :
    Function.Surjective (polynomialProjNonzeroVectorPoint n) := by
  intro p
  have hcover : schemeComplexPointImage (polynomialProjStructureMap ℂ n) p ∈
      ⨆ i : Fin (n + 1), (polynomialProjCoordinateImmersion ℂ n i).opensRange := by
    rw [polynomialProjCoordinateImmersion_covers]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcover
  let q := schemeComplexPointLift (polynomialProjStructureMap ℂ n)
    (polynomialProjCoordinateImmersion ℂ n i) p hi
  let qc : SchemeComplexPoint (complexAffineStructureMap (polynomialProjCoordinateRing ℂ n i)) :=
    ⟨q.val, by
      change q.val ≫ affineStructuralMap ℂ (.of (polynomialProjCoordinateRing ℂ n i)) = 𝟙 _
      rw [← polynomialProjCoordinateImmersion_structure]
      exact q.property⟩
  let a := affineSchemePoint_toAlgebra (polynomialProjCoordinateRing ℂ n i) qc
  let z := polynomialProjAlgebraPointVector n i a
  have hzi : z i = 1 := polynomialProjAlgebraPointVector_self n i a
  have hz : z ≠ 0 := by
    intro h
    have hzero := congrArg (fun v : Fin (n + 1) → ℂ => v i) h
    rw [hzi] at hzero
    exact one_ne_zero hzero
  refine ⟨⟨z, hz⟩, ?_⟩
  rw [polynomialProjNonzeroVectorPoint_eq_chart n ⟨z, hz⟩ i
    (by change z i ≠ 0; rw [hzi]; exact one_ne_zero)]
  apply Subtype.ext
  rw [polynomialProjVectorChartPoint_val, polynomialProjAlgebraPointVector_chartAlgebraPoint]
  change Spec.map (Spec.preimage q.val) ≫ polynomialProjCoordinateImmersion ℂ n i = p.val
  rw [Spec.map_preimage]
  exact schemeComplexPointLift_fac (polynomialProjStructureMap ℂ n)
    (polynomialProjCoordinateImmersion ℂ n i) p hi

/-- The genuine unit sphere in finite complex coordinate space with its standard sup norm. -/
abbrev polynomialProjComplexUnitSphere (n : ℕ) :=
  Metric.sphere (0 : Fin (n + 1) → ℂ) 1

/-- Every vector on the genuine unit sphere is nonzero. -/
theorem polynomialProjComplexUnitSphere_ne_zero (n : ℕ) (z : polynomialProjComplexUnitSphere n) :
    z.val ≠ 0 := by
  intro h
  have hz := z.property
  rw [h] at hz
  simp at hz

/-- The genuine native projective point map from the actual complex unit sphere. -/
def polynomialProjComplexUnitSpherePoint (n : ℕ) (z : polynomialProjComplexUnitSphere n) :
    SchemeComplexPoint (polynomialProjStructureMap ℂ n) :=
  polynomialProjNonzeroVectorPoint n ⟨z.val, polynomialProjComplexUnitSphere_ne_zero n z⟩

/-- The actual unit-sphere projective point map is continuous for the actual analytic topology. -/
theorem polynomialProjComplexUnitSpherePoint_continuous (n : ℕ) :
    let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    Continuous (polynomialProjComplexUnitSpherePoint n) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  exact (polynomialProjNonzeroVectorPoint_continuous n).comp
    (continuous_subtype_val.subtype_mk (polynomialProjComplexUnitSphere_ne_zero n))

/-- Actual normalization of a nonzero homogeneous vector proves genuine unit-sphere point-map surjectivity. -/
theorem polynomialProjComplexUnitSpherePoint_surjective (n : ℕ) :
    Function.Surjective (polynomialProjComplexUnitSpherePoint n) := by
  intro p
  obtain ⟨z, hzp⟩ := polynomialProjNonzeroVectorPoint_surjective n p
  let c : ℂ := (‖z.val‖ : ℂ)⁻¹
  have hnorm : ‖z.val‖ ≠ 0 := norm_ne_zero_iff.mpr z.property
  have hc : c ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hnorm)
  let w := c • z.val
  have hw : w ∈ polynomialProjComplexUnitSphere n := by
    change dist (c • z.val) 0 = 1
    rw [dist_zero_right, norm_smul, _root_.norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg z.val), inv_mul_cancel₀ hnorm]
  refine ⟨⟨w, hw⟩, ?_⟩
  obtain ⟨i, hi⟩ := polynomialProjVector_exists_nonzero_coordinate n z.val z.property
  have hwi : w i ≠ 0 := mul_ne_zero hc hi
  change polynomialProjNonzeroVectorPoint n ⟨w, polynomialProjComplexUnitSphere_ne_zero n ⟨w, hw⟩⟩ = p
  rw [polynomialProjNonzeroVectorPoint_eq_chart n _ i hwi,
    polynomialProjVectorChartPoint_smul n i z.val c hc,
    ← polynomialProjNonzeroVectorPoint_eq_chart n z i hi]
  exact hzp

/-- Native complex polynomial Proj is compact in its genuine analytic complex-point topology. -/
theorem polynomialProjComplexPoint_compactSpace (n : ℕ) :
    @CompactSpace (SchemeComplexPoint (polynomialProjStructureMap ℂ n))
      (schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  rw [← isCompact_univ_iff,
    ← (polynomialProjComplexUnitSpherePoint_surjective n).range_eq]
  exact isCompact_range (polynomialProjComplexUnitSpherePoint_continuous n)

/-- A genuine native closed subscheme of actual complex polynomial Proj has an actually compact analytic point space. -/
theorem closedPolynomialProjComplexPoint_compactSpace {Y : Scheme} (n : ℕ)
    (i : Y ⟶ polynomialProj ℂ n) [IsClosedImmersion i] :
    @CompactSpace (SchemeComplexPoint (i ≫ polynomialProjStructureMap ℂ n))
      (schemeAnalyticPointTopology (i ≫ polynomialProjStructureMap ℂ n)) := by
  let : @CompactSpace (SchemeComplexPoint (polynomialProjStructureMap ℂ n))
      (schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)) :=
    polynomialProjComplexPoint_compactSpace n
  exact closedImmersionComplexPoint_compactSpace (polynomialProjStructureMap ℂ n) i

end

end ComplexSchemes
