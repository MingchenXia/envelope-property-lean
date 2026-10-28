import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionIntersectionPositivity
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionCutCohomology
import EnvelopeProperty.AlgGeom.ProjectiveLineClosedPointEvaluation

/-! Same original Euler growth and global sections, without unknown-line ampleness. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace Filter Topology
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion
open SchemeCoherentEulerCharacteristic SchemeCoherentEulerIndex SchemeCoherentEulerExact SchemeLineSectionEvaluation
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

theorem polynomial_tendsto_nat_atTop_of_coeff_pos (P : Polynomial ℚ) (d : ℕ)
    (hd : 0 < d) (hdeg : P.natDegree ≤ d) (hc : 0 < P.coeff d) :
    Tendsto (fun n : ℕ => P.eval (n : ℚ)) atTop atTop := by
  have hnd : P.natDegree = d :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg (ne_of_gt hc)
  have hlead : 0 ≤ P.leadingCoeff := by
    rw [← Polynomial.coeff_natDegree, hnd]
    exact hc.le
  exact (P.tendsto_atTop_of_leadingCoeff_nonneg
    (Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)) hlead).comp
      tendsto_natCast_atTop_atTop

variable {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]

/-- An auxiliary bound on the original Euler sum. The geometric theorem below
internally supplies its actual higher-cohomology isomorphisms from two cuts. -/
theorem exists_eulerCharacteristic_le_sections_add_of_higher_isos
    (f : X ⟶ Spec (.of k)) (L : X.Modules) (hL : IsInvertible L)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (hiso : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℕ, Nonempty
      (fieldCech f (CanonicalGeometry.bundleTensorPower L (n + 1)) U (q + 2) ≅
        fieldCech f (CanonicalGeometry.bundleTensorPower L n) U (q + 2))) :
    ∃ (N : ℕ) (C : ℤ), ∀ n : ℕ, N ≤ n →
      eulerCharacteristic f (CanonicalGeometry.bundleTensorPower L n) ≤
        (Module.finrank k (fieldSections f (CanonicalGeometry.bundleTensorPower L n)) : ℤ) + C := by
  classical
  obtain ⟨N, hN⟩ := hiso
  have hrank (n : ℕ) (hn : N ≤ n) (q : ℕ) :
      Module.finrank k (fieldCech f (CanonicalGeometry.bundleTensorPower L n) U (q + 2)) =
        Module.finrank k (fieldCech f (CanonicalGeometry.bundleTensorPower L N) U (q + 2)) := by
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      obtain ⟨e⟩ := hN n hn q
      exact e.toLinearEquiv.finrank_eq.trans ih
  let B := Nat.card ι
  let C : ℤ := ∑ q ∈ Finset.range B, (-1 : ℤ) ^ (2 + q) *
    (Module.finrank k (fieldCech f (CanonicalGeometry.bundleTensorPower L N) U (2 + q)) : ℤ)
  refine ⟨N, C, fun n hn => ?_⟩
  let M := CanonicalGeometry.bundleTensorPower L n
  let : M.IsQuasicoherent :=
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n).isQuasicoherent
  have htail : (∑ q ∈ Finset.range B, (-1 : ℤ) ^ (2 + q) *
      (Module.finrank k (fieldCech f M U (2 + q)) : ℤ)) = C := by
    apply Finset.sum_congr rfl
    intro q _
    rw [show 2 + q = q + 2 by omega, hrank n hn q]
  have hzero : Module.finrank k (fieldCech f M U 0) =
      Module.finrank k (fieldSections f M) :=
    (fieldSectionsCechZeroIso f M U hU).toLinearEquiv.finrank_eq.symm
  have he : eulerCharacteristic f M =
      (Module.finrank k (fieldSections f M) : ℤ) -
        (Module.finrank k (fieldCech f M U 1) : ℤ) + C := by
    rw [eulerCharacteristic_eq_on_cover f M U hU hUa,
      coverEuler_eq_of_card_le f M U (show Nat.card ι ≤ Nat.card ι + 1 by omega)
        (show Nat.card ι + 1 ≤ 2 + B by dsimp [B]; omega)]
    unfold coverEuler
    rw [Finset.sum_range_add, htail]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
      one_mul, zero_add, neg_one_mul, hzero]
    ring
  have hnonneg : (0 : ℤ) ≤ Module.finrank k (fieldCech f M U 1) := Int.natCast_nonneg _
  change eulerCharacteristic f M ≤ (Module.finrank k (fieldSections f M) : ℤ) + C
  omega

private theorem finiteType_unit_sectionGrowth (Y : Scheme.{u}) :
    (unitObj Y).IsFiniteType := by
  let : (unitObj Y).IsFinitePresentation := isInvertible_unit.isFinitePresentation
  exact SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := Y.ringCatSheaf) (unitObj Y)

/-- Positive original top mixed difference makes the SAME original Euler
polynomial tend to positive infinity; no unknown-line ampleness is assumed. -/
theorem lineEulerPolynomial_tendsto_atTop_of_mixedEulerDifference_pos
    (f : X ⟶ Spec (.of k)) [IsProjective f]
    (d : ℕ) (hd : 0 < d) (hdim : topologicalKrullDim X ≤ d)
    (L : X.Modules) (hL : IsInvertible L)
    (hpos : 0 < mixedEulerDifference f (List.replicate d L) (unitObj X)) :
    Tendsto (fun n : ℕ => (lineEulerPolynomial f L hL).eval (n : ℚ)) atTop atTop := by
  let : (unitObj X).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj X).IsFiniteType := finiteType_unit_sectionGrowth X
  have hfactor := mixedEulerDifference_replicate_eq_factorial_mul_coeff f d hdim
    (unitObj X) L hL
  change (mixedEulerDifference f (List.replicate d L) (unitObj X) : ℚ) =
    (Nat.factorial d : ℚ) * (lineEulerPolynomial f L hL).coeff d at hfactor
  have hposQ : (0 : ℚ) < mixedEulerDifference f (List.replicate d L) (unitObj X) := by
    exact_mod_cast hpos
  have hfact : (0 : ℚ) < Nat.factorial d := by exact_mod_cast Nat.factorial_pos d
  have hc : 0 < (lineEulerPolynomial f L hL).coeff d := by nlinarith
  exact polynomial_tendsto_nat_atTop_of_coeff_pos _ d hd
    (lineEulerPolynomial_natDegree_le f L hL d hdim) hc

/-- The actual two-cut geometric comparison and positive original top
intersection yield unbounded SAME original Gamma. The later total Nakai
induction must internally obtain cut ampleness from its smaller-dimensional
ordinary numerical hypotheses. A section of L^r is NOT needed here. -/
theorem exists_eventual_sections_rank_gt_of_twoCut_ample [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsProjective f]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (d : ℕ) (hd : 0 < d) (hdim : topologicalKrullDim X ≤ d)
    (L B : X.Modules) (hL : IsInvertible L) (hB : IsInvertible B)
    (a : unitObj X ⟶ L ⊗ B) (ha : a ≠ 0) (b : unitObj X ⟶ B) (hb : b ≠ 0)
    (hpos : 0 < mixedEulerDifference f (List.replicate d L) (unitObj X)) :
    let hA := (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
    let I := LineSectionZeroIdeal.zeroIdeal (L ⊗ B) hA a
    let J := LineSectionZeroIdeal.zeroIdeal B hB b
    SchemeLineAmpleness.IsAmple (I.subschemeι ≫ f) ((Scheme.Modules.pullback I.subschemeι).obj L) →
    SchemeLineAmpleness.IsAmple (J.subschemeι ≫ f) ((Scheme.Modules.pullback J.subschemeι).obj L) →
    ∀ target : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      target < Module.finrank k (fieldSections f (CanonicalGeometry.bundleTensorPower L n)) := by
  dsimp only
  intro hI hJ target
  obtain ⟨N, C, hbound⟩ := exists_eulerCharacteristic_le_sections_add_of_higher_isos f L hL U hU hUa
    (SeshadriAmplenessCriterionCutCohomology.exists_twoCut_powerCohomologyIso_of_ample
      f U hU hUa L B hL hB a ha b hb hI hJ)
  have ht := lineEulerPolynomial_tendsto_atTop_of_mixedEulerDifference_pos f d hd hdim L hL hpos
  obtain ⟨N', hN'⟩ := eventually_atTop.mp
    (ht.eventually_gt_atTop (((target : ℤ) + C : ℤ) : ℚ))
  refine ⟨max N N', fun n hn => ?_⟩
  have hv := hN' n ((le_max_right N N').trans hn)
  rw [lineEulerPolynomial_eval] at hv
  have hvZ : (target : ℤ) + C < eulerCharacteristic f (CanonicalGeometry.bundleTensorPower L n) := by
    exact_mod_cast hv
  have hbnd := hbound n ((le_max_left N N').trans hn)
  have hresult : (target : ℤ) <
      (Module.finrank k (fieldSections f (CanonicalGeometry.bundleTensorPower L n)) : ℤ) := by omega
  exact_mod_cast hresult

/-- The SAME original positive top intersection and two proper-cut ample
restrictions internally yield the FIRST unknown-line-power section through any
specified original closed point. No section, H0-rank or evaluation certificate
is an input. The total Nakai induction must still supply the cut ampleness. -/
theorem exists_nonzero_power_section_at_closedPoint_of_twoCut_ample [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsProjective f]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (d : ℕ) (hd : 0 < d) (hdim : topologicalKrullDim X ≤ d)
    (L B : X.Modules) (hL : IsInvertible L) (hB : IsInvertible B)
    (a : unitObj X ⟶ L ⊗ B) (ha : a ≠ 0) (b : unitObj X ⟶ B) (hb : b ≠ 0)
    (hpos : 0 < mixedEulerDifference f (List.replicate d L) (unitObj X))
    (x : X) (hx : IsClosed ({x} : Set X)) :
    let hA := (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
    let I := LineSectionZeroIdeal.zeroIdeal (L ⊗ B) hA a
    let J := LineSectionZeroIdeal.zeroIdeal B hB b
    SchemeLineAmpleness.IsAmple (I.subschemeι ≫ f) ((Scheme.Modules.pullback I.subschemeι).obj L) →
    SchemeLineAmpleness.IsAmple (J.subschemeι ≫ f) ((Scheme.Modules.pullback J.subschemeι).obj L) →
    ∃ (r : ℕ) (_hr : 0 < r)
      (s : unitObj X ⟶ CanonicalGeometry.bundleTensorPower L r),
      s ≠ 0 ∧ pullbackSectionHom (X.fromSpecResidueField x) s = 0 ∧
      let Ipoint := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
      let D := LineSectionZeroIdeal.zeroIdeal (CanonicalGeometry.bundleTensorPower L r)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) s
      ∃ j : Ipoint.subscheme ⟶ D.subscheme,
        IsClosedImmersion j ∧ j ≫ D.subschemeι = Ipoint.subschemeι := by
  dsimp only
  intro hI hJ
  let := AffineSchemeLocalDegrees.residueAlgebra f x
  obtain ⟨N, hN⟩ := exists_eventual_sections_rank_gt_of_twoCut_ample
    f U hU hUa d hd hdim L B hL hB a ha b hb hpos hI hJ
      (Module.finrank k (X.residueField x))
  let r := max N 1
  have hr : 0 < r := lt_of_lt_of_le (by decide : 0 < 1) (le_max_right N 1)
  let P := CanonicalGeometry.bundleTensorPower L r
  let hP : IsInvertible P := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r
  have hfiber := ProjectiveLineClosedPointEvaluation.fiber_finite_finrank_eq_residue f x hx P hP
  have hdimfiber : Module.finrank k (fieldSections (X.fromSpecResidueField x ≫ f)
      ((Scheme.Modules.pullback (X.fromSpecResidueField x)).obj P)) <
        Module.finrank k (fieldSections f P) := by
    rw [hfiber.2]
    exact hN r (le_max_left N 1)
  obtain ⟨s, hs, hsx, j, hj, hcomp⟩ :=
    ProjectiveLineClosedPointEvaluation.exists_nonzero_section_vanishing_at_closedPoint_of_finrank_gt
      f x hx P hP hdimfiber
  exact ⟨r, hr, s, hs, hsx, j, hj, hcomp⟩

#check @polynomial_tendsto_nat_atTop_of_coeff_pos
#print axioms polynomial_tendsto_nat_atTop_of_coeff_pos
#check @exists_eulerCharacteristic_le_sections_add_of_higher_isos
#print axioms exists_eulerCharacteristic_le_sections_add_of_higher_isos
#check @lineEulerPolynomial_tendsto_atTop_of_mixedEulerDifference_pos
#print axioms lineEulerPolynomial_tendsto_atTop_of_mixedEulerDifference_pos
#check @exists_eventual_sections_rank_gt_of_twoCut_ample
#print axioms exists_eventual_sections_rank_gt_of_twoCut_ample
#check @exists_nonzero_power_section_at_closedPoint_of_twoCut_ample
#print axioms exists_nonzero_power_section_at_closedPoint_of_twoCut_ample
end EnvelopeProperty.SeshadriAmplenessCriterion
