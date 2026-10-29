import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionEulerPolynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-!
# Seshadri Ampleness Criterion Euler Polynomial Coefficients

Canonical original Euler polynomials and their actual top coefficients. -/

set_option pp.fullNames true in
#check @SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
#print axioms SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
set_option pp.fullNames true in
#check @Polynomial.eq_of_infinite_eval_eq
#print axioms Polynomial.eq_of_infinite_eval_eq

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace Polynomial
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion
open SchemeCoherentEulerCharacteristic
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private theorem polynomial_eq_of_nat_evals (p q : ℚ[X])
    (h : ∀ n : ℕ, p.eval (n : ℚ) = q.eval (n : ℚ)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.Ioi_infinite (0 : ℕ)).image
    (show Set.InjOn (fun n : ℕ => (n : ℚ)) (Set.Ioi (0 : ℕ)) from
      Nat.cast_injective.injOn)).mono
  rintro x ⟨n, _, rfl⟩
  exact h n

private theorem finiteType_of_invertible_forCoefficients {Y : Scheme.{u}}
    (M : Y.Modules) (hM : IsInvertible M) : M.IsFiniteType := by
  let : M.IsFinitePresentation := hM.isFinitePresentation
  exact SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := Y.ringCatSheaf) M

variable {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
variable (f : X ⟶ Spec (.of k)) [IsProjective f]

/-- The unique polynomial furnished by the genuine same-coefficient Euler theorem. -/
def eulerPolynomial (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (L : X.Modules) (hL : IsInvertible L) : ℚ[X] :=
  Classical.choose (exists_eulerPolynomial f F L hL)

theorem eulerPolynomial_eval (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (L : X.Modules) (hL : IsInvertible L) (n : ℕ) :
    (eulerPolynomial f F L hL).eval (n : ℚ) =
      (eulerCharacteristic f (F ⊗ CanonicalGeometry.bundleTensorPower L n) : ℚ) :=
  Classical.choose_spec (exists_eulerPolynomial f F L hL) n

theorem eulerPolynomial_natDegree_le (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (L : X.Modules) (hL : IsInvertible L) (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    (eulerPolynomial f F L hL).natDegree ≤ d := by
  obtain ⟨q, hdeg, hq⟩ := exists_eulerPolynomial_of_dimension_le d f hdim F L hL
  have heq : eulerPolynomial f F L hL = q := polynomial_eq_of_nat_evals _ _
    (fun n => (eulerPolynomial_eval f F L hL n).trans (hq n).symm)
  rw [heq]
  exact hdeg

/-- The canonical polynomial of the original line powers, with original unit coherence internal. -/
def lineEulerPolynomial (L : X.Modules) (hL : IsInvertible L) : ℚ[X] := by
  let : (unitObj X).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj X).IsFiniteType :=
    finiteType_of_invertible_forCoefficients (unitObj X) isInvertible_unit
  exact eulerPolynomial f (unitObj X) L hL

theorem lineEulerPolynomial_eval (L : X.Modules) (hL : IsInvertible L) (n : ℕ) :
    (lineEulerPolynomial f L hL).eval (n : ℚ) =
      (eulerCharacteristic f (CanonicalGeometry.bundleTensorPower L n) : ℚ) := by
  let : (unitObj X).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj X).IsFiniteType :=
    finiteType_of_invertible_forCoefficients (unitObj X) isInvertible_unit
  change (eulerPolynomial f (unitObj X) L hL).eval (n : ℚ) = _
  rw [eulerPolynomial_eval]
  let P := CanonicalGeometry.bundleTensorPower L n
  let e : unitObj X ⊗ P ≅ P :=
    ((ModularCurves.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl P) ≪≫ λ_ P
  exact congrArg (fun z : ℤ => (z : ℚ)) (eulerCharacteristic_eq_of_iso f e)

theorem lineEulerPolynomial_natDegree_le (L : X.Modules) (hL : IsInvertible L)
    (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    (lineEulerPolynomial f L hL).natDegree ≤ d := by
  let : (unitObj X).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj X).IsFiniteType :=
    finiteType_of_invertible_forCoefficients (unitObj X) isInvertible_unit
  change (eulerPolynomial f (unitObj X) L hL).natDegree ≤ d
  exact eulerPolynomial_natDegree_le f (unitObj X) L hL d hdim

private theorem isProjective_closedComp_coefficients {Z Y W : Scheme.{u}}
    (i : Z ⟶ Y) [IsClosedImmersion i] (p : Y ⟶ W) [IsProjective p] :
    IsProjective (i ≫ p) := by
  constructor
  obtain ⟨E, hE, hEF, j, hj, hjp⟩ := IsProjective.exists_isClosedImmersion (f := p)
  let : IsClosedImmersion j := hj
  refine ⟨E, hE, hEF, i ≫ j, inferInstance, ?_⟩
  exact (Category.assoc i j E.projectiveBundleπ).trans
    (congrArg (fun q => i ≫ q) hjp)

/-- An original invertible coefficient affects only lower full-Euler terms,
proved on its same actual Cartier cuts, with no polynomial comparison input. -/
theorem eulerPolynomial_sub_lineEulerPolynomial_natDegree_le [IsIntegral X]
    (T : X.Modules) [T.IsQuasicoherent] [T.IsFiniteType] (hT : IsInvertible T)
    (L : X.Modules) (hL : IsInvertible L) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ)) :
    (eulerPolynomial f T L hL - lineEulerPolynomial f L hL).natDegree ≤ d := by
  let hf := ProjectiveFactorizationRingIso.of_isProjective f
  obtain ⟨B, hB, a, b, ha, hb, _⟩ :=
    exists_eulerCharacteristic_powerCartierDifference f hf T hT
  let hA : IsInvertible (T ⊗ B) :=
    (hT.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso T B)
  let I := LineSectionZeroIdeal.zeroIdeal (T ⊗ B) hA a
  let J := LineSectionZeroIdeal.zeroIdeal B hB b
  let i := I.subschemeι
  let j := J.subschemeι
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace i
  let : CompactSpace J.subscheme := QuasiCompact.compactSpace_of_compactSpace j
  let : I.subscheme.IsSeparated := ⟨by
    have h : IsSeparated (i ≫ terminal.from X) := inferInstance
    simpa only [terminal.comp_from] using h⟩
  let : J.subscheme.IsSeparated := ⟨by
    have h : IsSeparated (j ≫ terminal.from X) := inferInstance
    simpa only [terminal.comp_from] using h⟩
  let : IsProjective (i ≫ f) := isProjective_closedComp_coefficients i f
  let : IsProjective (j ≫ f) := isProjective_closedComp_coefficients j f
  have hdimI : topologicalKrullDim I.subscheme ≤ d :=
    sectionZero_dimension_drop d hdim (T ⊗ B) hA a ha
  have hdimJ : topologicalKrullDim J.subscheme ≤ d :=
    sectionZero_dimension_drop d hdim B hB b hb
  let Fi := Scheme.Modules.pullback i
  let Fj := Scheme.Modules.pullback j
  let : Fi.Monoidal := Scheme.Modules.pullbackMonoidal i
  let TI := Fi.obj T
  let LI := Fi.obj L
  let LJ := Fj.obj L
  let hTI : IsInvertible TI := hT.pullback i
  let hLI : IsInvertible LI := hL.pullback i
  let hLJ : IsInvertible LJ := hL.pullback j
  let : TI.IsQuasicoherent := hTI.isQuasicoherent
  let : TI.IsFiniteType := finiteType_of_invertible_forCoefficients TI hTI
  let qI := eulerPolynomial (i ≫ f) TI LI hLI
  let qJ := lineEulerPolynomial (j ≫ f) LJ hLJ
  have hdI : qI.natDegree ≤ d := eulerPolynomial_natDegree_le (i ≫ f) TI LI hLI d hdimI
  have hdJ : qJ.natDegree ≤ d := lineEulerPolynomial_natDegree_le (j ≫ f) LJ hLJ d hdimJ
  have hqI (n : ℕ) : qI.eval (n : ℚ) =
      (eulerCharacteristic (i ≫ f) (TI ⊗ CanonicalGeometry.bundleTensorPower LI n) : ℚ) :=
    eulerPolynomial_eval (i ≫ f) TI LI hLI n
  have hqJ (n : ℕ) : qJ.eval (n : ℚ) =
      (eulerCharacteristic (j ≫ f) (CanonicalGeometry.bundleTensorPower LJ n) : ℚ) :=
    lineEulerPolynomial_eval (j ≫ f) LJ hLJ n
  have heq : eulerPolynomial f T L hL - lineEulerPolynomial f L hL = qI - qJ := by
    apply polynomial_eq_of_nat_evals
    intro n
    let P := CanonicalGeometry.bundleTensorPower L n
    let hP : IsInvertible P := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n
    let eI : Fi.obj (T ⊗ P) ≅ TI ⊗ CanonicalGeometry.bundleTensorPower LI n :=
      (Functor.Monoidal.μIso Fi T P).symm ≪≫
        (Iso.refl TI ⊗ᵢ TestConfigurationSectionTransport.tensorPowerPullbackIso i L n)
    let eJ : Fj.obj P ≅ CanonicalGeometry.bundleTensorPower LJ n :=
      TestConfigurationSectionTransport.tensorPowerPullbackIso j L n
    have h := eulerCharacteristic_cartierDifference f hf T B P hT hB hP a ha b hb
    change eulerCharacteristic f (T ⊗ P) - eulerCharacteristic f P =
      eulerCharacteristic (i ≫ f) (Fi.obj (T ⊗ P)) -
        eulerCharacteristic (j ≫ f) (Fj.obj P) at h
    rw [eulerCharacteristic_eq_of_iso (i ≫ f) eI,
      eulerCharacteristic_eq_of_iso (j ≫ f) eJ] at h
    calc
      (eulerPolynomial f T L hL - lineEulerPolynomial f L hL).eval (n : ℚ) =
          (eulerCharacteristic f (T ⊗ P) : ℚ) - (eulerCharacteristic f P : ℚ) := by
        rw [eval_sub, eulerPolynomial_eval, lineEulerPolynomial_eval]
      _ = (eulerCharacteristic (i ≫ f) (TI ⊗ CanonicalGeometry.bundleTensorPower LI n) : ℚ) -
          (eulerCharacteristic (j ≫ f) (CanonicalGeometry.bundleTensorPower LJ n) : ℚ) := by
        exact_mod_cast h
      _ = (qI - qJ).eval (n : ℚ) := by rw [eval_sub, hqI n, hqJ n]
  rw [heq]
  exact (natDegree_sub_le_iff_left hdJ).mpr hdI

/-- The actual positive-dimensional top Euler coefficient is unchanged by
an original invertible coefficient on the same integral projective ambient. -/
theorem eulerPolynomial_coeff_eq_lineEulerPolynomial [IsIntegral X]
    (T : X.Modules) [T.IsQuasicoherent] [T.IsFiniteType] (hT : IsInvertible T)
    (L : X.Modules) (hL : IsInvertible L) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ)) :
    (eulerPolynomial f T L hL).coeff (d + 1) = (lineEulerPolynomial f L hL).coeff (d + 1) := by
  have hdeg := eulerPolynomial_sub_lineEulerPolynomial_natDegree_le f T hT L hL d hdim
  have hz : (eulerPolynomial f T L hL - lineEulerPolynomial f L hL).coeff (d + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (Nat.lt_succ_self d))
  rw [coeff_sub] at hz
  exact sub_eq_zero.mp hz

#check @eulerPolynomial_sub_lineEulerPolynomial_natDegree_le
#print axioms eulerPolynomial_sub_lineEulerPolynomial_natDegree_le
#check @eulerPolynomial_coeff_eq_lineEulerPolynomial
#print axioms eulerPolynomial_coeff_eq_lineEulerPolynomial
#check @eulerPolynomial_eval
#print axioms eulerPolynomial_eval
#check @eulerPolynomial_natDegree_le
#print axioms eulerPolynomial_natDegree_le
#check @lineEulerPolynomial_eval
#print axioms lineEulerPolynomial_eval
#check @lineEulerPolynomial_natDegree_le
#print axioms lineEulerPolynomial_natDegree_le
end EnvelopeProperty.SeshadriAmplenessCriterion
