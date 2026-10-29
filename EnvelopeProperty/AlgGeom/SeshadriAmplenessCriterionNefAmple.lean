import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionNakai
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionNefAmpleCutPositivity
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionNefAmplePolynomials
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionNefAmpleThreshold
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionNefAmpleRealPositivity
import EnvelopeProperty.AlgGeom.NativeNumericalAmpleDomination
import EnvelopeProperty.AlgGeom.AmpleLinePositivePowers

/-! # Nef plus ample is ample

Let `p : X ⟶ Spec k` be projective, let `N` be an invertible module whose numerical class is
nef (nonnegative degree on every closed integral curve of `X`) and let `A` be ample. Then
`N ⊗ A` is ample (`isAmple_tensor_nef`). This is Kleiman's theorem in the form of
Lazarsfeld, *Positivity I*, Corollary 1.4.10 (nef plus ample is ample), proved as in
Theorem 1.4.9 via the Nakai criterion.

The proof is an induction on a bound `d + 1` for the dimension. By strata ampleness it suffices
to treat integral `X` of dimension exactly `d + 1`. For `a > 0` and `b > 0` the line
`B_{a,b} = N^b ⊗ A^a` restricts to an ample line on every closed subscheme of dimension `≤ d`
(induction hypothesis). With `f(t) = (N + tA)^{d+1}`, `h(t) = N · (N + tA)^d` and
`g(t) = A · (N + tA)^d` we have `f = h + t g` and, for rational `t = a / b > 0`:

* `f(t) > 0` implies that `B_{a,b}` is ample (integral Nakai step), hence `h(t) ≥ 0`
  (`mixedEulerDifference_nef_ample_nonneg`);
* `g(t) > 0` and `g'(t) ≥ 0` (cuts by sections of powers of `A`), so `g > 0` on `(0, ∞)`;
* `f` is eventually positive since its leading coefficient is `A^{d+1} > 0`.

The threshold argument (`positive_of_eventually_positive_and_rational_mixed_nonneg`) gives
`f > 0` on `(0, ∞)`; in particular `f(1) > 0` and `N ⊗ A = B_{1,1}` is ample.

We also record the consequences used elsewhere: positive powers of ample lines are ample on any
projective scheme (`positive_power_ample_general`), nonnegative powers of nef lines are nef, and
`N^b ⊗ A^a` is ample for all `b` and `a > 0`.

Blueprint: `seshadri-ampleness-criterion-nef-ample.tex`.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace Filter Topology
universe u

namespace EnvelopeProperty.SeshadriAmplenessCriterionNefAmple
open SeshadriAmplenessCriterion CanonicalGeometry
open SeshadriAmplenessCriterionNefAmpleMixedIntersections
open SeshadriAmplenessCriterionNefAmpleCutPositivity
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private theorem projective_closed_comp {Z Y W : Scheme.{u}}
    (i : Z ⟶ Y) [IsClosedImmersion i] (p : Y ⟶ W) [IsProjective p] :
    IsProjective (i ≫ p) := by
  constructor
  obtain ⟨E, hE, hEF, j, hj, hjp⟩ := IsProjective.exists_isClosedImmersion (f := p)
  let : IsClosedImmersion j := hj
  exact ⟨E, hE, hEF, i ≫ j, inferInstance,
    (Category.assoc i j E.projectiveBundleπ).trans
      (congrArg (fun q => i ≫ q) hjp)⟩

private theorem tensor_invertible {X : Scheme.{u}} {N A : X.Modules}
    (hN : IsInvertible N) (hA : IsInvertible A) : IsInvertible (N ⊗ A) :=
  (hN.tensorObj hA).of_iso (ModularCurves.monoidalTensorObjIso N A)

private theorem unit_finiteType (X : Scheme.{u}) : (unitObj X).IsFiniteType := by
  let : (unitObj X).IsFinitePresentation := isInvertible_unit.isFinitePresentation
  exact SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := X.ringCatSheaf) (unitObj X)

private theorem positive_rat_parameters (q : ℚ) (hq : 0 < q) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (q : ℝ) = (a : ℝ) / (b : ℝ) := by
  have hn : 0 < q.num := Rat.num_pos.mpr hq
  have ha : 0 < q.num.toNat := by omega
  have hc : (q.num.toNat : ℝ) = (q.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hn.le
  refine ⟨q.num.toNat, q.den, ha, q.den_pos, ?_⟩
  rw [Rat.cast_def, hc]

/-- Every positive tensor power of an ample line is ample, on an arbitrary (possibly reducible
or nonreduced) projective scheme: on each reduced point closure this is the integral case, and
strata ampleness concludes. -/
theorem positive_power_ample_general
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (A : X.Modules) (hA : SchemeLineAmpleness.IsAmple p A) (a : ℕ) (ha : 0 < a) :
    SchemeLineAmpleness.IsAmple p (bundleTensorPower A a) := by
  apply SeshadriAmplenessCriterionStrataAmpleness.isAmple_of_strataAmple p
    (bundleTensorPower A a) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.1 a)
  intro eta
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
  let i := I.subschemeι
  let : IsIntegral I.subscheme := SchemePointClosureIntegral.isIntegral_pointClosure eta
  let : IsProjective (i ≫ p) := projective_closed_comp i p
  have hAi := isAmple_closedPullback i p A hA
  have hpower := AmpleLinePositivePowers.isAmple_tensorPower (i ≫ p)
    ((Scheme.Modules.pullback i).obj A) hAi a ha
  exact AmpleTensorLines.ample_of_iso hpower (BundleTensorPowerPullback.pullbackIso i A a).symm

/-- Every tensor power `N^b` of a nef line `N` is nef: its degree on each curve is `b` times
the degree of `N`. -/
theorem lineClass_tensorPower_mem_nefCone
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (N : X.Modules) (hN : IsInvertible N)
    (hnef : NativeRealNumericalClasses.lineClass p N hN ∈
      NativeRealNumericalClasses.nefCone p) (b : ℕ) :
    NativeRealNumericalClasses.lineClass p (bundleTensorPower N b)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hN b) ∈
        NativeRealNumericalClasses.nefCone p := by
  rw [NativeRealNumericalClasses.lineClass_tensorPower p N hN b]
  exact NativeRealNumericalClasses.nefCone_smul_nonneg p hnef (Nat.cast_nonneg b)

private theorem strata_tensor_nef_reduction
    {k : Type u} [Field k] (d : ℕ)
    (H : ∀ {Y : Scheme.{u}} [IsIntegral Y]
      (q : Y ⟶ Spec (.of k)) [IsProjective q],
      topologicalKrullDim Y ≤ d → ∀ (M B : Y.Modules) (hM : IsInvertible M),
      NativeRealNumericalClasses.lineClass q M hM ∈ NativeRealNumericalClasses.nefCone q →
      SchemeLineAmpleness.IsAmple q B → SchemeLineAmpleness.IsAmple q (M ⊗ B))
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ d) (N A : X.Modules) (hN : IsInvertible N)
    (hnef : NativeRealNumericalClasses.lineClass p N hN ∈
      NativeRealNumericalClasses.nefCone p)
    (hA : SchemeLineAmpleness.IsAmple p A) : SchemeLineAmpleness.IsAmple p (N ⊗ A) := by
  apply SeshadriAmplenessCriterionStrataAmpleness.isAmple_of_strataAmple
    p (N ⊗ A) (tensor_invertible hN hA.1)
  intro eta
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
  let i := I.subschemeι
  let : IsIntegral I.subscheme := SchemePointClosureIntegral.isIntegral_pointClosure eta
  let : IsProjective (i ≫ p) := projective_closed_comp i p
  let F := Scheme.Modules.pullback i
  let : F.Monoidal := Scheme.Modules.pullbackMonoidal i
  have hNi := hN.pullback i
  have hnefi := lineClass_pullback_mem_nefCone_of_closed p N hN hnef i
  have hAi := isAmple_closedPullback i p A hA
  have hdimI := IntegralSchemeDimension.topologicalKrullDim_le_of_isIntegralHom i d hdim
  have h := H (i ≫ p) hdimI (F.obj N) (F.obj A) hNi hnefi hAi
  exact AmpleTensorLines.ample_of_iso h (Functor.Monoidal.μIso F N A)

private theorem pencil_closed_ample_of_lower_dimension
    {k : Type u} [Field k] (d : ℕ)
    (H : ∀ {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k)) [IsProjective q],
      topologicalKrullDim Y ≤ d → ∀ (M B : Y.Modules) (hM : IsInvertible M),
      NativeRealNumericalClasses.lineClass q M hM ∈ NativeRealNumericalClasses.nefCone q →
      SchemeLineAmpleness.IsAmple q B → SchemeLineAmpleness.IsAmple q (M ⊗ B))
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]
    (N A : X.Modules) (hN : IsInvertible N)
    (hnef : NativeRealNumericalClasses.lineClass p N hN ∈
      NativeRealNumericalClasses.nefCone p)
    (hA : SchemeLineAmpleness.IsAmple p A) (a b : ℕ) (ha : 0 < a)
    {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
    (hdimY : topologicalKrullDim Y ≤ d) :
    SchemeLineAmpleness.IsAmple (i ≫ p)
      ((Scheme.Modules.pullback i).obj (bundleTensorPower N b ⊗ bundleTensorPower A a)) := by
  let : IsProjective (i ≫ p) := projective_closed_comp i p
  let F := Scheme.Modules.pullback i
  let : F.Monoidal := Scheme.Modules.pullbackMonoidal i
  have hNi : IsInvertible (F.obj N) := hN.pullback i
  have hnefi := lineClass_pullback_mem_nefCone_of_closed p N hN hnef i
  have hAi : SchemeLineAmpleness.IsAmple (i ≫ p) (F.obj A) := isAmple_closedPullback i p A hA
  have hpowerN : IsInvertible (bundleTensorPower (F.obj N) b) :=
    TensorPowerBaseIdealGrading.tensorPower_isInvertible hNi b
  have hpowerNef := lineClass_tensorPower_mem_nefCone (i ≫ p) (F.obj N) hNi hnefi b
  have hpowerA := positive_power_ample_general (i ≫ p) (F.obj A) hAi a ha
  have h := H (i ≫ p) hdimY (bundleTensorPower (F.obj N) b) (bundleTensorPower (F.obj A) a)
    hpowerN hpowerNef hpowerA
  let e : F.obj (bundleTensorPower N b ⊗ bundleTensorPower A a) ≅
      bundleTensorPower (F.obj N) b ⊗ bundleTensorPower (F.obj A) a :=
    (Functor.Monoidal.μIso F (bundleTensorPower N b) (bundleTensorPower A a)).symm ≪≫
      (BundleTensorPowerPullback.pullbackIso i N b ⊗ᵢ BundleTensorPowerPullback.pullbackIso i A a)
  exact AmpleTensorLines.ample_of_iso h e.symm

/-- The polynomial part of the argument: if `f = h + t g` where `f` has degree `d + 1` with
positive leading coefficient, `f(q) > 0 ⇒ h(q) ≥ 0`, `g(q) > 0` and `g'(q) ≥ 0` at all positive
rationals `q`, then `f > 0` on `(0, ∞)`. -/
private theorem pencil_pos_of_rational_tests (F H G : Polynomial ℝ) (d : ℕ)
    (hsucc : F = H + Polynomial.X * G)
    (hcoeff : 0 < F.coeff (d + 1)) (hnat : F.natDegree ≤ d + 1)
    (hHrat : ∀ q : ℚ, 0 < q → 0 < F.eval (q : ℝ) → 0 ≤ H.eval (q : ℝ))
    (hGpos : ∀ q : ℚ, 0 < q → 0 < G.eval (q : ℝ))
    (hGderiv : ∀ q : ℚ, 0 < q → 0 ≤ G.derivative.eval (q : ℝ)) :
    ∀ t : ℝ, 0 < t → 0 < F.eval t := by
  have hGall := polynomial_pos_of_positive_rational_tests_and_derivative_nonneg G hGpos hGderiv
  have hdegree : F.natDegree = d + 1 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hnat hcoeff.ne'
  have hleading : 0 < F.leadingCoeff := by
    simpa only [Polynomial.leadingCoeff, hdegree] using hcoeff
  have hdegreePos : 0 < F.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hdegree]
    exact Nat.zero_lt_succ d
  have hevent : ∀ᶠ t : ℝ in atTop, 0 < F.eval t :=
    (F.tendsto_atTop_of_leadingCoeff_nonneg hdegreePos hleading.le).eventually_gt_atTop 0
  have hidentity : ∀ t : ℝ, 0 < t → F.eval t = H.eval t + t * G.eval t := by
    intro t _ht
    rw [hsucc, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  exact positive_of_eventually_positive_and_rational_mixed_nonneg
    (fun t => F.eval t) (fun t => G.eval t) (fun t => H.eval t)
    F.differentiable.continuous.continuousOn H.differentiable.continuous.continuousOn
    hidentity hGall hevent hHrat

/-- The successor step on an integral scheme of dimension at most `d + 1`, assuming the
theorem on all projective schemes of dimension at most `d`. -/
private theorem integral_tensor_nef_step
    {k : Type u} [Field k] (d : ℕ)
    (H : ∀ {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k)) [IsProjective q],
      topologicalKrullDim Y ≤ d → ∀ (M B : Y.Modules) (hM : IsInvertible M),
      NativeRealNumericalClasses.lineClass q M hM ∈ NativeRealNumericalClasses.nefCone q →
      SchemeLineAmpleness.IsAmple q B → SchemeLineAmpleness.IsAmple q (M ⊗ B))
    {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ))
    (N A : X.Modules) (hN : IsInvertible N)
    (hnef : NativeRealNumericalClasses.lineClass p N hN ∈
      NativeRealNumericalClasses.nefCone p)
    (hA : SchemeLineAmpleness.IsAmple p A) : SchemeLineAmpleness.IsAmple p (N ⊗ A) := by
  by_cases hlow : topologicalKrullDim X ≤ (d : ℕ)
  · exact H p hlow N A hN hnef hA
  let hp := ProjectiveFactorizationRingIso.of_isProjective p
  let : IsProper p := hp.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : X.IsSeparated := ⟨by
    have hsep : IsSeparated (p ≫ terminal.from (Spec (.of k))) := inferInstance
    simpa only [terminal.comp_from] using hsep⟩
  let : (unitObj X).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj X).IsFiniteType := unit_finiteType X
  have hdimExact : topologicalKrullDim X = (d + 1 : ℕ) := by
    apply le_antisymm hdim
    apply le_of_not_gt
    intro hlt
    apply hlow
    apply ENat.WithBot.lt_add_one_iff.mp
    simpa only [Nat.cast_add, Nat.cast_one] using hlt
  -- The pencil lines `B a b = N^b ⊗ A^a`, ample on all closed subschemes of dimension `≤ d`.
  let B : ℕ → ℕ → X.Modules := fun a b => bundleTensorPower N b ⊗ bundleTensorPower A a
  have hB (a b : ℕ) : IsInvertible (B a b) :=
    tensor_invertible (TensorPowerBaseIdealGrading.tensorPower_isInvertible hN b)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.1 a)
  have hclosed (a b : ℕ) (ha : 0 < a) :
      ∀ {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i],
        topologicalKrullDim Y ≤ d →
          SchemeLineAmpleness.IsAmple (i ≫ p) ((Scheme.Modules.pullback i).obj (B a b)) := by
    intro Y i _ hdimY
    exact pencil_closed_ample_of_lower_dimension d H p N A hN hnef hA a b ha i hdimY
  -- The intersection polynomials `f = (N + tA)^{d+1}`, `h = N·(N + tA)^d`, `g = A·(N + tA)^d`.
  let Fpoly := mixedPencilPolynomial p N A (d + 1) [] (unitObj X)
  let Hpoly := mixedPencilPolynomial p N A d [N] (unitObj X)
  let Gpoly := mixedPencilPolynomial p N A d [A] (unitObj X)
  have hFscale (a b : ℕ) (hb : 0 < b) :
      (b : ℝ) ^ (d + 1) * Fpoly.eval ((a : ℝ) / (b : ℝ)) =
        (mixedEulerDifference p (List.replicate (d + 1) (B a b)) (unitObj X) : ℝ) := by
    have hs := mixedPencilPolynomial_eval_scale p N A hN hA.1 (d + 1) [] (d + 1) hdim
      (by simp) (by simp) (unitObj X) a b hb
    rw [List.append_nil] at hs
    exact hs
  have hscale_cons (L : X.Modules) (hL : IsInvertible L) (a b : ℕ) (hb : 0 < b) :
      (b : ℝ) ^ d * (mixedPencilPolynomial p N A d [L] (unitObj X)).eval
        ((a : ℝ) / (b : ℝ)) =
        (mixedEulerDifference p (L :: List.replicate d (B a b)) (unitObj X) : ℝ) := by
    have hs := mixedPencilPolynomial_eval_scale p N A hN hA.1 d [L] (d + 1) hdim
      (by simp) (by simpa using hL) (unitObj X) a b hb
    rw [mixedEulerDifference_perm p (List.perm_append_singleton L _) (unitObj X)] at hs
    exact hs
  -- Rational points of positivity of `f` give ample pencil lines (integral Nakai step).
  have hamp (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
      (hpos : 0 < Fpoly.eval ((a : ℝ) / (b : ℝ))) :
      SchemeLineAmpleness.IsAmple p (B a b) := by
    have htopReal : (0 : ℝ) <
        (mixedEulerDifference p (List.replicate (d + 1) (B a b)) (unitObj X) : ℝ) := by
      rw [← hFscale a b hb]
      exact mul_pos (pow_pos (by exact_mod_cast hb) _) hpos
    have htop : 0 < mixedEulerDifference p
        (List.replicate (d + 1) (B a b)) (unitObj X) := by exact_mod_cast htopReal
    apply isAmple_of_positive_diagonal_and_properIntegralClosedAmple
      p (d + 1) (Nat.zero_lt_succ d) hdim (B a b) (hB a b) htop
    intro Y _ i hi hnonsurj
    let : IsClosedImmersion i := hi
    have hdimY := SeshadriAmplenessCriterionClosedMapDimension.closedImmersion_dimension_drop
      i hnonsurj d hdim
    exact hclosed a b ha i hdimY
  -- `f(q) > 0` implies `h(q) ≥ 0` at positive rationals.
  have hHrat : ∀ q : ℚ, 0 < q → 0 < Fpoly.eval (q : ℝ) → 0 ≤ Hpoly.eval (q : ℝ) := by
    intro q hq hFq
    obtain ⟨a, b, ha, hb, hpar⟩ := positive_rat_parameters q hq
    rw [hpar] at hFq ⊢
    have hBamp := hamp a b ha hb hFq
    have hmix := mixedEulerDifference_nef_ample_nonneg d p hdim N hN hnef
      (B a b) hBamp (unitObj X)
    have hproduct : (0 : ℝ) ≤ (b : ℝ) ^ d * Hpoly.eval ((a : ℝ) / (b : ℝ)) :=
      le_of_le_of_eq (by exact_mod_cast hmix) (hscale_cons N hN a b hb).symm
    exact (mul_nonneg_iff_of_pos_left
      (pow_pos (show (0 : ℝ) < b by exact_mod_cast hb) d)).mp hproduct
  -- `g > 0` at positive rationals.
  have hGpos : ∀ q : ℚ, 0 < q → 0 < Gpoly.eval (q : ℝ) := by
    intro q hq
    obtain ⟨a, b, ha, hb, hpar⟩ := positive_rat_parameters q hq
    rw [hpar]
    have hmix := mixedEulerDifference_ample_cons_pos_of_closed_pullback_ample
      p d hdimExact A (B a b) hA (hB a b) (hclosed a b ha)
    have hproduct : (0 : ℝ) < (b : ℝ) ^ d * Gpoly.eval ((a : ℝ) / (b : ℝ)) :=
      lt_of_lt_of_eq (by exact_mod_cast hmix) (hscale_cons A hA.1 a b hb).symm
    exact (mul_pos_iff_of_pos_left
      (pow_pos (show (0 : ℝ) < b by exact_mod_cast hb) d)).mp hproduct
  -- `g' ≥ 0` at positive rationals.
  have hGderiv : ∀ q : ℚ, 0 < q → 0 ≤ Gpoly.derivative.eval (q : ℝ) := by
    intro q hq
    obtain ⟨a, b, ha, hb, hpar⟩ := positive_rat_parameters q hq
    apply mixedPencilPolynomial_derivative_eval_nonneg p N A d [A] (unitObj X) (q : ℝ)
    intro e he
    have hdimE : topologicalKrullDim X ≤ (e + 1 + 1 : ℕ) := by
      rw [← he]
      exact hdim
    have hclosedE : ∀ {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i],
        topologicalKrullDim Y ≤ (e + 1 : ℕ) →
          SchemeLineAmpleness.IsAmple (i ≫ p) ((Scheme.Modules.pullback i).obj (B a b)) := by
      intro Y i _ hY
      exact hclosed a b ha i (by rw [he]; exact hY)
    have hmix := mixedEulerDifference_two_ample_cons_nonneg_of_closed_pullback_ample
      p e hdimE A (B a b) hA (hB a b) hclosedE
    have hInv : ∀ L ∈ [A, A], IsInvertible L := by
      intro L hL
      have hLA : L = A := by simpa using hL
      rw [hLA]
      exact hA.1
    have hs := mixedPencilPolynomial_eval_scale p N A hN hA.1 e [A, A] (d + 1) hdim
      (by simp only [List.length_cons, List.length_nil]; omega) hInv (unitObj X) a b hb
    change (b : ℝ) ^ e *
      (mixedPencilPolynomial p N A e [A, A] (unitObj X)).eval ((a : ℝ) / (b : ℝ)) =
        (mixedEulerDifference p (List.replicate e (B a b) ++ [A, A]) (unitObj X) : ℝ) at hs
    have hperm : (List.replicate e (B a b) ++ [A, A]).Perm
        (A :: A :: List.replicate e (B a b)) := List.perm_append_comm
    rw [mixedEulerDifference_perm p hperm (unitObj X)] at hs
    have hproduct : (0 : ℝ) ≤ (b : ℝ) ^ e *
        (mixedPencilPolynomial p N A e [A, A] (unitObj X)).eval ((a : ℝ) / (b : ℝ)) :=
      le_of_le_of_eq (by exact_mod_cast hmix) hs.symm
    rw [hpar]
    exact (mul_nonneg_iff_of_pos_left
      (pow_pos (show (0 : ℝ) < b by exact_mod_cast hb) e)).mp hproduct
  -- `f` is eventually positive: its leading coefficient is `A^{d+1} > 0`.
  have hApos := mixedEulerDifference_replicate_pos_of_isAmple p (d + 1) hdimExact A hA
  have hcoeff : 0 < Fpoly.coeff (d + 1) := by
    have h := mixedPencilPolynomial_coeff_top p N A (d + 1) [] (unitObj X)
    rw [List.append_nil] at h
    exact lt_of_lt_of_eq (by exact_mod_cast hApos) h.symm
  -- The threshold argument: `f > 0` on `(0, ∞)`.
  have hFall := pencil_pos_of_rational_tests Fpoly Hpoly Gpoly d
    (mixedPencilPolynomial_succ p N A d [] (unitObj X)) hcoeff
    (mixedPencilPolynomial_natDegree_le p N A (d + 1) [] (unitObj X)) hHrat hGpos hGderiv
  have hB11 := hamp 1 1 Nat.one_pos Nat.one_pos
    (by simpa only [Nat.cast_one, div_one] using hFall 1 one_pos)
  exact AmpleTensorLines.ample_of_iso hB11
    (bundleTensorLeftUnitIso N ⊗ᵢ bundleTensorLeftUnitIso A)

/-- **Nef plus ample is ample**, on projective schemes of dimension at most `d`. -/
theorem isAmple_tensor_nef_of_dimension_le
    {k : Type u} [Field k] :
    ∀ d : ℕ, ∀ {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p],
      topologicalKrullDim X ≤ d → ∀ (N A : X.Modules) (hN : IsInvertible N),
      NativeRealNumericalClasses.lineClass p N hN ∈ NativeRealNumericalClasses.nefCone p →
      SchemeLineAmpleness.IsAmple p A → SchemeLineAmpleness.IsAmple p (N ⊗ A) := by
  intro d
  induction d with
  | zero =>
    intro X p _ hdim N A hN hnef hA
    apply strata_tensor_nef_reduction 0 ?_ p hdim N A hN hnef hA
    intro Y _ q _ hdimY M B hM _hnefM hB
    exact SeshadriAmplenessCriterionDimensionZeroAmpleness.isAmple_of_dimension_le_zero
      q (by simpa only [Nat.cast_zero] using hdimY) (M ⊗ B) (tensor_invertible hM hB.1)
  | succ d ih =>
    intro X p _ hdim N A hN hnef hA
    apply strata_tensor_nef_reduction (d + 1) ?_ p hdim N A hN hnef hA
    intro Y _ q _ hdimY M B hM hnefM hB
    exact integral_tensor_nef_step d ih q hdimY M B hM hnefM hB

/-- **Nef plus ample is ample** (Kleiman; Lazarsfeld, *Positivity I*, Corollary 1.4.10).
On a projective scheme `p : X ⟶ Spec k`, if the numerical class of the invertible module `N` is
nef and `A` is ample, then `N ⊗ A` is ample. The scheme may be empty, reducible or nonreduced. -/
theorem isAmple_tensor_nef
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (N A : X.Modules) (hN : IsInvertible N)
    (hnef : NativeRealNumericalClasses.lineClass p N hN ∈
      NativeRealNumericalClasses.nefCone p)
    (hA : SchemeLineAmpleness.IsAmple p A) : SchemeLineAmpleness.IsAmple p (N ⊗ A) := by
  obtain ⟨d, hdim⟩ := NativeProjectiveDimensionBounds.exists_dimension_le_of_isProjective p
  exact isAmple_tensor_nef_of_dimension_le d p hdim N A hN hnef hA

/-- Nef plus ample is ample, with the factors in the other order: `A ⊗ N` is ample. -/
theorem isAmple_ample_tensor_nef
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (N A : X.Modules) (hN : IsInvertible N)
    (hnef : NativeRealNumericalClasses.lineClass p N hN ∈
      NativeRealNumericalClasses.nefCone p)
    (hA : SchemeLineAmpleness.IsAmple p A) : SchemeLineAmpleness.IsAmple p (A ⊗ N) :=
  AmpleTensorLines.ample_of_iso (isAmple_tensor_nef p N A hN hnef hA) (β_ N A)

/-- For a nef `N` and an ample `A`, the line `N^b ⊗ A^a` is ample for every `b` and every
`a > 0`. -/
theorem isAmple_tensorPower_tensor_tensorPower
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (N A : X.Modules) (hN : IsInvertible N)
    (hnef : NativeRealNumericalClasses.lineClass p N hN ∈
      NativeRealNumericalClasses.nefCone p)
    (hA : SchemeLineAmpleness.IsAmple p A) (a b : ℕ) (ha : 0 < a) :
    SchemeLineAmpleness.IsAmple p (bundleTensorPower N b ⊗ bundleTensorPower A a) :=
  isAmple_tensor_nef p (bundleTensorPower N b) (bundleTensorPower A a)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hN b)
    (lineClass_tensorPower_mem_nefCone p N hN hnef b) (positive_power_ample_general p A hA a ha)

/-- For a nef `N` and an ample `A`, the line `N^b ⊗ A` is ample for every `b`. -/
theorem isAmple_tensorPower_tensor
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (N A : X.Modules) (hN : IsInvertible N)
    (hnef : NativeRealNumericalClasses.lineClass p N hN ∈
      NativeRealNumericalClasses.nefCone p)
    (hA : SchemeLineAmpleness.IsAmple p A) (b : ℕ) :
    SchemeLineAmpleness.IsAmple p (bundleTensorPower N b ⊗ A) :=
  isAmple_tensor_nef p (bundleTensorPower N b) A
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hN b)
    (lineClass_tensorPower_mem_nefCone p N hN hnef b) hA

/-- For a nef `N` and an ample `A`, the line `N ⊗ A^a` is ample for every `a > 0`. -/
theorem isAmple_tensor_tensorPower
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (N A : X.Modules) (hN : IsInvertible N)
    (hnef : NativeRealNumericalClasses.lineClass p N hN ∈
      NativeRealNumericalClasses.nefCone p)
    (hA : SchemeLineAmpleness.IsAmple p A) (a : ℕ) (ha : 0 < a) :
    SchemeLineAmpleness.IsAmple p (N ⊗ bundleTensorPower A a) :=
  isAmple_tensor_nef p N (bundleTensorPower A a) hN hnef (positive_power_ample_general p A hA a ha)

/-- Restriction to closed subschemes: for a closed immersion `i : Y ⟶ X`, a nef `N` and an
ample `A` on `X`, the restriction `i^*(N ⊗ A)` is ample over `k`. -/
theorem isAmple_pullback_tensor_nef
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (N A : X.Modules) (hN : IsInvertible N)
    (hnef : NativeRealNumericalClasses.lineClass p N hN ∈
      NativeRealNumericalClasses.nefCone p)
    (hA : SchemeLineAmpleness.IsAmple p A) (i : Y ⟶ X) [IsClosedImmersion i] :
    SchemeLineAmpleness.IsAmple (i ≫ p) ((Scheme.Modules.pullback i).obj (N ⊗ A)) :=
  isAmple_closedPullback i p (N ⊗ A) (isAmple_tensor_nef p N A hN hnef hA)

end EnvelopeProperty.SeshadriAmplenessCriterionNefAmple
