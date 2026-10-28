import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationNativeSupportTrivial
import Mathlib.AlgebraicGeometry.FunctionField
import EnvelopeProperty.Berkovich.SchemeGenericCenterValuations

/-!
# The actual native function field of the original rank-one model

The literal original chart fraction-field theorem uses the explicit model
generation axiom (M3). The genuine native generic germ is retained on every
original homogeneous fraction. No arbitrary graded-subring birationality is
asserted. Complete route: owned audit `native-function-field-route.tex`.
-/

open scoped Classical NNReal Topology
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open EnvelopeProperty.Berkovich

noncomputable section
universe u
namespace EnvelopeProperty.MultiModel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

/-- The original trivial analytic point has the actual generic native support. -/
theorem nativeRankOneSupport_triv_eq_genericPoint :
    X.nativeRankOneSupport X.triv = genericPoint X.nativeRankOneScheme := by
  apply (DeJongAlterations.Geometry.ProjIntegral.isGenericPoint_of_asHomogeneousIdeal_eq_bot
    X.nativeTotalGrading (X.nativeRankOneSupport X.triv) ?_).eq
    (genericPoint_spec X.nativeRankOneScheme)
  apply HomogeneousIdeal.ext
  ext p
  change (X.triv : Berk k X.S).val p = 0 ↔ p = 0
  by_cases hp : p = 0
  · simp [hp]
  · rw [X.triv_val_of_ne_zero hp]
    simp only [one_ne_zero, hp]

/-- The actual trivial residue point at the true native generic point is
the native point of the original support-trivial generic analytic point. -/
theorem nativeRankOnePoint_supportTrivial_triv :
    X.nativeRankOnePoint (X.supportTrivialPoint X.triv) =
      SchemeValuedPoint.trivialAt (genericPoint X.nativeRankOneScheme) := by
  rw [X.nativeRankOnePoint_supportTrivialPoint,
    X.nativeRankOneSupport_triv_eq_genericPoint]

/-- A nonzero original chart coordinate defines a genuinely nonempty native open. -/
theorem nativeRankOneCoordinateOpen_nonempty (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    Nonempty (X.nativeRankOneCoordinateOpen (j 0)) := by
  refine ⟨⟨X.nativeRankOneSupport X.triv,
    (X.nativeRankOneSupport_mem_coordinateOpen X.triv (j 0)).mpr ?_⟩⟩
  rw [X.triv_val_of_ne_zero (X.nativeRankOneCoordinate_ne_zero (j 0) (hj 0))]
  exact one_ne_zero

/-- Every original nonzero coordinate open contains the actual generic point. -/
theorem nativeRankOneGenericPoint_mem_coordinateOpen (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    genericPoint X.nativeRankOneScheme ∈ X.nativeRankOneCoordinateOpen (j 0) := by
  rw [← X.nativeRankOneSupport_triv_eq_genericPoint]
  apply (X.nativeRankOneSupport_mem_coordinateOpen X.triv (j 0)).mpr
  rw [X.triv_val_of_ne_zero (X.nativeRankOneCoordinate_ne_zero (j 0) (hj 0))]
  exact one_ne_zero

/-- The actual generic germ on every original nonzero native coordinate open. -/
def nativeRankOneGenericGerm (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    Γ(X.nativeRankOneScheme, X.nativeRankOneCoordinateOpen (j 0)) →+*
      X.nativeRankOneScheme.functionField := by
  letI := X.nativeRankOneCoordinateOpen_nonempty j hj
  exact (X.nativeRankOneScheme.germToFunctionField _).hom

/-- The SAME original model field is the ACTUAL native generic stalk field.
The existing `isFractionRing_chartAlg` explicitly invokes model axiom (M3). -/
def nativeRankOneFunctionFieldEquiv (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    K ≃+* X.nativeRankOneScheme.functionField := by
  have := X.nativeRankOneCoordinateOpen_nonempty j hj
  have := X.isFractionRing_chartAlg hj
  have := functionField_isFractionRing_of_isAffineOpen X.nativeRankOneScheme
    (X.nativeRankOneCoordinateOpen (j 0)) (X.nativeRankOneCoordinateOpen_isAffine (j 0))
  exact IsFractionRing.ringEquivOfRingEquiv
    (X.nativeRankOneOriginalSectionsIso j hj).commRingCatIsoToRingEquiv

/-- EVERY original chart coefficient has its exact actual native generic germ. -/
theorem nativeRankOneFunctionFieldEquiv_coefficient (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) (a : X.chartAlg j) :
    X.nativeRankOneFunctionFieldEquiv j hj (a : K) =
      X.nativeRankOneGenericGerm j hj ((X.nativeRankOneOriginalSectionsIso j hj).hom a) := by
  have := X.nativeRankOneCoordinateOpen_nonempty j hj
  have := X.isFractionRing_chartAlg hj
  have := functionField_isFractionRing_of_isAffineOpen X.nativeRankOneScheme
    (X.nativeRankOneCoordinateOpen (j 0)) (X.nativeRankOneCoordinateOpen_isAffine (j 0))
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (X.nativeRankOneOriginalSectionsIso j hj).commRingCatIsoToRingEquiv a

/-- EVERY actual local section is sent back to its literal original coefficient. -/
theorem nativeRankOneFunctionFieldEquiv_symm_germ (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0)
    (s : Γ(X.nativeRankOneScheme, X.nativeRankOneCoordinateOpen (j 0))) :
    (X.nativeRankOneFunctionFieldEquiv j hj).symm (X.nativeRankOneGenericGerm j hj s) =
      ((X.nativeRankOneOriginalSectionsIso j hj).inv s : X.chartAlg j) := by
  apply (X.nativeRankOneFunctionFieldEquiv j hj).injective
  rw [RingEquiv.apply_symm_apply, X.nativeRankOneFunctionFieldEquiv_coefficient]
  exact congrArg (X.nativeRankOneGenericGerm j hj)
    ((X.nativeRankOneOriginalSectionsIso j hj).inv_hom_id_apply s).symm

/-- The actual native section of an ORIGINAL homogeneous coefficient in its
original coordinate frame; this is a genuine structure-sheaf section. -/
def nativeRankOneOriginalHomogeneousSection (j : X.ChartIndex)
    {a : Fin 1 →₀ ℕ} {f : K} (hf : f ∈ X.piece a) :
    Γ(X.nativeRankOneScheme, X.nativeRankOneCoordinateOpen (j 0)) :=
  (X.nativeRankOneHomogeneousSectionsIso (j 0)).hom
    (HomogeneousLocalization.Away.mk X.nativeTotalGrading
      (X.nativeRankOneCoordinate_mem (j 0)) a.degree (X.ofPiece hf)
      (by change (monomial a f).IsHomogeneous (a.degree • (1 : ℕ))
          exact MvPolynomial.isHomogeneous_monomial f (by simp)))

/-- The genuine native section is exactly the original dehomogenized coefficient. -/
theorem nativeRankOneOriginalHomogeneousSection_eq (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) {a : Fin 1 →₀ ℕ} {f : K}
    (hf : f ∈ X.piece a) :
    X.nativeRankOneOriginalHomogeneousSection j hf =
      (X.nativeRankOneOriginalSectionsIso j hj).hom
        ⟨f / X.chartDen j a, X.div_chartDen_mem_chartAlg hf⟩ := by
  have he : X.nativeRankOneChartEquiv j hj
      (HomogeneousLocalization.Away.mk X.nativeTotalGrading
        (X.nativeRankOneCoordinate_mem (j 0)) a.degree (X.ofPiece hf)
        (by change (monomial a f).IsHomogeneous (a.degree • (1 : ℕ))
            exact MvPolynomial.isHomogeneous_monomial f (by simp))) =
      ⟨f / X.chartDen j a, X.div_chartDen_mem_chartAlg hf⟩ := by
    change X.nativeRankOneChartDehom j hj _ = _
    rw [X.nativeRankOneChartDehom_mk j hj]
    exact Subtype.ext (X.dehom_monomial j a f)
  change (X.nativeRankOneHomogeneousSectionsIso (j 0)).hom _ =
    (X.nativeRankOneHomogeneousSectionsIso (j 0)).hom
      ((X.nativeRankOneChartEquiv j hj).symm _)
  apply congrArg (X.nativeRankOneHomogeneousSectionsIso (j 0)).hom
  exact ((X.nativeRankOneChartEquiv j hj).eq_symm_apply).mpr he

/-- The field comparison retains the actual generic germ of EVERY original
homogeneous coefficient in the original coordinate frame. -/
theorem nativeRankOneFunctionFieldEquiv_homogeneous (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) {a : Fin 1 →₀ ℕ} {f : K}
    (hf : f ∈ X.piece a) :
    X.nativeRankOneFunctionFieldEquiv j hj (f / X.chartDen j a) =
      X.nativeRankOneGenericGerm j hj (X.nativeRankOneOriginalHomogeneousSection j hf) := by
  rw [X.nativeRankOneOriginalHomogeneousSection_eq j hj hf]
  exact X.nativeRankOneFunctionFieldEquiv_coefficient j hj
    ⟨f / X.chartDen j a, X.div_chartDen_mem_chartAlg hf⟩

/-- SAME-degree original homogeneous ratios retain their literal actual
generic-germ quotient, a prerequisite for the genuine H0 comparison. -/
theorem nativeRankOneFunctionFieldEquiv_homogeneous_ratio (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) {a : Fin 1 →₀ ℕ} {f g : K}
    (hf : f ∈ X.piece a) (hg : g ∈ X.piece a) :
    X.nativeRankOneFunctionFieldEquiv j hj (f / g) =
      X.nativeRankOneGenericGerm j hj (X.nativeRankOneOriginalHomogeneousSection j hf) /
        X.nativeRankOneGenericGerm j hj (X.nativeRankOneOriginalHomogeneousSection j hg) := by
  rw [← X.nativeRankOneFunctionFieldEquiv_homogeneous j hj hf,
    ← X.nativeRankOneFunctionFieldEquiv_homogeneous j hj hg, ← map_div₀]
  exact congrArg (X.nativeRankOneFunctionFieldEquiv j hj)
    (div_div_div_cancel_right₀ (X.chartDen_ne_zero hj a) f g).symm

/-- The genuine Proj stalk map retains the ENTIRE original homogeneous
fraction, through its actual map between homogeneous localizations. -/
theorem nativeRankOneGenericGerm_homogeneous_stalk (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) {a : Fin 1 →₀ ℕ} {f : K}
    (hf : f ∈ X.piece a) :
    Proj.stalkIso' X.nativeTotalGrading (genericPoint X.nativeRankOneScheme)
        (X.nativeRankOneGenericGerm j hj (X.nativeRankOneOriginalHomogeneousSection j hf)) =
      HomogeneousLocalization.mapId X.nativeTotalGrading
        (Submonoid.powers_le.mpr (X.nativeRankOneGenericPoint_mem_coordinateOpen j hj))
        (HomogeneousLocalization.Away.mk X.nativeTotalGrading
          (X.nativeRankOneCoordinate_mem (j 0)) a.degree (X.ofPiece hf)
          (by change (monomial a f).IsHomogeneous (a.degree • (1 : ℕ))
              exact MvPolynomial.isHomogeneous_monomial f (by simp))) := by
  change Proj.stalkIso' X.nativeTotalGrading (genericPoint X.nativeRankOneScheme)
    (X.nativeRankOneScheme.presheaf.germ _ _
      (X.nativeRankOneGenericPoint_mem_coordinateOpen j hj)
      (X.nativeRankOneOriginalHomogeneousSection j hf)) = _
  erw [Proj.stalkIso'_germ]
  rfl

private theorem nativeRankOneGenericGerm_homogeneous_cross
    (j l : X.ChartIndex) (hj : ∀ c, X.coord c (j c) ≠ 0)
    (hl : ∀ c, X.coord c (l c) ≠ 0) {a : Fin 1 →₀ ℕ} {f g : K}
    (hf : f ∈ X.piece a) (hg : g ∈ X.piece a) :
    X.nativeRankOneGenericGerm j hj (X.nativeRankOneOriginalHomogeneousSection j hf) *
        X.nativeRankOneGenericGerm l hl (X.nativeRankOneOriginalHomogeneousSection l hg) =
      X.nativeRankOneGenericGerm l hl (X.nativeRankOneOriginalHomogeneousSection l hf) *
        X.nativeRankOneGenericGerm j hj (X.nativeRankOneOriginalHomogeneousSection j hg) := by
  apply (Proj.stalkIso' X.nativeTotalGrading (genericPoint X.nativeRankOneScheme)).injective
  erw [map_mul, map_mul, X.nativeRankOneGenericGerm_homogeneous_stalk,
    X.nativeRankOneGenericGerm_homogeneous_stalk, X.nativeRankOneGenericGerm_homogeneous_stalk,
    X.nativeRankOneGenericGerm_homogeneous_stalk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mul]
  change Localization.mk (X.ofPiece hf) _ * Localization.mk (X.ofPiece hg) _ =
    Localization.mk (X.ofPiece hf) _ * Localization.mk (X.ofPiece hg) _
  erw [Localization.mk_mul, Localization.mk_mul]
  congr 1
  exact Subtype.ext (mul_comm _ _)

/-- A nonzero original homogeneous coefficient has nonzero genuine generic germ. -/
theorem nativeRankOneGenericGerm_homogeneous_ne_zero (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) {a : Fin 1 →₀ ℕ} {g : K}
    (hg : g ∈ X.piece a) (hg0 : g ≠ 0) :
    X.nativeRankOneGenericGerm j hj (X.nativeRankOneOriginalHomogeneousSection j hg) ≠ 0 := by
  rw [← X.nativeRankOneFunctionFieldEquiv_homogeneous j hj hg]
  intro hz
  exact (div_ne_zero hg0 (X.chartDen_ne_zero hj a))
    ((X.nativeRankOneFunctionFieldEquiv j hj).injective
      (hz.trans (map_zero (X.nativeRankOneFunctionFieldEquiv j hj)).symm))

/-- The original-model / ACTUAL native generic-field equivalence is
independent of the original nonzero coordinate chart. -/
theorem nativeRankOneFunctionFieldEquiv_independent
    (j l : X.ChartIndex) (hj : ∀ c, X.coord c (j c) ≠ 0)
    (hl : ∀ c, X.coord c (l c) ≠ 0) :
    X.nativeRankOneFunctionFieldEquiv j hj = X.nativeRankOneFunctionFieldEquiv l hl := by
  apply RingEquiv.ext
  intro z
  obtain ⟨a, f, g, hf, hg, hg0, rfl⟩ := X.exists_eq_div z
  rw [X.nativeRankOneFunctionFieldEquiv_homogeneous_ratio j hj hf hg,
    X.nativeRankOneFunctionFieldEquiv_homogeneous_ratio l hl hf hg]
  apply (div_eq_div_iff (X.nativeRankOneGenericGerm_homogeneous_ne_zero j hj hg hg0)
    (X.nativeRankOneGenericGerm_homogeneous_ne_zero l hl hg hg0)).mpr
  exact X.nativeRankOneGenericGerm_homogeneous_cross j l hj hl hf hg

/-- Generic support of the ORIGINAL seminorm gives the actual native
generic point, through equality of the whole original homogeneous kernel. -/
theorem nativeRankOneSupport_eq_genericPoint (x : X.an)
    (hx : X.HasGenericSupport x.1) :
    X.nativeRankOneSupport x = genericPoint X.nativeRankOneScheme := by
  apply (DeJongAlterations.Geometry.ProjIntegral.isGenericPoint_of_asHomogeneousIdeal_eq_bot
    X.nativeTotalGrading (X.nativeRankOneSupport x) ?_).eq
    (genericPoint_spec X.nativeRankOneScheme)
  apply HomogeneousIdeal.ext
  ext p
  change x.1.val p = 0 ↔ p = 0
  constructor
  · intro hp
    by_contra hne
    exact hx p hne hp
  · rintro rfl
    exact map_zero _

/-- The actual native WHOLE function-field valuation has the exact original
homogeneous fraction value at EVERY original generic-support point. -/
theorem nativeRankOneGenericValuation_homogeneous (x : X.an)
    (hx : X.HasGenericSupport x.1) (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) {a : Fin 1 →₀ ℕ} {f : K}
    (hf : f ∈ X.piece a) :
    SchemeValuedPoint.genericValuation (X.nativeRankOnePoint x)
        (X.nativeRankOneSupport_eq_genericPoint x hx)
        (X.nativeRankOneGenericGerm j hj (X.nativeRankOneOriginalHomogeneousSection j hf)) =
      x.1.val (X.ofPiece hf) / x.1.val (X.coordElem ⟨0, j 0⟩) ^ a.degree := by
  have := X.nativeRankOneCoordinateOpen_nonempty j hj
  have hxU : (X.nativeRankOnePoint x).point ∈ X.nativeRankOneCoordinateOpen (j 0) := by
    change X.nativeRankOneSupport x ∈ _
    rw [X.nativeRankOneSupport_eq_genericPoint x hx]
    exact X.nativeRankOneGenericPoint_mem_coordinateOpen j hj
  change SchemeValuedPoint.genericValuation _ _
    (X.nativeRankOneScheme.germToFunctionField _
      (X.nativeRankOneOriginalHomogeneousSection j hf)) = _
  rw [SchemeValuedPoint.genericValuation_eval _ _ _ hxU]
  exact X.nativeRankOnePoint_eval_mk x (j 0) hxU a.degree (X.ofPiece hf)
    (by change (monomial a f).IsHomogeneous (a.degree • (1 : ℕ))
        exact MvPolynomial.isHomogeneous_monomial f (by simp))

/-- The ENTIRE original model field valuation is the SAME actual native
generic-point function-field valuation, through the genuine original field
equivalence; no valuation-matching certificate is supplied. -/
theorem nativeRankOneGenericValuation_comap_eq_fieldVal (x : X.an)
    (hx : X.HasGenericSupport x.1) (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    (SchemeValuedPoint.genericValuation (X.nativeRankOnePoint x)
      (X.nativeRankOneSupport_eq_genericPoint x hx)).comap
        (X.nativeRankOneFunctionFieldEquiv j hj).toRingHom = X.fieldVal x hx := by
  apply Valuation.ext
  intro z
  obtain ⟨a, f, g, hf, hg, _, rfl⟩ := X.exists_eq_div z
  erw [Valuation.comap_apply,
    X.nativeRankOneFunctionFieldEquiv_homogeneous_ratio j hj hf hg,
    map_div₀, X.nativeRankOneGenericValuation_homogeneous x hx j hj hf,
    X.nativeRankOneGenericValuation_homogeneous x hx j hj hg, X.fieldVal_div x hx hf hg]
  exact div_div_div_cancel_right₀
    (pow_ne_zero a.degree (hx _ (X.nativeRankOneCoordinate_ne_zero (j 0) (hj 0)))) _ _

end EnvelopeProperty.MultiModel

#check @EnvelopeProperty.MultiModel.nativeRankOneSupport_triv_eq_genericPoint
#check @EnvelopeProperty.MultiModel.nativeRankOnePoint_supportTrivial_triv
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinateOpen_nonempty
#check @EnvelopeProperty.MultiModel.nativeRankOneGenericGerm
#check @EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldEquiv
#check @EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldEquiv_coefficient
#check @EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldEquiv_symm_germ
#check @EnvelopeProperty.MultiModel.nativeRankOneOriginalHomogeneousSection
#check @EnvelopeProperty.MultiModel.nativeRankOneOriginalHomogeneousSection_eq
#check @EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldEquiv_homogeneous
#check @EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldEquiv_homogeneous_ratio
#check @EnvelopeProperty.MultiModel.nativeRankOneGenericPoint_mem_coordinateOpen
#check @EnvelopeProperty.MultiModel.nativeRankOneGenericGerm_homogeneous_stalk
#check @EnvelopeProperty.MultiModel.nativeRankOneGenericGerm_homogeneous_ne_zero
#check @EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldEquiv_independent
#check @EnvelopeProperty.MultiModel.nativeRankOneSupport_eq_genericPoint
#check @EnvelopeProperty.MultiModel.nativeRankOneGenericValuation_homogeneous
#check @EnvelopeProperty.MultiModel.nativeRankOneGenericValuation_comap_eq_fieldVal
#print axioms EnvelopeProperty.MultiModel.nativeRankOneSupport_triv_eq_genericPoint
#print axioms EnvelopeProperty.MultiModel.nativeRankOnePoint_supportTrivial_triv
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinateOpen_nonempty
#print axioms EnvelopeProperty.MultiModel.nativeRankOneGenericGerm
#print axioms EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldEquiv
#print axioms EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldEquiv_coefficient
#print axioms EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldEquiv_symm_germ
#print axioms EnvelopeProperty.MultiModel.nativeRankOneOriginalHomogeneousSection
#print axioms EnvelopeProperty.MultiModel.nativeRankOneOriginalHomogeneousSection_eq
#print axioms EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldEquiv_homogeneous
#print axioms EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldEquiv_homogeneous_ratio
#print axioms EnvelopeProperty.MultiModel.nativeRankOneGenericPoint_mem_coordinateOpen
#print axioms EnvelopeProperty.MultiModel.nativeRankOneGenericGerm_homogeneous_stalk
#print axioms EnvelopeProperty.MultiModel.nativeRankOneGenericGerm_homogeneous_ne_zero
#print axioms EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldEquiv_independent
#print axioms EnvelopeProperty.MultiModel.nativeRankOneSupport_eq_genericPoint
#print axioms EnvelopeProperty.MultiModel.nativeRankOneGenericValuation_homogeneous
#print axioms EnvelopeProperty.MultiModel.nativeRankOneGenericValuation_comap_eq_fieldVal
