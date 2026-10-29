import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionPrimeFiltration
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionEulerPolynomialBase
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionPolynomialSummation
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorFiniteType
import EnvelopeProperty.AlgGeom.NativeProjectiveDimensionBounds
import EnvelopeProperty.Projective.TestConfigurationSectionTransport

/-!
# Seshadri Ampleness Criterion Euler Polynomial

The actual Euler polynomial on general original projective schemes. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace
open Polynomial
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion
open SchemeCoherentEulerCharacteristic
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private theorem isProjective_closedComp_euler {Z X Y : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (p : X ⟶ Y) [IsProjective p] :
    IsProjective (i ≫ p) := by
  constructor
  obtain ⟨E, hE, hEF, j, hj, hjp⟩ := IsProjective.exists_isClosedImmersion (f := p)
  let : IsClosedImmersion j := hj
  refine ⟨E, hE, hEF, i ≫ j, inferInstance, ?_⟩
  exact (Category.assoc i j E.projectiveBundleπ).trans
    (congrArg (fun q => i ≫ q) hjp)

private theorem integralEulerPolynomial_zero
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) [IsProjective f]
    (hdim : topologicalKrullDim X ≤ 0)
    (T : X.Modules) (hT : IsInvertible T) (L : X.Modules) (hL : IsInvertible L) :
    ∃ q : ℚ[X], q.natDegree ≤ 0 ∧ ∀ n : ℕ,
      q.eval (n : ℚ) = (eulerCharacteristic f (T ⊗ CanonicalGeometry.bundleTensorPower L n) : ℚ) := by
  let hf := ProjectiveFactorizationRingIso.of_isProjective f
  refine ⟨C (eulerCharacteristic f (T ⊗ CanonicalGeometry.bundleTensorPower L 0) : ℚ),
    by simp, ?_⟩
  intro n
  rw [eval_C]
  apply congrArg (fun z : ℤ => (z : ℚ))
  induction n with
  | zero => rfl
  | succ n ih =>
    let P := CanonicalGeometry.bundleTensorPower L n
    let hP : IsInvertible P := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n
    let hTP : IsInvertible (T ⊗ P) :=
      (hT.tensorObj hP).of_iso (ModularCurves.monoidalTensorObjIso T P)
    let e : L ⊗ (T ⊗ P) ≅ T ⊗ CanonicalGeometry.bundleTensorPower L (n + 1) :=
      β_ L (T ⊗ P) ≪≫ α_ T P L ≪≫
        (Iso.refl T ⊗ᵢ ModularCurves.monoidalTensorObjIso P L)
    have h : eulerCharacteristic f (T ⊗ CanonicalGeometry.bundleTensorPower L (n + 1)) =
        eulerCharacteristic f (T ⊗ P) :=
      (eulerCharacteristic_eq_of_iso f e).symm.trans
        (eulerCharacteristic_tensor_eq_of_dimension_le_zero f hf hdim L (T ⊗ P) hL hTP)
    exact ih.trans h.symm

-- Propagation of the genuine integral-line dimensional induction hypothesis.
private theorem coherentEulerPolynomial_of_integralLines
    {k : Type u} [Field k] (d : ℕ)
    (H : ∀ {Z : Scheme.{u}} [IsIntegral Z] [CompactSpace Z] [Z.IsSeparated]
      (g : Z ⟶ Spec (.of k)) [IsProjective g] (_ : topologicalKrullDim Z ≤ d)
      (T : Z.Modules) (_ : IsInvertible T) (L : Z.Modules) (_ : IsInvertible L),
      ∃ q : ℚ[X], q.natDegree ≤ d ∧ ∀ n : ℕ,
        q.eval (n : ℚ) = (eulerCharacteristic g (T ⊗ CanonicalGeometry.bundleTensorPower L n) : ℚ))
    {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) [IsProjective f] (hdim : topologicalKrullDim X ≤ d)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (L : X.Modules) (hL : IsInvertible L) :
    ∃ q : ℚ[X], q.natDegree ≤ d ∧ ∀ n : ℕ,
      q.eval (n : ℚ) = (eulerCharacteristic f (F ⊗ CanonicalGeometry.bundleTensorPower L n) : ℚ) := by
  let hf := ProjectiveFactorizationRingIso.of_isProjective f
  obtain ⟨m, hfil⟩ := exists_finite_coherent_primeFiltration f F
  induction hfil with
  | zero M hM =>
    refine ⟨0, by simp, fun n => ?_⟩
    let P := CanonicalGeometry.bundleTensorPower L n
    let hP := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n
    let : (tensorRight P).IsEquivalence :=
      SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence P hP
    have hz : IsZero (M ⊗ P) := (tensorRight P).map_isZero hM
    have hchi := eulerCharacteristic_eq_zero_of_isZero f (M ⊗ P) hz
    rw [Polynomial.eval_zero]
    change (0 : ℚ) = (eulerCharacteristic f (M ⊗ P) : ℚ)
    rw [hchi]
    rfl
  | iso e _ ih =>
    obtain ⟨q, hdeg, hq⟩ := ih
    refine ⟨q, hdeg, fun n => ?_⟩
    exact (hq n).trans (congrArg (fun z : ℤ => (z : ℚ))
      (eulerCharacteristic_eq_of_iso f (e ⊗ᵢ Iso.refl (CanonicalGeometry.bundleTensorPower L n))))
  | extension S hS hQ₁ hQ₂ hQ₃ hF₁ hF₂ hF₃ eta T hT e _ ih =>
    let : S.X₁.IsQuasicoherent := hQ₁
    let : S.X₂.IsQuasicoherent := hQ₂
    let : S.X₃.IsQuasicoherent := hQ₃
    let : S.X₁.IsFiniteType := hF₁
    let : S.X₂.IsFiniteType := hF₂
    let : S.X₃.IsFiniteType := hF₃
    let I := Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
    let Z := I.subscheme
    let i : Z ⟶ X := I.subschemeι
    let : IsIntegral Z := SchemePointClosureIntegral.isIntegral_pointClosure eta
    let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
    let : Z.IsSeparated := ⟨by
      have h : IsSeparated (i ≫ terminal.from X) := inferInstance
      simpa only [terminal.comp_from] using h⟩
    let : IsProjective (i ≫ f) := isProjective_closedComp_euler i f
    have hdimZ : topologicalKrullDim Z ≤ d :=
      IntegralSchemeDimension.topologicalKrullDim_le_of_isIntegralHom i d hdim
    let K := (Scheme.Modules.pullback i).obj L
    let hK : IsInvertible K := hL.pullback i
    obtain ⟨q₃, hd₃, hq₃⟩ := H (i ≫ f) hdimZ T hT K hK
    obtain ⟨q₁, hd₁, hq₁⟩ := ih
    refine ⟨q₁ + q₃, natDegree_add_le_of_degree_le hd₁ hd₃, fun n => ?_⟩
    let P := CanonicalGeometry.bundleTensorPower L n
    let hP : IsInvertible P := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n
    let : (S.X₁ ⊗ P).IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight S.X₁ P hP
    let : (S.X₂ ⊗ P).IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight S.X₂ P hP
    let : (S.X₃ ⊗ P).IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight S.X₃ P hP
    let : (S.X₁ ⊗ P).IsFiniteType :=
      SchemeInvertibleTensorFiniteType.isFiniteType_tensorRight S.X₁ P hP
    let : (S.X₂ ⊗ P).IsFiniteType :=
      SchemeInvertibleTensorFiniteType.isFiniteType_tensorRight S.X₂ P hP
    let : (S.X₃ ⊗ P).IsFiniteType :=
      SchemeInvertibleTensorFiniteType.isFiniteType_tensorRight S.X₃ P hP
    let : (tensorRight P).IsEquivalence :=
      SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence P hP
    let SP := S.map (tensorRight P)
    have hSP : SP.ShortExact :=
      SchemeInvertibleTensorEquivalence.tensorRight_shortExact P hP S hS
    let : SP.X₁.IsQuasicoherent := by
      change (S.X₁ ⊗ P).IsQuasicoherent
      infer_instance
    let : SP.X₁.IsFiniteType := by
      change (S.X₁ ⊗ P).IsFiniteType
      infer_instance
    let : SP.X₂.IsQuasicoherent := by
      change (S.X₂ ⊗ P).IsQuasicoherent
      infer_instance
    let : SP.X₂.IsFiniteType := by
      change (S.X₂ ⊗ P).IsFiniteType
      infer_instance
    let : SP.X₃.IsQuasicoherent := by
      change (S.X₃ ⊗ P).IsQuasicoherent
      infer_instance
    let : SP.X₃.IsFiniteType := by
      change (S.X₃ ⊗ P).IsFiniteType
      infer_instance
    have hEuler := eulerCharacteristic_add f hf SP hSP
    let e₁ : S.X₃ ⊗ P ≅ (Scheme.Modules.pushforward i).obj
        (T ⊗ (Scheme.Modules.pullback i).obj P) :=
      (e ⊗ᵢ Iso.refl P) ≪≫ SchemeLineProjectionFormula.lineProjectionFormulaObj i P hP T
    let e₂ : T ⊗ (Scheme.Modules.pullback i).obj P ≅
        T ⊗ CanonicalGeometry.bundleTensorPower K n :=
      Iso.refl T ⊗ᵢ TestConfigurationSectionTransport.tensorPowerPullbackIso i L n
    let hTP : IsInvertible (T ⊗ (Scheme.Modules.pullback i).obj P) :=
      (hT.tensorObj (hP.pullback i)).of_iso
        (ModularCurves.monoidalTensorObjIso T ((Scheme.Modules.pullback i).obj P))
    let : (T ⊗ (Scheme.Modules.pullback i).obj P).IsQuasicoherent := hTP.isQuasicoherent
    have hchi₃ : eulerCharacteristic f (S.X₃ ⊗ P) =
        eulerCharacteristic (i ≫ f) (T ⊗ CanonicalGeometry.bundleTensorPower K n) :=
      (eulerCharacteristic_eq_of_iso f e₁).trans
        ((SchemeCoherentEulerAffine.eulerCharacteristic_pushforward i f _).symm.trans
          (eulerCharacteristic_eq_of_iso (i ≫ f) e₂))
    rw [eval_add, hq₁ n, hq₃ n, ← hchi₃]
    exact_mod_cast hEuler.symm

-- The lower-dimensional general statement is discharged in the final induction.
private theorem integralEulerPolynomial_succ
    {k : Type u} [Field k] (d : ℕ)
    (H : ∀ {Z : Scheme.{u}} [CompactSpace Z] [Z.IsSeparated]
      (g : Z ⟶ Spec (.of k)) [IsProjective g] (_ : topologicalKrullDim Z ≤ d)
      (F : Z.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (K : Z.Modules) (_ : IsInvertible K),
      ∃ q : ℚ[X], q.natDegree ≤ d ∧ ∀ n : ℕ,
        q.eval (n : ℚ) = (eulerCharacteristic g (F ⊗ CanonicalGeometry.bundleTensorPower K n) : ℚ))
    {X : Scheme.{u}} [IsIntegral X] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) [IsProjective f] (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ))
    (T : X.Modules) (hT : IsInvertible T) (L : X.Modules) (hL : IsInvertible L) :
    ∃ q : ℚ[X], q.natDegree ≤ d + 1 ∧ ∀ n : ℕ,
      q.eval (n : ℚ) = (eulerCharacteristic f (T ⊗ CanonicalGeometry.bundleTensorPower L n) : ℚ) := by
  let hf := ProjectiveFactorizationRingIso.of_isProjective f
  obtain ⟨B, hB, a, b, ha, hb, _⟩ :=
    exists_eulerCharacteristic_powerCartierDifference f hf L hL
  let hA : IsInvertible (L ⊗ B) :=
    (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
  let I := LineSectionZeroIdeal.zeroIdeal (L ⊗ B) hA a
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
  let : IsProjective (i ≫ f) := isProjective_closedComp_euler i f
  let : IsProjective (j ≫ f) := isProjective_closedComp_euler j f
  have hdimI : topologicalKrullDim I.subscheme ≤ d :=
    sectionZero_dimension_drop d hdim (L ⊗ B) hA a ha
  have hdimJ : topologicalKrullDim J.subscheme ≤ d :=
    sectionZero_dimension_drop d hdim B hB b hb
  let Fi := Scheme.Modules.pullback i
  let Fj := Scheme.Modules.pullback j
  let : Fi.Monoidal := Scheme.Modules.pullbackMonoidal i
  let : Fj.Monoidal := Scheme.Modules.pullbackMonoidal j
  let TI := Fi.obj (L ⊗ T)
  let TJ := Fj.obj T
  let LI := Fi.obj L
  let LJ := Fj.obj L
  let hLT : IsInvertible (L ⊗ T) :=
    (hL.tensorObj hT).of_iso (ModularCurves.monoidalTensorObjIso L T)
  let hTI : IsInvertible TI := hLT.pullback i
  let hTJ : IsInvertible TJ := hT.pullback j
  let : TI.IsFinitePresentation := hTI.isFinitePresentation
  let : TJ.IsFinitePresentation := hTJ.isFinitePresentation
  let : TI.IsQuasicoherent := hTI.isQuasicoherent
  let : TJ.IsQuasicoherent := hTJ.isQuasicoherent
  let : TI.IsFiniteType := by
    obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData TI
    apply SheafOfModules.IsFiniteType.mk (R := I.subscheme.ringCatSheaf)
    refine ⟨q.localGeneratorsData, ?_⟩
    constructor
    intro t
    change (q.presentation t).generators.IsFiniteType
    exact (hq.isFinite_presentation t).isFiniteType_generators
  let : TJ.IsFiniteType := by
    obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData TJ
    apply SheafOfModules.IsFiniteType.mk (R := J.subscheme.ringCatSheaf)
    refine ⟨q.localGeneratorsData, ?_⟩
    constructor
    intro t
    change (q.presentation t).generators.IsFiniteType
    exact (hq.isFinite_presentation t).isFiniteType_generators
  obtain ⟨qI, hdI, hqI⟩ := H (i ≫ f) hdimI TI LI (hL.pullback i)
  obtain ⟨qJ, hdJ, hqJ⟩ := H (j ≫ f) hdimJ TJ LJ (hL.pullback j)
  let seq : ℕ → ℚ := fun n =>
    (eulerCharacteristic f (T ⊗ CanonicalGeometry.bundleTensorPower L n) : ℚ)
  apply exists_polynomial_of_polynomial_difference seq (qI - qJ) d
    ((natDegree_sub_le_iff_left hdJ).mpr hdI)
  intro n
  let P := CanonicalGeometry.bundleTensorPower L n
  let hP : IsInvertible P := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n
  let hTP : IsInvertible (T ⊗ P) :=
    (hT.tensorObj hP).of_iso (ModularCurves.monoidalTensorObjIso T P)
  let e : L ⊗ (T ⊗ P) ≅ T ⊗ CanonicalGeometry.bundleTensorPower L (n + 1) :=
    β_ L (T ⊗ P) ≪≫ α_ T P L ≪≫
      (Iso.refl T ⊗ᵢ ModularCurves.monoidalTensorObjIso P L)
  let eI : Fi.obj (L ⊗ (T ⊗ P)) ≅ TI ⊗ CanonicalGeometry.bundleTensorPower LI n :=
    Fi.mapIso (α_ L T P).symm ≪≫
      (Functor.Monoidal.μIso Fi (L ⊗ T) P).symm ≪≫
      (Iso.refl TI ⊗ᵢ TestConfigurationSectionTransport.tensorPowerPullbackIso i L n)
  let eJ : Fj.obj (T ⊗ P) ≅ TJ ⊗ CanonicalGeometry.bundleTensorPower LJ n :=
    (Functor.Monoidal.μIso Fj T P).symm ≪≫
      (Iso.refl TJ ⊗ᵢ TestConfigurationSectionTransport.tensorPowerPullbackIso j L n)
  have h := eulerCharacteristic_cartierDifference f hf L B (T ⊗ P) hL hB hTP a ha b hb
  change eulerCharacteristic f (L ⊗ (T ⊗ P)) - eulerCharacteristic f (T ⊗ P) =
    eulerCharacteristic (i ≫ f) (Fi.obj (L ⊗ (T ⊗ P))) -
      eulerCharacteristic (j ≫ f) (Fj.obj (T ⊗ P)) at h
  rw [eulerCharacteristic_eq_of_iso f e,
    eulerCharacteristic_eq_of_iso (i ≫ f) eI,
    eulerCharacteristic_eq_of_iso (j ≫ f) eJ] at h
  rw [eval_sub, hqI n, hqJ n]
  change (eulerCharacteristic f (T ⊗ CanonicalGeometry.bundleTensorPower L (n + 1)) : ℚ) -
      (eulerCharacteristic f (T ⊗ P) : ℚ) =
    (eulerCharacteristic (i ≫ f) (TI ⊗ CanonicalGeometry.bundleTensorPower LI n) : ℚ) -
      (eulerCharacteristic (j ≫ f) (TJ ⊗ CanonicalGeometry.bundleTensorPower LJ n) : ℚ)
  exact_mod_cast h

-- Simultaneous dimensional induction; no hypothesis is a public premise.
theorem exists_eulerPolynomial_of_dimension_le
    {k : Type u} [Field k] (d : ℕ)
    {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) [IsProjective f] (hdim : topologicalKrullDim X ≤ d)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (L : X.Modules) (hL : IsInvertible L) :
    ∃ q : ℚ[X], q.natDegree ≤ d ∧ ∀ n : ℕ,
      q.eval (n : ℚ) = (eulerCharacteristic f (F ⊗ CanonicalGeometry.bundleTensorPower L n) : ℚ) := by
  have all : ∀ d : ℕ, ∀ {Y : Scheme.{u}} [CompactSpace Y] [Y.IsSeparated]
      (g : Y ⟶ Spec (.of k)) [IsProjective g] (hdimY : topologicalKrullDim Y ≤ d)
      (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
      (K : Y.Modules) (hK : IsInvertible K),
      ∃ q : ℚ[X], q.natDegree ≤ d ∧ ∀ n : ℕ,
        q.eval (n : ℚ) = (eulerCharacteristic g (M ⊗ CanonicalGeometry.bundleTensorPower K n) : ℚ) := by
    intro d
    induction d with
    | zero =>
      intro Y _ _ g _ hdimY M _ _ K hK
      refine coherentEulerPolynomial_of_integralLines 0 ?_ g hdimY M K hK
      intro Z _ _ _ p _ hdimZ T hT A hA
      exact integralEulerPolynomial_zero p hdimZ T hT A hA
    | succ d ih =>
      intro Y _ _ g _ hdimY M _ _ K hK
      refine coherentEulerPolynomial_of_integralLines (d + 1) ?_ g hdimY M K hK
      intro Z _ _ _ p _ hdimZ T hT A hA
      exact integralEulerPolynomial_succ d ih p hdimZ T hT A hA
  exact all d f hdim F L hL

/-- Native projectivity internally supplies the finite whole dimension bound;
the same original coherent coefficient and original line have an actual Euler polynomial. -/
theorem exists_eulerPolynomial
    {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) [IsProjective f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (L : X.Modules) (hL : IsInvertible L) :
    ∃ q : ℚ[X], ∀ n : ℕ,
      q.eval (n : ℚ) = (eulerCharacteristic f (F ⊗ CanonicalGeometry.bundleTensorPower L n) : ℚ) := by
  obtain ⟨d, hdim⟩ := NativeProjectiveDimensionBounds.exists_dimension_le_of_isProjective f
  obtain ⟨q, _, hq⟩ := exists_eulerPolynomial_of_dimension_le d f hdim F L hL
  exact ⟨q, hq⟩

#check @integralEulerPolynomial_succ
#print axioms integralEulerPolynomial_succ
#check @exists_eulerPolynomial_of_dimension_le
#print axioms exists_eulerPolynomial_of_dimension_le
#check @exists_eulerPolynomial
#print axioms exists_eulerPolynomial
#check @coherentEulerPolynomial_of_integralLines
#print axioms coherentEulerPolynomial_of_integralLines
#check @integralEulerPolynomial_zero
#print axioms integralEulerPolynomial_zero
#check @SchemeInvertibleTensorFiniteType.isFiniteType_tensorRight
#print axioms SchemeInvertibleTensorFiniteType.isFiniteType_tensorRight
#check @TestConfigurationSectionTransport.tensorPowerPullbackIso
#print axioms TestConfigurationSectionTransport.tensorPowerPullbackIso
#check @NativeProjectiveDimensionBounds.exists_dimension_le_of_isProjective
#print axioms NativeProjectiveDimensionBounds.exists_dimension_le_of_isProjective
end EnvelopeProperty.SeshadriAmplenessCriterion
