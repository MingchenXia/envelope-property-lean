import EnvelopeProperty.Vanishing.NadelGlobalNormalizationAffine
import EnvelopeProperty.Vanishing.NadelGlobalNormalizationSourceIso
import EnvelopeProperty.Vanishing.NadelGlobalNormalizationFunctionField

/-! # Actual WHOLE original native normalization charts

The literal original global function-field tensor algebra, native affine
normalization and actual open raw chart construct the whole native normalized
chart. Every comparison and projection triangle is proved internally.
-/

open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalNormalization.Chart
open NadelAuxiliaryMulticover NadelAdaptedChartMatching
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {X : Scheme.{u}} [IsIntegral X] (U : X.affineOpens) [Nonempty U.1]
  (D : List (AuxiliarySection X)) (e : NadelAuxiliaryMulticoverCharts.Frames U.1 D)

/-- The SAME actual native original germ action in the whole generic tensor algebra. -/
local instance coefficientAlgebra : Algebra Γ(X, U.1) X.functionField :=
  GenericChart.coefficientAlgebra U

/-- The canonical native ring underlying the WHOLE tensor commutative
ring, made explicit for the actual integral-closure subtype instance. -/
local instance genericRing : Ring (GenericChart.Ring U D e) :=
  (inferInstance : CommRing (GenericChart.Ring U D e)).toRing

/-- The actual whole original generic projection is qc, as already proved. -/
local instance originalGenericQC : QuasiCompact (genericProjection D) := genericProjection_quasiCompact D

/-- The actual whole original generic projection is qs, as already proved. -/
local instance originalGenericQS : QuasiSeparated (genericProjection D) := genericProjection_quasiSeparated D

/-- The SAME original whole raw chart is genuinely an open immersion. -/
local instance originalRawOpen : IsOpenImmersion (RawChart.map U D e) := RawChart.isOpenImmersion U D e

/-- The literal whole tensor generic affine map is qc. -/
local instance tensorGenericQC : QuasiCompact
    (Affine.genericSpecMap (WholeChart.Ring U D e) (GenericChart.Ring U D e)) :=
  Affine.genericSpecMap_quasiCompact _ _

/-- The literal whole tensor generic affine map is qs. -/
local instance tensorGenericQS : QuasiSeparated
    (Affine.genericSpecMap (WholeChart.Ring U D e) (GenericChart.Ring U D e)) :=
  Affine.genericSpecMap_quasiSeparated _ _

/-- The actual original local generic projection, before normalization. -/
abbrev localGenericProjection := Limits.pullback.snd (genericProjection D) (RawChart.map U D e)

/-- The actual WHOLE generic source comparison internally transports its
native relative normalization, retaining the same original raw target. -/
def tensorNormalizationIso :
    (Affine.genericSpecMap (WholeChart.Ring U D e) (GenericChart.Ring U D e)).normalization ≅
      (localGenericProjection U D e).normalization :=
  sourceIso (GenericChart.localGenericIso U D e)
    (Affine.genericSpecMap (WholeChart.Ring U D e) (GenericChart.Ring U D e))
    (localGenericProjection U D e) (GenericChart.localGenericIso_projection U D e)

/-- The actual native local generic normalization is the spectrum of the
WHOLE closure in the SAME original global function-field tensor algebra. -/
def closureSpecIso : Spec (.of (integralClosure (WholeChart.Ring U D e) (GenericChart.Ring U D e))) ≅
    (localGenericProjection U D e).normalization :=
  Affine.normalizationSpectrumIso _ _ ≪≫ tensorNormalizationIso U D e

/-- The actual normalized local generic model identifies the literal native
base change of the WHOLE original global relative normalization. -/
def normalizedPullbackIso :
    Spec (.of (integralClosure (WholeChart.Ring U D e) (GenericChart.Ring U D e))) ≅
      Limits.pullback (normalizationProjection D) (RawChart.map U D e) :=
  closureSpecIso U D e ≪≫ asIso ((genericProjection D).normalizationPullback (RawChart.map U D e))

/-- The ENTIRE original normalized chart preserves the actual raw-algebra
structure map, rather than only giving an abstract spectrum isomorphism. -/
theorem normalizedPullbackIso_projection : (normalizedPullbackIso U D e).hom ≫
    Limits.pullback.snd (normalizationProjection D) (RawChart.map U D e) =
      Spec.map (CommRingCat.ofHom (algebraMap (WholeChart.Ring U D e)
        (integralClosure (WholeChart.Ring U D e) (GenericChart.Ring U D e)))) := by
  change (Affine.normalizationSpectrumIso _ _).hom ≫
    ((tensorNormalizationIso U D e).hom ≫
      ((genericProjection D).normalizationPullback (RawChart.map U D e) ≫ _)) = _
  rw [Scheme.Hom.normalizationPullback_snd]
  rw [show (tensorNormalizationIso U D e).hom ≫ (localGenericProjection U D e).fromNormalization =
      (Affine.genericSpecMap (WholeChart.Ring U D e) (GenericChart.Ring U D e)).fromNormalization from
    sourceIso_projection _ _ _ _]
  exact Affine.normalizationSpectrumIso_projection _ _

/-- The actual whole original normalized chart, constructed into the SAME
native global relative-normalization object. -/
def map : Spec (.of (integralClosure (WholeChart.Ring U D e) (GenericChart.Ring U D e))) ⟶ normalizedScheme D :=
  (normalizedPullbackIso U D e).hom ≫ Limits.pullback.fst (normalizationProjection D) (RawChart.map U D e)

/-- This genuine whole original normalized chart is an actual open immersion. -/
theorem isOpenImmersion : IsOpenImmersion (map U D e) := by
  unfold map
  infer_instance

/-- The whole native normalized chart has exactly the SAME original raw
projection, fixing every original raw coefficient and cyclic root. -/
theorem map_over_raw : map U D e ≫ normalizationProjection D =
    Spec.map (CommRingCat.ofHom (algebraMap (WholeChart.Ring U D e)
      (integralClosure (WholeChart.Ring U D e) (GenericChart.Ring U D e)))) ≫ RawChart.map U D e := by
  rw [map, Category.assoc, Limits.pullback.condition, ← Category.assoc, normalizedPullbackIso_projection]

attribute [local instance] isOpenImmersion

/-- The genuine whole normalized chart has EXACTLY the original whole
preimage of U as its open range. -/
theorem opensRange_map : (map U D e).opensRange = normalizedToOriginal D ⁻¹ᵁ U.1 := by
  simp only [map, Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackFst,
    RawChart.opensRange_map]
  rfl

/-- The actual whole original normalization over U is this ENTIRE affine
integral-closure spectrum; no selected generic component is substituted. -/
def imageIso : Spec (.of (integralClosure (WholeChart.Ring U D e) (GenericChart.Ring U D e))) ≅
    (normalizedToOriginal D ⁻¹ᵁ U.1).toScheme :=
  IsOpenImmersion.isoOfRangeEq (map U D e) (normalizedToOriginal D ⁻¹ᵁ U.1).ι
    (by
      rw [Scheme.Opens.range_ι]
      exact congrArg (fun V : (normalizedScheme D).Opens => (V : Set (normalizedScheme D)))
        (opensRange_map U D e))

/-- The actual whole affine normalization restriction retains its original
open-subscheme inclusion into the SAME native global normalization. -/
theorem imageIso_inclusion : (imageIso U D e).hom ≫ (normalizedToOriginal D ⁻¹ᵁ U.1).ι = map U D e :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

include e in
/-- The ENTIRE original normalized preimage of U is genuinely affine. -/
theorem preimage_isAffine : IsAffine (normalizedToOriginal D ⁻¹ᵁ U.1).toScheme :=
  IsAffine.of_isIso (imageIso U D e).inv

end EnvelopeProperty.Vanishing.NadelGlobalNormalization.Chart
