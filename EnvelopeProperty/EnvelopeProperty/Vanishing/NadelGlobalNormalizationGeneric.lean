import EnvelopeProperty.Vanishing.NadelGlobalNormalizationRawChart
import EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverNormalization
import Mathlib.Algebra.Category.Ring.Constructions

/-! # The WHOLE actual original global base-generic fibre on its original raw chart

The original native function field and original germ map are used literally.
The actual complete tensor pushout and original raw cartesian chart produce
the generic isomorphisms, retaining every original root and component.
-/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalNormalization.GenericChart
open NadelAuxiliaryMulticover NadelAdaptedChartMatching
variable {X : Scheme.{u}} [IsIntegral X] (U : X.affineOpens) [Nonempty U.1]
  (D : List (AuxiliarySection X)) (e : NadelAuxiliaryMulticoverCharts.Frames U.1 D)

/-- The SAME actual native original germ action, explicit at the original
function field to retain its precise coefficient-ring instance. -/
local instance coefficientAlgebra : Algebra Γ(X, U.1) X.functionField :=
  (X.germToFunctionField U.1).hom.toAlgebra

/-- The ACTUAL original generic germ morphism on the SAME original affine ring. -/
def affineGenericMap : Spec X.functionField ⟶ Spec Γ(X, U.1) :=
  Spec.map (X.germToFunctionField U.1)

/-- This is the SAME original global generic morphism, via its actual
original nonempty affine open; no function-field matching is an input. -/
theorem affineGenericMap_over : affineGenericMap U ≫ U.2.fromSpec =
    IntegralSchemeNormalization.genericMap X := by
  exact U.2.fromSpecStalk_eq_fromSpecStalk
    (((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr (by simpa using ‹Nonempty U.1›))

/-- The literal WHOLE original base-generic affine algebra, with the SAME
original function field, native original germ action and full original raw ring. -/
abbrev Ring := X.functionField ⊗[Γ(X, U.1)] WholeChart.Ring U D e

/-- The actual full original raw-ring inclusion under Spec. -/
def toRawChart : Spec (.of (Ring U D e)) ⟶ Spec (.of (WholeChart.Ring U D e)) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)

/-- The actual SAME original global function-field projection. -/
def toFunctionField : Spec (.of (Ring U D e)) ⟶ Spec X.functionField :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
    (R := Γ(X, U.1)) (A := X.functionField) (B := WholeChart.Ring U D e)))

/-- The WHOLE native tensor square is the actual original affine base change. -/
theorem tensor_isPullback : IsPullback (toRawChart U D e) (toFunctionField U D e)
    (RawChart.baseMap U D e) (affineGenericMap U) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(X, U.1) X.functionField (WholeChart.Ring U D e)).flip

/-- The actual entire generic source maps to the SAME original raw multicover. -/
def toRaw : Spec (.of (Ring U D e)) ⟶ rawScheme D := toRawChart U D e ≫ RawChart.map U D e

/-- The WHOLE actual affine generic algebra IS the original global
base-generic pullback, by genuine native tensor and original chart pasting. -/
theorem whole_isPullback : IsPullback (toRaw U D e) (toFunctionField U D e)
    (projection D) (IntegralSchemeNormalization.genericMap X) := by
  have hh := ((tensor_isPullback U D e).flip.paste_vert (RawChart.isPullback U D e).flip).flip
  rw [affineGenericMap_over] at hh
  exact hh

/-- The ENTIRE actual original global generic fibre is this actual whole
affine tensor spectrum, without selecting any generic component. -/
def wholeGenericIso : Spec (.of (Ring U D e)) ≅ genericFiber D :=
  (whole_isPullback U D e).isoPullback

/-- The WHOLE original generic comparison retains its actual raw projection. -/
theorem wholeGenericIso_projection : (wholeGenericIso U D e).hom ≫ genericProjection D = toRaw U D e :=
  (whole_isPullback U D e).isoPullback_hom_fst

/-- The same whole generic projection base-changed to the ACTUAL original
raw chart is genuinely this literal whole tensor spectrum. -/
theorem local_isPullback : IsPullback (wholeGenericIso U D e).hom (toRawChart U D e)
    (genericProjection D) (RawChart.map U D e) := by
  let : IsOpenImmersion (RawChart.map U D e) := RawChart.isOpenImmersion U D e
  exact IsPullback.of_horiz_isIso_mono ⟨wholeGenericIso_projection U D e⟩

/-- The actual whole native local generic-fibre pullback, with all original
raw generators and every whole unit-root factor retained. -/
def localGenericIso : Spec (.of (Ring U D e)) ≅
    Limits.pullback (genericProjection D) (RawChart.map U D e) :=
  (local_isPullback U D e).isoPullback

/-- The ACTUAL local generic comparison preserves the whole original raw ring map. -/
theorem localGenericIso_projection : (localGenericIso U D e).hom ≫
    Limits.pullback.snd (genericProjection D) (RawChart.map U D e) = toRawChart U D e :=
  (local_isPullback U D e).isoPullback_hom_snd

end EnvelopeProperty.Vanishing.NadelGlobalNormalization.GenericChart
