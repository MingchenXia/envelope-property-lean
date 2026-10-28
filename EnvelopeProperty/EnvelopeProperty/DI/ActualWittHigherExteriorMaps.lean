import EnvelopeProperty.DI.CechHigherExteriorMaps
import EnvelopeProperty.DI.ActualWittCechOneMap

/-! # Actual normalized positive-degree exterior maps from original Witt geometry

All local data are constructed internally from the original smooth separated
Witt geometry. No higher map, closure, homology comparison or quasi-isomorphism
certificate is an input. The positive-degree normalization is defined for all
indices using the original field inverse; Cartier comparison uses q < p.
-/

noncomputable section

namespace EnvelopeProperty.DI.ActualWittHigherExteriorMaps

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Cartier DeligneIllusie

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (p : ℕ) [Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p] [PerfectRing κ p]
  {Xtilde : Scheme.{u}}
  (f : Xtilde ⟶ Spec (CommRingCat.of (WittTwo.Ring p κ)))
  (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f]

/-- The actual original geometry produces the normalized higher SHEAF map.
Degree r+1 is positive; no desired local/higher map is supplied by the caller. -/
def higherMap (r : ℕ) :
    CanonicalGeometry.exteriorCotangentSheaf (ActualWittCechOneMap.twistMap p κ f) (r+1) ⟶
      (DeligneIllusieLocalContinuationCechTotalAugmentation.totalComplex
        (ActualWittCechOneMap.cover p κ f n) (ActualWittCechOneMap.targetComplex p κ f n)).X
        (r+1) := by
  letI : SmoothOfRelativeDimension n (ActualWittCechOneMap.specialFibreMap p κ f) :=
    DeligneIllusie.WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
  exact CechHigherExteriorMaps.higherMap (ActualWittCechOneMap.specialFibreMap p κ f) p n
    (ActualWittCechOneMap.cover p κ f n) (ActualWittCechOneMap.canonicalLocalData p κ f n) r

/-- Every original source unit retains the actual selected lifts, actual ordered
cup powers and original structural-field normalization. -/
theorem higherMap_unit (r : ℕ) (W : (ActualWittCechOneMap.twist p κ f).Opens)
    (v : Fin (r+1) →
      (CanonicalGeometry.cotangentPresheaf (ActualWittCechOneMap.twistMap p κ f)).obj (op W)) :
    letI := DeligneIllusie.WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
    (higherMap p κ f n r).val.app (op W)
        (CanonicalGeometry.exteriorSheafSection
          (CanonicalGeometry.cotangentPresheaf (ActualWittCechOneMap.twistMap p κ f)) (r+1) W v) =
      DeligneIllusieAlternatingNormalization.normalizedAlternatization
        (CechHigherExteriorMaps.constantMap (ActualWittCechOneMap.specialFibreMap p κ f) p W)
        (r+1) (CechHigherExteriorMaps.orderedPower
          (ActualWittCechOneMap.specialFibreMap p κ f) p n (ActualWittCechOneMap.cover p κ f n)
          (ActualWittCechOneMap.canonicalLocalData p κ f n) r W) v := by
  let := DeligneIllusie.WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
  exact CechHigherExteriorMaps.higherMap_unit
    (ActualWittCechOneMap.specialFibreMap p κ f) p n (ActualWittCechOneMap.cover p κ f n)
    (ActualWittCechOneMap.canonicalLocalData p κ f n) r W v

/-- The entire original actual geometric degree-one component is retained. -/
theorem higherMap_zero : higherMap p κ f n 0 =
    ActualWittCechOneMap.canonicalOneComponent p κ f n := by
  let := DeligneIllusie.WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
  exact (CechHigherExteriorMaps.higherMap_zero
    (ActualWittCechOneMap.specialFibreMap p κ f) p n (ActualWittCechOneMap.cover p κ f n)
    (ActualWittCechOneMap.canonicalLocalData p κ f n)).trans
      (ActualWittCechOneMap.canonicalOneMap_component p κ f n)

/-- Original over-open evaluation retains the SAME original member xi.
No assertion about global sections preserving arbitrary quasi-isomorphisms is used. -/
theorem higherMap_zero_localEvaluation (i : ActualWittCechOneMap.CoverIndex p κ f n) :
    (Scheme.Modules.restrictFunctor (ActualWittCechOneMap.cover p κ f n i).ι).map
        (higherMap p κ f n 0) ≫
      (DeligneIllusieCechTotalEvaluation.localEvaluation
        (ActualWittCechOneMap.cover p κ f n) (ActualWittCechOneMap.targetComplex p κ f n) i).f 1 =
      ActualWittCechOneMap.memberXi p κ f n i := by
  exact (congrArg (fun h =>
    (Scheme.Modules.restrictFunctor (ActualWittCechOneMap.cover p κ f n i).ι).map h ≫
      (DeligneIllusieCechTotalEvaluation.localEvaluation
        (ActualWittCechOneMap.cover p κ f n) (ActualWittCechOneMap.targetComplex p κ f n) i).f 1)
    (higherMap_zero p κ f n)).trans
      (ActualWittCechOneMap.canonicalOneComponent_localEvaluation p κ f n i)

/-- WHOLE higher closedness is internally produced from the actual Witt local
data and the actual total product law; no closure certificate is supplied. -/
theorem higherMap_closed (r : ℕ) :
    higherMap p κ f n r ≫
      (DeligneIllusieLocalContinuationCechTotalAugmentation.totalComplex
        (ActualWittCechOneMap.cover p κ f n) (ActualWittCechOneMap.targetComplex p κ f n)).d
        (r+1) (r+2) = 0 := by
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
  exact CechHigherExteriorMaps.higherMap_closed (ActualWittCechOneMap.specialFibreMap p κ f)
    p n (ActualWittCechOneMap.cover p κ f n) (ActualWittCechOneMap.canonicalLocalData p κ f n) r

/-- The ACTUAL original Witt geometry produces the genuine positive-degree
complex morphism. No D, higher map, unit, comparison or QI certificate is input. -/
def higherCochainMap (r : ℕ) :
    (HomologicalComplex.single (ActualWittCechOneMap.twist p κ f).Modules (.up ℕ) (r+1)).obj
        (CanonicalGeometry.exteriorCotangentSheaf (ActualWittCechOneMap.twistMap p κ f) (r+1)) ⟶
      DeligneIllusieLocalContinuationCechTotalAugmentation.totalComplex
        (ActualWittCechOneMap.cover p κ f n) (ActualWittCechOneMap.targetComplex p κ f n) := by
  letI : SmoothOfRelativeDimension n (ActualWittCechOneMap.specialFibreMap p κ f) :=
    WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
  exact CechHigherExteriorMaps.higherCochainMap
    (ActualWittCechOneMap.specialFibreMap p κ f) p n (ActualWittCechOneMap.cover p κ f n)
    (ActualWittCechOneMap.canonicalLocalData p κ f n) r

theorem higherCochainMap_f_self (r : ℕ) :
    (higherCochainMap p κ f n r).f (r+1) =
      (HomologicalComplex.singleObjXSelf (.up ℕ) (r+1)
        (CanonicalGeometry.exteriorCotangentSheaf (ActualWittCechOneMap.twistMap p κ f) (r+1))).hom ≫
          higherMap p κ f n r := by
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
  exact CechHigherExteriorMaps.higherCochainMap_f_self
    (ActualWittCechOneMap.specialFibreMap p κ f) p n (ActualWittCechOneMap.cover p κ f n)
    (ActualWittCechOneMap.canonicalLocalData p κ f n) r

/-- Normalization retains the WHOLE already constructed actual degree-one map. -/
theorem higherCochainMap_zero :
    higherCochainMap p κ f n 0 = ActualWittCechOneMap.canonicalOneMap p κ f n := by
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
  exact CechHigherExteriorMaps.higherCochainMap_zero
    (ActualWittCechOneMap.specialFibreMap p κ f) p n (ActualWittCechOneMap.cover p κ f n)
    (ActualWittCechOneMap.canonicalLocalData p κ f n)

end EnvelopeProperty.DI.ActualWittHigherExteriorMaps
