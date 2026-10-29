import EnvelopeProperty.DI.ActualWittHigherExteriorMaps
import EnvelopeProperty.DI.FiniteSourceAssembly
import EnvelopeProperty.Cartier.DeligneIllusieDimensionSource

noncomputable section
namespace EnvelopeProperty.DI.ActualWittDecomposition
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomologicalComplex
open DeligneIllusie Cartier
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p] [PerfectRing κ p]
  {Xtilde : Scheme.{u}} (f : Xtilde ⟶ Spec (.of (WittTwo.Ring p κ)))
  (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f]

local notation "f₀" => ActualWittCechOneMap.specialFibreMap p κ f
local notation "g" => ActualWittCechOneMap.twistMap p κ f
local notation "Y" => ActualWittCechOneMap.twist p κ f
local notation "U" => ActualWittCechOneMap.cover p κ f n
local notation "K" => ActualWittCechOneMap.targetComplex p κ f n
local notation "T" => DeligneIllusieLocalContinuationCechTotalAugmentation.totalComplex U K

local instance specialFibre_smooth : SmoothOfRelativeDimension n f₀ :=
  WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n

def sourceNat : CochainComplex (Y).Modules ℕ :=
  DeligneIllusieDimensionSource.source f₀ p p

def componentMap (q : Fin p) :
    (single (Y).Modules (ComplexShape.up ℕ) q.val).obj
      (CanonicalGeometry.exteriorCotangentSheaf g q.val) ⟶ T := by
  rcases q with ⟨q, _⟩
  cases q with
  | zero => exact FiniteSourceAssembly.zeroTotalMap f₀ p n U
  | succ r => exact ActualWittHigherExteriorMaps.higherCochainMap p κ f n r

def finiteCochainMap : sourceNat p κ f ⟶ T :=
  Sigma.desc (componentMap p κ f n)

theorem componentMap_zero (h : 0 < p) :
    componentMap p κ f n ⟨0, h⟩ = FiniteSourceAssembly.zeroTotalMap f₀ p n U := rfl

theorem componentMap_succ (r : ℕ) (h : r + 1 < p) :
    componentMap p κ f n ⟨r + 1, h⟩ =
      ActualWittHigherExteriorMaps.higherCochainMap p κ f n r := rfl

theorem summand_finiteCochainMap (q : Fin p) :
    Sigma.ι (fun i : Fin p =>
      (single (Y).Modules (ComplexShape.up ℕ) i.val).obj
        (CanonicalGeometry.exteriorCotangentSheaf g i.val)) q ≫
      finiteCochainMap p κ f n = componentMap p κ f n q :=
  Sigma.ι_desc _ q

def truncatedCochainMap :
    (sourceNat p κ f).extend ComplexShape.embeddingUpNat ⟶
      DeligneIllusieCechGoodTruncation.goodTruncation T p :=
  FiniteSourceAssembly.truncatedMap
    (fun q : Fin p => CanonicalGeometry.exteriorCotangentSheaf g q.val)
    (finiteCochainMap p κ f n)

theorem truncatedCochainMap_inclusion :
    truncatedCochainMap p κ f n ≫
      CochainComplex.ιTruncLE ((T).extend ComplexShape.embeddingUpNat) ((p : ℤ) - 1) =
        HomologicalComplex.extendMap (finiteCochainMap p κ f n)
          ComplexShape.embeddingUpNat :=
  FiniteSourceAssembly.truncatedMap_inclusion
    (fun q : Fin p => CanonicalGeometry.exteriorCotangentSheaf g q.val)
    (finiteCochainMap p κ f n)

theorem componentMap_zero_quasiIsoAt (h : 0 < p) :
    QuasiIsoAt (componentMap p κ f n ⟨0, h⟩) 0 := by
  let z := FiniteSourceAssembly.zeroCochainMap f₀ p n
  have hz : QuasiIsoAt z 0 := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let e := singleObjHomologySelfIso (ComplexShape.up ℕ) 0
      (CanonicalGeometry.exteriorCotangentSheaf g 0)
    have : IsIso (e.inv ≫ homologyMap z 0) := by
      change IsIso ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0
        (CanonicalGeometry.exteriorCotangentSheaf g 0)).inv ≫
          homologyMap (FiniteSourceAssembly.zeroCochainMap f₀ p n) 0)
      rw [FiniteSourceAssembly.zeroCochainMap_class]
      infer_instance
    exact IsIso.of_isIso_comp_left e.inv _
  let : QuasiIsoAt z 0 := hz
  let : QuasiIso
      (DeligneIllusieLocalContinuationCechTotalAugmentation.totalAugmentation U K) :=
    DeligneIllusieLocalContinuationCechTotalQuasiIso.totalAugmentation_quasiIso
      U K (ActualWittCechOneMap.cover_iSup p κ f n)
  change QuasiIsoAt
    (z ≫ DeligneIllusieLocalContinuationCechTotalAugmentation.totalAugmentation U K) 0
  infer_instance

theorem finiteCochainMap_quasiIsoAt_iff (q : Fin p) :
    QuasiIsoAt (finiteCochainMap p κ f n) q.val ↔
      QuasiIsoAt (componentMap p κ f n q) q.val := by
  rw [DeligneIllusieGradedSourceHomology.quasiIsoAt_iff_inclusion
    (ComplexShape.up ℕ) Fin.val
    (fun i : Fin p => CanonicalGeometry.exteriorCotangentSheaf g i.val)
    Fin.val_injective (finiteCochainMap p κ f n) q]
  rw [summand_finiteCochainMap]

theorem finiteCochainMap_quasiIsoAt_zero :
    QuasiIsoAt (finiteCochainMap p κ f n) 0 := by
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  exact (finiteCochainMap_quasiIsoAt_iff p κ f n ⟨0, hp⟩).mpr
    (componentMap_zero_quasiIsoAt p κ f n hp)

end EnvelopeProperty.DI.ActualWittDecomposition
