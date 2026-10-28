import EnvelopeProperty.DI.ActualWittHigherSheafCartier
import EnvelopeProperty.DI.ActualWittDecomposition
import EnvelopeProperty.DI.FiniteSourceRangeQuasiIso
import EnvelopeProperty.Cartier.DeligneIllusieCechLocalQuasiIso

/-! The actual global Deligne--Illusie decomposition from original Witt geometry. -/
noncomputable section
namespace EnvelopeProperty.DI.ActualWittDecomposition
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomologicalComplex
open DeligneIllusie Cartier
universe w u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p] [PerfectRing κ p]
  {Xtilde : Scheme.{u}} (f : Xtilde ⟶ Spec (.of (WittTwo.Ring p κ)))
  (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f]
local notation "f₀" => ActualWittCechOneMap.specialFibreMap p κ f
local notation "Y" => ActualWittCechOneMap.twist p κ f
local notation "g" => ActualWittCechOneMap.twistMap p κ f
local notation "U" => ActualWittCechOneMap.cover p κ f n
local notation "K" => ActualWittCechOneMap.targetComplex p κ f n
local notation "M" r => CanonicalGeometry.exteriorCotangentSheaf g (r+1)
local notation "H" r => ActualWittHigherExteriorMaps.higherCochainMap p κ f n r
private abbrev actualMemberMap := ActualWittHigherSheafCartier.actualMemberMap p κ f n
private instance specialFibreSmooth : SmoothOfRelativeDimension n f₀ :=
  WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n

theorem higherCochainMap_quasiIsoAt (r : ℕ) (hr : r+1 < p) :
    QuasiIsoAt (H r) (r+1) := by
  have hclass := fun i => ActualWittHigherSheafCartier.memberClass p κ f n r hr i
  let q := r+1
  let S := (HomologicalComplex.single (Y).Modules (.up ℕ) q).obj (M r)
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply DeligneIllusieCechLocalQuasiIso.isIso_of_restrictions U
    (ActualWittCechOneMap.cover_iSup p κ f n)
  intro i
  let L := Scheme.Modules.restrictFunctor (U i).ι
  let : L.PreservesHomology := SchemeOpenRestrictionHomology.preservesHomology (U i).ι
  let Ai := (L.mapHomologicalComplex (.up ℕ)).map (H r)
  let εi := DeligneIllusieCechTotalEvaluation.localEvaluation U K i
  let αi := (HomologicalComplex.singleMapHomologicalComplex L (.up ℕ) q).app (M r)
  let φi := actualMemberMap p κ f n r i
  let σi := (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) q (L.obj (M r))).inv
  let τi := (SchemeOpenRestrictionHomology.homologyIso (U i).ι K q).hom
  have hci : IsIso (σi ≫ HomologicalComplex.homologyMap φi q ≫ τi) := by
    change IsIso ((HomologicalComplex.singleObjHomologySelfIso (.up ℕ) (r+1)
      ((Scheme.Modules.restrictFunctor (U i).ι).obj (M r))).inv ≫
      HomologicalComplex.homologyMap (actualMemberMap p κ f n r i) (r+1) ≫
      (SchemeOpenRestrictionHomology.homologyIso (U i).ι K (r+1)).hom)
    rw [hclass i]
    infer_instance
  let := hci
  let : IsIso (HomologicalComplex.homologyMap φi q ≫ τi) :=
    IsIso.of_isIso_comp_left σi _
  let : IsIso (HomologicalComplex.homologyMap φi q) :=
    IsIso.of_isIso_comp_right _ τi
  have hφi : QuasiIsoAt φi q :=
    (quasiIsoAt_iff_isIso_homologyMap φi q).mpr inferInstance
  let : QuasiIso αi.inv := quasiIso_of_isIso αi.inv
  have hAε : QuasiIsoAt (Ai ≫ εi) q :=
    (quasiIsoAt_iff_comp_left αi.inv (Ai ≫ εi) q).mp hφi
  let : QuasiIso εi := DeligneIllusieCechTotalEvaluation.localEvaluation_quasiIso U K
    (ActualWittCechOneMap.cover_iSup p κ f n) i
  have hAi : QuasiIsoAt Ai q := (quasiIsoAt_iff_comp_right Ai εi q).mp hAε

  -- The SAME native restriction-homology square, specialized to Nat/q.
  -- No new local-QI theorem and no Gamma(Tot) exactness enters this step.
  let b := (HomologicalComplex.shortComplexFunctor (Y).Modules (.up ℕ) q).map (H r)
  have hb : ShortComplex.QuasiIso (L.mapShortComplex.map b) := hAi.quasiIso
  let : IsIso (ShortComplex.homologyMap (L.mapShortComplex.map b)) :=
    (ShortComplex.quasiIso_iff _).mp hb
  have hh : IsIso (((S.sc q).mapHomologyIso L).hom ≫
      L.map (ShortComplex.homologyMap b)) := by
    rw [← ShortComplex.mapHomologyIso_hom_naturality b L]
    infer_instance
  let := hh
  change IsIso (L.map (ShortComplex.homologyMap b))
  exact IsIso.of_isIso_comp_left ((S.sc q).mapHomologyIso L).hom _

theorem finiteCochainMap_quasiIsoAt :
    ∀ q : ℕ, q < p →
      QuasiIsoAt (ActualWittDecomposition.finiteCochainMap p κ f n) q := by
  intro q hq
  cases q with
  | zero =>
      exact ActualWittDecomposition.finiteCochainMap_quasiIsoAt_zero p κ f n
  | succ r =>
      have hc : QuasiIsoAt
          (ActualWittDecomposition.componentMap p κ f n ⟨r+1, hq⟩) (r+1) := by
        rw [ActualWittDecomposition.componentMap_succ]
        exact higherCochainMap_quasiIsoAt p κ f n r hq
      exact (ActualWittDecomposition.finiteCochainMap_quasiIsoAt_iff
        p κ f n ⟨r+1, hq⟩).mpr hc


theorem truncatedCochainMap_quasiIso : QuasiIso (truncatedCochainMap p κ f n) := by
  exact FiniteSourceRangeQuasiIso.quasiIso_truncatedMap_of_range
    (fun q : Fin p => CanonicalGeometry.exteriorCotangentSheaf g q.val)
    (finiteCochainMap p κ f n) (finiteCochainMap_quasiIsoAt p κ f n)

def truncatedDerivedIso [HasDerivedCategory.{w} (Y).Modules] :
    DerivedCategory.Q.obj ((sourceNat p κ f).extend ComplexShape.embeddingUpNat) ≅
      DerivedCategory.Q.obj (DeligneIllusieCechGoodTruncation.goodTruncation K p) := by
  let : QuasiIso (truncatedCochainMap p κ f n) := truncatedCochainMap_quasiIso p κ f n
  exact asIso (DerivedCategory.Q.map (truncatedCochainMap p κ f n)) ≪≫
    (DeligneIllusieCechGoodTruncation.derivedAugmentationIso U K
      (ActualWittCechOneMap.cover_iSup p κ f n) p).symm

def fullDerivedIso [HasDerivedCategory.{w} (Y).Modules] (hp : n < p) :
    DerivedCategory.Q.obj ((DeligneIllusieDimensionSource.source f₀ p (n + 1)).extend
      ComplexShape.embeddingUpNat) ≅
      DerivedCategory.Q.obj ((K).extend ComplexShape.embeddingUpNat) := by
  let : SmoothOfRelativeDimension n f₀ :=
    WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
  let eS := DeligneIllusieDimensionSource.sourceIso f₀ p n hp
  let eS' := (ComplexShape.embeddingUpNat.extendFunctor (Y).Modules).mapIso eS
  let a := DeligneIllusieDimensionBound.goodTruncationInclusion f₀ n p
  let : IsIso a := DeligneIllusieDimensionBound.goodTruncationInclusion_isIso f₀ n p hp
  exact DerivedCategory.Q.mapIso eS' ≪≫ truncatedDerivedIso p κ f n ≪≫
    asIso (DerivedCategory.Q.map a)


end EnvelopeProperty.DI.ActualWittDecomposition
