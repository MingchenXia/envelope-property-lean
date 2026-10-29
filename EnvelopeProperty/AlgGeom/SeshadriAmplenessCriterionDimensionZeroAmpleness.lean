import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionEulerPolynomialBase
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness
import EnvelopeProperty.AlgGeom.ProjectiveFactorizationRingIso
import EnvelopeProperty.AlgGeom.TensorPowerBaseIdealGrading
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order
open Scheme.Modules MvPolynomial
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterionDimensionZeroAmpleness
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem nonempty_unitIso_of_dimension_le_zero
    {X : Scheme.{u}} [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 0) (L : X.Modules) (hL : IsInvertible L) :
    Nonempty (L ≅ unitObj X) := by
  classical
  obtain ⟨ι, U, hU, hframe⟩ := hL
  have hx : genericPoint X ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let Z : Closeds X := ⟨(U i : Set X)ᶜ, (U i).isOpen.isClosed_compl⟩
  have hZ : Z ≠ ⊤ := by
    intro h
    have hg : genericPoint X ∈ (Z : Set X) := by rw [h]; trivial
    exact hg hi
  let : IsEmpty Z :=
    SeshadriAmplenessCriterion.properClosed_isEmpty_of_dimension_le_zero Z hZ hdim
  have htop : U i = ⊤ := by
    apply top_unique
    intro x _hx
    by_contra hxi
    exact isEmptyElim (⟨x, hxi⟩ : Z)
  have he : Nonempty ((Scheme.Modules.pullback (⊤ : X.Opens).ι).obj L ≅
      unitObj (⊤ : X.Opens).toScheme) := by
    exact htop ▸ (hframe i)
  let e := he.some
  let F := Scheme.Modules.pullback X.topIso.hom
  let : F.IsEquivalence := Scheme.Modules.pullback_isEquivalence_of_iso X.topIso
  exact ⟨F.preimageIso (e ≪≫ (pullbackUnitIso X.topIso.hom).symm)⟩

theorem isVeryAmple_of_dimension_le_zero
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ 0) (L : X.Modules) (hL : IsInvertible L) :
    SchemeLineAmpleness.IsVeryAmple p L := by
  classical
  obtain ⟨d, i, hi, hbase⟩ := ProjectiveFactorizationRingIso.of_isProjective p
  let H : X.Modules := (Scheme.Modules.pullback i).obj
    (coordinateHyperplaneTwist (R := k) (0 : Fin (d + 1)) 1)
  have hH : IsInvertible H :=
    (coordinateHyperplaneTwist_isInvertible (R := k) (0 : Fin (d + 1)) 1).pullback i
  obtain ⟨eH⟩ := nonempty_unitIso_of_dimension_le_zero hdim H hH
  obtain ⟨eL⟩ := nonempty_unitIso_of_dimension_le_zero hdim L hL
  refine ⟨d, i, hi, ?_, ⟨eH ≪≫ eL.symm⟩⟩
  convert hbase using 1
  unfold homogeneousProjπ Alterations.projectiveSpaceStructure
  congr 1

theorem isAmple_of_dimension_le_zero
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ 0) (L : X.Modules) (hL : IsInvertible L) :
    SchemeLineAmpleness.IsAmple p L := by
  refine ⟨hL, 1, by decide, ?_⟩
  exact isVeryAmple_of_dimension_le_zero p hdim (bundleTensorPower L 1)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL 1)

#print axioms nonempty_unitIso_of_dimension_le_zero
#print axioms isVeryAmple_of_dimension_le_zero
#print axioms isAmple_of_dimension_le_zero
end EnvelopeProperty.SeshadriAmplenessCriterionDimensionZeroAmpleness
