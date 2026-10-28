import EnvelopeProperty.Potential.CurveNetAllValuations
import EnvelopeProperty.Potential.IntegralSchemeCurveMaximum
import EnvelopeProperty.Berkovich.SchemeNetPSH

/-! # Genuine directed local PL nets retain actual integral scheme-curve maxima -/

open scoped NNReal Polynomial Topology Classical
open Polynomial Topology Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum

universe u
variable {K B : Type u} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
variable [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
  [Ring.KrullDimLE 1 B]

/-- Derive genuine finite-free coordinates (or a whole singleton point space) from
the original integral affine curve, retaining the actual local-maximum hypothesis. -/
theorem IsLocallyNetPSHOn.eventually_eq_of_isLocalMax_integral_affineCurve_allValuations
    {Ω : Set (RelativeSpectrum w B)} {u : RelativeSpectrum w B → EReal}
    (hu : IsLocallyNetPSHOn Ω u)
    (y : RelativeSpectrum w B) (hy : y ∈ Ω) (hmax : IsLocalMax u y) :
    ∀ᶠ z in 𝓝 y, u z = u y := by
  classical
  by_cases hB : IsField B
  · let := hB.toField
    have : Module.Finite K B := finite_of_finite_type_of_isJacobsonRing K B
    have : Algebra.IsIntegral K B := Algebra.IsIntegral.of_finite K B
    have hcoeff := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B)
    have hpoint (z : RelativeSpectrum w B) : z = y := by
      apply ext_val
      intro b
      obtain ⟨a, rfl⟩ := hcoeff.surjective b
      rw [val_algebraMap, val_algebraMap]
    exact Filter.Eventually.of_forall fun z => congrArg u (hpoint z)
  · obtain ⟨φ, _, hfinite, hfree⟩ :=
      exists_finiteFree_injective_polynomial_of_dimension_le_one K B hB
    let : Algebra K[X] B := φ.toRingHom.toAlgebra
    let : IsScalarTower K K[X] B :=
      IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
    let : Module.Finite K[X] B := hfinite
    let : Module.Free K[X] B := hfree
    let basis := Module.Free.chooseBasis K[X] B
    let : Fintype (Module.Free.ChooseBasisIndex K[X] B) := Fintype.ofFinite _
    exact hu.eventually_eq_of_isLocalMax_finiteFree_allValuations basis y hy hmax

end EnvelopeProperty.Berkovich.RelativeSpectrum

open scoped NNReal Topology
open Topology Filter CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {K : Type u} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
  {X : Scheme.{u}} [IsIntegral X]

/-- Genuine affine charts carry the unchanged intrinsic class and actual maximum
to a derived integral affine curve, then return equality in the original topology. -/
theorem IsLocallyNetPSHOn.eventually_eq_of_isLocalMax_integral_curve_allValuations
    {f : X ⟶ Spec (CommRingCat.of K)} [LocallyOfFiniteType f]
    (hX : topologicalKrullDim X ≤ 1)
    {Ω : Set (RelativeSchemeValuedPoint w f)} {u : RelativeSchemeValuedPoint w f → EReal}
    (hu : IsLocallyNetPSHOn Ω u)
    (y : RelativeSchemeValuedPoint w f) (hy : y ∈ Ω) (hmax : IsLocalMax u y) :
    ∀ᶠ z in 𝓝 y, u z = u y := by
  classical
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top y.1.point)
  have : Nonempty U := ⟨⟨y.1.point, hyU⟩⟩
  let A := Γ(X, U)
  let : Algebra K A := (FiniteTypePoint.affineBaseMap f hU).toAlgebra
  have : Algebra.FiniteType K A :=
    RingHom.finiteType_algebraMap.mp (FiniteTypePoint.affineBaseMap_finiteType f hU)
  have : Ring.KrullDimLE 1 A :=
    affineOpen_krullDimLE_one_of_topologicalKrullDim_le_one hX hU
  let fA := Spec.map (CommRingCat.ofHom (algebraMap K A))
  have hg : hU.fromSpec ≫ f = fA := (FiniteTypePoint.affineBaseMap_spec f hU).symm
  let E : RelativeSchemeValuedPoint w fA ≃ₜ RelativeSpectrum w A := affineSpectrumHomeomorph
  let q : RelativeSpectrum w A → RelativeSchemeValuedPoint w f :=
    fun a => map hU.fromSpec hg (E.symm a)
  have hq : IsOpenEmbedding q :=
    (isOpenEmbedding_map_of_isOpenImmersion hU.fromSpec hg).comp E.symm.isOpenEmbedding
  have hyrange : y ∈ Set.range (map (v := w) hU.fromSpec hg) := by
    rw [range_map_of_isOpenImmersion hU.fromSpec hg, hU.opensRange_fromSpec]
    exact hyU
  obtain ⟨z, hz⟩ := hyrange
  let a := E z
  have hqa : q a = y := by
    simpa only [q, a, Homeomorph.symm_apply_apply] using hz
  have hchart : IsLocallyNetPSHOn (map hU.fromSpec hg ⁻¹' Ω)
      (fun z => u (map hU.fromSpec hg z)) := by
    have h := hu.comp_mapOverBase (RingHom.id K) (fun _ => rfl) hU.fromSpec
      (by simpa using hg)
    exact h
  have hlocal := hchart.to_affineSpectrum
  change RelativeSpectrum.IsLocallyNetPSHOn (q ⁻¹' Ω) (fun z => u (q z)) at hlocal
  have hmaxA : IsLocalMax (fun z => u (q z)) a := by
    have hm : IsLocalMax u (q a) := by simpa only [hqa] using hmax
    exact hm.comp_continuous hq.continuous.continuousAt
  have ha : a ∈ q ⁻¹' Ω := by
    change q a ∈ Ω
    rw [hqa]
    exact hy
  have hconstant := hlocal.eventually_eq_of_isLocalMax_integral_affineCurve_allValuations a ha hmaxA
  rw [← hqa, ← hq.map_nhds_eq a]
  exact hconstant

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X]

/-- Native original local psh on an actual integral scheme curve obeys the
whole maximum principle, with its analytic preconnectedness derived internally. -/
theorem IsLocallyNetPSHOn.eq_of_isMaxOn_univ_integral_curve
    {f : X ⟶ Spec (CommRingCat.of K)} [LocallyOfFiniteType f]
    (hX : topologicalKrullDim X ≤ 1)
    {u : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f → EReal}
    (hu : IsLocallyNetPSHOn Set.univ u)
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f)
    (hmax : IsMaxOn u Set.univ y) : ∀ z, u z = u y := by
  let := preconnectedSpace_integral_curve f hX
  let M : Set (RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f) := {z | u y ≤ u z}
  have husc : UpperSemicontinuous u := upperSemicontinuousOn_univ_iff.mp hu.upperSemicontinuousOn
  have hMc : IsClosed M := husc.isClosed_preimage (u y)
  have hMo : IsOpen M := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hzeq : u z = u y := le_antisymm (hmax (Set.mem_univ z)) hz
    have hzmax : IsLocalMax u z := Filter.Eventually.of_forall
      (fun q => (hmax (Set.mem_univ q)).trans_eq hzeq.symm)
    have hflat := hu.eventually_eq_of_isLocalMax_integral_curve_allValuations
      hX z (Set.mem_univ z) hzmax
    exact hflat.mono (fun q hq => (hq.trans hzeq).ge)
  have hMu : M = Set.univ :=
    (show IsClopen M from ⟨hMc, hMo⟩).eq_univ ⟨y, show u y ≤ u y from le_rfl⟩
  intro z
  have hz : z ∈ M := by rw [hMu]; exact Set.mem_univ z
  exact le_antisymm (hmax (Set.mem_univ z)) hz


end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
