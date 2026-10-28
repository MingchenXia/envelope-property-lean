import EnvelopeProperty.Potential.IntegralCurveConnectedness
import EnvelopeProperty.Berkovich.SchemeCurveLocalMaximumAllValuations
import EnvelopeProperty.Berkovich.SchemeLocalPSHContinuity

/-! # Derived whole native connectedness and maxima on original integral scheme curves -/

open scoped NNReal Topology Classical
open Topology Filter CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X]

/-- An actual nonempty affine open and genuine generic-support density derive
whole analytic preconnectedness of every original integral scheme curve. -/
theorem preconnectedSpace_integral_curve
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    (hX : topologicalKrullDim X ≤ 1) :
    PreconnectedSpace (RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f) := by
  classical
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top x)
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let A := Γ(X, U)
  let : Algebra K A := (FiniteTypePoint.affineBaseMap f hU).toAlgebra
  have : Algebra.FiniteType K A :=
    RingHom.finiteType_algebraMap.mp (FiniteTypePoint.affineBaseMap_finiteType f hU)
  have : Ring.KrullDimLE 1 A :=
    affineOpen_krullDimLE_one_of_topologicalKrullDim_le_one hX hU
  let := RelativeSpectrum.preconnectedSpace_integral_affineCurve (K := K) (B := A)
  let fA := Spec.map (CommRingCat.ofHom (algebraMap K A))
  have hg : hU.fromSpec ≫ f = fA := (FiniteTypePoint.affineBaseMap_spec f hU).symm
  let E : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) fA ≃ₜ
      RelativeSpectrum (NormedField.valuation (K := K)) A := affineSpectrumHomeomorph
  let q : RelativeSpectrum (NormedField.valuation (K := K)) A →
      RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f :=
    fun a => map hU.fromSpec hg (E.symm a)
  have hqr : Set.range q = {y | y.1.point ∈ U} := by
    change Set.range ((map hU.fromSpec hg) ∘ E.symm) = _
    rw [E.symm.surjective.range_comp, range_map_of_isOpenImmersion, hU.opensRange_fromSpec]
  have hd := denseRange_map_open_of_integral_curve (NormedField.valuation (K := K)) f hX U
  change Dense (Set.range (map (v := NormedField.valuation) (fX := U.ι ≫ f) U.ι rfl)) at hd
  rw [range_map_of_isOpenImmersion, Scheme.Opens.opensRange_ι] at hd
  have hdq : DenseRange q := by
    change Dense (Set.range q)
    rw [hqr]
    exact hd
  exact hdq.preconnectedSpace ((continuous_map hU.fromSpec hg).comp E.symm.continuous)

/-- Native original local psh on an actual integral scheme curve obeys the
whole maximum principle, with its analytic preconnectedness derived internally. -/
theorem IsLocallyPSHOn.eq_of_isMaxOn_univ_integral_curve
    {f : X ⟶ Spec (CommRingCat.of K)} [LocallyOfFiniteType f]
    (hX : topologicalKrullDim X ≤ 1)
    {u : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f → EReal}
    (hu : IsLocallyPSHOn Set.univ u)
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
