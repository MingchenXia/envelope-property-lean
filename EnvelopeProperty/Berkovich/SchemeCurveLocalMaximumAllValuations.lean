/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.IntegralCurveLocalMaximumAllValuations
import EnvelopeProperty.Berkovich.SchemeCurveGenericDensity
import EnvelopeProperty.Berkovich.SchemeAffineLocalPSH

/-! # Every valuation retains actual original native integral-curve local maxima -/

open scoped NNReal Topology
open Topology Filter CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {K : Type u} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
  {X : Scheme.{u}} [IsIntegral X]

/-- Genuine affine charts carry the unchanged intrinsic class and actual maximum
to a derived integral affine curve, then return equality in the original topology. -/
theorem IsLocallyPSHOn.eventually_eq_of_isLocalMax_integral_curve_allValuations
    {f : X ⟶ Spec (CommRingCat.of K)} [LocallyOfFiniteType f]
    (hX : topologicalKrullDim X ≤ 1)
    {Ω : Set (RelativeSchemeValuedPoint w f)} {u : RelativeSchemeValuedPoint w f → EReal}
    (hu : IsLocallyPSHOn Ω u)
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
  have hchart : IsLocallyPSHOn (map hU.fromSpec hg ⁻¹' Ω)
      (fun z => u (map hU.fromSpec hg z)) := by
    have h := hu.comp_mapOverBase (RingHom.id K) (fun _ => rfl) hU.fromSpec
      (by simpa using hg)
    exact h
  have hlocal := hchart.to_affineSpectrum
  change RelativeSpectrum.IsLocallyPSHOn (q ⁻¹' Ω) (fun z => u (q z)) at hlocal
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
