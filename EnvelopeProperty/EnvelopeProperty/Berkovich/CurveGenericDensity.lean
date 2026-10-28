/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.FiniteCurveLineParameter
import EnvelopeProperty.Berkovich.SpectrumLineInflation
import EnvelopeProperty.Berkovich.SpectrumFiniteFreeOpen
import EnvelopeProperty.Berkovich.SchemeRelativeValuedPoints
import Mathlib.RingTheory.Ideal.GoingUp

open scoped Polynomial NNReal Topology
open Polynomial Topology CategoryTheory AlgebraicGeometry
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {F : Type*} [Field F] (v : Valuation F ℝ≥0)

/-- Every positive original line inflation has zero support, derived from EVERY original polynomial. -/
theorem lineGaussInflation_supp_eq_bot_of_pos (x : RelativeSpectrum v F[X])
    (r : ℝ≥0) (hr : 0<r) : (lineGaussInflation x r).1.val.supp=⊥ := by
  apply le_antisymm
  · intro p hp
    change p=0
    by_contra hp0
    let q : F[X][X] := Polynomial.algEquivAevalXAddC (X : F[X]) (p.map C)
    have hlead : q.leadingCoeff=C p.leadingCoeff := by
      dsimp [q]
      rw [Polynomial.algEquivAevalXAddC_apply]
      change ((p.map C).comp (X+C (X : F[X]))).leadingCoeff = _
      rw [Polynomial.leadingCoeff_comp]
      · simp only [Polynomial.leadingCoeff_map_of_injective C_injective,
          Polynomial.leadingCoeff_X_add_C,one_pow,mul_one]
      · simp
    have hcoeff : x.1.val (q.coeff q.natDegree)=v p.leadingCoeff := by
      rw [coeff_natDegree,hlead]
      exact x.2 _
    have hb := Spectrum.le_gauss_val x.1 r q q.natDegree
    rw [hcoeff] at hb
    have hpos : 0<v p.leadingCoeff*r^q.natDegree :=
      mul_pos (pos_iff_ne_zero.mpr ((v.ne_zero_iff).mpr (leadingCoeff_ne_zero.mpr hp0))) (pow_pos hr _)
    have hz : val (lineGaussInflation x r) p=0 := hp
    change (gauss x r).1.val q=0 at hz
    exact (not_lt_of_ge (hz ▸ hb)) hpos
  · exact bot_le

/-- The ENTIRE original line zero-support locus is genuinely dense for every prescribed field valuation. -/
theorem dense_zeroSupport_line : Dense {x : RelativeSpectrum v F[X] | x.1.val.supp=⊥} := by
  intro x
  have h0 : (0 : ℝ≥0)∈closure (Set.Ioi (0 : ℝ≥0)) := by
    rw [closure_Ioi (0 : ℝ≥0)]
    exact Set.mem_Ici.mpr le_rfl
  have hm := mem_closure_image (continuous_lineGaussInflation x).continuousAt h0
  rw [lineGaussInflation_zero] at hm
  apply closure_mono ?_ hm
  rintro _ ⟨r,hr,rfl⟩
  exact lineGaussInflation_supp_eq_bot_of_pos v x r hr

/-- Actual open finite-free curve maps derive native zero-support density, without algebraic density. -/
theorem dense_zeroSupport_of_dimension_le_one {C : Type*} [CommRing C] [Algebra F C]
    [IsDomain C] [Algebra.FiniteType F C] [Ring.KrullDimLE 1 C] :
    Dense {x : RelativeSpectrum v C | x.1.val.supp=⊥} := by
  by_cases hC : IsField C
  · let := hC.toField
    intro x
    apply subset_closure
    apply le_antisymm
    · intro c hc
      change c=0
      change x.1.val c=0 at hc
      by_contra hcz
      exact ((x.1.val.ne_zero_iff).mpr hcz) hc
    · exact bot_le
  · obtain ⟨φ,_,hfin,hfree⟩ := exists_finiteFree_injective_polynomial_of_dimension_le_one F C hC
    let : Algebra F[X] C := φ.toRingHom.toAlgebra
    let : Module.Finite F[X] C := hfin
    have hd := (dense_zeroSupport_line v).preimage (isOpenMap_comap_of_finiteFree φ hfree hfin)
    apply hd.mono
    intro x hx
    have hc : x.1.val.supp.comap (algebraMap F[X] C)=⊥ := hx
    exact Ideal.eq_bot_of_comap_eq_bot hc

end EnvelopeProperty.Berkovich.RelativeSpectrum

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
universe u
variable {F C : Type u} [Field F] [CommRing C] [Algebra F C]
variable [IsDomain C] [Algebra.FiniteType F C] [Ring.KrullDimLE 1 C]

/-- Actual ORIGINAL native affine-curve points with generic scheme support are dense. -/
theorem dense_genericSupport_affine_of_dimension_le_one (v : Valuation F ℝ≥0) :
    Dense {y : RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap F C))) |
      y.1.point.asIdeal=⊥} := by
  let e := affineSpectrumHomeomorph (v := v) (A := C)
  have hd := (RelativeSpectrum.dense_zeroSupport_of_dimension_le_one (C := C) v).preimage e.isOpenMap
  apply hd.mono
  intro y hy
  have he : Spectrum.support (e y).1 = y.1.point :=
    ValuedPoint.support_toSpectrum (SchemeValuedPoint.toValuedPoint y.1)
  have hh := congrArg PrimeSpectrum.asIdeal he
  change (e y).1.val.supp=y.1.point.asIdeal at hh
  exact hh.symm.trans hy
end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
