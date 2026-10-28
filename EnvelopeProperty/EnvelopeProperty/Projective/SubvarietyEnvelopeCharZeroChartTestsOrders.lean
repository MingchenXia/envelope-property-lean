/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.DVRMappedIdealOrder
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroChartTestsEnvelope

/-!
# Actual original generators and chart DVR ideal orders

The whole mapped obstacle ideal has its DVR order attained by an original
obstacle generator. This relates the actual native affine ideal order to
the original obstacle potential without restricting any cone valuation.
-/

open scoped NNReal ENNReal Topology Polynomial

noncomputable section

namespace EnvelopeProperty.Char0

open IsDiscreteValuationRing

/-- An actual original generator, rather than only an arbitrary member of
its span, attains the finite order of the whole nonzero extended ideal. -/
theorem exists_generator_eq_dvrIdealOrder_map_span
    {R W : Type*} [CommRing R] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (ρ : R →+* W) (S : Set R) (hne : (Ideal.span S).map ρ ≠ ⊥) :
    ∃ s ∈ S, addVal W (ρ s) = dvrIdealOrder ((Ideal.span S).map ρ) := by
  classical
  have hfinite := dvrIdealOrder_ne_top_of_ne_bot ((Ideal.span S).map ρ) hne
  let r : ℕ := (dvrIdealOrder ((Ideal.span S).map ρ)).toNat
  have hr : (r : ℕ∞) = dvrIdealOrder ((Ideal.span S).map ρ) :=
    ENat.natCast_toNat hfinite
  by_contra hnone
  have hspan : Ideal.span S ≤ (IsLocalRing.maximalIdeal W ^ (r + 1)).comap ρ := by
    apply Ideal.span_le.mpr
    intro s hs
    apply (mem_dvr_maximalIdeal_pow_iff (r + 1) (ρ s)).mpr
    have hle : dvrIdealOrder ((Ideal.span S).map ρ) ≤ addVal W (ρ s) :=
      iInf₂_le (ρ s) (Ideal.mem_map_of_mem ρ (Ideal.subset_span hs))
    have hgt : (r : ℕ∞) < addVal W (ρ s) := by
      rw [hr]
      exact lt_of_not_ge fun hge => hnone ⟨s, hs, le_antisymm hge hle⟩
    simpa only [Nat.cast_add, Nat.cast_one] using ENat.natCast_add_one_le_iff.mpr hgt
  obtain ⟨s, hs, _, horder⟩ := exists_mem_eq_dvrIdealOrder_map ρ (Ideal.span S) hne
  have hcut : ((r + 1 : ℕ) : ℕ∞) ≤ addVal W (ρ s) :=
    (mem_dvr_maximalIdeal_pow_iff (r + 1) (ρ s)).mp (hspan hs)
  rw [horder, ← hr] at hcut
  have hnat : r + 1 ≤ r := by exact_mod_cast hcut
  omega

end EnvelopeProperty.Char0

namespace EnvelopeProperty.ProjSubvariety

open Char0
open ProjBerk (phiIdeal)

universe u

variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}

/-- The actual extended ideal order of the whole original dehomogenized
obstacle ideal gives a lower bound on its original analytic potential.
The original chart map and actual DVR map are retained in the formula. -/
theorem chartTest_dvrIdealOrder_le_phiIdeal_obstacleIdeal (j : X.ChartIdx)
    (V : BirationalDVR k (X.ChartRing j.1)) (b : ℕ) (hb : 0 < b)
    (htorus : ∀ F : X.ChartRing j.1, V.ord F = F.support.inf fun ℓ =>
      V.ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞))
    {d q : ℕ} {φ : X.an → ℝ}
    (hne : ((X.obstacleIdeal d φ q).map
      (Polynomial.mapRingHom (X.quotDehom j.1).toRingHom)).map V.toRing.toRingHom ≠ ⊥) :
    -(((b : ℝ)⁻¹ : ℝ) : EReal) *
      (dvrIdealOrder (((X.obstacleIdeal d φ q).map
        (Polynomial.mapRingHom (X.quotDehom j.1).toRingHom)).map V.toRing.toRingHom) : EReal) ≤
          phiIdeal (X.obstacleIdeal d φ q) (X.chartDivPoint j.1 V b).1 := by
  let ρ := Polynomial.mapRingHom (X.quotDehom j.1).toRingHom
  have hmap :
      (Ideal.span (X.obstacleSpace d φ q : Set (MvPolynomial (Fin (M + 1)) k)[X])).map
        (V.toRing.toRingHom.comp ρ) ≠ ⊥ := by
    change (X.obstacleIdeal d φ q).map (V.toRing.toRingHom.comp ρ) ≠ ⊥
    rw [← Ideal.map_map]
    exact hne
  obtain ⟨F, hF, horder⟩ := exists_generator_eq_dvrIdealOrder_map_span
    (V.toRing.toRingHom.comp ρ)
    (X.obstacleSpace d φ q : Set (MvPolynomial (Fin (M + 1)) k)[X]) hmap
  have horder' : V.ord (F.map (X.quotDehom j.1).toRingHom) =
      dvrIdealOrder (((X.obstacleIdeal d φ q).map ρ).map V.toRing.toRingHom) := by
    simpa [ρ, Ideal.map_map, BirationalDVR.ord, obstacleIdeal] using horder
  have h := chartTest_order_le_phiIdeal_obstacleIdeal j V b hb htorus hF
  rw [horder'] at h
  exact h

end EnvelopeProperty.ProjSubvariety
