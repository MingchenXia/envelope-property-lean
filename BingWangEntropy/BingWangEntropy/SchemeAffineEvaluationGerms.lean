import BingWangEntropy.SchemeAnalyticOverlapAlgebra
import Mathlib.Analysis.Analytic.Polynomial

/-! # Genuine regular-evaluation germs across actual affine charts

Families representing the same actual global scheme points are related by
literal fractions in a fixed actual principal refinement. Analyticity of
actual regular evaluations transfers through these genuine fraction germs.
-/

open CategoryTheory AlgebraicGeometry
open scoped Topology

set_option backward.isDefEq.respectTransparency false

namespace BingWangEntropy

noncomputable section

theorem complexAffineEvaluation_fractionGerm {X : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (c d : ComplexAffineChart X) (n : ℕ)
    (E : (Fin n → ℂ) → ComplexAffineChartPoint f c)
    (G : (Fin n → ℂ) → ComplexAffineChartPoint f d) (t : Fin n → ℂ)
    (hxy : (fun u => complexAffineChartPointMap f d (G u)) =ᶠ[𝓝 t]
      (fun u => complexAffineChartPointMap f c (E u)))
    (hG : letI := affinePointFieldAlgebra (d.map ≫ f)
      ∀ r : d.ring, ContinuousAt (fun u => affineSchemePointEquivOfStructure (d.map ≫ f) (G u) r) t)
    (a : c.ring) :
    letI := affinePointFieldAlgebra (c.map ≫ f)
    letI := affinePointFieldAlgebra (d.map ≫ f)
    ∃ r : d.ring, ∃ k : ℕ, ∃ b : d.ring,
      affineSchemePointEquivOfStructure (d.map ≫ f) (G t) r ≠ 0 ∧
      (fun u => affineSchemePointEquivOfStructure (c.map ≫ f) (E u) a) =ᶠ[𝓝 t]
        (fun u => affineSchemePointEquivOfStructure (d.map ≫ f) (G u) b /
          affineSchemePointEquivOfStructure (d.map ≫ f) (G u) r ^ k) := by
  let := affinePointFieldAlgebra (c.map ≫ f)
  let := affinePointFieldAlgebra (d.map ≫ f)
  obtain ⟨r, hr, q, _, _, hden⟩ :=
    exists_complexAffine_common_overlap_point f c d (E t) (G t) hxy.eq_of_nhds
  obtain ⟨k, b, hab⟩ := complexAffine_overlap_ringMap_fraction c d r hr a
  refine ⟨r, k, b, hden, ?_⟩
  have hU : IsOpen {z : ℂ | z ≠ 0} := isClosed_singleton.isOpen_compl
  have hnz : ∀ᶠ u in 𝓝 t, affineSchemePointEquivOfStructure (d.map ≫ f) (G u) r ≠ 0 :=
    Filter.Tendsto.eventually (p := fun z : ℂ => z ≠ 0) (hG r) (hU.mem_nhds hden)
  filter_upwards [hxy, hnz] with u hu hru
  exact complexAffine_common_overlap_eval_fraction f c d r hr (E u) (G u) hu hru a k b hab

theorem complexAffineEvaluation_analyticAt {X : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (c d : ComplexAffineChart X) (n : ℕ)
    (E : (Fin n → ℂ) → ComplexAffineChartPoint f c)
    (G : (Fin n → ℂ) → ComplexAffineChartPoint f d) (t : Fin n → ℂ)
    (hxy : (fun u => complexAffineChartPointMap f d (G u)) =ᶠ[𝓝 t]
      (fun u => complexAffineChartPointMap f c (E u)))
    (hG : letI := affinePointFieldAlgebra (d.map ≫ f)
      ∀ r : d.ring, AnalyticAt ℂ (fun u => affineSchemePointEquivOfStructure (d.map ≫ f) (G u) r) t)
    (a : c.ring) :
    letI := affinePointFieldAlgebra (c.map ≫ f)
    AnalyticAt ℂ (fun u => affineSchemePointEquivOfStructure (c.map ≫ f) (E u) a) t := by
  let := affinePointFieldAlgebra (c.map ≫ f)
  let := affinePointFieldAlgebra (d.map ≫ f)
  obtain ⟨r, k, b, hnz, hfrac⟩ := complexAffineEvaluation_fractionGerm f c d n E G t hxy
    (fun r => (hG r).continuousAt) a
  exact ((hG b).div ((hG r).pow k) (pow_ne_zero k hnz)).congr hfrac.symm

end

end BingWangEntropy
