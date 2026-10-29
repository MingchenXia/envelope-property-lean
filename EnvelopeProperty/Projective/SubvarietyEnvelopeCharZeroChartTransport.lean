/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroChartTransportCore
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroOrders

/-!
# Genuine scheme multiplier estimates in actual original chart coordinates

The given algebra isomorphism is an actual chart presentation. Its true
fraction-field extension constructs the DVR used by the original scheme
estimate. The entire original ideal sequence and affine sections are
retained, and the discrepancy is fixed before the multiplier index.
-/

open scoped NNReal ENNReal Topology Polynomial

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory IsDiscreteValuationRing TopologicalSpace

universe u v

variable {k : Type u} [Field k] [CharZero k]
variable {Y : Scheme.{u}} [IsIntegral Y]
variable {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]

/-- A genuine affine chart isomorphism transports the actual whole original
scheme estimate to the original chart DVR. The constant is produced from
the genuine source Jacobian and is independent of the multiplier degree.
Both degree zero and infinite orders of zero sections are retained. -/
theorem exists_schemeAsymptoticMultiplierIdeal_chart_order_bound
    (f : Y ⟶ Spec (.of k)) [Smooth f]
    {J : ℕ → Y.IdealSheafData} (hJ : ∀ r s, J r * J s ≤ J (r + s))
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint Y) ≠ ⊥)
    (U : Y.affineOpens) [Nonempty U.1]
    (eA : letI := f.sectionsAlgebra U.1; Γ(Y, U) ≃ₐ[k] A)
    (V : BirationalDVR k A) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ m : ℕ, ∀ a : ℝ, 0 < a → ∃ q : ℕ, 0 < q ∧
      ∀ s ∈ (schemeAsymptoticMultiplierIdealSheaf f J hne m).ideal U,
        ((-a : ℝ) : EReal) * (V.ord (eA s) : EReal) ≤
          (((m : ℝ) / q : ℝ) : EReal) *
            (((-a : ℝ) : EReal) *
              (dvrIdealOrder ((((J q).ideal U).map eA.toRingHom).map V.toRing.toRingHom) :
                EReal)) + ((a * D : ℝ) : EReal) := by
  let _ := f.stalkAlgebra (genericPoint Y)
  let _ := f.sectionsAlgebra U.1
  let C := f.sectionsFunctionFieldSubalgebra U.1
  let es := f.sectionsFunctionFieldEquiv U.1
  have : IsFractionRing C Y.functionField :=
    f.sectionsFunctionFieldSubalgebra_isFractionRing U.1 U.2
  let e : A ≃ₐ[k] C := eA.symm.trans es
  let W := ChartDVRTransport.ring C e V
  have hCW : C ≤ W := ChartDVRTransport.source_le C e V
  let D : ℝ := 2 + (dvrIdealOrder (intrinsicDVRSourceJacobianIdeal C W hCW)).toNat
  have hsource (s : Γ(Y, U)) :
      addVal W (Subalgebra.inclusion hCW (es s)) = V.ord (eA s) := by
    simpa [e] using ChartDVRTransport.order_source C e V (eA s)
  have hecomp : e.toRingHom.comp eA.toRingHom = es.toRingHom := by
    apply RingHom.ext
    intro s
    simp [e]
  have hsideal (I : Ideal Γ(Y, U)) :
      (I.map eA.toRingHom).map e.toRingHom = I.map es.toRingHom := by
    rw [Ideal.map_map, hecomp]
  have horder (I : Ideal Γ(Y, U)) :
      dvrIdealOrder (I.map ((Subalgebra.inclusion hCW).toRingHom.comp es.toRingHom)) =
        dvrIdealOrder ((I.map eA.toRingHom).map V.toRing.toRingHom) := by
    have h := ChartDVRTransport.ideal_order C e V (I.map eA.toRingHom)
    rw [hsideal] at h
    simpa only [Ideal.map_map] using h
  refine ⟨D, by dsimp only [D]; positivity, fun m a ha => ?_⟩
  obtain ⟨q, hq, hbound⟩ :=
    exists_schemeAsymptoticMultiplierIdealSheaf_ereal_order_bound f hJ hne m U W hCW ha
  refine ⟨q, hq, fun s hs => ?_⟩
  have h := hbound s hs
  change ((-a : ℝ) : EReal) * (addVal W (Subalgebra.inclusion hCW (es s)) : EReal) ≤
    (((m : ℝ) / q : ℝ) : EReal) *
      (((-a : ℝ) : EReal) *
        (dvrIdealOrder (((J q).ideal U).map
          ((Subalgebra.inclusion hCW).toRingHom.comp es.toRingHom)) : EReal)) +
            ((a * D : ℝ) : EReal) at h
  rw [hsource, horder] at h
  exact h

end EnvelopeProperty.Char0
