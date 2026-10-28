/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.AsymptoticDivisorialBound
import EnvelopeProperty.Char0.DVRMappedIdealOrder
import EnvelopeProperty.Char0.SchemeAsymptoticMultiplierIdeal
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroCore

/-!
# Finite-index discrepancy bounds from the actual asymptotic multiplier ideal

The finite sequence index is selected from the genuine normalized-order
infimum. The bound retains the original source algebra, the actual full
asymptotic ideal, the intrinsic original-source Jacobian, all multiplier
degrees including zero, and the infinite order of the zero element.
-/

open scoped NNReal ENNReal Topology Polynomial

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory IsDiscreteValuationRing Set TopologicalSpace

/-- A positive original index approximates the actual normalized-order
infimum with a fixed error after multiplication by any natural index. -/
theorem exists_positive_index_normalized_order_lt (N : ℕ → ℝ)
    (hN : ∀ q : ℕ, 0 < q → 0 ≤ N q) (m : ℕ) :
    ∃ q : ℕ, 0 < q ∧ (m : ℝ) / q * N q <
      (m : ℝ) * sInf (Set.range fun r : {r : ℕ // 0 < r} => N r.val / r.val) + 1 := by
  by_cases hm : m = 0
  · exact ⟨1, one_pos, by simp [hm]⟩
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hne : (Set.range fun r : {r : ℕ // 0 < r} => N r.val / r.val).Nonempty :=
    ⟨_, ⟨⟨1, one_pos⟩, rfl⟩⟩
  have hbdd : BddBelow (Set.range fun r : {r : ℕ // 0 < r} => N r.val / r.val) := by
    refine ⟨0, ?_⟩
    rintro x ⟨q, rfl⟩
    exact div_nonneg (hN q.val q.property) (Nat.cast_nonneg q.val)
  obtain ⟨x, hx, hlt⟩ := (csInf_lt_iff hbdd hne).mp
    (lt_add_of_pos_right (sInf (Set.range fun r : {r : ℕ // 0 < r} => N r.val / r.val))
      (div_pos one_pos hmR))
  obtain ⟨q, rfl⟩ := hx
  refine ⟨q.val, q.property, ?_⟩
  calc (m : ℝ) / q.val * N q.val = (m : ℝ) * (N q.val / q.val) := by ring
    _ < (m : ℝ) * (sInf (Set.range fun r : {r : ℕ // 0 < r} => N r.val / r.val) +
        1 / (m : ℝ)) := mul_lt_mul_of_pos_left hlt hmR
    _ = _ := by field_simp

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
variable (C V : Subalgebra k K) [IsFractionRing C K] [IsNoetherianRing C]
variable [IsDiscreteValuationRing V] [IsFractionRing V K] [Algebra.EssFiniteType k V]
variable (hCV : C ≤ V)

/-- The actual asymptotic multiplier discrepancy estimate supplies one
original positive sequence index that works for every original member.
The multiplier degree zero is included. -/
theorem exists_asymptoticMultiplierIdeal_element_order_bound
    {J : ℕ → Ideal C} (hJ : ∀ a b, J a * J b ≤ J (a + b))
    (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) :
    ∃ q : ℕ, 0 < q ∧ ∀ f ∈ asymptoticMultiplierIdeal C J hne m, ∀ ν : ℕ,
      addVal V (Subalgebra.inclusion hCV f) = ν →
        (m : ℝ) / q *
          ((dvrIdealOrder ((J q).map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℝ) -
            (2 + (dvrIdealOrder (intrinsicDVRSourceJacobianIdeal C V hCV)).toNat : ℝ) ≤ ν := by
  let N : ℕ → ℝ := fun q =>
    ((dvrIdealOrder ((J q).map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℝ)
  obtain ⟨q, hq, happrox⟩ := exists_positive_index_normalized_order_lt N
    (fun _ _ => Nat.cast_nonneg _) m
  change (m : ℝ) / q * N q <
    (m : ℝ) * asymptoticDivisorialOrder C V hCV J hne + 1 at happrox
  refine ⟨q, hq, fun f hf ν hν => ?_⟩
  have hf0 : f ≠ 0 := by
    intro hfzero
    rw [hfzero, map_zero, addVal_zero] at hν
    exact ENat.natCast_ne_top ν hν.symm
  have hbound := asymptoticMultiplierIdeal_divisorial_bound C V hCV hJ hne m f hf hf0
  rw [hν, ENat.toNat_natCast] at hbound
  change (m : ℝ) / q * N q -
    (2 + (dvrIdealOrder (intrinsicDVRSourceJacobianIdeal C V hCV)).toNat : ℝ) ≤ ν
  linarith

/-- The same actual index works for every lower bound on the orders of
members of the original sequence ideal. This is the elementwise interface
used by the cone-potential conversion lemma. -/
theorem exists_asymptoticMultiplierIdeal_lower_order_bound
    {J : ℕ → Ideal C} (hJ : ∀ a b, J a * J b ≤ J (a + b))
    (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) :
    ∃ q : ℕ, 0 < q ∧ ∀ o : ℕ,
      (∀ g ∈ J q, (o : ℕ∞) ≤ addVal V (Subalgebra.inclusion hCV g)) →
      ∀ f ∈ asymptoticMultiplierIdeal C J hne m, ∀ ν : ℕ,
        addVal V (Subalgebra.inclusion hCV f) = ν →
          (m : ℝ) / q * o -
            (2 + (dvrIdealOrder (intrinsicDVRSourceJacobianIdeal C V hCV)).toNat : ℝ) ≤ ν := by
  obtain ⟨q, hq, hbound⟩ :=
    exists_asymptoticMultiplierIdeal_element_order_bound C V hCV hJ hne m
  refine ⟨q, hq, fun o ho f hf ν hν => ?_⟩
  have hmap : (J q).map (Subalgebra.inclusion hCV).toRingHom ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (Subalgebra.inclusion_injective hCV)).mp.mt (hne q hq)
  obtain ⟨g, hg, _, hgorder⟩ :=
    exists_mem_eq_dvrIdealOrder_map (Subalgebra.inclusion hCV).toRingHom (J q) hmap
  have hoorder : (o : ℕ∞) ≤
      dvrIdealOrder ((J q).map (Subalgebra.inclusion hCV).toRingHom) := by
    rw [← hgorder]
    exact ho g hg
  have hfinite := dvrIdealOrder_map_inclusion_ne_top C V hCV (J q) (hne q hq)
  rw [← ENat.natCast_toNat hfinite] at hoorder
  have hoNat : o ≤
      (dvrIdealOrder ((J q).map (Subalgebra.inclusion hCV).toRingHom)).toNat := by
    exact_mod_cast hoorder
  have hoReal : (o : ℝ) ≤
      ((dvrIdealOrder ((J q).map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℝ) := by
    exact_mod_cast hoNat
  have hmul := mul_le_mul_of_nonneg_left hoReal
    (div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg q))
  linarith [hbound f hf ν hν]

/-- The finite-index bound in `EReal`, retaining zero elements and their
infinite order. No finite-order or nonzero premise is placed on the member. -/
theorem exists_asymptoticMultiplierIdeal_ereal_order_bound
    {J : ℕ → Ideal C} (hJ : ∀ a b, J a * J b ≤ J (a + b))
    (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ q : ℕ, 0 < q ∧ ∀ f ∈ asymptoticMultiplierIdeal C J hne m,
      ((-a : ℝ) : EReal) * (addVal V (Subalgebra.inclusion hCV f) : EReal) ≤
        (((m : ℝ) / q : ℝ) : EReal) *
          (((-a : ℝ) : EReal) *
            (dvrIdealOrder ((J q).map (Subalgebra.inclusion hCV).toRingHom) : EReal)) +
              ((a * (2 + (dvrIdealOrder
                (intrinsicDVRSourceJacobianIdeal C V hCV)).toNat) : ℝ) : EReal) := by
  obtain ⟨q, hq, hbound⟩ :=
    exists_asymptoticMultiplierIdeal_element_order_bound C V hCV hJ hne m
  refine ⟨q, hq, fun f hf => ?_⟩
  by_cases hf0 : f = 0
  · rw [hf0, map_zero, addVal_zero]
    change ((-a : ℝ) : EReal) * ⊤ ≤ _
    rw [EReal.coe_mul_top_of_neg (neg_neg_of_pos ha)]
    exact bot_le
  · have hfV : Subalgebra.inclusion hCV f ≠ 0 := by
      intro hz
      exact hf0 ((map_eq_zero_iff _ (Subalgebra.inclusion_injective hCV)).mp hz)
    obtain ⟨ν, hν⟩ := ENat.ne_top_iff_exists.mp ((addVal_eq_top_iff).not.mpr hfV)
    have hfinite := dvrIdealOrder_map_inclusion_ne_top C V hCV (J q) (hne q hq)
    have hNcoe :
        (dvrIdealOrder ((J q).map (Subalgebra.inclusion hCV).toRingHom) : EReal) =
          (((dvrIdealOrder ((J q).map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℝ) :
            EReal) := by
      rw [← ENat.natCast_toNat hfinite]
      norm_cast
    rw [hν.symm, show ((ν : ℕ∞) : EReal) = ((ν : ℝ) : EReal) by norm_cast,
      hNcoe, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    have h := hbound f hf ν hν.symm
    nlinarith

variable {Y : Scheme.{u}} [IsIntegral Y]

/-- Finite-index logarithmic comparison on the original scheme, for all
sections of the full asymptotic ideal on an original nonempty affine open.
The literal composite from original sections into the actual DVR is retained. -/
theorem exists_schemeAsymptoticMultiplierIdealSheaf_ereal_order_bound
    (f : Y ⟶ Spec (.of k)) [Smooth f]
    {J : ℕ → Y.IdealSheafData} (hJ : ∀ r s, J r * J s ≤ J (r + s))
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint Y) ≠ ⊥)
    (m : ℕ) (U : Y.affineOpens) [Nonempty U.1]
    (W : letI := f.stalkAlgebra (genericPoint Y); Subalgebra k Y.functionField)
    [IsDiscreteValuationRing W] [IsFractionRing W Y.functionField]
    [Algebra.EssFiniteType k W]
    (hUW : letI := f.stalkAlgebra (genericPoint Y);
      f.sectionsFunctionFieldSubalgebra U.1 ≤ W) {a : ℝ} (ha : 0 < a) :
    letI := f.stalkAlgebra (genericPoint Y)
    letI := f.sectionsAlgebra U.1
    let D := f.sectionsFunctionFieldSubalgebra U.1
    let e := f.sectionsFunctionFieldEquiv U.1
    let g := (Subalgebra.inclusion hUW).toRingHom.comp e.toRingHom
    ∃ q : ℕ, 0 < q ∧
      ∀ s ∈ (schemeAsymptoticMultiplierIdealSheaf f J hne m).ideal U,
        ((-a : ℝ) : EReal) * (addVal W (g s) : EReal) ≤
          (((m : ℝ) / q : ℝ) : EReal) *
            (((-a : ℝ) : EReal) * (dvrIdealOrder (((J q).ideal U).map g) : EReal)) +
              ((a * (2 + (dvrIdealOrder
                (intrinsicDVRSourceJacobianIdeal D W hUW)).toNat) : ℝ) : EReal) := by
  let _ := f.stalkAlgebra (genericPoint Y)
  let _ := f.sectionsAlgebra U.1
  let D := f.sectionsFunctionFieldSubalgebra U.1
  let e := f.sectionsFunctionFieldEquiv U.1
  let A : ℕ → Ideal D := fun q => ((J q).ideal U).map e.toRingHom
  have hA (q : ℕ) (hq : 0 < q) : A q ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective e.injective).mp.mt
      (affineIdeal_ne_bot_of_generic_stalk_ne_bot (J q) (hne q hq) U)
  have hgraded (r s : ℕ) : A r * A s ≤ A (r + s) := by
    dsimp only [A]
    rw [← Ideal.map_mul]
    exact Ideal.map_mono ((hJ r s) U)
  have : IsFractionRing D Y.functionField :=
    f.sectionsFunctionFieldSubalgebra_isFractionRing U.1 U.2
  have hsm : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k D))) :=
    f.smooth_sectionsFunctionFieldSubalgebra U.1 U.2
  have : Algebra.Smooth k D := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm)
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing k D
  obtain ⟨q, hq, hbound⟩ :=
    exists_asymptoticMultiplierIdeal_ereal_order_bound D W hUW hgraded hA m ha
  refine ⟨q, hq, fun s hs => ?_⟩
  rw [schemeAsymptoticMultiplierIdealSheaf_ideal_nonempty f J hne m U] at hs
  have hmem : e s ∈ asymptoticMultiplierIdeal D A hA m := hs
  simpa [A, D, e, Ideal.map_map] using hbound (e s) hmem

end EnvelopeProperty.Char0
