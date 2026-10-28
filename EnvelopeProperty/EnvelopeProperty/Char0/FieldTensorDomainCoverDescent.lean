import EnvelopeProperty.Char0.SmoothAffineDomainCover
import EnvelopeProperty.Char0.CountableComplexModel
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.Ideal

/-! # Whole original ideal products descend from the actual tensor-domain charts -/

set_option autoImplicit false
noncomputable section
open scoped TensorProduct

namespace EnvelopeProperty.Char0.FieldTensorDomainCoverDescent

open SmoothAffineDomainCover
universe u v w

private theorem ideal_le_of_localization_maps
    {R : Type u} [CommRing R] {ι : Type v} (g : ι → R)
    (hg : Ideal.span (Set.range g) = ⊤) (K P : Ideal R)
    (h : ∀ i, K.map (algebraMap R (Localization.Away (g i))) ≤
      P.map (algebraMap R (Localization.Away (g i)))) : K ≤ P := by
  intro x hx
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem P (Set.range g) hg x
  rintro ⟨s, i, rfl⟩
  have hmem := h i (Ideal.mem_map_of_mem (algebraMap R (Localization.Away (g i))) hx)
  obtain ⟨s, hs, hmem⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers (g i)) (Localization.Away (g i)) P x).mp hmem
  obtain ⟨N, rfl⟩ := hs
  exact ⟨N, hmem⟩

/-- ANY whole original ideal-product containment is detected by all SAME actual
tensor/localization coefficient maps of a genuine unit principal cover. -/
theorem ideal_le_mul_iff_componentMaps
    {F L A : Type u} [Field F] [Field L] [CommRing A]
    [Algebra F L] [Algebra F A] {ι : Type v} (g : ι → L ⊗[F] A)
    (hg : Ideal.span (Set.range g) = ⊤) (K I J : Ideal A) :
    K ≤ I * J ↔ ∀ i,
      K.map (componentCoefficientMap (g i)) ≤
        I.map (componentCoefficientMap (g i)) * J.map (componentCoefficientMap (g i)) := by
  refine ⟨fun h i => ?_, fun h => ?_⟩
  · rw [← Ideal.map_mul]
    exact Ideal.map_mono h
  · let B := L ⊗[F] A
    let : Algebra A B := Algebra.TensorProduct.rightAlgebra
    let : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_linearEquiv A
      (A ⊗[F] L) (Algebra.TensorProduct.commRight F A L).symm.toLinearEquiv
    have hB : K.map (algebraMap A B) ≤ (I * J).map (algebraMap A B) := by
      apply ideal_le_of_localization_maps g hg
      intro i
      rw [Ideal.map_map, Ideal.map_map]
      change K.map (componentCoefficientMap (g i)) ≤
        (I * J).map (componentCoefficientMap (g i))
      rw [Ideal.map_mul]
      exact h i
    have hc := Ideal.comap_mono (f := algebraMap A B) hB
    simpa only [Ideal.comap_map_eq_self_of_faithfullyFlat] using hc

/-- The genuine countable-field embedding and SAME finite smooth integral complex
principal cover jointly detect EVERY original ideal-product containment. -/
theorem exists_complex_domain_cover_detects_ideal_products
    (F A : Type) [Field F] [CharZero F] [Countable F]
    [CommRing A] [Algebra F A] [Algebra.Smooth F A] [IsDomain A] :
    ∃ ι : F →+* ℂ,
      let : Algebra F ℂ := ι.toAlgebra
      ∃ (N : ℕ) (g : Fin N → ℂ ⊗[F] A),
        Ideal.span (Set.range g) = ⊤ ∧
        (∀ i, IsDomain (Localization.Away (g i)) ∧
          Algebra.Smooth ℂ (Localization.Away (g i))) ∧
        (∀ K I J : Ideal A, K ≤ I * J ↔ ∀ i,
          K.map (componentCoefficientMap (g i)) ≤
            I.map (componentCoefficientMap (g i)) * J.map (componentCoefficientMap (g i))) ∧
        (∀ i (I : Ideal A), I ≠ ⊥ → I.map (componentCoefficientMap (g i)) ≠ ⊥) := by
  obtain ⟨ι⟩ := CountableComplexModel.nonempty_complex_embedding F
  let : Algebra F ℂ := ι.toAlgebra
  obtain ⟨N, g, hg, hdomain, _hcover⟩ :=
    exists_fieldTensor_principal_domain_cover (F := F) (L := ℂ) (A₀ := A)
  refine ⟨ι, N, g, hg, hdomain, fun K I J =>
    ideal_le_mul_iff_componentMaps g hg K I J, ?_⟩
  intro i I hI
  let : IsDomain (Localization.Away (g i)) := (hdomain i).1
  exact map_original_ideal_ne_bot (g i) I hI

end EnvelopeProperty.Char0.FieldTensorDomainCoverDescent
