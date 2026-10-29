import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Localization.Away.Basic

/-! # A finite original algebra map becomes surjective near its central quotient

The localization parameter is produced by the determinant form of Nakayama,
not supplied as a surjectivity or cokernel-vanishing certificate.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped Pointwise
universe u v
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodAlgebra

/-- A finite ORIGINAL ring map which surjects onto its actual central quotient
internally produces a SAME-map surjective localization containing the full central divisor. -/
theorem exists_localization_surjective {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.Finite) (t : A)
    (h₀ : Function.Surjective
      ((Ideal.Quotient.mk (Ideal.span {φ t})).comp φ)) :
    ∃ r : A, r - 1 ∈ Ideal.span {t} ∧
      Function.Surjective (Localization.awayMap φ r) := by
  let : Algebra A B := φ.toAlgebra
  let : Module.Finite A B := hφ
  let N : Submodule A B := LinearMap.range (Algebra.linearMap A B)
  have htop : (⊤ : Submodule A B) ≤ N ⊔ (Ideal.span {t}) • ⊤ := by
    intro b _
    obtain ⟨a, ha⟩ := h₀ (Ideal.Quotient.mk (Ideal.span {φ t}) b)
    change Ideal.Quotient.mk (Ideal.span {φ t}) (φ a) =
      Ideal.Quotient.mk (Ideal.span {φ t}) b at ha
    have hd : b - φ a ∈ Ideal.span {φ t} := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, ha, sub_self]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hd
    have htc : t • c ∈ (Ideal.span {t} : Ideal A) • (⊤ : Submodule A B) :=
      Submodule.smul_mem_smul (Ideal.subset_span (by simp)) (by trivial)
    apply Submodule.mem_sup.mpr
    refine ⟨φ a, ?_, t • c, htc, ?_⟩
    · exact ⟨a, rfl⟩
    · change φ a + φ t * c = b
      rw [← hc]
      abel
  obtain ⟨r, hr, hR⟩ :=
    Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
      (I := Ideal.span {t}) (N := N) (N' := ⊤) (P := ⊤)
      Module.Finite.fg_top le_rfl htop
  refine ⟨r, hr, Localization.awayMap_surjective_iff.mpr ?_⟩
  intro b
  have hmem : r • b ∈ N :=
    hR (Submodule.smul_mem_pointwise_smul b r ⊤ (by trivial))
  obtain ⟨a, ha⟩ := hmem
  refine ⟨a, 1, ?_⟩
  change φ a = φ r * b at ha
  simpa only [pow_one] using ha

/-- The SAME finite original affine map has an actual closed-immersion localization,
with parameter congruent to one along the entire original central divisor. -/
theorem exists_closedImmersion_localization {A B : Type u}
    [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.Finite) (t : A)
    (h₀ : Function.Surjective
      ((Ideal.Quotient.mk (Ideal.span {φ t})).comp φ)) :
    ∃ r : A, r - 1 ∈ Ideal.span {t} ∧
      IsClosedImmersion (Spec.map (CommRingCat.ofHom (Localization.awayMap φ r))) := by
  obtain ⟨r, hr, hs⟩ := exists_localization_surjective φ hφ t h₀
  exact ⟨r, hr, IsClosedImmersion.spec_of_surjective _ hs⟩

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodAlgebra
