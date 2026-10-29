/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.EtaleDerivationJacobian
import EnvelopeProperty.Char0.JacobianSourceLocalization

/-!
# Actual derivative determinant ideals preserve the original source under localization

The actual universal differential spanning theorem extends determinant
membership from all original source tuples to every localized tuple.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open Module Ideal
open scoped Classical

universe u

variable {k R S A : Type u} [CommRing k] [CommRing R] [CommRing S] [CommRing A]
  [Algebra k R] [Algebra k S] [Algebra k A] [Algebra R S] [Algebra S A]
  [IsScalarTower k R S] [IsScalarTower k S A] {n : ℕ}

/-- Every actual original-source derivative determinant ideal is unchanged by an actual
source localization; no selected tuple subfamily replaces the original source. -/
theorem derivationSourceJacobianIdeal_source_localization
    (M : Submonoid R) [IsLocalization M S] (D : Fin n → Derivation k S A) :
    derivationSourceJacobianIdeal (R := R) D =
      derivationSourceJacobianIdeal (R := S) D := by
  let f : MultilinearMap S (fun _ : Fin n => KaehlerDifferential k S) A :=
    (((Pi.basisFun A (Fin n)).det.toMultilinearMap).restrictScalars S).compLinearMap
      (fun _ => LinearMap.pi fun j => (D j).liftKaehlerDifferential)
  have hf (w : Fin n → S) :
      f (fun i => KaehlerDifferential.D k S (w i)) =
        (Matrix.of fun i j => D j (w i)).det := by
    change (Pi.basisFun A (Fin n)).det
      (fun i j => (D j).liftKaehlerDifferential (KaehlerDifferential.D k S (w i))) = _
    simp only [Derivation.liftKaehlerDifferential_comp_D, Basis.det_apply]
    exact Matrix.det_transpose _
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact Ideal.subset_span ⟨fun i => algebraMap R S (w i), rfl⟩
  · let I := derivationSourceJacobianIdeal (R := R) D
    have hspan : Submodule.span S
        (Set.range fun r : R => KaehlerDifferential.D k S (algebraMap R S r)) = ⊤ := by
      simpa only [Function.comp_def, KaehlerDifferential.map_D] using
        (KaehlerDifferential.span_range_map_derivation_of_isLocalization
          (R := k) (S := R) (T := S) M)
    have hgen (w : Fin n → R) :
        f (fun i => KaehlerDifferential.D k S (algebraMap R S (w i))) ∈ I.restrictScalars S := by
      rw [hf]
      exact Ideal.subset_span ⟨w, rfl⟩
    apply Ideal.span_le.mpr
    rintro _ ⟨w, rfl⟩
    have h := multilinearMap_mem_submodule_of_span_eq_top _ hspan f (I.restrictScalars S)
      hgen (fun i => KaehlerDifferential.D k S (w i))
    rwa [hf] at h

end EnvelopeProperty.Char0
