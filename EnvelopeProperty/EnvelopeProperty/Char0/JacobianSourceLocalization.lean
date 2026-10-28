/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.JacobianBaseChangeGeneral
import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-!
# Genuine Jacobian ideals preserve the actual original source under localization

The quotient determinant vanishes on tuples of original source differentials,
so spanning extends that membership to every localized source tuple.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory Module Ideal
open scoped Classical

universe u

/-- Actual quotient multilinear extensionality extends submodule membership from tuples
of a spanning family to all tuples, including the empty index type. -/
theorem multilinearMap_mem_submodule_of_span_eq_top
    {R M N ι α : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Fintype ι]
    (g : α → M) (hg : Submodule.span R (Set.range g) = ⊤)
    (f : MultilinearMap R (fun _ : ι => M) N) (P : Submodule R N)
    (h : ∀ w : ι → α, f (fun i => g (w i)) ∈ P) (v : ι → M) : f v ∈ P := by
  have heq : P.mkQ.compMultilinearMap f = 0 := by
    apply MultilinearMap.ext_of_span_eq_top (g := fun {_ : ι} => g) (fun _ => hg)
    intro w
    change P.mkQ (f (fun i => g (w i))) = 0
    exact (Submodule.Quotient.mk_eq_zero P).mpr (h w)
  have hv := DFunLike.congr_fun heq v
  change P.mkQ (f v) = 0 at hv
  exact (Submodule.Quotient.mk_eq_zero P).mp hv

variable {k R S A : Type u} [CommRing k] [CommRing R] [CommRing S] [CommRing A]
  [Algebra k R] [Algebra k S] [Algebra k A] [Algebra R S] [Algebra R A] [Algebra S A]
  [IsScalarTower k R S] [IsScalarTower k S A] [IsScalarTower R S A] {n : ℕ}

/-- The genuine all-original-functions Jacobian ideal is unchanged by an actual source
localization. This retains the original source for principal Rees refinement nodes. -/
theorem affineRelativeJacobianIdeal_source_localization (M : Submonoid R) [IsLocalization M S]
    (bA : Basis (Fin n) A (KaehlerDifferential k A)) :
    affineRelativeJacobianIdeal (R := R) bA = affineRelativeJacobianIdeal (R := S) bA := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨w, rfl⟩
    have hmat : sourceFunctionDifferentialMatrix (R := R) bA w =
        sourceFunctionDifferentialMatrix (R := S) bA (fun i => algebraMap R S (w i)) := by
      ext i j
      simp only [sourceFunctionDifferentialMatrix, ← IsScalarTower.algebraMap_apply R S A]
    change (sourceFunctionDifferentialMatrix (R := R) bA w).det ∈ _
    rw [hmat]
    exact Ideal.subset_span ⟨_, rfl⟩
  · let I := affineRelativeJacobianIdeal (R := R) bA
    let f : MultilinearMap S (fun _ : Fin n => KaehlerDifferential k S) A :=
      (bA.det.toMultilinearMap.restrictScalars S).compLinearMap
        (fun _ => KaehlerDifferential.map k k S A)
    have hspan : Submodule.span S
        (Set.range fun r : R => KaehlerDifferential.D k S (algebraMap R S r)) = ⊤ := by
      simpa only [Function.comp_def, KaehlerDifferential.map_D] using
        (KaehlerDifferential.span_range_map_derivation_of_isLocalization
          (R := k) (S := R) (T := S) M)
    have hgen (w : Fin n → R) :
        f (fun i => KaehlerDifferential.D k S (algebraMap R S (w i))) ∈ I.restrictScalars S := by
      change bA.det (fun i => KaehlerDifferential.map k k S A
        (KaehlerDifferential.D k S (algebraMap R S (w i)))) ∈ I
      simp only [KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_apply R S A, Basis.det_apply]
      change (sourceFunctionDifferentialMatrix (R := R) bA w).det ∈ I
      exact Ideal.subset_span ⟨w, rfl⟩
    apply Ideal.span_le.mpr
    rintro _ ⟨w, rfl⟩
    have hw := multilinearMap_mem_submodule_of_span_eq_top _ hspan f (I.restrictScalars S)
      hgen (fun i => KaehlerDifferential.D k S (w i))
    change bA.det (fun i => KaehlerDifferential.map k k S A
      (KaehlerDifferential.D k S (w i))) ∈ I at hw
    simp only [KaehlerDifferential.map_D, Basis.det_apply] at hw
    exact hw

end EnvelopeProperty.Char0
