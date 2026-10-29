import EnvelopeProperty.AlgGeom.CoordinateTupleComplex
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorQuasicoherent
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Bounded exact resolutions by original coordinate tuples

The full family of short exact kernel sequences can be truncated at any length.
Its finite-sum terms and all kernels are quasicoherent when the coefficient is.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u v
namespace EnvelopeProperty.CoordinateTupleResolution
section Generic
variable {C : Type u} [Category.{v} C] [Abelian C]

private def syzygy (D : ChainComplex C ℕ) : ℕ → C
  | 0 => D.X 0
  | n + 1 => kernel (D.d (n + 1) n)

private def inclusion (D : ChainComplex C ℕ) (n : ℕ) : syzygy D (n + 1) ⟶ D.X (n + 1) :=
  kernel.ι (D.d (n + 1) n)

private def projection (D : ChainComplex C ℕ) : ∀ n, D.X (n + 1) ⟶ syzygy D n
  | 0 => D.d 1 0
  | n + 1 => kernel.lift (D.d (n + 1) n) (D.d (n + 2) (n + 1)) (D.d_comp_d _ _ _)

private theorem inclusion_projection (D : ChainComplex C ℕ) (n : ℕ) :
    inclusion D n ≫ projection D n = 0 := by
  cases n with
  | zero => exact kernel.condition _
  | succ n =>
    change kernel.ι (D.d (n + 2) (n + 1)) ≫
      kernel.lift (D.d (n + 1) n) (D.d (n + 2) (n + 1)) _ = 0
    apply (cancel_mono (kernel.ι (D.d (n + 1) n))).mp
    simp only [Category.assoc, kernel.lift_ι, kernel.condition, zero_comp]

private theorem shortExact (D : ChainComplex C ℕ) (h0 : Epi (D.d 1 0))
    (hD : ∀ n, (ShortComplex.mk (D.d (n + 2) (n + 1)) (D.d (n + 1) n)
      (D.d_comp_d _ _ _)).Exact) (n : ℕ) :
    (ShortComplex.mk (inclusion D n) (projection D n) (inclusion_projection D n)).ShortExact := by
  let := h0
  cases n with
  | zero =>
    change (ShortComplex.kernelSequence (D.d 1 0)).ShortExact
    exact { exact := ShortComplex.kernelSequence_exact (D.d 1 0), epi_g := h0 }
  | succ n =>
    let S := ShortComplex.mk (inclusion D (n + 1)) (projection D (n + 1))
      (inclusion_projection D (n + 1))
    let T := ShortComplex.kernelSequence (D.d (n + 2) (n + 1))
    let φ : S ⟶ T :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := kernel.ι (D.d (n + 1) n)
        comm₁₂ := by
          change 𝟙 _ ≫ kernel.ι _ = kernel.ι _ ≫ 𝟙 _
          simp only [Category.id_comp, Category.comp_id]
        comm₂₃ := by
          change 𝟙 _ ≫ D.d (n + 2) (n + 1) =
            kernel.lift (D.d (n + 1) n) (D.d (n + 2) (n + 1)) _ ≫ kernel.ι _
          simp only [Category.id_comp, kernel.lift_ι] }
    have : Epi φ.τ₁ := by change Epi (𝟙 (kernel (D.d (n + 2) (n + 1)))); infer_instance
    have : IsIso φ.τ₂ := by change IsIso (𝟙 (D.X (n + 2))); infer_instance
    have : Mono φ.τ₃ := by change Mono (kernel.ι (D.d (n + 1) n)); infer_instance
    have : Mono S.f := by change Mono (kernel.ι (D.d (n + 2) (n + 1))); infer_instance
    have : Epi S.g := (hD n).epi_kernelLift
    change S.ShortExact
    exact ShortComplex.ShortExact.mk'
      ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
        (ShortComplex.kernelSequence_exact _)) inferInstance inferInstance


private theorem shortExact_aug {A : C} (D : ChainComplex C ℕ)
    (h0 : Epi (D.d 1 0)) (e : D.X 0 ≅ A) :
    (ShortComplex.mk (kernel.ι (D.d 1 0)) (D.d 1 0 ≫ e.hom)
      (by rw [← Category.assoc, kernel.condition, zero_comp])).ShortExact := by
  let S := ShortComplex.kernelSequence (D.d 1 0)
  let T := ShortComplex.mk (kernel.ι (D.d 1 0)) (D.d 1 0 ≫ e.hom)
    (by rw [← Category.assoc, kernel.condition, zero_comp])
  let iso : S ≅ T := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e
    (by change 𝟙 _ ≫ kernel.ι _ = kernel.ι _ ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id])
    (by change 𝟙 _ ≫ (D.d 1 0 ≫ e.hom) = D.d 1 0 ≫ e.hom
        exact Category.id_comp _)
  exact ShortComplex.shortExact_of_iso iso
    { exact := ShortComplex.kernelSequence_exact (D.d 1 0), epi_g := h0 }
end Generic

open CategoryTheory.MonoidalCategory MvPolynomial CoordinateTupleComplex
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {σ : Type} [Finite σ]

/-- The kernel terms of the original coordinate resolution, with literal M(t) in degree zero. -/
def coordinateSyzygy (M : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) (t : ℤ) :
    ℕ → (Proj (homogeneousSubmodule σ R)).Modules
  | 0 => M ⊗ coordinateHyperplaneTwist (R := R) j t
  | n + 1 => syzygy (coordinateTupleComplex M j id t) (n + 1)

/-- The inclusion of each actual coordinate kernel into its finite-sum term. -/
def coordinateKernelInclusion (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j : σ) (t : ℤ) (n : ℕ) :
    coordinateSyzygy M j t (n + 1) ⟶ (coordinateTupleComplex M j id t).X (n + 1) :=
  inclusion (coordinateTupleComplex M j id t) n

/-- The coordinate differential onto its preceding kernel, with literal original augmentation at zero. -/
def coordinateKernelProjection (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j : σ) (t : ℤ) : ∀ n, (coordinateTupleComplex M j id t).X (n + 1) ⟶ coordinateSyzygy M j t n
  | 0 => coordinateTupleAugmentation M j id t
  | n + 1 => projection (coordinateTupleComplex M j id t) (n + 1)

/-- Successive coordinate kernel maps have zero composite. -/
theorem coordinateKernel_zero (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j : σ) (t : ℤ) (n : ℕ) :
    coordinateKernelInclusion M j t n ≫ coordinateKernelProjection M j t n = 0 := by
  cases n with
  | zero =>
    change kernel.ι _ ≫ (_ ≫ (coordinateTupleAugmentIso M j id t).hom) = 0
    rw [← Category.assoc, kernel.condition, zero_comp]
  | succ n => exact inclusion_projection (coordinateTupleComplex M j id t) (n + 1)

/-- All short exact sequences of the actual coordinate resolution, including its literal original target. -/
theorem coordinateKernel_shortExact (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j : σ) (t : ℤ) (n : ℕ) :
    (ShortComplex.mk (coordinateKernelInclusion M j t n) (coordinateKernelProjection M j t n)
      (coordinateKernel_zero M j t n)).ShortExact := by
  let D := coordinateTupleComplex M j id t
  let e := coordinateTupleAugmentIso M j id t
  have h0 : Epi (D.d 1 0) := by
    let : Epi (D.d 1 0 ≫ e.hom) := coordinateTupleAugmentation_epi M j t
    exact (epi_comp_iff_of_isIso (D.d 1 0) e.hom).mp inferInstance
  cases n with
  | zero => exact shortExact_aug D h0 e
  | succ n => exact shortExact D h0 (coordinateTupleComplex_exact M j t) (n + 1)

/-- Actual coordinate-resolution terms are quasicoherent for quasicoherent coefficients. -/
theorem coordinateTupleTerm_isQuasicoherent
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ) (t : ℤ) (r : ℕ) : ((coordinateTupleComplex M j id t).X r).IsQuasicoherent := by
  have hT : (M ⊗ coordinateHyperplaneTwist (R := R) j (t - (r : ℤ))).IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight M _
      (coordinateHyperplaneTwist_isInvertible j _)
  exact (isQuasicoherent _).prop_of_iso (coordinateTupleTermIso M j id t r).symm
    (isQuasicoherent_coproduct _ (fun _ => hT))

/-- Every actual coordinate kernel is quasicoherent; no Noetherian or finite-type condition is needed. -/
theorem coordinateSyzygy_isQuasicoherent
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ) (t : ℤ) (r : ℕ) : (coordinateSyzygy M j t r).IsQuasicoherent := by
  cases r with
  | zero =>
    exact SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight M _
      (coordinateHyperplaneTwist_isInvertible j t)
  | succ n =>
    let : ((coordinateTupleComplex M j id t).X (n + 1)).IsQuasicoherent :=
      coordinateTupleTerm_isQuasicoherent M j t (n + 1)
    let : ((coordinateTupleComplex M j id t).X n).IsQuasicoherent :=
      coordinateTupleTerm_isQuasicoherent M j t n
    exact isQuasicoherent_kernel ((coordinateTupleComplex M j id t).d (n + 1) n)

end EnvelopeProperty.CoordinateTupleResolution
