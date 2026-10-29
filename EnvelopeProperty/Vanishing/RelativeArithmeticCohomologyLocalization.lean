import EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyBaseChange
import EnvelopeProperty.Algebra.FreeFiberDetection
import Mathlib.RingTheory.Flat.Stability

/-! # A free localized cohomology fibre detects vanishing

Both scalar comparisons are constructed from the same original bounded flat
complex. A zero fibre of arbitrary-rank localized free cohomology gives zero
homology after every further scalar extension from that localization.
-/

open CategoryTheory CategoryTheory.Limits TensorProduct

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyLocalization

open SpecializationDerivedReplacementStep SpecializationDerivedNatural
  RelativeArithmeticCohomologyBaseChange

variable {A T C : Type u} [CommRing A] [CommRing T] [CommRing C]
    [Algebra A T] [Algebra A C] [Algebra T C] [IsScalarTower A T C]

/-- The native iterated scalar complex is isomorphic to direct scalar
extension through the actual scalar tower. -/
def iteratedShortIso (S : ShortComplex (ModuleCat.{u} A)) :
    baseChangeComplex (baseChangeComplex S T) C ≅ baseChangeComplex S C := by
  let e₁ := AlgebraTensorModule.cancelBaseChange A T C C S.X₁
  let e₂ := AlgebraTensorModule.cancelBaseChange A T C C S.X₂
  let e₃ := AlgebraTensorModule.cancelBaseChange A T C C S.X₃
  refine ShortComplex.isoMk e₁.toModuleIso e₂.toModuleIso e₃.toModuleIso ?_ ?_
  · apply ModuleCat.hom_ext
    change S.f.hom.baseChange C ∘ₗ e₁.toLinearMap =
      e₂.toLinearMap ∘ₗ (S.f.hom.baseChange T).baseChange C
    rw [LinearMap.baseChange_baseChange]
    ext x
    simp [e₁, e₂]
  · apply ModuleCat.hom_ext
    change S.g.hom.baseChange C ∘ₗ e₂.toLinearMap =
      e₃.toLinearMap ∘ₗ (S.g.hom.baseChange T).baseChange C
    rw [LinearMap.baseChange_baseChange]
    ext x
    simp [e₂, e₃]

/-- The actual original cochain complex after scalar extension to T. -/
def scalarComplex (K : CochainComplex (ModuleCat.{u} A) ℕ) :
    CochainComplex (ModuleCat.{u} T) ℕ :=
  ((FiniteCechFlatBaseChange.tensorFunctor (R := A) (S := T)).mapHomologicalComplex
    (.up ℕ)).obj K

/-- Genuine flat extension compares native homology in every degree. -/
def flatHomologyIso [Module.Flat A T]
    (K : CochainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    (scalarComplex (T := T) K).homology n ≅
      ModuleCat.of T (T ⊗[A] K.homology n) := by
  let F := FiniteCechFlatBaseChange.tensorFunctor (R := A) (S := T)
  let : F.PreservesHomology :=
    { preservesKernels := by
        intro P Q f
        exact preserves_kernel_of_bijective_comparison (C := T) f
          (ModularCurves.kerBaseChangeComparison_bijective_of_flat T f.hom)
      preservesCokernels := by
        intro P Q f
        exact preserves_cokernel (C := T) f }
  exact (K.sc n).mapHomologyIso F

/-- A nonzero zero fibre of free homology of the actual extended complex
annihilates the actual direct scalar homology over every further T-algebra. -/
theorem natural_homology_isZero_of_free_scalar_fibre [Nontrivial C]
    (K : CochainComplex (ModuleCat.{u} A) ℕ)
    [∀ n, Module.Flat A (K.X n)]
    [∀ n, Module.Free T ((scalarComplex (T := T) K).homology n)]
    (N : ℕ) (hnext : IsZero (K.X (N + 1))) (t : ℕ) (ht : 0 < t) (htN : t ≤ N)
    (hzero : IsZero (baseChangeComplex (naturalSegment K t) C).homology)
    (D : Type u) [CommRing D] [Algebra A D] [Algebra T D] [IsScalarTower A T D] :
    IsZero (baseChangeComplex (naturalSegment K t) D).homology := by
  let KT := scalarComplex (T := T) K
  let : ∀ n, Module.Flat T (KT.X n) := fun n =>
    inferInstanceAs (Module.Flat T (T ⊗[A] K.X n))
  let : ∀ n, Module.Flat T (KT.homology n) := fun _ => inferInstance
  have hnextT : IsZero (KT.X (N + 1)) := by
    let : Subsingleton (K.X (N + 1)) := ModuleCat.subsingleton_of_isZero hnext
    change IsZero (ModuleCat.of T (T ⊗[A] K.X (N + 1)))
    exact ModuleCat.isZero_of_subsingleton _
  let eC := naturalHomologyIso (C := C) KT N hnextT t ht htN
  have hlocal : IsZero (baseChangeComplex (naturalSegment KT t) C).homology :=
    hzero.of_iso (ShortComplex.homologyMapIso
      (iteratedShortIso (T := T) (C := C) (naturalSegment K t)))
  have hC : Subsingleton (C ⊗[T] KT.homology t) :=
    ModuleCat.subsingleton_of_isZero (hlocal.of_iso eC.symm)
  let : Subsingleton (KT.homology t) := FreeFiberDetection.subsingleton_of_baseChange hC
  have hD : IsZero (ModuleCat.of D (D ⊗[T] KT.homology t)) :=
    ModuleCat.isZero_of_subsingleton _
  have hlocalD : IsZero (baseChangeComplex (naturalSegment KT t) D).homology :=
    hD.of_iso (naturalHomologyIso (C := D) KT N hnextT t ht htN)
  exact hlocalD.of_iso (ShortComplex.homologyMapIso
    (iteratedShortIso (T := T) (C := D) (naturalSegment K t))).symm

end EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyLocalization
