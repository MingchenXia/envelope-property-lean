import EnvelopeProperty.AlgGeom.CyclicSectionBaseChange
import EnvelopeProperty.AlgGeom.CyclicSectionPowerBasis
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Actual affine cyclic-cover geometry

The same original quotients and coefficient maps form genuine scheme pullback
squares. Positive-degree covers are finite, flat and surjective; no normalization
or vanishing claim is made here.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.CyclicSectionAffineCover
open CyclicSectionAlgebra CyclicSectionBaseChange
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The original affine cyclic-cover morphism for the actual section coefficient. -/
def structureMap (n : ℕ) (a : R) :
    Spec (.of (RootRing n a)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (RootRing n a)))

/-- The original spectrum morphism induced by the actual coefficient extension. -/
def coefficientSpecMap (n : ℕ) (a : R) (b : S) (h : b = algebraMap R S a) :
    Spec (.of (RootRing n b)) ⟶ Spec (.of (RootRing n a)) :=
  Spec.map (CommRingCat.ofHom (coefficientMap n a b h).toRingHom)

/-- The WHOLE original coefficient square commutes as actual scheme morphisms. -/
theorem coefficientSpecMap_structure (n : ℕ) (a : R) (b : S) (h : b = algebraMap R S a) :
    coefficientSpecMap n a b h ≫ structureMap n a =
      structureMap n b ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  simp only [coefficientSpecMap, structureMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun r => (coefficientMap n a b h).commutes r)

/-- The actual cyclic coefficient square is cartesian, with its original four maps. -/
theorem isPullback (n : ℕ) (a : R) (b : S) (h : b = algebraMap R S a) :
    IsPullback (structureMap n b) (coefficientSpecMap n a b h)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (structureMap n a) := by
  let e := (baseChangeEquiv n a b h).toRingEquiv.toCommRingCatIso
  have hp := CommRingCat.isPushout_tensorProduct R S (RootRing n a)
  apply isPullback_SpecMap_of_isPushout
  refine hp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp) ?_ ?_
  · apply CommRingCat.hom_ext
    exact RingHom.ext (fun s => (baseChangeEquiv n a b h).commutes s)
  · apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (baseChangeEquiv_includeRight n a b h)

/-- Original affine restrictions remain actual open immersions upstairs. -/
theorem isOpenImmersion_coefficientSpecMap (n : ℕ) (a : R) (b : S)
    (h : b = algebraMap R S a)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    IsOpenImmersion (coefficientSpecMap n a b h) := by
  have hp := isPullback n a b h
  rw [← hp.isoPullback_hom_snd]
  infer_instance

/-- A positive-degree original cyclic algebra is faithfully flat over every base ring. -/
theorem faithfullyFlat (n : ℕ) (a : R) (hn : 0 < n) :
    Module.FaithfullyFlat R (RootRing n a) := by
  have := CyclicSectionPowerBasis.free n a hn
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := hR
    refine { toFlat := inferInstance, submodule_ne_top := ?_ }
    intro m hm
    exact False.elim (hm.ne_top (Subsingleton.elim _ _))
  · have := hR
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Module.FaithfullyFlat.of_linearEquiv R (Fin n →₀ R)
      (CyclicSectionPowerBasis.basis n a hn).repr

/-- The original positive-degree cover morphism is finite. -/
theorem isFinite_structureMap (n : ℕ) (a : R) (hn : 0 < n) :
    IsFinite (structureMap n a) := by
  have := CyclicSectionPowerBasis.finite n a hn
  apply (IsFinite.SpecMap_iff _).2
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- The original positive-degree cover morphism is flat. -/
theorem flat_structureMap (n : ℕ) (a : R) (hn : 0 < n) :
    Flat (structureMap n a) := by
  have := CyclicSectionPowerBasis.free n a hn
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The original positive-degree cover morphism is surjective, including zero bases. -/
theorem surjective_structureMap (n : ℕ) (a : R) (hn : 0 < n) :
    Surjective (structureMap n a) := by
  exact ((flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap R (RootRing n a)))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr (faithfullyFlat n a hn))).2

end EnvelopeProperty.CyclicSectionAffineCover
