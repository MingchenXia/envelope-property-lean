import EnvelopeProperty.AlgGeom.CyclicSectionSNCInjectiveBaseChange
import EnvelopeProperty.AlgGeom.CyclicSectionSNCAffineRoundedCover

/-! # Actual rounded affine models under general injective coefficient extension

The original actual rounded projection and raw-comparison maps form native
scheme pullbacks. Actual affine functions and the original raw root have their
proved pullback formulas. No localization presentation or cartesian certificate
is assumed, and the original actual rounded models are retained.
-/

open CategoryTheory AlgebraicGeometry
open scoped BigOperators
noncomputable section
universe u v
attribute [local instance] OreLocalization.instAlgebra

namespace EnvelopeProperty.CyclicSectionSNCAffineInjectiveBaseChange
open CyclicSectionAlgebra CyclicSectionSNCNormalizationRounded
open CyclicSectionSNCAffineRoundedCover CyclicSectionSNCInjectiveBaseChange
variable {R : Type u} [CommRing R] [IsDomain R]
variable {J : Type v} [Fintype J]
variable (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
variable (hn : 0 < n) (hf : ∀ j, f j ≠ 0)
local notation "M" => roundedAlgebra n α u f hn hf

/-- The SAME original raw quotient root, in the SAME actual rounded algebra. -/
def rootElement : M :=
  rawToRounded n α u f hn hf (root n (u * ∏ j, f j ^ α j))

/-- The SAME original raw root is an actual global function on the original rounded model. -/
def rootSection : Γ(Spec (.of M), ⊤) :=
  (Scheme.ΓSpecIso (.of M)).inv (rootElement n α u f hn hf)

/-- The actual original raw-comparison map pulls back precisely the SAME raw root function. -/
theorem rawComparison_rootSection :
    (rawComparison n α u f hn hf).appTop
      ((Scheme.ΓSpecIso (.of (RootRing n (u * ∏ j, f j ^ α j)))).inv
        (root n (u * ∏ j, f j ^ α j))) = rootSection n α u f hn hf := by
  exact (congrArg
    (fun k : CommRingCat.of (RootRing n (u * ∏ j, f j ^ α j)) ⟶ Γ(Spec (.of M), ⊤) =>
      k (root n (u * ∏ j, f j ^ α j)))
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (rawToRounded n α u f hn hf).toRingHom))).symm

variable {A : Type u} [CommRing A] [IsDomain A] [Algebra R A]
variable (hRA : Function.Injective (algebraMap R A))
local notation "MA" => roundedAlgebra n α (algebraMap R A u)
  (fun j => algebraMap R A (f j)) hn (mapped_nonzero hRA f hf)

/-- The actual spectrum map of the SAME rounded map for the original coefficient injection. -/
def coefficientSpecMap : Spec (.of MA) ⟶ Spec (.of M) :=
  Spec.map (CommRingCat.ofHom (roundedMap hRA n α u f hn hf).toRingHom)

/-- The original projection square is the spectrum of its internally produced actual pushout. -/
theorem isPullback_projection :
    IsPullback
      (projection n α (algebraMap R A u) (fun j => algebraMap R A (f j)) hn
        (mapped_nonzero hRA f hf))
      (coefficientSpecMap n α u f hn hf hRA)
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (projection n α u f hn hf) := by
  let := baseChangeAlgebra hRA n α u f hn hf
  have := baseChangeAlgebra_tower hRA n α u f hn hf
  have := roundedMap_isPushout hRA n α u f hn hf
  apply isPullback_SpecMap_of_isPushout
  exact CommRingCat.isPushout_of_isPushout R A M MA

/-- The ENTIRE actual coefficient-extension projection square commutes. -/
theorem coefficientSpecMap_projection :
    coefficientSpecMap n α u f hn hf hRA ≫ projection n α u f hn hf =
      projection n α (algebraMap R A u) (fun j => algebraMap R A (f j)) hn
        (mapped_nonzero hRA f hf) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  (isPullback_projection n α u f hn hf hRA).w.symm

/-- The ENTIRE original raw-comparison square commutes under the actual coefficient injection. -/
theorem coefficientSpecMap_rawComparison :
    coefficientSpecMap n α u f hn hf hRA ≫ rawComparison n α u f hn hf =
      rawComparison n α (algebraMap R A u) (fun j => algebraMap R A (f j)) hn
        (mapped_nonzero hRA f hf) ≫
          CyclicSectionAffineCover.coefficientSpecMap n (u * ∏ j, f j ^ α j)
            (algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j)
            (by simp only [map_mul, map_prod, map_pow]) := by
  simp only [coefficientSpecMap, rawComparison, CyclicSectionAffineCover.coefficientSpecMap,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (roundedMap_comp_rawToRounded hRA n α u f hn hf)

/-- The SAME actual original raw comparison has a genuine cartesian coefficient-extension square. -/
theorem isPullback_rawComparison :
    IsPullback
      (rawComparison n α (algebraMap R A u) (fun j => algebraMap R A (f j)) hn
        (mapped_nonzero hRA f hf))
      (coefficientSpecMap n α u f hn hf hRA)
      (CyclicSectionAffineCover.coefficientSpecMap n (u * ∏ j, f j ^ α j)
        (algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j)
        (by simp only [map_mul, map_prod, map_pow]))
      (rawComparison n α u f hn hf) := by
  have hp : IsPullback
      (rawComparison n α (algebraMap R A u) (fun j => algebraMap R A (f j)) hn
        (mapped_nonzero hRA f hf) ≫
          CyclicSectionAffineCover.structureMap n
            (algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j))
      (coefficientSpecMap n α u f hn hf hRA)
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (rawComparison n α u f hn hf ≫
        CyclicSectionAffineCover.structureMap n (u * ∏ j, f j ^ α j)) := by
    rw [rawComparison_projection, rawComparison_projection]
    exact isPullback_projection n α u f hn hf hRA
  exact hp.of_right (coefficientSpecMap_rawComparison n α u f hn hf hRA).symm
    (CyclicSectionAffineCover.isPullback n (u * ∏ j, f j ^ α j)
      (algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j)
      (by simp only [map_mul, map_prod, map_pow]))

/-- A genuine actual affine open immersion remains an open immersion on the SAME rounded models. -/
theorem isOpenImmersion_coefficientSpecMap
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R A)))] :
    IsOpenImmersion (coefficientSpecMap n α u f hn hf hRA) := by
  have hp := isPullback_projection n α u f hn hf hRA
  rw [← hp.isoPullback_hom_snd]
  infer_instance

/-- Its actual original open range is EXACTLY the original projection's inverse-image open. -/
theorem coefficientSpecMap_opensRange
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R A)))] :
    letI := isOpenImmersion_coefficientSpecMap n α u f hn hf hRA
    (coefficientSpecMap n α u f hn hf hRA).opensRange =
      (projection n α u f hn hf) ⁻¹ᵁ
        (Spec.map (CommRingCat.ofHom (algebraMap R A))).opensRange := by
  let := isOpenImmersion_coefficientSpecMap n α u f hn hf hRA
  have hp := isPullback_projection n α u f hn hf hRA
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange]
  rw [← hp.isoPullback_hom_snd]
  change ((hp.isoPullback.hom ≫ CategoryTheory.Limits.pullback.snd _ _).opensRange :
    Set (Spec (.of M))) = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackSnd]

/-- EVERY original rounded global function pulls back by the SAME actual rounded coefficient map. -/
theorem coefficientSpecMap_appTop (y : M) :
    (coefficientSpecMap n α u f hn hf hRA).appTop ((Scheme.ΓSpecIso (.of M)).inv y) =
      (Scheme.ΓSpecIso (.of MA)).inv (roundedMap hRA n α u f hn hf y) := by
  exact (congrArg (fun k : CommRingCat.of M ⟶ Γ(Spec (.of MA), ⊤) => k y)
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (roundedMap hRA n α u f hn hf).toRingHom))).symm

/-- The SAME original rounded root element maps to the actual mapped-family root element. -/
theorem roundedMap_rootElement :
    roundedMap hRA n α u f hn hf (rootElement n α u f hn hf) =
      rootElement n α (algebraMap R A u) (fun j => algebraMap R A (f j)) hn
        (mapped_nonzero hRA f hf) := by
  have h := AlgHom.congr_fun (roundedMap_comp_rawToRounded hRA n α u f hn hf)
    (root n (u * ∏ j, f j ^ α j))
  change roundedMap hRA n α u f hn hf
      (rawToRounded n α u f hn hf (root n (u * ∏ j, f j ^ α j))) =
    rawToRounded n α (algebraMap R A u) (fun j => algebraMap R A (f j)) hn
      (mapped_nonzero hRA f hf)
      (CyclicSectionBaseChange.coefficientMap n (u * ∏ j, f j ^ α j)
        (algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j)
        (by simp only [map_mul, map_prod, map_pow])
        (root n (u * ∏ j, f j ^ α j))) at h
  rw [CyclicSectionBaseChange.coefficientMap_root] at h
  exact h

/-- The actual original raw-root section is natural under general injective coefficient extension. -/
theorem coefficientSpecMap_rootSection :
    (coefficientSpecMap n α u f hn hf hRA).appTop (rootSection n α u f hn hf) =
      rootSection n α (algebraMap R A u) (fun j => algebraMap R A (f j)) hn
        (mapped_nonzero hRA f hf) := by
  change (coefficientSpecMap n α u f hn hf hRA).appTop
      ((Scheme.ΓSpecIso (.of M)).inv (rootElement n α u f hn hf)) = _
  rw [coefficientSpecMap_appTop, roundedMap_rootElement]
  rfl

end EnvelopeProperty.CyclicSectionSNCAffineInjectiveBaseChange
