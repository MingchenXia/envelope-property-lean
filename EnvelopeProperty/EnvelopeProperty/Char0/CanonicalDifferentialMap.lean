/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.CanonicalDifferentialImage

/-!
# The actual pulled-back top differential map has the full source image

The canonical map is constructed from the genuine map on Kaehler
differentials, its universal exterior extension and actual extension of
scalars. Its complete image is computed, not assumed.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open Module
open scoped Classical TensorProduct

variable {k R A : Type*} [CommRing k] [CommRing R] [CommRing A]
  [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A]

private def canonicalTargetAlternatingMap (n : ℕ) :
    (KaehlerDifferential k A) [⋀^Fin n]→ₗ[R] (⋀[A]^n (KaehlerDifferential k A)) where
  toMultilinearMap := (exteriorPower.ιMulti A n).toMultilinearMap.restrictScalars R
  map_eq_zero_of_eq' := fun v _i _j h hne => (exteriorPower.ιMulti A n).map_eq_zero_of_eq v h hne

private def canonicalDifferentialMapBeforeScalarExtension (n : ℕ) :
    (⋀[R]^n (KaehlerDifferential k R)) →ₗ[R] (⋀[A]^n (KaehlerDifferential k A)) :=
  exteriorPower.alternatingMapLinearEquiv
    ((canonicalTargetAlternatingMap (k := k) (R := R) (A := A) n).compLinearMap
      (KaehlerDifferential.map k k R A))

/-- The actual scalar-extended map on top Kaehler differential modules. -/
def affineCanonicalDifferentialMap (n : ℕ) :
    A ⊗[R] (⋀[R]^n (KaehlerDifferential k R)) →ₗ[A]
      (⋀[A]^n (KaehlerDifferential k A)) :=
  (canonicalDifferentialMapBeforeScalarExtension (k := k) (R := R) (A := A) n).liftBaseChange A

/-- The actual canonical map sends every actual scalar tensor with every
decomposable source form to the wedge of the genuine differential images. -/
theorem affineCanonicalDifferentialMap_tmul_wedge (n : ℕ) (a : A)
    (η : Fin n → KaehlerDifferential k R) :
    affineCanonicalDifferentialMap (k := k) (R := R) (A := A) n
      (a ⊗ₜ[R] exteriorPower.ιMulti R n η) =
        a • exteriorPower.ιMulti A n (fun j => KaehlerDifferential.map k k R A (η j)) := by
  simp only [affineCanonicalDifferentialMap, LinearMap.liftBaseChange_tmul,
    canonicalDifferentialMapBeforeScalarExtension, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  rfl

/-- The genuine canonical differential map retains every actual original-source
function wedge and the exact original algebra map. -/
theorem affineCanonicalDifferentialMap_sourceFunctions (n : ℕ) (w : Fin n → R) :
    affineCanonicalDifferentialMap (k := k) (R := R) (A := A) n
      ((1 : A) ⊗ₜ[R] exteriorPower.ιMulti R n (fun j => KaehlerDifferential.D k R (w j))) =
        exteriorPower.ιMulti A n (fun j => KaehlerDifferential.D k A (algebraMap R A (w j))) := by
  simp only [affineCanonicalDifferentialMap, LinearMap.liftBaseChange_one_tmul,
    canonicalDifferentialMapBeforeScalarExtension, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply, KaehlerDifferential.map_D]
  rfl

private theorem sourceFunctionWedges_span (n : ℕ) :
    Submodule.span R (Set.range fun w : Fin n → R => exteriorPower.ιMulti R n
      (fun j => KaehlerDifferential.D k R (w j))) = ⊤ := by
  have hset : Set.range (fun w : Fin n → R => exteriorPower.ιMulti R n
      (fun j => KaehlerDifferential.D k R (w j))) =
      exteriorPower.ιMulti R n ''
        {v : Fin n → KaehlerDifferential k R | Set.range v ⊆ Set.range (KaehlerDifferential.D k R)} := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨fun j => KaehlerDifferential.D k R (w j),
        fun _ ⟨j, hj⟩ => ⟨w j, hj⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      choose w hw using fun j => hv (Set.mem_range_self j)
      refine ⟨w, ?_⟩
      exact congrArg (exteriorPower.ιMulti R n) (funext hw)
  rw [hset]
  exact exteriorPower.ιMulti_span_of_span R n (KaehlerDifferential k R)
    (KaehlerDifferential.span_range_derivation k R)

/-- The entire range of the actual pulled-back canonical map is precisely the
basis-independent original-source top differential image. -/
theorem range_affineCanonicalDifferentialMap (n : ℕ) :
    LinearMap.range (affineCanonicalDifferentialMap (k := k) (R := R) (A := A) n) =
      affineCanonicalDifferentialImage (k := k) (R := R) (A := A) n := by
  let f := canonicalDifferentialMapBeforeScalarExtension (k := k) (R := R) (A := A) n
  have hf (w : Fin n → R) :
      f (exteriorPower.ιMulti R n (fun j => KaehlerDifferential.D k R (w j))) =
        exteriorPower.ιMulti A n (fun j => KaehlerDifferential.D k A (algebraMap R A (w j))) := by
    simpa only [affineCanonicalDifferentialMap, LinearMap.liftBaseChange_one_tmul] using
      (affineCanonicalDifferentialMap_sourceFunctions (k := k) (R := R) (A := A) n w)
  have hrange : LinearMap.range f ≤
      (affineCanonicalDifferentialImage (k := k) (R := R) (A := A) n).restrictScalars R := by
    rw [← Submodule.map_top, ← sourceFunctionWedges_span (k := k) (R := R) n, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    rw [hf]
    exact Submodule.subset_span ⟨w, rfl⟩
  change LinearMap.range (f.liftBaseChange A) = _
  rw [LinearMap.range_liftBaseChange]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    exact hrange hx
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    apply Submodule.subset_span
    exact ⟨_, hf w⟩

/-- The actual canonical map, expressed in an actual target volume trivialization,
has precisely the full all-original-functions Jacobian ideal as its image. -/
theorem range_differentialVolumeCoordinate_comp_affineCanonicalDifferentialMap {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential k A)) :
    LinearMap.range ((differentialVolumeEquiv b).toLinearMap.comp
      (affineCanonicalDifferentialMap (k := k) (R := R) (A := A) n)) =
        (affineRelativeJacobianIdeal (R := R) b : Submodule A A) := by
  rw [LinearMap.range_comp, range_affineCanonicalDifferentialMap, map_affineCanonicalDifferentialImage]

end EnvelopeProperty.Char0
