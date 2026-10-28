/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.CanonicalDifferentialMap

/-!
# Exact whole-module composition of actual canonical differential maps

Every transition is the actual map of the original algebra tower.
The commutation identity is proved on all genuine forms, with no
commutation certificate or selected source-function family supplied.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open Module
open scoped Classical TensorProduct

variable {k R A : Type*} [CommRing k] [CommRing R] [CommRing A]
  [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A]

/-- The genuine canonical differential map with the original source scalars. -/
def canonicalDifferentialLinearMap (n : ℕ) :
    (⋀[R]^n (KaehlerDifferential k R)) →ₗ[R] (⋀[A]^n (KaehlerDifferential k A)) :=
  ((affineCanonicalDifferentialMap (k := k) (R := R) (A := A) n).restrictScalars R).comp
    (TensorProduct.mk R A (⋀[R]^n (KaehlerDifferential k R)) 1)

/-- The original-scalar map is the actual canonical image of the actual pure tensor. -/
theorem canonicalDifferentialLinearMap_apply (n : ℕ) (ω : ⋀[R]^n (KaehlerDifferential k R)) :
    canonicalDifferentialLinearMap (k := k) (R := R) (A := A) n ω =
      affineCanonicalDifferentialMap (k := k) (R := R) (A := A) n ((1 : A) ⊗ₜ[R] ω) := rfl

/-- Every decomposable original source wedge maps to the wedge of its genuine
actual differential images. -/
theorem canonicalDifferentialLinearMap_wedge (n : ℕ) (η : Fin n → KaehlerDifferential k R) :
    canonicalDifferentialLinearMap (k := k) (R := R) (A := A) n (exteriorPower.ιMulti R n η) =
      exteriorPower.ιMulti A n (fun j => KaehlerDifferential.map k k R A (η j)) := by
  rw [canonicalDifferentialLinearMap_apply, affineCanonicalDifferentialMap_tmul_wedge, one_smul]

section Tower

variable {B : Type*} [CommRing B] [Algebra k B] [Algebra R B] [Algebra A B]
  [IsScalarTower k R B] [IsScalarTower k A B] [IsScalarTower R A B]

/-- Actual canonical differential maps compose exactly on the entire original
exterior module in the actual algebra tower. -/
theorem canonicalDifferentialLinearMap_comp (n : ℕ) :
    ((canonicalDifferentialLinearMap (k := k) (R := A) (A := B) n).restrictScalars R).comp
        (canonicalDifferentialLinearMap (k := k) (R := R) (A := A) n) =
      canonicalDifferentialLinearMap (k := k) (R := R) (A := B) n := by
  refine LinearMap.ext_on_range (exteriorPower.ιMulti_span R n (KaehlerDifferential k R)) fun η => ?_
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    canonicalDifferentialLinearMap_wedge]
  congr 1
  funext j
  exact kaehlerDifferential_map_comp_tower (k := k) (R := R) (A := A) (L := B) (η j)

/-- The actual scalar-extended canonical maps commute on every actual original
source form, with the two literal pure-tensor maps retained. -/
theorem affineCanonicalDifferentialMap_one_tmul_comp (n : ℕ)
    (ω : ⋀[R]^n (KaehlerDifferential k R)) :
    affineCanonicalDifferentialMap (k := k) (R := A) (A := B) n
      ((1 : B) ⊗ₜ[A] (affineCanonicalDifferentialMap (k := k) (R := R) (A := A) n
        ((1 : A) ⊗ₜ[R] ω))) =
      affineCanonicalDifferentialMap (k := k) (R := R) (A := B) n ((1 : B) ⊗ₜ[R] ω) := by
  exact LinearMap.congr_fun (canonicalDifferentialLinearMap_comp (k := k) (R := R) (A := A) (B := B) n) ω

end Tower

end EnvelopeProperty.Char0
