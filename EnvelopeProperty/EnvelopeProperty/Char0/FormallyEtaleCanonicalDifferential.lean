import EnvelopeProperty.AlgGeom.Canonical.ExteriorSheaf
import EnvelopeProperty.Char0.CanonicalDifferentialMap
import Mathlib.RingTheory.Etale.Kaehler

/-! # Genuine whole original canonical differential equivalence under formal etaleness -/
noncomputable section
namespace EnvelopeProperty.Char0
open Module
open scoped TensorProduct
universe u v
variable {k R A : Type u} [CommRing k] [CommRing R] [CommRing A]
  [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A]
  [Algebra.FormallyEtale R A] {I : Type v} [LinearOrder I]

/-- Actual scalar extension of the original exterior differential has a genuine inverse
from formal etaleness and the SAME original free differential basis, in EVERY degree. -/
def affineCanonicalDifferentialEquivOfFormallyEtale
    (b : Basis I R (KaehlerDifferential k R)) (q : ℕ) :
    A ⊗[R] (⋀[R]^q (KaehlerDifferential k R)) ≃ₗ[A]
      (⋀[A]^q (KaehlerDifferential k A)) :=
  (CanonicalGeometry.exteriorBasisBaseChangeEquiv b q).trans
    (CanonicalGeometry.exteriorLinearEquiv
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R A) q)

private theorem originalFormallyEtaleExteriorWedge
    (b : Basis I R (KaehlerDifferential k R)) (q : ℕ)
    (m : Fin q → KaehlerDifferential k R) :
    affineCanonicalDifferentialEquivOfFormallyEtale (A := A) b q
      (1 ⊗ₜ[R] exteriorPower.ιMulti R q m) =
      exteriorPower.ιMulti A q (fun j => KaehlerDifferential.map k k R A (m j)) := by
  simp [affineCanonicalDifferentialEquivOfFormallyEtale,
    CanonicalGeometry.exteriorBasisBaseChangeEquiv_wedge,
    KaehlerDifferential.mapBaseChange_tmul, Function.comp_def]

/-- The ENTIRE genuine equivalence is EXACTLY the SAME pre-existing original
canonical differential map, not a basis-matched replacement. -/
theorem affineCanonicalDifferentialEquivOfFormallyEtale_toLinearMap
    (b : Basis I R (KaehlerDifferential k R)) (q : ℕ) :
    (affineCanonicalDifferentialEquivOfFormallyEtale (A := A) b q).toLinearMap =
      affineCanonicalDifferentialMap (k := k) (R := R) (A := A) q := by
  have hOne (z : ⋀[R]^q (KaehlerDifferential k R)) :
      affineCanonicalDifferentialEquivOfFormallyEtale (A := A) b q (1 ⊗ₜ[R] z) =
        affineCanonicalDifferentialMap (k := k) (R := R) (A := A) q (1 ⊗ₜ[R] z) := by
    let F := ((affineCanonicalDifferentialEquivOfFormallyEtale (A := A) b q).toLinearMap.restrictScalars R).comp
      (TensorProduct.mk R A (⋀[R]^q (KaehlerDifferential k R)) 1)
    let G := ((affineCanonicalDifferentialMap (k := k) (R := R) (A := A) q).restrictScalars R).comp
      (TensorProduct.mk R A (⋀[R]^q (KaehlerDifferential k R)) 1)
    have he : F = G := by
      apply LinearMap.ext_on (exteriorPower.ιMulti_span R q (KaehlerDifferential k R))
      rintro _ ⟨m, rfl⟩
      change affineCanonicalDifferentialEquivOfFormallyEtale (A := A) b q
          (1 ⊗ₜ[R] exteriorPower.ιMulti R q m) =
        affineCanonicalDifferentialMap (k := k) (R := R) (A := A) q
          (1 ⊗ₜ[R] exteriorPower.ιMulti R q m)
      exact (originalFormallyEtaleExteriorWedge b q m).trans
        (by simpa only [one_smul] using
          (affineCanonicalDifferentialMap_tmul_wedge (k := k) (R := R) (A := A) q 1 m).symm)
    exact LinearMap.congr_fun he z
  apply TensorProduct.AlgebraTensorModule.ext
  intro a z
  have htmul : a ⊗ₜ[R] z = a • ((1 : A) ⊗ₜ[R] z) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [htmul, LinearMap.map_smul, LinearMap.map_smul]
  exact congrArg (fun w => a • w) (hOne z)

/-- Formal etaleness DERIVES bijectivity of the ENTIRE SAME actual original
canonical differential map in EVERY degree, without target freeness or inverse data. -/
theorem affineCanonicalDifferentialMap_bijective_of_formallyEtale
    (b : Basis I R (KaehlerDifferential k R)) (q : ℕ) :
    Function.Bijective (affineCanonicalDifferentialMap (k := k) (R := R) (A := A) q) := by
  rw [← affineCanonicalDifferentialEquivOfFormallyEtale_toLinearMap b q]
  exact (affineCanonicalDifferentialEquivOfFormallyEtale b q).bijective

end EnvelopeProperty.Char0
