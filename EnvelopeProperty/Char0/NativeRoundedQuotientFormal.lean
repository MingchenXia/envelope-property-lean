import EnvelopeProperty.Char0.NativeRoundedQuotientStalk
import EnvelopeProperty.Char0.NativeClosedFibreFormalFlatness

/-! # The SAME original quotient tensor in the actual original native formal source

The actual native tensor-local lift retains every original affine coefficient
and every series in the entire original base formal ring. Its faithful
flatness is derived from the actual smooth geometry.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite TensorProduct ComplexSchemes HolomorphicGerms
open EnvelopeProperty.CanonicalGeometry

noncomputable section

namespace EnvelopeProperty.Char0.NativeRoundedQuotientFormal

open NativeClosedFibreFormalFlatness

variable {R A : Type} [CommRing R] [CommRing A]
    (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Spec (.of A) ⟶ Spec (.of R))
    (n m : ℕ) [SmoothOfRelativeDimension n (π ≫ f)] [SmoothOfRelativeDimension m f]
    [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] [IsSeparated f] [QuasiCompact f]
    (p : SchemeComplexPoint (π ≫ f))

omit [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] in
/-- Actual native base Taylor flatness and localization derive flatness of the
ENTIRE original affine coefficient map to the SAME tensor-local point ring. -/
theorem nativeTensorLocal_flat :
    letI := originalMorphismAlgebra π
    letI := baseFormalAlgebra f π m p
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    (algebraMap A (OriginalClosedFibreLocalRing f π m p)).Flat := by
  let := originalMorphismAlgebra π
  let := baseFormalAlgebra f π m p
  let : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  let T := A ⊗[R] MvPowerSeries (Fin m) ℂ
  let D := OriginalClosedFibreLocalRing f π m p
  let : Module.Flat R (MvPowerSeries (Fin m) ℂ) := by
    apply RingHom.flat_algebraMap_iff.mp
    change (schemeAffineNativeFormal f m (originalBasePoint f π p)).Flat
    exact schemeAffineNativeFormal_flat f m (originalBasePoint f π p)
  have hi : (Algebra.TensorProduct.includeLeft : A →ₐ[R] T).toRingHom.Flat := by
    change (algebraMap A T).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have hl : (algebraMap T D).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  exact hi.comp hl

/-- The actual manufactured native lift reflects membership for the WHOLE original ideal,
with EVERY original affine coefficient and EVERY original formal base series. -/
theorem nativeTensorLocalIdeal_mem_iff (I : Ideal A) (j : A) (s : MvPowerSeries (Fin m) ℂ) :
    letI := originalMorphismAlgebra π
    letI := baseFormalAlgebra f π m p
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    let T := A ⊗[R] MvPowerSeries (Fin m) ℂ
    let D := OriginalClosedFibreLocalRing f π m p
    algebraMap T D ((Algebra.TensorProduct.includeRight : MvPowerSeries (Fin m) ℂ →ₐ[R] T) s) *
      algebraMap A D j ∈ I.map (algebraMap A D) ↔
      schemeMorphismFormalPullback f π n m p s *
        schemeAffineNativeFormal (π ≫ f) n p j ∈
          I.map (schemeAffineNativeFormal (π ≫ f) n p) := by
  let := originalMorphismAlgebra π
  let := baseFormalAlgebra f π m p
  let : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  let T := A ⊗[R] MvPowerSeries (Fin m) ℂ
  let D := OriginalClosedFibreLocalRing f π m p
  let liftHom := originalClosedFibreLocalLift f π n m p
  let t : D := algebraMap T D
    ((Algebra.TensorProduct.includeRight : MvPowerSeries (Fin m) ℂ →ₐ[R] T) s)
  have hleft : liftHom.comp (algebraMap A D) = schemeAffineNativeFormal (π ≫ f) n p :=
    RingHom.ext (originalClosedFibreLocalLift_includeLeft f π n m p)
  have hright : liftHom t = schemeMorphismFormalPullback f π n m p s :=
    originalClosedFibreLocalLift_includeRight f π n m p s
  have he : t * algebraMap A D j ∈ I.map (algebraMap A D) ↔
      liftHom (t * algebraMap A D j) ∈ (I.map (algebraMap A D)).map liftHom := by
    let : Algebra D (MvPowerSeries (Fin n) ℂ) := liftHom.toAlgebra
    let : Module D (MvPowerSeries (Fin n) ℂ) := Algebra.toModule
    let : Module.FaithfullyFlat D (MvPowerSeries (Fin n) ℂ) :=
      originalClosedFibreLocalLift_faithfullyFlat f π n m p
    change _ ↔ t * algebraMap A D j ∈
      ((I.map (algebraMap A D)).map (algebraMap D (MvPowerSeries (Fin n) ℂ))).comap
        (algebraMap D (MvPowerSeries (Fin n) ℂ))
    rw [Ideal.comap_map_eq_self_of_faithfullyFlat]
  change t * algebraMap A D j ∈ I.map (algebraMap A D) ↔ _
  rw [he, map_mul, hright,
    show liftHom (algebraMap A D j) = schemeAffineNativeFormal (π ≫ f) n p j from
      RingHom.congr_fun hleft j,
    Ideal.map_map, hleft]

end EnvelopeProperty.Char0.NativeRoundedQuotientFormal
