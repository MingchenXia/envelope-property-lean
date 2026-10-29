import EnvelopeProperty.Char0.NativeRoundedQuotientFormal
import EnvelopeProperty.AlgGeom.AffinePullbackStalkTensorReadback

/-! # The intrinsic original section kernel before introducing native coefficient rings -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite TensorProduct ComplexSchemes HolomorphicGerms
open EnvelopeProperty.FlatSectionKernel
noncomputable section

namespace EnvelopeProperty.Char0.NativeTensorSectionCriterion

open NativeClosedFibreFormalFlatness

variable {R A : Type} [CommRing R] [CommRing A]
    (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Spec (.of A) ⟶ Spec (.of R))
    (n m : ℕ) [SmoothOfRelativeDimension n (π ≫ f)] [SmoothOfRelativeDimension m f]
    [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] [IsSeparated f] [QuasiCompact f]

/-- Native scalar extension of an arbitrary original section is computed from its
intrinsic whole original coefficient kernel, before any particular quotient is substituted. -/
theorem tensorSection_eq_zero_iff_nativeIdeal
    (M : (Spec (.of A)).Modules)
    (μ : AffineModuleFlatBaseChange.sections (𝟙 (Spec (.of A))) M)
    (I : Ideal A) (j : A)
    (hK : sectionKernel (𝟙 (Spec (.of A))) M μ = I.colon {j}) :
    ∀ (p : SchemeComplexPoint (π ≫ f)) (s : MvPowerSeries (Fin m) ℂ),
    letI := originalMorphismAlgebra π
    letI := baseFormalAlgebra f π m p
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    let T := A ⊗[R] MvPowerSeries (Fin m) ℂ
    let D := OriginalClosedFibreLocalRing f π m p
    let inc : CommRingCat.of A ⟶ CommRingCat.of T :=
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A →ₐ[R] T).toRingHom
    letI : Algebra A T := inc.hom.toAlgebra
    letI : Algebra A D := ((algebraMap T D).comp inc.hom).toAlgebra
    letI : Module A D := Algebra.toModule
    let t : D := algebraMap T D
      ((Algebra.TensorProduct.includeRight : MvPowerSeries (Fin m) ℂ →ₐ[R] T) s)
    t ⊗ₜ[A] μ = (0 : D ⊗[A] AffineModuleFlatBaseChange.sections (𝟙 (Spec (.of A))) M) ↔
      schemeMorphismFormalPullback f π n m p s * schemeAffineNativeFormal (π ≫ f) n p j ∈
        I.map (schemeAffineNativeFormal (π ≫ f) n p) := by
  intro p s
  let := originalMorphismAlgebra π
  let := baseFormalAlgebra f π m p
  let : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  let T := A ⊗[R] MvPowerSeries (Fin m) ℂ
  let D := OriginalClosedFibreLocalRing f π m p
  let inc : CommRingCat.of A ⟶ CommRingCat.of T :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A →ₐ[R] T).toRingHom
  let : Algebra A T := inc.hom.toAlgebra
  let : Algebra A D := ((algebraMap T D).comp inc.hom).toAlgebra
  let : Module A D := Algebra.toModule
  have hflat : ((algebraMap T D).comp inc.hom).Flat :=
    NativeRoundedQuotientFormal.nativeTensorLocal_flat f π m p
  let : Module.Flat A D := RingHom.flat_algebraMap_iff.mp hflat
  let t : D := algebraMap T D
    ((Algebra.TensorProduct.includeRight : MvPowerSeries (Fin m) ℂ →ₐ[R] T) s)
  have hk : t ⊗ₜ[A] μ =
      (0 : D ⊗[A] AffineModuleFlatBaseChange.sections (𝟙 (Spec (.of A))) M) ↔
      t ∈ (sectionKernel (𝟙 (Spec (.of A))) M μ).map (algebraMap A D) := by
    change _ ↔ t ∈ Ideal.map (algebraMap A D) (LinearMap.toSpanSingleton A _ μ).ker
    rw [map_kernel_eq]
    simp only [LinearMap.mem_ker, coefficientBaseChange_apply,
      LinearMap.toSpanSingleton_apply, one_smul]
  have hcolon : t ∈ (sectionKernel (𝟙 (Spec (.of A))) M μ).map (algebraMap A D) ↔
      t * algebraMap A D j ∈ I.map (algebraMap A D) := by
    rw [hK, map_colon_singleton_of_flat, Submodule.mem_colon_singleton, smul_eq_mul]
  change t ⊗ₜ[A] μ =
    (0 : D ⊗[A] AffineModuleFlatBaseChange.sections (𝟙 (Spec (.of A))) M) ↔ _
  exact hk.trans (hcolon.trans
    (NativeRoundedQuotientFormal.nativeTensorLocalIdeal_mem_iff f π n m p I j s))

/-- The actual native tensor-chart pullback germ of an arbitrary original section
has the SAME exact native formal ideal criterion, with the literal actual point and unit. -/
theorem pullbackGerm_eq_zero_iff_nativeIdeal
    (M : (Spec (.of A)).Modules) [M.IsQuasicoherent]
    (μ : AffineModuleFlatBaseChange.sections (R := A) (𝟙 (Spec (.of A))) M)
    (I : Ideal A) (j : A)
    (hK : sectionKernel (R := A) (𝟙 (Spec (.of A))) M μ = I.colon {j}) :
    ∀ (p : SchemeComplexPoint (π ≫ f)) (s : MvPowerSeries (Fin m) ℂ),
    letI := originalMorphismAlgebra π
    letI := originalResidueAlgebra f π p
    letI := baseFormalAlgebra f π m p
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    let T := A ⊗[R] MvPowerSeries (Fin m) ℂ
    let inc : CommRingCat.of A ⟶ CommRingCat.of T :=
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A →ₐ[R] T).toRingHom
    let x : PrimeSpectrum T :=
      ⟨ClosedFibreLocalRing.pointIdeal (ClosedFibreLocalRing.pointTensorMap
        (baseFormalResidue f π m p) (originalPoint f π p)), inferInstance⟩
    let N := (Scheme.Modules.pullback (Spec.map inc)).obj M
    let t : T := (Algebra.TensorProduct.includeRight : MvPowerSeries (Fin m) ℂ →ₐ[R] T) s
    N.presheaf.germ ⊤ x trivial
      (t • (show (moduleSpecΓFunctor (R := CommRingCat.of T)).obj N from
        Scheme.Modules.affinePullbackUnitTop (Spec.map inc) M μ)) = 0 ↔
      schemeMorphismFormalPullback f π n m p s * schemeAffineNativeFormal (π ≫ f) n p j ∈
        I.map (schemeAffineNativeFormal (π ≫ f) n p) := by
  intro p s
  let := originalMorphismAlgebra π
  let := originalResidueAlgebra f π p
  let := baseFormalAlgebra f π m p
  let : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  let T := A ⊗[R] MvPowerSeries (Fin m) ℂ
  let inc : CommRingCat.of A ⟶ CommRingCat.of T :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A →ₐ[R] T).toRingHom
  let x : PrimeSpectrum T :=
    ⟨ClosedFibreLocalRing.pointIdeal (ClosedFibreLocalRing.pointTensorMap
      (baseFormalResidue f π m p) (originalPoint f π p)), inferInstance⟩
  let N := (Scheme.Modules.pullback (Spec.map inc)).obj M
  let t : T := (Algebra.TensorProduct.includeRight : MvPowerSeries (Fin m) ℂ →ₐ[R] T) s
  have hg := AffinePullbackStalkTensorReadback.pullbackGerm_eq_zero_iff_identitySectionsTensor
    (B := CommRingCat.of A) (T := CommRingCat.of T) M inc x t μ
  have ht := tensorSection_eq_zero_iff_nativeIdeal f π n m M μ I j hK p s
  exact hg.trans ht

end EnvelopeProperty.Char0.NativeTensorSectionCriterion
