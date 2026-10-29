import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationMap

/-! # Original-base affine section comparison on the actual geometric product

The tensor-domain comparison is derived from the genuine original ring pushout.
Its comparison with the actual original section map is proved on pure tensors.
No module base-change comparison or Laurent decomposition is supplied.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings LaurentPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules

section OriginalProduct
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  [Module.Flat R S] [QuasiCompact f] [QuasiSeparated f]

/-- The ACTUAL original-base tensor domain is canonically the native
whole-function extension domain, by the original geometric ring pushout. -/
def originalProductTensorEquiv (M : X.Modules) :
    (ModuleCat.extendScalars (algebraMap R S)).obj (originalBaseSections f M) ≃+
      (ModuleCat.extendScalars (FlatGlobalSections.firstProjection (S := S) f).appTop.hom).obj
        (ModuleCat.of Γ(X, ⊤) Γ(M, ⊤)) := by
  letI : Algebra R Γ(X, ⊤) := FlatGlobalSections.sectionsAlgebra f
  letI : Algebra S Γ(FlatGlobalSections.baseChange (S := S) f, ⊤) :=
    FlatGlobalSections.sectionsAlgebra (FlatGlobalSections.structureMap (S := S) f)
  letI : Algebra Γ(X, ⊤) Γ(FlatGlobalSections.baseChange (S := S) f, ⊤) :=
    (FlatGlobalSections.firstProjection (S := S) f).appTop.hom.toAlgebra
  letI : Algebra R Γ(FlatGlobalSections.baseChange (S := S) f, ⊤) :=
    ((ProperBirationalSections.coefficientMap (FlatGlobalSections.structureMap (S := S) f)).comp
      (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S Γ(FlatGlobalSections.baseChange (S := S) f, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower R Γ(X, ⊤) Γ(FlatGlobalSections.baseChange (S := S) f, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (RingHom.congr_fun (originalCoefficientSquare f
        (FlatGlobalSections.structureMap (S := S) f)
        (FlatGlobalSections.firstProjection (S := S) f) pullback.condition) r).symm
  letI : Algebra.IsPushout R S Γ(X, ⊤) Γ(FlatGlobalSections.baseChange (S := S) f, ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp
      (FlatGlobalSections.originalSectionSquare (S := S) f).flip
  letI : IsScalarTower R Γ(X, ⊤) (originalBaseSections f M) :=
    ⟨fun r a m => by
      change (ProperBirationalSections.coefficientMap f r * a) • m =
        ProperBirationalSections.coefficientMap f r • (a • m)
      exact mul_smul _ _ _⟩
  exact (TensorProduct.congr (originalScalarEquiv (R := R) (S := S))
    (LinearEquiv.refl R (originalBaseSections f M))).toAddEquiv |>.trans
      (Algebra.IsPushout.cancelBaseChange R S Γ(X, ⊤)
        Γ(FlatGlobalSections.baseChange (S := S) f, ⊤) (originalBaseSections f M)).symm.toAddEquiv
      |>.trans (TensorProduct.congr
        (originalScalarEquiv (R := Γ(X, ⊤))
          (S := Γ(FlatGlobalSections.baseChange (S := S) f, ⊤))).symm
        (LinearEquiv.refl Γ(X, ⊤) Γ(M, ⊤))).toAddEquiv

/-- The domain comparison keeps the literal coefficient image under the
SAME original second projection, without a supplied map comparison. -/
theorem originalProductTensorEquiv_tmul (M : X.Modules) (b : S)
    (s : originalBaseSections f M) :
    originalProductTensorEquiv (S := S) f M (b ⊗ₜ[R, algebraMap R S] s) =
      (ProperBirationalSections.coefficientMap (FlatGlobalSections.structureMap (S := S) f) b)
        ⊗ₜ[Γ(X, ⊤), (FlatGlobalSections.firstProjection (S := S) f).appTop.hom] s := by
  simp [originalProductTensorEquiv, originalScalarEquiv,
    Algebra.IsPushout.cancelBaseChange_symm_tmul]
  rfl

/-- The actual original-base map on the SAME product equals the native
whole-function map after the internally derived tensor-domain comparison. -/
theorem originalProductMap_eq_sectionExtensionMap (M : X.Modules)
    (z : (ModuleCat.extendScalars (algebraMap R S)).obj (originalBaseSections f M)) :
    originalBaseChangeMap f (FlatGlobalSections.structureMap (S := S) f)
        (FlatGlobalSections.firstProjection (S := S) f) pullback.condition M z =
      sectionExtensionMap (FlatGlobalSections.firstProjection (S := S) f) M
        (originalProductTensorEquiv (S := S) f M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b s =>
      rw [originalBaseChangeMap_tmul, originalProductTensorEquiv_tmul,
        sectionExtensionMap_tmul]
      rfl
  | add z w hz hw => simp only [map_add, hz, hw]

/-- Affineness and quasicoherence DERIVE bijectivity of the SAME
original-base map on the actual geometric product. -/
theorem originalProductMap_bijective_of_affine [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] :
    Function.Bijective (originalBaseChangeMap f (FlatGlobalSections.structureMap (S := S) f)
      (FlatGlobalSections.firstProjection (S := S) f) pullback.condition M) := by
  have h : (fun z => originalBaseChangeMap f (FlatGlobalSections.structureMap (S := S) f)
      (FlatGlobalSections.firstProjection (S := S) f) pullback.condition M z) =
      (fun z => sectionExtensionMap (FlatGlobalSections.firstProjection (S := S) f) M
        (originalProductTensorEquiv (S := S) f M z)) :=
    funext (originalProductMap_eq_sectionExtensionMap (S := S) f M)
  rw [show (originalBaseChangeMap f (FlatGlobalSections.structureMap (S := S) f)
      (FlatGlobalSections.firstProjection (S := S) f) pullback.condition M : _ → _) = _ from h]
  exact (sectionExtensionMap_bijective_of_affine
    (FlatGlobalSections.firstProjection (S := S) f) M).comp
      (originalProductTensorEquiv (S := S) f M).bijective

end OriginalProduct
section AffineLaurent
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The literal finite reconstruction formula for the original-base map,
using its derived actual tensor coefficients and original pullback sections. -/
theorem originalBaseChangeMap_laurent_reconstruction
    (f : X ⟶ Spec (CommRingCat.of R)) {Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of R[T;T⁻¹])) (g : Y ⟶ X)
    (hg : g ≫ f = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])))
    (M : X.Modules) (c : ℤ →₀ originalBaseSections f M) :
    originalBaseChangeMap f q g hg M
        ((originalLaurentDomainCoefficients (originalBaseSections f M)).symm c) =
      c.sum (fun n s => (LaurentPolynomial.T n : R[T;T⁻¹]) •
        (show originalBaseSections q ((Scheme.Modules.pullback g).obj M) from affinePullbackUnitTop g M s)) := by
  rw [originalLaurentDomainCoefficients_symm]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  exact originalBaseChangeMap_tmul f q g hg M _ _

/-- Every WHOLE original section on the actual affine Laurent product has
UNIQUE finite original coefficients, with no decomposition given as input. -/
theorem exists_unique_affine_laurent_expansion [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) [M.IsQuasicoherent]
    (s : originalBaseSections (FlatGlobalSections.structureMap (S := R[T;T⁻¹]) f)
      ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) f)).obj M)) :
    ∃! c : ℤ →₀ originalBaseSections f M,
      c.sum (fun n m => (LaurentPolynomial.T n : R[T;T⁻¹]) •
        (show originalBaseSections (FlatGlobalSections.structureMap (S := R[T;T⁻¹]) f)
          ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) f)).obj M) from
            affinePullbackUnitTop (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) f) M m)) = s := by
  let : Module.Free R R[T;T⁻¹] := Module.Free.of_basis (AddMonoidAlgebra.basis ℤ R)
  have hb := originalProductMap_bijective_of_affine (S := R[T;T⁻¹]) f M
  obtain ⟨z, hz⟩ := hb.2 s
  refine ⟨originalLaurentDomainCoefficients (originalBaseSections f M) z, ?_, ?_⟩
  · have hc := originalBaseChangeMap_laurent_reconstruction f
      (FlatGlobalSections.structureMap (S := R[T;T⁻¹]) f)
      (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) f) pullback.condition M
      (originalLaurentDomainCoefficients (originalBaseSections f M) z)
    rw [(originalLaurentDomainCoefficients _).symm_apply_apply] at hc
    exact hc.symm.trans hz
  · intro c hc
    apply (originalLaurentDomainCoefficients (originalBaseSections f M)).symm.injective
    apply hb.1
    rw [(originalLaurentDomainCoefficients _).symm_apply_apply,
      originalBaseChangeMap_laurent_reconstruction]
    exact hc.trans hz.symm

end AffineLaurent
end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
