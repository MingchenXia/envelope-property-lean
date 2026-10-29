/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.AffineLineComponents
import EnvelopeProperty.GeometricDomain
import EnvelopeProperty.Berkovich.AlgebraScalarExtension
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Genuine scalar extension of ambient affine maps and their line components

The actual scalar-extended polynomial principal-open coordinate ring is
identified by whole tensor/localization isomorphisms. This constructs the
literal coefficient-extended ambient map and proves its genuine finiteness
and injectivity under coefficient flatness. For an original domain over an
algebraically closed field, actual geometric domain preservation supplies the
extended ambient domain. The actual component producers then derive whole
injectivity, quotient dimension one and prime-map surjectivity after any
field extension, without a geometric-domain or component witness.

No completeness, field norm, infinitude, perfectness, separability or original
normality is assumed. Finite coordinates are used only in component geometry;
normalization and potential-theoretic conclusions remain separate producers.
-/

open scoped Classical Polynomial TensorProduct
noncomputable section
namespace EnvelopeProperty.AffineLine
variable {k F σ : Type*} [CommRing k] [CommRing F] [Algebra k F]

/-- The actual whole scalar-extended polynomial principal-open ring is the principal open of the actual coefficient polynomial map. -/
def principalOpenTensorEquiv (g : MvPolynomial σ k) :
    F ⊗[k] Localization.Away g ≃ₐ[F]
      Localization.Away (MvPolynomial.map (algebraMap k F) g) :=
  (IsLocalization.Away.tensorProductEquivTMulRight k F g (Localization.Away g)).trans
    (IsLocalization.algEquivOfAlgEquiv
      (M := Submonoid.powers ((1 : F) ⊗ₜ[k] g))
      (T := Submonoid.powers (MvPolynomial.map (algebraMap k F) g))
      (Localization.Away ((1 : F) ⊗ₜ[k] g))
      (Localization.Away (MvPolynomial.map (algebraMap k F) g))
      (MvPolynomial.algebraTensorAlgEquiv (σ := σ) k F) (by
        rw [Submonoid.map_powers]
        congr 1
        simp only [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]))

/-- Every entire original polynomial and coefficient is retained by the true localized tensor equivalence. -/
theorem principalOpenTensorEquiv_tmul (g q : MvPolynomial σ k) (s : F) :
    principalOpenTensorEquiv g (s ⊗ₜ[k] (algebraMap _ (Localization.Away g) q)) =
      algebraMap _ (Localization.Away (MvPolynomial.map (algebraMap k F) g))
        (s • MvPolynomial.map (algebraMap k F) q) := by
  rw [principalOpenTensorEquiv, AlgEquiv.trans_apply,
    IsLocalization.Away.tensorProductEquivTMulRight_tmul,
    IsLocalization.algEquivOfAlgEquiv_eq, MvPolynomial.algebraTensorAlgEquiv_tmul]

variable {B : Type*} [CommRing B] [Algebra k B]

/-- The actual scalar-extended whole ambient homomorphism, expressed over the true polynomial principal-open ring. -/
def principalOpenScalarMap (g : MvPolynomial σ k)
    (φ : Localization.Away g →ₐ[k] B) :
    Localization.Away (MvPolynomial.map (algebraMap k F) g) →ₐ[F] F ⊗[k] B :=
  (Algebra.TensorProduct.map (AlgHom.id F F) φ).comp
    (principalOpenTensorEquiv g).symm.toAlgHom

/-- The complete tensor diagram holds on every original scalar-extended localized element. -/
theorem principalOpenScalarMap_tensor (g : MvPolynomial σ k)
    (φ : Localization.Away g →ₐ[k] B) (z : F ⊗[k] Localization.Away g) :
    principalOpenScalarMap g φ (principalOpenTensorEquiv g z) =
      Algebra.TensorProduct.map (AlgHom.id F F) φ z := by
  simp only [principalOpenScalarMap, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]

/-- The actual new map preserves every entire original polynomial in the scalar-extension diagram. -/
theorem principalOpenScalarMap_algebraMap (g q : MvPolynomial σ k)
    (φ : Localization.Away g →ₐ[k] B) :
    principalOpenScalarMap g φ
        (algebraMap _ (Localization.Away (MvPolynomial.map (algebraMap k F) g))
          (MvPolynomial.map (algebraMap k F) q)) =
      (1 : F) ⊗ₜ[k] φ (algebraMap _ (Localization.Away g) q) := by
  have he := principalOpenTensorEquiv_tmul (F := F) g q 1
  simp only [one_smul] at he
  rw [← he, principalOpenScalarMap_tensor]
  rfl

/-- True tensor cancellation preserves finiteness of the entire original ambient map under scalar extension. -/
theorem principalOpenScalarMap_finite (g : MvPolynomial σ k)
    (φ : Localization.Away g →ₐ[k] B) (hφ : φ.toRingHom.Finite) :
    (principalOpenScalarMap (F := F) g φ).toRingHom.Finite := by
  let R := Localization.Away g
  let : Algebra R B := φ.toRingHom.toAlgebra
  have : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have : Module.Finite R B := hφ
  have hm : (Algebra.TensorProduct.map (AlgHom.id F F) φ).toRingHom.Finite := by
    let : Algebra (F ⊗[k] R) (F ⊗[k] B) := ScalarExtension.algebra k F R B
    exact ScalarExtension.moduleFinite k F R B
  exact hm.comp (RingHom.Finite.of_surjective _ (principalOpenTensorEquiv g).symm.surjective)

end EnvelopeProperty.AffineLine

namespace EnvelopeProperty.AffineLine
variable {k F σ B : Type*} [CommRing k] [CommRing F] [CommRing B]
  [Algebra k F] [Algebra k B] [Module.Flat k F]

/-- Genuine coefficient flatness preserves injectivity of the entire original ambient homomorphism. -/
theorem principalOpenScalarMap_injective (g : MvPolynomial σ k)
    (φ : Localization.Away g →ₐ[k] B) (hiφ : Function.Injective φ) :
    Function.Injective (principalOpenScalarMap (F := F) g φ) := by
  have hm : Function.Injective (Algebra.TensorProduct.map (AlgHom.id F F) φ) := by
    exact Module.Flat.lTensor_preserves_injective_linearMap φ.toLinearMap hiφ
  exact hm.comp (principalOpenTensorEquiv g).symm.injective

end EnvelopeProperty.AffineLine

namespace EnvelopeProperty.AffineLine
variable {k F σ B : Type*} [Field k] [IsAlgClosed k] [Field F]
  [CommRing B] [IsDomain B] [Algebra k F] [Algebra k B]

variable [Fintype σ]
variable (g : MvPolynomial σ k) (hg : g ≠ 0)
variable (φ : Localization.Away g →ₐ[k] B) (hφ : φ.toRingHom.Finite)
variable (hiφ : Function.Injective φ)
variable (a b : σ → F) (j : σ) (hb : b j ≠ 0)
variable (hline : subst a b (MvPolynomial.map (algebraMap k F) g) ≠ 0)
variable (P : Ideal (F ⊗[k] B))
variable (hP : P ∈ ((lineIdeal a b j).map
  ((principalOpenScalarMap g φ).toRingHom.comp
    (algebraMap _ (Localization.Away (MvPolynomial.map (algebraMap k F) g))))).minimalPrimes)

include hg hφ hiφ hline in
/-- Genuine geometric domain preservation and the true extended finite map derive injectivity for every actual scalar-extended line component. -/
theorem scalarComponentLineHom_injective :
    Function.Injective (componentLineHom a b j
      (MvPolynomial.map (algebraMap k F) g) hb (principalOpenScalarMap g φ) P hP) := by
  have : IsDomain (F ⊗[k] B) := tensorProduct_isDomain_of_algClosed k F B
  have hg' : MvPolynomial.map (algebraMap k F) g ≠ 0 :=
    (map_ne_zero_iff (MvPolynomial.map (algebraMap k F))
      (MvPolynomial.map_injective _ (RingHom.injective (algebraMap k F)))).mpr hg
  exact componentLineHom_injective a b j _ hb _ P hP hg' hline
    (principalOpenScalarMap_finite g φ hφ) (principalOpenScalarMap_injective g φ hiφ)

include hg hφ hiφ hb hline hP in
/-- Every actual original line component after field scalar extension has true quotient dimension one. -/
theorem scalarComponent_quotient_ringKrullDim_eq_one :
    ringKrullDim ((F ⊗[k] B) ⧸ P) = 1 := by
  have : IsDomain (F ⊗[k] B) := tensorProduct_isDomain_of_algClosed k F B
  have hg' : MvPolynomial.map (algebraMap k F) g ≠ 0 :=
    (map_ne_zero_iff (MvPolynomial.map (algebraMap k F))
      (MvPolynomial.map_injective _ (RingHom.injective (algebraMap k F)))).mpr hg
  exact component_quotient_ringKrullDim_eq_one a b j _ hb _ P hP hg' hline
    (principalOpenScalarMap_finite g φ hφ) (principalOpenScalarMap_injective g φ hiφ)

include hg hφ hiφ hline in
/-- The actual scalar-extended line component maps onto the entire original open line by genuine integral lying-over. -/
theorem scalarComponentLineHom_comap_surjective :
    Function.Surjective (PrimeSpectrum.comap
      (componentLineHom a b j (MvPolynomial.map (algebraMap k F) g) hb
        (principalOpenScalarMap g φ) P hP).toRingHom) := by
  have : IsDomain (F ⊗[k] B) := tensorProduct_isDomain_of_algClosed k F B
  have hg' : MvPolynomial.map (algebraMap k F) g ≠ 0 :=
    (map_ne_zero_iff (MvPolynomial.map (algebraMap k F))
      (MvPolynomial.map_injective _ (RingHom.injective (algebraMap k F)))).mpr hg
  exact componentLineHom_comap_surjective a b j _ hb _ P hP hg' hline
    (principalOpenScalarMap_finite g φ hφ) (principalOpenScalarMap_injective g φ hiφ)

end EnvelopeProperty.AffineLine
