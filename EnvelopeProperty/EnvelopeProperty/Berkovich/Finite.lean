/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.ResidueField
import EnvelopeProperty.Berkovich.Topology
import EnvelopeProperty.Berkovich.ValuationIntegral
import EnvelopeProperty.Berkovich.ValuationExtension
import EnvelopeProperty.Berkovich.SpectrumIntegral
import EnvelopeProperty.Berkovich.SpectrumBridge
import EnvelopeProperty.Berkovich.SpectrumFinite
import EnvelopeProperty.Berkovich.SpectrumIntegralImage
import EnvelopeProperty.Berkovich.SpectrumResidueFieldBridge

/-!
# Analytifications of finite morphisms

Let `k` be a field with the trivial absolute value and `φ : B → A` a homomorphism of
`k`-algebras such that `A` is integral over `B` (a finite morphism `π : Spec A → Spec B` when `A`
is of finite type). This file proves the basic properties of `π^an = Berk.comap φ` used in FHX
§5.5 (`lem:finite-flat-norm`, `prop:nonflat-norm`, `prop:projection-step`), following the
description of fibres through completed residue fields (Berkovich, *Spectral theory and analytic
geometry over non-Archimedean fields*, §1.2; see `EnvelopeProperty.Berkovich.ResidueField`).
The completed tensor maps, maximal-kernel classification and fibre finiteness specialize
the arbitrary-ring producers through the canonical trivial-field and completed-field bridges.

* **Properness.** Preimages of compact sets under `π^an` are compact
  (`Berk.isCompact_preimage_comap`), so `π^an` is proper and closed when `B` is of finite type
  (`Berk.isProperMap_comap`, `Berk.isClosedMap_comap`). The proof is the integral equation
  estimate: if `a^n + b_{n-1} a^{n-1} + ⋯ + b_0 = 0` then
  `|a|_y ≤ max(1, max_i |b_i|_{π(y)})` (`EnvelopeProperty.Valuation.le_of_monic_eval₂_eq_zero`).
* **Fibres.** For `y` over `x` there is a homomorphism `H(x) ⊗_B A → H(y)` (`Berk.fibreHom`)
  whose kernel is a maximal ideal (`Berk.isMaximal_ker_fibreHom`); this gives a bijection between
  the fibre of `π^an` over `x` and the maximal spectrum of `H(x) ⊗_B A`
  (`Berk.fibreToMaximalSpectrum_bijective`, `Berk.fibreEquivMaximalSpectrum`): distinct points
  give distinct kernels (`Berk.eq_of_ker_fibreHom_eq`, by uniqueness of extensions of the norm of
  `H(x)`), and every maximal ideal `m` arises (`Berk.exists_ker_fibreHom_eq`: extend the norm of
  `H(x)` to the residue field at `m`). Hence for `A` finite over `B` the fibres of `π^an` are
  finite (`Berk.finite_preimage_singleton`, `Berk.finite_preimage_comap_singleton`).
* **Surjectivity.** If `ker φ ⊆ supp x` (e.g. `φ` injective), there is a point over `x`
  (`Berk.exists_comap_eq`, `Berk.exists_comap_eq_of_isIntegral`,
  `Berk.comap_surjective_of_isIntegral`): the fibre algebra is nonzero by lying over
  (`Berk.nontrivial_fibre`), so it has a maximal ideal.
* **Extensions of absolute values.** For a complete nonarchimedean normed field `K` and an
  algebraic extension `L`, the norm of `K` extends to a unique `ℝ≥0`-valued valuation on `L`
  (`EnvelopeProperty.Valuation.exists_extends_norm`,
  `EnvelopeProperty.Valuation.eq_of_extends_norm`): Mathlib's spectral norm if the norm of `K`
  is nontrivial, the trivial absolute value otherwise.
-/

open scoped NNReal ENNReal Topology

open Topology

noncomputable section

namespace EnvelopeProperty


namespace Berk

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]
  {A : Type*} [CommRing A] [Algebra k A]

/-! ### Properness -/

/-- If `a` is integral over `B`, then `|a|_y` is bounded on the preimage of a compact set. -/
theorem exists_abs_le_of_isIntegral (φ : B →ₐ[k] A) {a : A} (ha : (φ : B →+* A).IsIntegralElem a)
    {K : Set (Berk k B)} (hK : IsCompact K) :
    ∃ R : ℝ≥0, ∀ y : Berk k A, comap φ y ∈ K → y.val a ≤ R := by
  classical
  obtain ⟨p, hp, hpa⟩ := ha
  obtain ⟨R, hR⟩ := exists_forall_abs_le_of_isCompact hK
    ((Finset.range p.natDegree).image p.coeff)
  refine ⟨max 1 R, fun y hy => ?_⟩
  refine Valuation.le_of_monic_eval₂_eq_zero y.val (φ : B →+* A) hp hpa (le_max_left _ _)
    fun i hi => ?_
  exact (hR hy (p.coeff i) (Finset.mem_image_of_mem _ (Finset.mem_range.2 hi))).trans
    (le_max_right _ _)

/-- **Properness of finite morphisms.** If `A` is integral over `B`, the preimage under
`π^an = comap φ` of a compact subset of `(Spec B)^an` is compact. -/
theorem isCompact_preimage_comap (φ : B →ₐ[k] A) (hφ : (φ : B →+* A).IsIntegral)
    {K : Set (Berk k B)} (hK : IsCompact K) : IsCompact (comap φ ⁻¹' K) := by
  let eA := relativeSpectrumHomeomorph (k := k) (A := A)
  let eB := relativeSpectrumHomeomorph (k := k) (A := B)
  have heq : eA ⁻¹' (Berkovich.RelativeSpectrum.comap φ ⁻¹' (eB '' K)) =
      comap φ ⁻¹' K := by
    ext y
    change eB (comap φ y) ∈ eB '' K ↔ comap φ y ∈ K
    constructor
    · rintro ⟨x, hx, hxy⟩
      have he : x = comap φ y := eB.injective hxy
      rwa [he] at hx
    · intro hy
      exact ⟨comap φ y, hy, rfl⟩
  rw [← heq]
  exact eA.isCompact_preimage.mpr
    (Berkovich.RelativeSpectrum.isCompact_preimage_comap_of_isIntegral φ hφ
      (hK.image eB.continuous))

/-- For `A` integral over `B` and `B` of finite type, `π^an = comap φ` is a proper map. -/
theorem isProperMap_comap [Algebra.FiniteType k B] (φ : B →ₐ[k] A)
    (hφ : (φ : B →+* A).IsIntegral) : IsProperMap (comap (k := k) φ) :=
  isProperMap_iff_isCompact_preimage.2
    ⟨continuous_comap φ, fun _ hK => isCompact_preimage_comap φ hφ hK⟩

/-- For `A` integral over `B` and `B` of finite type, `π^an = comap φ` is a closed map. -/
theorem isClosedMap_comap [Algebra.FiniteType k B] (φ : B →ₐ[k] A)
    (hφ : (φ : B →+* A).IsIntegral) : IsClosedMap (comap (k := k) φ) :=
  (isProperMap_comap φ hφ).isClosedMap

/-! ### Fibres: points over `x` and the fibre algebra `H(x) ⊗_B A` -/

section fibre

open TensorProduct

variable [Algebra B A] [IsScalarTower k B A]

/-- The paper fibre is exactly the corresponding fibre in the prescribed trivial-base spectrum. -/
private def relativeFibreEquiv (x : Berk k B) :
    comap (IsScalarTower.toAlgHom k B A) ⁻¹' {x} ≃
      Berkovich.RelativeSpectrum.Fibre (B := A) (relativeSpectrumHomeomorph x) where
  toFun y := ⟨relativeSpectrumHomeomorph y.1,
    congrArg relativeSpectrumHomeomorph (Set.mem_singleton_iff.mp y.2)⟩
  invFun y := ⟨relativeSpectrumHomeomorph.symm y.1, by
    apply Set.mem_singleton_iff.mpr
    apply relativeSpectrumHomeomorph.injective
    rw [relativeSpectrumHomeomorph_comap]
    simpa only [Homeomorph.apply_symm_apply] using y.2⟩
  left_inv y := Subtype.ext (relativeSpectrumHomeomorph.symm_apply_apply y.1)
  right_inv y := Subtype.ext (relativeSpectrumHomeomorph.apply_symm_apply y.1)

/-- For a point `y ∈ (Spec A)^an` over `x ∈ (Spec B)^an`, the homomorphism
`H(x) ⊗_B A → H(y)`, `c ⊗ a ↦ c · a`, built from `H(x) → H(y)` and `A → H(y)`. -/
def fibreHom {x : Berk k B} {y : Berk k A} (h : comap (IsScalarTower.toAlgHom k B A) y = x) :
    H x ⊗[B] A →+* H y :=
  Berkovich.Spectrum.fibreHom (x := x.toSpectrum) (y := y.toSpectrum)
    (show Berkovich.Spectrum.comap (algebraMap B A) y.toSpectrum = x.toSpectrum from
      congrArg toSpectrum h)

@[simp]
theorem fibreHom_tmul {x : Berk k B} {y : Berk k A}
    (h : comap (IsScalarTower.toAlgHom k B A) y = x) (c : H x) (a : A) :
    fibreHom h (c ⊗ₜ a) = H.map _ h c * toH y a :=
  rfl

theorem fibreHom_one_tmul {x : Berk k B} {y : Berk k A}
    (h : comap (IsScalarTower.toAlgHom k B A) y = x) (a : A) :
    fibreHom h (1 ⊗ₜ a) = toH y a := by
  rw [fibreHom_tmul, map_one, one_mul]

theorem fibreHom_tmul_one {x : Berk k B} {y : Berk k A}
    (h : comap (IsScalarTower.toAlgHom k B A) y = x) (c : H x) :
    fibreHom h (c ⊗ₜ 1) = H.map _ h c := by
  rw [fibreHom_tmul, map_one, mul_one]

/-- For `A` integral over `B`, the kernel of `H(x) ⊗_B A → H(y)` is a maximal ideal. -/
theorem isMaximal_ker_fibreHom [Algebra.IsIntegral B A] {x : Berk k B} {y : Berk k A}
    (h : comap (IsScalarTower.toAlgHom k B A) y = x) : (RingHom.ker (fibreHom h)).IsMaximal :=
  Berkovich.Spectrum.isMaximal_ker_fibreHom (x := x.toSpectrum) (y := y.toSpectrum)
    (show Berkovich.Spectrum.comap (algebraMap B A) y.toSpectrum = x.toSpectrum from
      congrArg toSpectrum h)

omit [Algebra k A] [IsScalarTower k B A] in
/-- `b ⊗ 1 = 1 ⊗ b` in `H(x) ⊗_B A`. -/
theorem algebraMap_tmul_one_eq (x : Berk k B) (b : B) :
    (algebraMap B (H x) b ⊗ₜ[B] (1 : A)) = (1 : H x) ⊗ₜ algebraMap B A b :=
  (Algebra.TensorProduct.algebraMap_apply b).symm.trans (Algebra.TensorProduct.algebraMap_apply' b)

/-- **Distinct points over `x` give distinct maximal ideals of `H(x) ⊗_B A`.** For `A` integral
over `B`, a point `y` over `x` is determined by the kernel of `H(x) ⊗_B A → H(y)`: both points
induce absolute values on the residue field of the kernel, an algebraic extension of the complete
field `H(x)`, extending the norm of `H(x)`, and such extensions are unique. -/
theorem eq_of_ker_fibreHom_eq [Algebra.IsIntegral B A] {x : Berk k B} {y₁ y₂ : Berk k A}
    (h₁ : comap (IsScalarTower.toAlgHom k B A) y₁ = x)
    (h₂ : comap (IsScalarTower.toAlgHom k B A) y₂ = x)
    (hker : RingHom.ker (fibreHom h₁) = RingHom.ker (fibreHom h₂)) : y₁ = y₂ := by
  have he := Berkovich.Spectrum.eq_of_ker_fibreHom_eq (x := x.toSpectrum)
    (y₁ := y₁.toSpectrum) (y₂ := y₂.toSpectrum)
    (show Berkovich.Spectrum.comap (algebraMap B A) y₁.toSpectrum = x.toSpectrum from
      congrArg toSpectrum h₁)
    (show Berkovich.Spectrum.comap (algebraMap B A) y₂.toSpectrum = x.toSpectrum from
      congrArg toSpectrum h₂) hker
  exact ext_val fun a => congrArg (fun z : Berkovich.Spectrum A => z.val a) he

/-- For `A` integral over `B`, the map from the fibre of `π^an` over `x` to the maximal spectrum
of the fibre algebra `H(x) ⊗_B A`, `y ↦ ker (H(x) ⊗_B A → H(y))`. It is bijective
(`Berk.fibreToMaximalSpectrum_bijective`). -/
def fibreToMaximalSpectrum [Algebra.IsIntegral B A] (x : Berk k B) :
    comap (IsScalarTower.toAlgHom k B A) ⁻¹' {x} → MaximalSpectrum (H x ⊗[B] A) :=
  fun y => ⟨RingHom.ker (fibreHom y.2), isMaximal_ker_fibreHom y.2⟩

/-- **Points over `x` ↔ maximal ideals of `H(x) ⊗_B A`** (FHX §5.5, proof of
`lem:finite-flat-norm`). -/
theorem fibreToMaximalSpectrum_bijective [Algebra.IsIntegral B A] (x : Berk k B) :
    Function.Bijective (fibreToMaximalSpectrum (A := A) x) := by
  have he : fibreToMaximalSpectrum (A := A) x =
      Berkovich.RelativeSpectrum.fibreEquivMaximalSpectrum (relativeSpectrumHomeomorph x) ∘
        relativeFibreEquiv (A := A) x := by
    funext y
    apply MaximalSpectrum.ext
    rfl
  rw [he]
  exact (Berkovich.RelativeSpectrum.fibreEquivMaximalSpectrum
    (relativeSpectrumHomeomorph x)).bijective.comp (relativeFibreEquiv x).bijective

/-- The bijection between the fibre of `π^an` over `x` and the maximal spectrum of
`H(x) ⊗_B A`. -/
def fibreEquivMaximalSpectrum [Algebra.IsIntegral B A] (x : Berk k B) :
    comap (IsScalarTower.toAlgHom k B A) ⁻¹' {x} ≃ MaximalSpectrum (H x ⊗[B] A) :=
  Equiv.ofBijective _ (fibreToMaximalSpectrum_bijective x)

omit [Algebra k A] [IsScalarTower k B A] in
/-- If `A` is integral over `B` and `x` lies in the image of `Spec A → Spec B` (e.g. `B → A`
injective), the fibre algebra `H(x) ⊗_B A` is nonzero. -/
theorem nontrivial_fibre [Algebra.IsIntegral B A] (x : Berk k B)
    (hx : RingHom.ker (algebraMap B A) ≤ x.val.supp) : Nontrivial (H x ⊗[B] A) :=
  Berkovich.Spectrum.nontrivial_fibre (B := A) x.toSpectrum hx

/-- **Every maximal ideal of `H(x) ⊗_B A` comes from a point over `x`.** This specializes
 the genuine completed tensor-fibre classification; the canonical point correspondence
 preserves the kernel of the whole tensor homomorphism. -/
theorem exists_ker_fibreHom_eq [Algebra.IsIntegral B A] (x : Berk k B)
    (m : Ideal (H x ⊗[B] A)) [m.IsMaximal] :
    ∃ (y : Berk k A) (h : comap (IsScalarTower.toAlgHom k B A) y = x),
      RingHom.ker (fibreHom h) = m := by
  obtain ⟨y, hy⟩ := (fibreToMaximalSpectrum_bijective (A := A) x).2 ⟨m, inferInstance⟩
  refine ⟨y.1, Set.mem_singleton_iff.mp y.2, ?_⟩
  exact congrArg MaximalSpectrum.asIdeal hy

/-- **Surjectivity of finite morphisms.** If `A` is integral over `B` and
`ker (B → A) ⊆ supp x`, there is a point `y ∈ (Spec A)^an` over `x`: the fibre algebra
`H(x) ⊗_B A` is nonzero (`Berk.nontrivial_fibre`), and any maximal ideal of it comes from a point
over `x` (`Berk.exists_ker_fibreHom_eq`). -/
theorem exists_comap_eq [Algebra.IsIntegral B A] (x : Berk k B)
    (hx : RingHom.ker (algebraMap B A) ≤ x.val.supp) :
    ∃ y : Berk k A, comap (IsScalarTower.toAlgHom k B A) y = x := by
  obtain ⟨y, hy⟩ := Berkovich.RelativeSpectrum.exists_comap_eq_of_isIntegral
    (IsScalarTower.toAlgHom k B A) (fun a => Algebra.IsIntegral.isIntegral a)
    (relativeSpectrumHomeomorph x) hx
  refine ⟨relativeSpectrumHomeomorph.symm y, ?_⟩
  apply relativeSpectrumHomeomorph.injective
  rw [relativeSpectrumHomeomorph_comap]
  simpa only [Homeomorph.apply_symm_apply] using hy

/-- **Finiteness of fibres.** If `A` is a finite `B`-module, every fibre of
`π^an : (Spec A)^an → (Spec B)^an` is finite: it is in bijection with the maximal spectrum of the
fibre algebra `H(x) ⊗_B A`, which is a finite `H(x)`-algebra, hence Artinian. -/
theorem finite_preimage_singleton [Module.Finite B A] (x : Berk k B) :
    (comap (IsScalarTower.toAlgHom k B A) ⁻¹' {x}).Finite := by
  have : Finite (Berkovich.RelativeSpectrum.Fibre (B := A) (relativeSpectrumHomeomorph x)) :=
    Berkovich.RelativeSpectrum.finite_fibre (relativeSpectrumHomeomorph x)
  have : Finite (comap (IsScalarTower.toAlgHom k B A) ⁻¹' {x}) :=
    Finite.of_injective _ (relativeFibreEquiv (A := A) x).injective
  exact Set.toFinite _

end fibre

/-! ### Fibres for a `k`-algebra homomorphism `φ : B → A` -/

section hom

/-- **Finiteness of fibres** for a finite `k`-algebra map `φ : B → A`. -/
theorem finite_preimage_comap_singleton (φ : B →ₐ[k] A) (hφ : (φ : B →+* A).Finite)
    (x : Berk k B) : (comap φ ⁻¹' {x}).Finite := by
  let : Algebra B A := (φ : B →+* A).toAlgebra
  have : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have : Module.Finite B A := hφ
  have e : IsScalarTower.toAlgHom k B A = φ := AlgHom.ext fun _ => rfl
  rw [← e]
  exact finite_preimage_singleton x

/-- **Points over `x`** for an integral `k`-algebra map `φ : B → A` with `ker φ ⊆ supp x`. -/
theorem exists_comap_eq_of_isIntegral (φ : B →ₐ[k] A) (hφ : (φ : B →+* A).IsIntegral)
    (x : Berk k B) (hx : RingHom.ker (φ : B →+* A) ≤ x.val.supp) :
    ∃ y : Berk k A, comap φ y = x := by
  obtain ⟨y, hy⟩ := Berkovich.RelativeSpectrum.exists_comap_eq_of_isIntegral
    φ hφ (relativeSpectrumHomeomorph x) hx
  refine ⟨relativeSpectrumHomeomorph.symm y, ?_⟩
  apply relativeSpectrumHomeomorph.injective
  rw [relativeSpectrumHomeomorph_comap]
  simpa only [Homeomorph.apply_symm_apply] using hy

/-- **Surjectivity of finite morphisms**: for an injective integral `k`-algebra map `φ : B → A`,
`π^an = comap φ` is surjective. -/
theorem comap_surjective_of_isIntegral (φ : B →ₐ[k] A) (hφ : (φ : B →+* A).IsIntegral)
    (hinj : Function.Injective φ) : Function.Surjective (comap (k := k) φ) := fun x =>
  exists_comap_eq_of_isIntegral φ hφ x (by
    rw [(RingHom.injective_iff_ker_eq_bot (φ : B →+* A)).1 hinj]
    exact bot_le)

end hom

end Berk

end EnvelopeProperty
