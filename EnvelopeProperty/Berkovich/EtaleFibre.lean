/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.NormIdentity
import EnvelopeProperty.Berkovich.NormForm
import EnvelopeProperty.Berkovich.Finite
import EnvelopeProperty.Berkovich.SpectrumEtaleNormForm

/-!
# Fibres of finite free étale morphisms and the norm identity at a point

Let `k` be a field with the trivial absolute value, `B → A` a homomorphism of `k`-algebras making
`A` a finite free étale `B`-algebra, and `π = π^an : (Spec A)^an → (Spec B)^an` the induced map
(`Berk.comap (IsScalarTower.toAlgHom k B A)`). This file proves the pointwise part of
Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Lemma 5.13
(`lem:finite-flat-norm`), in the finite free étale form of the blueprint remark
`rmk:finite-flat-norm-etale`.

For `x ∈ (Spec B)^an` the fibre algebra `E = H(x) ⊗_B A` is a finite étale algebra over the
complete field `H(x)`; it is reduced and Artinian, hence `E ≃ ∏_m E/m` over its maximal ideals
(`Berk.fibreEquivPi`), and the factors `E/m` are finite separable field extensions of `H(x)`.
The points `y` over `x` correspond to the maximal ideals `m_y = ker (E → H(y))`
(`Berk.fibreEquivMaximalSpectrum`). The **multiplicity** of `y` is the residue degree
`m_y(π) = [E/m_y : H(x)]` (`Berk.fibreMult`); it is positive (`Berk.one_le_fibreMult`) and the
multiplicities over `x` add up to the degree `[A : B]` (`Berk.sum_fibreMult`).

For `b_j ∈ A` (`j ∈ σ`, a finite type) the **norm form** `P = N_{B[X]⊗_B A/B[X]}(∑_j X_j ⊗ b_j)`
(`EnvelopeProperty.normForm`) is a polynomial with coefficients in `B`, and its image in `K[X]`
evaluates at `t ∈ K^σ` to `N_{K ⊗_B A/K}(∑_j t_j (1 ⊗ b_j))` for every `B`-algebra `K`
(`EnvelopeProperty.eval_map_normForm`). The **norm identity at a point**
(`Berk.wgaussValuation_map_normForm_of_etale`): for radii `r_j ≥ 0`,
`max_α |c_α|_x r^α = ∏_{π(y) = x} (max_j |b_j|_y r_j)^{m_y(π)}`,
where `P = ∑_α c_α X^α`. The actual determinant polynomial commutes with completed
residue-field base change and splits over an algebraic closure. Completeness identifies
the conjugate values. This proof needs no infinitude of `k` or `H(x)`.

## Main definitions

* `Berk.fibreMult B y`: the multiplicity `m_y(π) = [(H(x) ⊗_B A)/m_y : H(x)]`, `x = π(y)`.
* `Berk.fibreEquivPi x`: `H(x) ⊗_B A ≃ₐ[H(x)] ∏_m (H(x) ⊗_B A)/m` (étale case).
* `EnvelopeProperty.normForm B b`: the norm form `N(∑_j X_j b_j) ∈ B[X_j : j ∈ σ]`.

## Main results

* `Berk.one_le_fibreMult`, `Berk.sum_fibreMult`: `m_y(π) ≥ 1` and `∑_{π(y) = x} m_y(π) = [A : B]`.
* `EnvelopeProperty.eval_map_normForm`: the norm form commutes with base change.
* `Berk.val_algebraNorm`: the scalar norm identity, without an infinitude hypothesis.
* `Berk.wgaussValuation_map_normForm_of_etale`, `Berk.wgaussValuation_normForm_of_etale`:
  the weighted norm-form identity without an infinitude hypothesis.
* `Berk.wgaussValuation_map_normForm`: the original compatibility interface.
-/

open scoped NNReal ENNReal Topology TensorProduct

open MvPolynomial

noncomputable section

namespace EnvelopeProperty


namespace Berk

variable {k : Type*} [Field k] {B A : Type*} [CommRing B] [CommRing A] [kB : Algebra k B]
  [Algebra k A] [Algebra B A] [tower : IsScalarTower k B A]

/-- An absolute point over the paper's fixed base point inherits all trivial scalar values. -/
private def pointOfSpectrumFibre (x : Berk k B)
    (y : Berkovich.Spectrum.comap (algebraMap B A) ⁻¹' {x.toSpectrum}) : Berk k A where
  val := y.1.val
  val_algebraMap c hc := by
    have h := congrArg (fun z : Berkovich.Spectrum B => z.val (algebraMap k B c))
      (Set.mem_singleton_iff.mp y.2)
    change y.1.val (algebraMap B A (algebraMap k B c)) = x.val (algebraMap k B c) at h
    rw [← IsScalarTower.algebraMap_apply k B A] at h
    exact h.trans (x.val_algebraMap c hc)

/-- The whole-point fibre correspondence between the old and absolute seminorm interfaces. -/
private def spectrumFibreEquiv (x : Berk k B) :
    comap (IsScalarTower.toAlgHom k B A) ⁻¹' {x} ≃
      Berkovich.Spectrum.comap (algebraMap B A) ⁻¹' {x.toSpectrum} where
  toFun y := ⟨y.1.toSpectrum, Set.mem_singleton_iff.mpr
    (congrArg toSpectrum (Set.mem_singleton_iff.mp y.2))⟩
  invFun y := ⟨pointOfSpectrumFibre x y, Set.mem_singleton_iff.mpr (by
    apply ext_val
    intro b
    exact congrArg (fun z : Berkovich.Spectrum B => z.val b)
      (Set.mem_singleton_iff.mp y.2))⟩
  left_inv y := Subtype.ext (Berk.ext rfl)
  right_inv y := Subtype.ext (Berkovich.Spectrum.ext rfl)

omit [Algebra k A] [IsScalarTower k B A] in
/-- A ring with a point in its analytification is nontrivial (it maps to the field `H(x)`). -/
theorem nontrivial_of_berk (x : Berk k B) : Nontrivial B := (toH x).domain_nontrivial

/-! ### Fibre multiplicities -/

/-- The **multiplicity** `m_y(π)` of a point `y ∈ (Spec A)^an` in its fibre over
`x = π(y)`: the residue degree `[(H(x) ⊗_B A)/m_y : H(x)]`, where
`m_y = ker (H(x) ⊗_B A → H(y))` (FHX `lem:finite-flat-norm`, `rmk:finite-flat-norm-etale`). -/
def fibreMult {k : Type*} [Field k] (B : Type*) {A : Type*}
    [CommRing B] [CommRing A] [Algebra k B] [Algebra k A]
    [Algebra B A] [IsScalarTower k B A] (y : Berk k A) : ℕ :=
  Berkovich.Spectrum.fibreMult B y.toSpectrum

/-- The multiplicity of `y` computed at any `x` with `π(y) = x`. -/
theorem fibreMult_eq {x : Berk k B} {y : Berk k A}
    (h : comap (IsScalarTower.toAlgHom k B A) y = x) :
    fibreMult B y = Module.finrank (H x) ((H x ⊗[B] A) ⧸ RingHom.ker (fibreHom h)) := by
  subst h; rfl

/-- **Multiplicities are positive** (for `A` finite over `B`): `(H(x) ⊗_B A)/m_y` is a nonzero
finite-dimensional `H(x)`-vector space. -/
theorem one_le_fibreMult [Module.Finite B A] (y : Berk k A) : 1 ≤ fibreMult B y :=
  Berkovich.Spectrum.one_le_fibreMult (B := B) y.toSpectrum

/-- The maximal ideal attached to a point `y` over `x` is `ker (H(x) ⊗_B A → H(y))`. -/
theorem fibreEquivMaximalSpectrum_asIdeal [Algebra.IsIntegral B A] (x : Berk k B)
    (y : comap (IsScalarTower.toAlgHom k B A) ⁻¹' {x}) :
    (fibreEquivMaximalSpectrum x y).asIdeal = RingHom.ker (fibreHom y.2) := rfl

/-! ### The fibre algebra of a finite étale morphism -/

omit [Algebra k A] [IsScalarTower k B A] in
instance isArtinianRing_fibre [Module.Finite B A] (x : Berk k B) :
    IsArtinianRing (H x ⊗[B] A) :=
  Berkovich.Spectrum.isArtinianRing_fibre x.toSpectrum

omit [Algebra k A] [IsScalarTower k B A] in
/-- The fibre algebra of an étale morphism is reduced: it is étale over the field `H(x)`. -/
instance isReduced_fibre [Algebra.Etale B A] (x : Berk k B) : IsReduced (H x ⊗[B] A) :=
  Berkovich.Spectrum.isReduced_fibre x.toSpectrum

omit [Algebra k A] [IsScalarTower k B A] in
/-- For `A` finite étale over `B`, the fibre algebra `H(x) ⊗_B A` is the product of its residue
fields at its maximal ideals (a reduced Artinian ring, `IsArtinianRing.equivPi`). -/
def fibreEquivPi [Module.Finite B A] [Algebra.Etale B A] (x : Berk k B) :
    (H x ⊗[B] A) ≃ₐ[H x] ∀ m : MaximalSpectrum (H x ⊗[B] A), (H x ⊗[B] A) ⧸ m.asIdeal :=
  Berkovich.Spectrum.fibreEquivPi x.toSpectrum

omit [Algebra k A] [IsScalarTower k B A] in
theorem fibreEquivPi_apply [Module.Finite B A] [Algebra.Etale B A] (x : Berk k B)
    (z : H x ⊗[B] A) (m : MaximalSpectrum (H x ⊗[B] A)) :
    fibreEquivPi x z m = Ideal.Quotient.mk m.asIdeal z := rfl

/-- **The multiplicities over a point add up to the degree** (FHX `lem:finite-flat-norm`, finite
free étale case): `∑_{π(y) = x} m_y(π) = [A : B]`. Indeed `[A : B] = [H(x) ⊗_B A : H(x)]`
(base change of a free module), `H(x) ⊗_B A ≃ ∏_m (H(x) ⊗_B A)/m` (`Berk.fibreEquivPi`), and the
maximal ideals correspond to the points over `x` (`Berk.fibreEquivMaximalSpectrum`). -/
theorem sum_fibreMult [Module.Free B A] [Module.Finite B A] [Algebra.Etale B A] (x : Berk k B) :
    ∑ y ∈ (finite_preimage_singleton (A := A) x).toFinset, fibreMult B y =
      Module.finrank B A := by
  classical
  have hg := Berkovich.Spectrum.sum_fibreMult (A := A) x.toSpectrum
  rw [← hg]
  refine Finset.sum_bij
    (fun y hy => (spectrumFibreEquiv x ⟨y, (Set.Finite.mem_toFinset _).mp hy⟩).1) ?_ ?_ ?_ ?_
  · intro y hy
    exact (Set.Finite.mem_toFinset _).mpr (spectrumFibreEquiv x ⟨y,
      (Set.Finite.mem_toFinset _).mp hy⟩).2
  · intro y₁ hy₁ y₂ hy₂ he
    exact congrArg Subtype.val ((spectrumFibreEquiv x).injective (Subtype.ext he))
  · intro y hy
    obtain ⟨z, hz⟩ := (spectrumFibreEquiv x).surjective ⟨y, (Set.Finite.mem_toFinset _).mp hy⟩
    exact ⟨z.1, (Set.Finite.mem_toFinset _).mpr z.2, congrArg Subtype.val hz⟩
  · intro y hy
    rfl

/-- Scalar norm identity from the generic producer, with no infinitude hypothesis. -/
theorem val_algebraNorm [Module.Free B A] [Module.Finite B A] [Algebra.Etale B A]
    (b : A) (x : Berk k B) :
    x.val (Algebra.norm B b) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset, y.val b ^ fibreMult B y := by
  classical
  have hg := Berkovich.Spectrum.val_algebraNorm (B := B) b x.toSpectrum
  change x.toSpectrum.val (Algebra.norm B b) = _
  rw [hg]
  symm
  refine Finset.prod_bij
    (fun y hy => (spectrumFibreEquiv x ⟨y, (Set.Finite.mem_toFinset _).mp hy⟩).1) ?_ ?_ ?_ ?_
  · intro y hy
    exact (Set.Finite.mem_toFinset _).mpr (spectrumFibreEquiv x ⟨y,
      (Set.Finite.mem_toFinset _).mp hy⟩).2
  · intro y₁ hy₁ y₂ hy₂ he
    exact congrArg Subtype.val ((spectrumFibreEquiv x).injective (Subtype.ext he))
  · intro y hy
    obtain ⟨z, hz⟩ := (spectrumFibreEquiv x).surjective ⟨y, (Set.Finite.mem_toFinset _).mp hy⟩
    exact ⟨z.1, (Set.Finite.mem_toFinset _).mpr z.2, congrArg Subtype.val hz⟩
  · intro y hy
    rfl

/-! ### The norm identity at a point -/

/-- The norm-form identity at a paper-interface point without any infinitude
hypothesis. The generic producer compares the actual determinant polynomial
with its split form over an algebraic closure. -/
theorem wgaussValuation_map_normForm_of_etale [Module.Free B A] [Module.Finite B A]
    [Algebra.Etale B A] {σ : Type*} [Fintype σ] (b : σ → A) (r : σ → ℝ≥0) (x : Berk k B) :
    wgaussValuation NormedField.valuation r (map (toH x) (normForm B b)) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ fibreMult B y := by
  classical
  have hg := Berkovich.Spectrum.wgaussValuation_map_normForm_of_etale b r x.toSpectrum
  change wgaussValuation NormedField.valuation r
    (map (Berkovich.Spectrum.toH x.toSpectrum) (normForm B b)) = _
  rw [hg]
  symm
  refine Finset.prod_bij
    (fun y hy => (spectrumFibreEquiv x ⟨y, (Set.Finite.mem_toFinset _).mp hy⟩).1) ?_ ?_ ?_ ?_
  · intro y hy
    exact (Set.Finite.mem_toFinset _).mpr (spectrumFibreEquiv x ⟨y,
      (Set.Finite.mem_toFinset _).mp hy⟩).2
  · intro y₁ hy₁ y₂ hy₂ he
    exact congrArg Subtype.val ((spectrumFibreEquiv x).injective (Subtype.ext he))
  · intro y hy
    obtain ⟨z, hz⟩ := (spectrumFibreEquiv x).surjective ⟨y, (Set.Finite.mem_toFinset _).mp hy⟩
    exact ⟨z.1, (Set.Finite.mem_toFinset _).mpr z.2, congrArg Subtype.val hz⟩
  · intro y hy
    rfl

/-- The same norm-form identity on the original coefficient seminorm, without
an infinitude hypothesis on the trivially valued field or H(x). -/
theorem wgaussValuation_normForm_of_etale [Module.Free B A] [Module.Finite B A]
    [Algebra.Etale B A] {σ : Type*} [Fintype σ] (b : σ → A) (r : σ → ℝ≥0) (x : Berk k B) :
    wgaussValuation x.val r (normForm B b) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ fibreMult B y := by
  rw [← wgaussValuation_map x.val r (toH x) NormedField.valuation
    (fun a => nnnorm_toH x a)]
  exact wgaussValuation_map_normForm_of_etale b r x

/-- Compatibility form of the paper's norm identity at a point (FHX
`lem:finite-flat-norm`, finite free etale case). Its original infinitude
hypothesis is retained in the interface; the stronger producer
`wgaussValuation_map_normForm_of_etale` proves the formula without it. -/
theorem wgaussValuation_map_normForm [Infinite k] [Module.Free B A] [Module.Finite B A]
    [Algebra.Etale B A] {σ : Type*} [Fintype σ] (b : σ → A) (r : σ → ℝ≥0) (x : Berk k B) :
    wgaussValuation NormedField.valuation r (map (toH x) (normForm B b)) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ fibreMult B y :=
  wgaussValuation_map_normForm_of_etale b r x

end Berk

end EnvelopeProperty
