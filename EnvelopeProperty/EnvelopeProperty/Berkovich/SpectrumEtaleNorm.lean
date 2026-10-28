/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumFinite
import EnvelopeProperty.Berkovich.NormForm

/-!
# Norms of finite free etale algebras at arbitrary seminorm points

Completed tensor fibres supply actual quotient-field multiplicities. Scalar norm
identities need no infinitude of the completed field. The weighted norm-form
identity retains an explicit Infinite H(x) for its interpolation proof. Original
and coefficient rings may carry arbitrary real-valued ultrametric seminorms.
-/

open scoped NNReal ENNReal Topology TensorProduct

open MvPolynomial

noncomputable section

namespace EnvelopeProperty

namespace Berkovich.Spectrum

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

/-- Finite structural fibres as actual finite point sets. -/
theorem finite_preimage_singleton [Module.Finite B A] (x : Spectrum B) :
    (comap (algebraMap B A) ⁻¹' {x}).Finite := by
  have : Finite (Fibre (B := A) x) := finite_fibre x
  apply Set.finite_coe_iff.mp
  exact Finite.of_injective
    (fun y : comap (algebraMap B A) ⁻¹' {x} =>
      (⟨y.1, Set.mem_singleton_iff.mp y.2⟩ : Fibre (B := A) x))
    (fun _ _ h => Subtype.ext (congrArg Subtype.val h))

/-- Transport the genuine fibre equivalence to the inverse-image point subtype. -/
def pointFibreEquivMaximalSpectrum [Algebra.IsIntegral B A] (x : Spectrum B) :
    comap (algebraMap B A) ⁻¹' {x} ≃ MaximalSpectrum (H x ⊗[B] A) :=
  (Equiv.subtypeEquivRight fun _ => Set.mem_singleton_iff).trans (fibreEquivMaximalSpectrum x)

/-- A ring with a point in its analytification is nontrivial (it maps to the field `H(x)`). -/
theorem nontrivial_of_spectrum (x : Spectrum B) : Nontrivial B := (toH x).domain_nontrivial

/-! ### Fibre multiplicities -/

variable (B) in
/-- The **residue-degree multiplicity used for finite etale fibres** of a point
`y ∈ (Spec A)^an` in its fibre over
`x = π(y)`: the residue degree `[(H(x) ⊗_B A)/m_y : H(x)]`, where
`m_y = ker (H(x) ⊗_B A → H(y))` (FHX `lem:finite-flat-norm`, `rmk:finite-flat-norm-etale`). -/
def fibreMult (y : Spectrum A) : ℕ :=
  Module.finrank (H (comap (algebraMap B A) y))
    ((H (comap (algebraMap B A) y) ⊗[B] A) ⧸
      RingHom.ker (fibreHom (rfl : comap (algebraMap B A) y = _)))

/-- The multiplicity of `y` computed at any `x` with `π(y) = x`. -/
theorem fibreMult_eq {x : Spectrum B} {y : Spectrum A}
    (h : comap (algebraMap B A) y = x) :
    fibreMult B y = Module.finrank (H x) ((H x ⊗[B] A) ⧸ RingHom.ker (fibreHom h)) := by
  subst h; rfl

/-- **Multiplicities are positive** (for `A` finite over `B`): `(H(x) ⊗_B A)/m_y` is a nonzero
finite-dimensional `H(x)`-vector space. -/
theorem one_le_fibreMult [Module.Finite B A] (y : Spectrum A) : 1 ≤ fibreMult B y := by
  have := isMaximal_ker_fibreHom (rfl : comap (algebraMap B A) y = _)
  exact Module.finrank_pos

/-- The maximal ideal attached to a point `y` over `x` is `ker (H(x) ⊗_B A → H(y))`. -/
theorem pointFibreEquivMaximalSpectrum_asIdeal [Algebra.IsIntegral B A] (x : Spectrum B)
    (y : comap (algebraMap B A) ⁻¹' {x}) :
    (pointFibreEquivMaximalSpectrum x y).asIdeal = RingHom.ker (fibreHom y.2) := rfl

/-! ### The fibre algebra of a finite étale morphism -/

instance isArtinianRing_fibre [Module.Finite B A] (x : Spectrum B) :
    IsArtinianRing (H x ⊗[B] A) :=
  IsArtinianRing.of_finite (H x) _

/-- The fibre algebra of an étale morphism is reduced: it is étale over the field `H(x)`. -/
instance isReduced_fibre [Algebra.Etale B A] (x : Spectrum B) : IsReduced (H x ⊗[B] A) :=
  Algebra.FormallyUnramified.isReduced_of_field (H x) _

/-- For `A` finite étale over `B`, the fibre algebra `H(x) ⊗_B A` is the product of its residue
fields at its maximal ideals (a reduced Artinian ring, `IsArtinianRing.equivPi`). -/
def fibreEquivPi [Module.Finite B A] [Algebra.Etale B A] (x : Spectrum B) :
    (H x ⊗[B] A) ≃ₐ[H x] ∀ m : MaximalSpectrum (H x ⊗[B] A), (H x ⊗[B] A) ⧸ m.asIdeal :=
  (IsArtinianRing.equivPi (H x ⊗[B] A)).restrictScalars (H x)

theorem fibreEquivPi_apply [Module.Finite B A] [Algebra.Etale B A] (x : Spectrum B)
    (z : H x ⊗[B] A) (m : MaximalSpectrum (H x ⊗[B] A)) :
    fibreEquivPi x z m = Ideal.Quotient.mk m.asIdeal z := rfl

/-- **The multiplicities over a point add up to the degree** (FHX `lem:finite-flat-norm`, finite
free étale case): `∑_{π(y) = x} m_y(π) = [A : B]`. Indeed `[A : B] = [H(x) ⊗_B A : H(x)]`
(base change of a free module), `H(x) ⊗_B A ≃ ∏_m (H(x) ⊗_B A)/m` (`Berk.fibreEquivPi`), and the
maximal ideals correspond to the points over `x` (`Berk.pointFibreEquivMaximalSpectrum`). -/
theorem sum_fibreMult [Module.Free B A] [Module.Finite B A] [Algebra.Etale B A] (x : Spectrum B) :
    ∑ y ∈ (finite_preimage_singleton (A := A) x).toFinset, fibreMult B y =
      Module.finrank B A := by
  classical
  have := nontrivial_of_spectrum x
  have : Fintype (MaximalSpectrum (H x ⊗[B] A)) := Fintype.ofFinite _
  have h1 : Module.finrank B A = ∑ m : MaximalSpectrum (H x ⊗[B] A),
      Module.finrank (H x) ((H x ⊗[B] A) ⧸ m.asIdeal) := by
    rw [← Module.finrank_baseChange (R := H x), (fibreEquivPi x).toLinearEquiv.finrank_eq,
      Module.finrank_pi_fintype]
  rw [h1]
  refine Finset.sum_bij (fun y hy => pointFibreEquivMaximalSpectrum x
      ⟨y, (Set.Finite.mem_toFinset _).1 hy⟩) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro y₁ h₁ y₂ h₂ h
    exact congrArg Subtype.val ((pointFibreEquivMaximalSpectrum x).injective h)
  · intro m _
    obtain ⟨⟨y, hy⟩, hym⟩ := (pointFibreEquivMaximalSpectrum x).surjective m
    exact ⟨y, (Set.Finite.mem_toFinset _).2 hy, hym⟩
  · intro y hy
    have hy' : y ∈ comap (algebraMap B A) ⁻¹' {x} :=
      (Set.Finite.mem_toFinset _).1 hy
    rw [fibreMult_eq hy', pointFibreEquivMaximalSpectrum_asIdeal]

/-! ### The norm identity at a point -/

/-- **Norm identity at a point** (FHX `lem:finite-flat-norm`, finite free étale case,
`rmk:finite-flat-norm-etale`). Let `A` be finite free étale over `B`, `H(x)` infinite, `b_j ∈ A`,
`r_j ≥ 0`, and `P = ∑_α c_α X^α` the norm form of `∑_j X_j b_j` (`EnvelopeProperty.normForm`).
For every `x ∈ (Spec B)^an`,
`max_α |c_α|_x r^α = ∏_{π(y) = x} (max_j |b_j|_y r_j)^{m_y(π)}`.

Proof: the image of `P` in `H(x)[X]` evaluates to the norm form of the fibre algebra
`E = H(x) ⊗_B A` (`EnvelopeProperty.eval_map_normForm`); `E ≃ ∏_m E/m` with `E/m` finite separable
over `H(x)` (étaleness), and on `E/m_y` the absolute value `z mod m_y ↦ |z|_{H(y)}` extends the
norm of `H(x)` and takes the value `|b|_y` on `1 ⊗ b`; apply
`EnvelopeProperty.wgaussValuation_eq_prod_of_eval_eq_norm` and reindex the product by the fibre. -/
theorem wgaussValuation_map_normForm [Module.Free B A] [Module.Finite B A]
    [Algebra.Etale B A] {σ : Type*} [Fintype σ] (b : σ → A) (r : σ → ℝ≥0) (x : Spectrum B) [Infinite (H x)] :
    wgaussValuation NormedField.valuation r (map (toH x) (normForm B b)) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ fibreMult B y := by
  classical
  have : Fintype (MaximalSpectrum (H x ⊗[B] A)) := Fintype.ofFinite _
  let _ : ∀ m : MaximalSpectrum (H x ⊗[B] A), Field ((H x ⊗[B] A) ⧸ m.asIdeal) :=
    fun m => Ideal.Quotient.field m.asIdeal
  have : ∀ m : MaximalSpectrum (H x ⊗[B] A),
      Algebra.IsSeparable (H x) ((H x ⊗[B] A) ⧸ m.asIdeal) :=
    fun m => Algebra.FormallyUnramified.isSeparable _ _
  -- the point over `x` attached to a maximal ideal `m`, and the absolute value on `E/m`
  let yOf : MaximalSpectrum (H x ⊗[B] A) → Spectrum A :=
    fun m => ((pointFibreEquivMaximalSpectrum x).symm m : Spectrum A)
  have hyOf : ∀ m, comap (algebraMap B A) (yOf m) = x :=
    fun m => ((pointFibreEquivMaximalSpectrum x).symm m).2
  have hker : ∀ m, RingHom.ker (fibreHom (hyOf m)) = m.asIdeal := fun m => by
    rw [← pointFibreEquivMaximalSpectrum_asIdeal, Equiv.apply_symm_apply]
  let g : ∀ m : MaximalSpectrum (H x ⊗[B] A), ((H x ⊗[B] A) ⧸ m.asIdeal) →+* H (yOf m) :=
    fun m => Ideal.Quotient.lift m.asIdeal (fibreHom (hyOf m))
      (fun a ha => by rwa [← hker m, RingHom.mem_ker] at ha)
  let w : ∀ m : MaximalSpectrum (H x ⊗[B] A), Valuation ((H x ⊗[B] A) ⧸ m.asIdeal) ℝ≥0 :=
    fun m => (NormedField.valuation (K := H (yOf m))).comap (g m)
  have hw : ∀ m (c : H x), w m (algebraMap (H x) _ c) = ‖c‖₊ := by
    intro m c
    simp only [w, g]
    rw [Valuation.comap_apply, NormedField.valuation_apply, ← Ideal.Quotient.mk_algebraMap,
      Ideal.Quotient.lift_mk, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, fibreHom_tmul_one]
    exact NNReal.eq (H.norm_map _ (hyOf m) c)
  have hwb : ∀ m (a : A), w m (Ideal.Quotient.mk _ ((1 : H x) ⊗ₜ a)) = (yOf m).val a := by
    intro m a
    simp only [w, g]
    rw [Valuation.comap_apply, NormedField.valuation_apply, Ideal.Quotient.lift_mk,
      fibreHom_one_tmul, nnnorm_toH]
  rw [← algebraMap_H, wgaussValuation_eq_prod_of_eval_eq_norm (fibreEquivPi x) w hw
    (fun j => (1 : H x) ⊗ₜ[B] b j) r (eval_map_normForm b)]
  symm
  refine Finset.prod_bij (fun y hy => pointFibreEquivMaximalSpectrum x
      ⟨y, (Set.Finite.mem_toFinset _).1 hy⟩) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro y₁ h₁ y₂ h₂ h
    exact congrArg Subtype.val ((pointFibreEquivMaximalSpectrum x).injective h)
  · intro m _
    obtain ⟨⟨y, hy⟩, hym⟩ := (pointFibreEquivMaximalSpectrum x).surjective m
    exact ⟨y, (Set.Finite.mem_toFinset _).2 hy, hym⟩
  · intro y hy
    have hy' : y ∈ comap (algebraMap B A) ⁻¹' {x} :=
      (Set.Finite.mem_toFinset _).1 hy
    have hyy : yOf (pointFibreEquivMaximalSpectrum x ⟨y, hy'⟩) = y := by simp [yOf]
    rw [fibreMult_eq hy', ← pointFibreEquivMaximalSpectrum_asIdeal x ⟨y, hy'⟩]
    congr 1
    refine Finset.sup_congr rfl fun j _ => ?_
    rw [fibreEquivPi_apply, hwb, hyy]


/-- The scalar norm is the product of the actual fibre values with residue-degree
multiplicities. Unlike polynomial interpolation, this needs no Infinite H(x). -/
theorem val_algebraNorm [Module.Free B A] [Module.Finite B A] [Algebra.Etale B A]
    (b : A) (x : Spectrum B) :
    x.val (Algebra.norm B b) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset, y.val b ^ fibreMult B y := by
  classical
  have : Fintype (MaximalSpectrum (H x ⊗[B] A)) := Fintype.ofFinite _
  let _ : ∀ m : MaximalSpectrum (H x ⊗[B] A), Field ((H x ⊗[B] A) ⧸ m.asIdeal) :=
    fun m => Ideal.Quotient.field m.asIdeal
  have : ∀ m : MaximalSpectrum (H x ⊗[B] A),
      Algebra.IsSeparable (H x) ((H x ⊗[B] A) ⧸ m.asIdeal) :=
    fun m => Algebra.FormallyUnramified.isSeparable _ _
  -- the point over `x` attached to a maximal ideal `m`, and the absolute value on `E/m`
  let yOf : MaximalSpectrum (H x ⊗[B] A) → Spectrum A :=
    fun m => ((pointFibreEquivMaximalSpectrum x).symm m : Spectrum A)
  have hyOf : ∀ m, comap (algebraMap B A) (yOf m) = x :=
    fun m => ((pointFibreEquivMaximalSpectrum x).symm m).2
  have hker : ∀ m, RingHom.ker (fibreHom (hyOf m)) = m.asIdeal := fun m => by
    rw [← pointFibreEquivMaximalSpectrum_asIdeal, Equiv.apply_symm_apply]
  let g : ∀ m : MaximalSpectrum (H x ⊗[B] A), ((H x ⊗[B] A) ⧸ m.asIdeal) →+* H (yOf m) :=
    fun m => Ideal.Quotient.lift m.asIdeal (fibreHom (hyOf m))
      (fun a ha => by rwa [← hker m, RingHom.mem_ker] at ha)
  let w : ∀ m : MaximalSpectrum (H x ⊗[B] A), Valuation ((H x ⊗[B] A) ⧸ m.asIdeal) ℝ≥0 :=
    fun m => (NormedField.valuation (K := H (yOf m))).comap (g m)
  have hw : ∀ m (c : H x), w m (algebraMap (H x) _ c) = ‖c‖₊ := by
    intro m c
    simp only [w, g]
    rw [Valuation.comap_apply, NormedField.valuation_apply, ← Ideal.Quotient.mk_algebraMap,
      Ideal.Quotient.lift_mk, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, fibreHom_tmul_one]
    exact NNReal.eq (H.norm_map _ (hyOf m) c)
  have hwb : ∀ m (a : A), w m (Ideal.Quotient.mk _ ((1 : H x) ⊗ₜ a)) = (yOf m).val a := by
    intro m a
    simp only [w, g]
    rw [Valuation.comap_apply, NormedField.valuation_apply, Ideal.Quotient.lift_mk,
      fibreHom_one_tmul, nnnorm_toH]
  have hbase : x.val (Algebra.norm B b) =
      (NormedField.valuation (K := H x)) (Algebra.norm (H x) ((1 : H x) ⊗ₜ[B] b)) := by
    rw [← algebraNorm_baseChange_tmul (K := H x) b, algebraMap_H,
      NormedField.valuation_apply, nnnorm_toH]
  rw [hbase, valuation_algebraNorm_eq_prod_of_algEquiv (fibreEquivPi x) w hw]
  symm
  refine Finset.prod_bij (fun y hy => pointFibreEquivMaximalSpectrum x
      ⟨y, (Set.Finite.mem_toFinset _).1 hy⟩) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro y₁ h₁ y₂ h₂ h
    exact congrArg Subtype.val ((pointFibreEquivMaximalSpectrum x).injective h)
  · intro m _
    obtain ⟨⟨y, hy⟩, hym⟩ := (pointFibreEquivMaximalSpectrum x).surjective m
    exact ⟨y, (Set.Finite.mem_toFinset _).2 hy, hym⟩
  · intro y hy
    have hy' : y ∈ comap (algebraMap B A) ⁻¹' {x} :=
      (Set.Finite.mem_toFinset _).1 hy
    have hyy : yOf (pointFibreEquivMaximalSpectrum x ⟨y, hy'⟩) = y := by simp [yOf]
    rw [fibreMult_eq hy', ← pointFibreEquivMaximalSpectrum_asIdeal x ⟨y, hy'⟩]
    congr 1
    rw [fibreEquivPi_apply, hwb, hyy]

/-- The weighted norm-form identity holds directly for every original coefficient
seminorm value, with explicit infinitude only for the interpolation argument. -/
theorem wgaussValuation_normForm [Module.Free B A] [Module.Finite B A] [Algebra.Etale B A]
    {σ : Type*} [Fintype σ] (b : σ → A) (r : σ → ℝ≥0) (x : Spectrum B) [Infinite (H x)] :
    wgaussValuation x.val r (normForm B b) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ fibreMult B y := by
  rw [← wgaussValuation_map x.val r (toH x) NormedField.valuation
    (fun a => nnnorm_toH x a)]
  exact wgaussValuation_map_normForm b r x

end Berkovich.Spectrum

end EnvelopeProperty
