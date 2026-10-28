/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.EtaleFibre
import EnvelopeProperty.Berkovich.Localization
import EnvelopeProperty.Berkovich.NormIdentityGeneral

/-!
# Fibres of finite morphisms: multiplicities and the norm identity at a point

Let `k` be a field with the trivial absolute value, `B → A` a homomorphism of `k`-algebras making
`A` a finite `B`-module, and `π = π^an : (Spec A)^an → (Spec B)^an`. This file proves the
pointwise part of Fang–Han–Xia, *The envelope property for unibranch projective varieties*,
Lemma 5.13 (`lem:finite-flat-norm`) in the generality of the source (no étaleness).

For `x ∈ (Spec B)^an` the fibre algebra `E = H(x) ⊗_B A` is a finite algebra over the complete
field `H(x)`, hence Artinian: `E ≃ ∏_m E_m` is the product of its localizations at its maximal
ideals, which correspond to the points `y` over `x` (`Berk.fibreEquivMaximalSpectrum`). The
**multiplicity** of `y` is `m_y(π) = dim_{H(x)} E_{m_y}`, the dimension of the local Artinian
factor at `y` (`Berk.flatFibreMult`); it is positive, the multiplicities over `x` add up to
`dim_{H(x)} E` (`Berk.sum_flatFibreMult`), which is `[A : B]` for `A` free
(`Berk.sum_flatFibreMult_of_free`), and in the finite free étale case `m_y(π)` is the residue
degree `Berk.fibreMult` of `EnvelopeProperty.Berkovich.EtaleFibre`
(`Berk.flatFibreMult_eq_fibreMult`).

**Norm identity at a point** (`Berk.wgaussValuation_eq_prod_flatFibreMult`). For `b_j ∈ A` and a
polynomial `P = ∑_α c_α X^α ∈ H(x)[X_j]` with `P(t) = N_{E/H(x)}(∑_j t_j (1 ⊗ b_j))` for all
`t ∈ H(x)^σ`, and radii `r_j ≥ 0`,
`max_α |c_α| r^α = ∏_{π(y) = x} (max_j |b_j|_y r_j)^{m_y(π)}`.
This is `EnvelopeProperty.wgaussValuation_eq_prod_of_eval_eq_norm_finite` for the fibre algebra,
with the absolute values `|·|_y` on `E` (through `E → H(y)`). It applies to:

* the norm form `N(∑_j X_j b_j) ∈ B[X]` when `A` is free over `B`
  (`Berk.wgaussValuation_normForm_flat`);
* the norm form over a `B`-algebra `B'` over which `B' ⊗_B A` is free, at points `x'` of
  `(Spec B')^an` such that `B' → H(π'(x'))` exists isometrically
  (`Berk.wgaussValuation_normForm_baseChange`), in particular for a localization `B' = B_h`
  (`Berk.wgaussValuation_normForm_away`). For `A` finite flat over a noetherian `B`, every prime
  of `B` has such a principal neighbourhood (`EnvelopeProperty.exists_free_localizationAway`).

## Main definitions

* `Berk.flatFibreMult B y`: the multiplicity `m_y(π) = dim_{H(x)} (H(x) ⊗_B A)_{m_y}`.

## Main results

* `Berk.one_le_flatFibreMult`, `Berk.sum_flatFibreMult`, `Berk.sum_flatFibreMult_of_free`,
  `Berk.exists_sum_flatFibreMult_le`, `Berk.flatFibreMult_eq_fibreMult`.
* `Berk.wgaussValuation_eq_prod_flatFibreMult`: the norm identity at a point.
* `Berk.wgaussValuation_normForm_flat`, `Berk.wgaussValuation_normForm_baseChange`,
  `Berk.wgaussValuation_normForm_away`: its instances for norm forms.
* `EnvelopeProperty.exists_free_localizationAway`: local freeness of finite flat modules.
-/

open scoped NNReal ENNReal Topology TensorProduct

open MvPolynomial

noncomputable section

namespace EnvelopeProperty

/-- **Finite flat modules are locally free** (on principal opens). If `A` is a finite flat
module over a noetherian ring `B` and `p` is a prime of `B`, there is `h ∉ p` such that
`B_h ⊗_B A` is free over `B_h`: `A_p` is finite flat over the local ring `B_p`, hence free, and a
basis spreads out to a principal neighbourhood (`A` is finitely presented). -/
theorem exists_free_localizationAway {B A : Type*} [CommRing B] [IsNoetherianRing B]
    [AddCommGroup A] [Module B A] [Module.Finite B A] [Module.Flat B A] (p : Ideal B)
    [p.IsPrime] : ∃ h ∉ p, Module.Free (Localization.Away h) (Localization.Away h ⊗[B] A) := by
  have : Module.FinitePresentation B A := Module.finitePresentation_of_finite B A
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl A) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl A) (Localization.AtPrime p)
  refine ⟨r, hr, ?_⟩
  exact Module.Free.of_equiv (IsLocalizedModule.isBaseChange (Submonoid.powers r)
    (Localization.Away r) (LocalizedModule.mkLinearMap (Submonoid.powers r) A)).equiv.symm

namespace Berk

variable {k : Type*} [Field k] {B A : Type*} [CommRing B] [CommRing A] [Algebra k B]
  [Algebra k A] [Algebra B A] [IsScalarTower k B A]

/-! ### Length multiplicities -/

/-- The kernel of `H(x) ⊗_B A → H(y)` is a prime ideal (`H(y)` is a field). -/
instance isPrime_ker_fibreHom {x : Berk k B} {y : Berk k A}
    (h : comap (IsScalarTower.toAlgHom k B A) y = x) : (RingHom.ker (fibreHom h)).IsPrime :=
  RingHom.ker_isPrime _

variable (B) in
/-- The **multiplicity** `m_y(π)` of a point `y ∈ (Spec A)^an` in its fibre over `x = π(y)`
(FHX `lem:finite-flat-norm`): the dimension over `H(x)` of the local Artinian factor
`(H(x) ⊗_B A)_{m_y}` of the fibre algebra at `m_y = ker (H(x) ⊗_B A → H(y))`. -/
def flatFibreMult (y : Berk k A) : ℕ :=
  Module.finrank (H (comap (IsScalarTower.toAlgHom k B A) y))
    (Localization.AtPrime
      (RingHom.ker (fibreHom (rfl : comap (IsScalarTower.toAlgHom k B A) y = _))))

/-- The multiplicity of `y` computed at any `x` with `π(y) = x`. -/
theorem flatFibreMult_eq {x : Berk k B} {y : Berk k A}
    (h : comap (IsScalarTower.toAlgHom k B A) y = x) :
    flatFibreMult B y =
      Module.finrank (H x) (Localization.AtPrime (RingHom.ker (fibreHom h))) := by
  subst h; rfl

omit [Algebra k A] [IsScalarTower k B A] in
/-- Transport of `dim_{H(x)} E_p` along an equality of prime ideals. -/
theorem finrank_localization_congr (x : Berk k B) {p q : Ideal (H x ⊗[B] A)} [p.IsPrime]
    [q.IsPrime] (h : p = q) :
    Module.finrank (H x) (Localization.AtPrime p) =
      Module.finrank (H x) (Localization.AtPrime q) := by
  subst h; rfl

omit [Algebra k A] [IsScalarTower k B A] in
/-- The local factors of the fibre algebra of a finite morphism are finite over `H(x)`. -/
theorem finite_localization_fibre [Module.Finite B A] (x : Berk k B) (p : Ideal (H x ⊗[B] A))
    [p.IsPrime] : Module.Finite (H x) (Localization.AtPrime p) :=
  Module.Finite.of_surjective (IsScalarTower.toAlgHom (H x) (H x ⊗[B] A)
    (Localization.AtPrime p)).toLinearMap
    (IsArtinianRing.localization_surjective p.primeCompl _)

/-- **Multiplicities are positive** (for `A` finite over `B`). -/
theorem one_le_flatFibreMult [Module.Finite B A] (y : Berk k A) : 1 ≤ flatFibreMult B y := by
  have := finite_localization_fibre (A := A) (comap (IsScalarTower.toAlgHom k B A) y)
    (RingHom.ker (fibreHom (rfl : comap (IsScalarTower.toAlgHom k B A) y = _)))
  exact Module.finrank_pos

/-- **The multiplicities over a point add up to the dimension of the fibre algebra**:
`∑_{π(y) = x} m_y(π) = dim_{H(x)} (H(x) ⊗_B A)`, as `H(x) ⊗_B A ≃ ∏_m (H(x) ⊗_B A)_m`
(`MaximalSpectrum.toPiLocalizationEquiv`, an Artinian ring) and the maximal ideals correspond
to the points over `x` (`Berk.fibreEquivMaximalSpectrum`). -/
theorem sum_flatFibreMult [Module.Finite B A] (x : Berk k B) :
    ∑ y ∈ (finite_preimage_singleton (A := A) x).toFinset, flatFibreMult B y =
      Module.finrank (H x) (H x ⊗[B] A) := by
  classical
  have : Fintype (MaximalSpectrum (H x ⊗[B] A)) := Fintype.ofFinite _
  have := fun m : MaximalSpectrum (H x ⊗[B] A) => finite_localization_fibre (A := A) x m.asIdeal
  have h1 : Module.finrank (H x) (H x ⊗[B] A) = ∑ m : MaximalSpectrum (H x ⊗[B] A),
      Module.finrank (H x) (Localization.AtPrime m.asIdeal) := by
    rw [((MaximalSpectrum.toPiLocalizationEquiv (H x ⊗[B] A)).restrictScalars
      (H x)).toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  rw [h1]
  refine Finset.sum_bij (fun y hy => fibreEquivMaximalSpectrum x
      ⟨y, (Set.Finite.mem_toFinset _).1 hy⟩) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro y₁ h₁ y₂ h₂ h
    exact congrArg Subtype.val ((fibreEquivMaximalSpectrum x).injective h)
  · intro m _
    obtain ⟨⟨y, hy⟩, hym⟩ := (fibreEquivMaximalSpectrum x).surjective m
    exact ⟨y, (Set.Finite.mem_toFinset _).2 hy, hym⟩
  · intro y hy
    have hy0 : y ∈ comap (IsScalarTower.toAlgHom k B A) ⁻¹' {x} :=
      (Set.Finite.mem_toFinset _).1 hy
    have hy' : comap (IsScalarTower.toAlgHom k B A) y = x := hy0
    rw [flatFibreMult_eq hy']
    exact finrank_localization_congr x (p := RingHom.ker (fibreHom hy'))
      (fibreEquivMaximalSpectrum_asIdeal x ⟨y, hy'⟩).symm

/-- **The multiplicities over a point add up to the degree** for `A` finite free over `B`:
`∑_{π(y) = x} m_y(π) = [A : B]` (FHX `lem:finite-flat-norm`). -/
theorem sum_flatFibreMult_of_free [Module.Free B A] [Module.Finite B A] (x : Berk k B) :
    ∑ y ∈ (finite_preimage_singleton (A := A) x).toFinset, flatFibreMult B y =
      Module.finrank B A := by
  have := nontrivial_of_berk x
  rw [sum_flatFibreMult, Module.finrank_baseChange]

/-- The sums of the multiplicities over the points of `(Spec B)^an` are bounded: by the number of
generators of the `B`-module `A`. -/
theorem exists_sum_flatFibreMult_le [Module.Finite B A] :
    ∃ n : ℕ, ∀ x : Berk k B,
      ∑ y ∈ (finite_preimage_singleton (A := A) x).toFinset, flatFibreMult B y ≤ n := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := B) (M := A)
  refine ⟨S.card, fun x => ?_⟩
  rw [sum_flatFibreMult]
  have hspan : Submodule.span (H x) ((S.image (TensorProduct.mk B (H x) A 1) : Finset _) :
      Set (H x ⊗[B] A)) = ⊤ := by
    rw [Finset.coe_image, ← Submodule.baseChange_span, hS, Submodule.baseChange_top]
  calc Module.finrank (H x) (H x ⊗[B] A)
      = Module.finrank (H x) (⊤ : Submodule (H x) (H x ⊗[B] A)) := (finrank_top _ _).symm
    _ = Module.finrank (H x) (Submodule.span (H x) ((S.image (TensorProduct.mk B (H x) A 1) :
          Finset _) : Set (H x ⊗[B] A))) := by rw [hspan]
    _ ≤ (S.image (TensorProduct.mk B (H x) A 1)).card := finrank_span_finset_le_card _
    _ ≤ S.card := Finset.card_image_le

/-- The residue degree is at most the multiplicity `m_y(π)`: `(H(x) ⊗_B A)/m_y` is a quotient of
the local factor `(H(x) ⊗_B A)_{m_y}`. -/
theorem fibreMult_le_flatFibreMult [Module.Finite B A] (y : Berk k A) :
    fibreMult B y ≤ flatFibreMult B y := by
  set x := comap (IsScalarTower.toAlgHom k B A) y
  set p := RingHom.ker (fibreHom (rfl : comap (IsScalarTower.toAlgHom k B A) y = x))
  have hp : p.IsMaximal := isMaximal_ker_fibreHom _
  have := finite_localization_fibre (A := A) x p
  rw [fibreMult_eq (rfl : comap (IsScalarTower.toAlgHom k B A) y = x),
    flatFibreMult_eq (rfl : comap (IsScalarTower.toAlgHom k B A) y = x)]
  let : Field ((H x ⊗[B] A) ⧸ p) := Ideal.Quotient.field p
  let f : Localization.AtPrime p →ₐ[H x] (H x ⊗[B] A) ⧸ p :=
    IsLocalization.liftAlgHom (M := p.primeCompl) (f := Ideal.Quotient.mkₐ (H x) p)
      fun z => isUnit_iff_ne_zero.2 fun h0 =>
        z.2 ((Ideal.Quotient.eq_zero_iff_mem).1 h0)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨algebraMap _ (Localization.AtPrime p) z, ?_⟩
    change IsLocalization.lift _ (algebraMap _ _ z) = _
    rw [IsLocalization.lift_eq]
    rfl
  exact f.toLinearMap.finrank_le_finrank_of_surjective hf

/-- In the finite free étale case the multiplicity `m_y(π)` is the residue degree
(`Berk.fibreMult`): both add up to `[A : B]` over every point and `fibreMult ≤ flatFibreMult`. -/
theorem flatFibreMult_eq_fibreMult [Module.Free B A] [Module.Finite B A] [Algebra.Etale B A]
    (y : Berk k A) : flatFibreMult B y = fibreMult B y := by
  set x := comap (IsScalarTower.toAlgHom k B A) y
  have hy : y ∈ (finite_preimage_singleton (A := A) x).toFinset :=
    (Set.Finite.mem_toFinset _).2 rfl
  have h := (Finset.sum_eq_sum_iff_of_le fun y _ => fibreMult_le_flatFibreMult (B := B) y).1
    ((sum_fibreMult (A := A) x).trans (sum_flatFibreMult_of_free x).symm) y hy
  exact h.symm

/-! ### The norm identity at a point -/

/-- **Norm identity at a point** (FHX `lem:finite-flat-norm`, proof). Let `A` be finite over
`B`, `k` infinite, `b_j ∈ A`, `r_j ≥ 0`, `x ∈ (Spec B)^an`, and `P = ∑_α c_α X^α ∈ H(x)[X]` with
`P(t) = N_{H(x) ⊗_B A/H(x)}(∑_j t_j (1 ⊗ b_j))` for all `t ∈ H(x)^σ`. Then
`max_α |c_α| r^α = ∏_{π(y) = x} (max_j |b_j|_y r_j)^{m_y(π)}`.

Proof: `EnvelopeProperty.wgaussValuation_eq_prod_of_eval_eq_norm_finite` for the fibre algebra
`E = H(x) ⊗_B A`, with the absolute value `z ↦ |z|_{H(y)}` (through `E → H(y)`) attached to the
maximal ideal `m_y`; reindex the product by the fibre. -/
theorem wgaussValuation_eq_prod_flatFibreMult [Infinite k] [Module.Finite B A] {σ : Type*}
    [Fintype σ] (b : σ → A) (r : σ → ℝ≥0) (x : Berk k B) {P : MvPolynomial σ (H x)}
    (hP : ∀ t : σ → H x, eval t P = Algebra.norm (H x) (∑ j, t j • ((1 : H x) ⊗ₜ[B] b j))) :
    wgaussValuation NormedField.valuation r P =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ flatFibreMult B y := by
  classical
  have : Fintype (MaximalSpectrum (H x ⊗[B] A)) := Fintype.ofFinite _
  have : Infinite (H x) := Infinite.of_injective _ (algebraMap k (H x)).injective
  let yOf : MaximalSpectrum (H x ⊗[B] A) → Berk k A :=
    fun m => ((fibreEquivMaximalSpectrum x).symm m : Berk k A)
  have hyOf : ∀ m, comap (IsScalarTower.toAlgHom k B A) (yOf m) = x :=
    fun m => ((fibreEquivMaximalSpectrum x).symm m).2
  have hker : ∀ m, RingHom.ker (fibreHom (hyOf m)) = m.asIdeal := fun m => by
    rw [← fibreEquivMaximalSpectrum_asIdeal, Equiv.apply_symm_apply]
  let w : MaximalSpectrum (H x ⊗[B] A) → Valuation (H x ⊗[B] A) ℝ≥0 :=
    fun m => (NormedField.valuation (K := H (yOf m))).comap (fibreHom (hyOf m))
  have hw : ∀ m (c : H x), w m (algebraMap (H x) _ c) = ‖c‖₊ := by
    intro m c
    simp only [w]
    rw [Valuation.comap_apply, NormedField.valuation_apply,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      fibreHom_tmul_one]
    exact NNReal.eq (H.norm_map _ (hyOf m) c)
  have hsupp : ∀ m, m.asIdeal ≤ (w m).supp := fun m z hz => by
    rw [← hker m, RingHom.mem_ker] at hz
    rw [Valuation.mem_supp_iff, Valuation.comap_apply, hz, map_zero]
  have hwb : ∀ m (a : A), w m ((1 : H x) ⊗ₜ a) = (yOf m).val a := by
    intro m a
    simp only [w]
    rw [Valuation.comap_apply, NormedField.valuation_apply, fibreHom_one_tmul, nnnorm_toH]
  rw [wgaussValuation_eq_prod_of_eval_eq_norm_finite w hw hsupp
    (fun j => (1 : H x) ⊗ₜ[B] b j) r hP]
  symm
  refine Finset.prod_bij (fun y hy => fibreEquivMaximalSpectrum x
      ⟨y, (Set.Finite.mem_toFinset _).1 hy⟩) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro y₁ h₁ y₂ h₂ h
    exact congrArg Subtype.val ((fibreEquivMaximalSpectrum x).injective h)
  · intro m _
    obtain ⟨⟨y, hy⟩, hym⟩ := (fibreEquivMaximalSpectrum x).surjective m
    exact ⟨y, (Set.Finite.mem_toFinset _).2 hy, hym⟩
  · intro y hy
    have hy0 : y ∈ comap (IsScalarTower.toAlgHom k B A) ⁻¹' {x} :=
      (Set.Finite.mem_toFinset _).1 hy
    have hy' : comap (IsScalarTower.toAlgHom k B A) y = x := hy0
    have hyy : yOf (fibreEquivMaximalSpectrum x ⟨y, hy'⟩) = y := by simp [yOf]
    have hexp : flatFibreMult B y = Module.finrank (H x)
        (Localization.AtPrime (fibreEquivMaximalSpectrum x ⟨y, hy'⟩).asIdeal) := by
      rw [flatFibreMult_eq hy']
      exact finrank_localization_congr x (p := RingHom.ker (fibreHom hy'))
        (fibreEquivMaximalSpectrum_asIdeal x ⟨y, hy'⟩).symm
    rw [hexp]
    congr 1
    refine Finset.sup_congr rfl fun j _ => ?_
    rw [hwb, hyy]

/-- **Norm identity at a point for a finite free morphism** (FHX `lem:finite-flat-norm`): for
`A` finite free over `B`, `k` infinite, the norm form `P = N(∑_j X_j b_j) = ∑_α c_α X^α ∈ B[X]`
(`EnvelopeProperty.normForm`) satisfies, at every `x ∈ (Spec B)^an`,
`max_α |c_α|_x r^α = ∏_{π(y) = x} (max_j |b_j|_y r_j)^{m_y(π)}`. -/
theorem wgaussValuation_normForm_flat [Infinite k] [Module.Free B A] [Module.Finite B A]
    {σ : Type*} [Fintype σ] (b : σ → A) (r : σ → ℝ≥0) (x : Berk k B) :
    wgaussValuation x.val r (normForm B b) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ flatFibreMult B y := by
  rw [← wgaussValuation_map x.val r (toH x) NormedField.valuation
    (fun c => by rw [NormedField.valuation_apply, nnnorm_toH])]
  exact wgaussValuation_eq_prod_flatFibreMult b r x (by
    rw [← algebraMap_H]
    exact eval_map_normForm b)

/-- **Norm identity at a point after base change** (FHX `lem:finite-flat-norm`, used for the
reduction of the finite flat case to the free case). Let `B'` be a `B`-algebra such that
`B' ⊗_B A` is finite free over `B'`, `x' ∈ (Spec B')^an` with image `x ∈ (Spec B)^an`, and
`ψ : B' → H(x)` a ring map extending `B → H(x)` with `|ψ(c)| = |c|_{x'}`. Then the norm form
`P = ∑_α c_α X^α ∈ B'[X]` of `∑_j X_j (1 ⊗ b_j)` over `B'` satisfies
`max_α |c_α|_{x'} r^α = ∏_{π(y) = x} (max_j |b_j|_y r_j)^{m_y(π)}`: indeed
`H(x) ⊗_{B'} (B' ⊗_B A) ≃ H(x) ⊗_B A`. -/
theorem wgaussValuation_normForm_baseChange [Infinite k] [Module.Finite B A] {B' : Type*}
    [CommRing B'] [Algebra k B'] [Algebra B B'] [IsScalarTower k B B']
    [Module.Free B' (B' ⊗[B] A)] [Module.Finite B' (B' ⊗[B] A)] {σ : Type*} [Fintype σ]
    (b : σ → A) (r : σ → ℝ≥0) (x' : Berk k B')
    (ψ : B' →+* H (comap (IsScalarTower.toAlgHom k B B') x'))
    (hψ : ∀ c : B, ψ (algebraMap B B' c) = toH _ c) (hψv : ∀ c, ‖ψ c‖₊ = x'.val c) :
    wgaussValuation x'.val r (normForm B' fun j => (1 : B') ⊗ₜ[B] b j) =
      ∏ y ∈ (finite_preimage_singleton (A := A)
          (comap (IsScalarTower.toAlgHom k B B') x')).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ flatFibreMult B y := by
  rw [← wgaussValuation_map x'.val r ψ NormedField.valuation
    (fun c => by rw [NormedField.valuation_apply, hψv])]
  let : Algebra B' (H (comap (IsScalarTower.toAlgHom k B B') x')) := ψ.toAlgebra
  have : IsScalarTower B B' (H (comap (IsScalarTower.toAlgHom k B B') x')) :=
    IsScalarTower.of_algebraMap_eq fun c => (hψ c).symm
  refine wgaussValuation_eq_prod_flatFibreMult b r _ fun t => ?_
  have h := eval_map_normForm (K := H (comap (IsScalarTower.toAlgHom k B B') x')) (B := B')
    (fun j => (1 : B') ⊗ₜ[B] b j) t
  refine h.trans ?_
  rw [← Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.cancelBaseChange B B'
    (H (comap (IsScalarTower.toAlgHom k B B') x')) (H (comap (IsScalarTower.toAlgHom k B B') x'))
    A)]
  congr 1
  simp [map_sum, Algebra.TensorProduct.cancelBaseChange_tmul]

/-- For `x'` a point of the principal open `(Spec B_h)^an`, the map `B → H(x)`, `x` the image of
`x'`, extends to `ψ : B_h → H(x)` with `|ψ(c)| = |c|_{x'}`. -/
theorem exists_lift_toH_away (h : B) (x' : Berk k (Localization.Away h)) :
    ∃ ψ : Localization.Away h →+* H (awayComap h x'),
      (∀ c : B, ψ (algebraMap B _ c) = toH _ c) ∧ ∀ c, ‖ψ c‖₊ = x'.val c := by
  set x := awayComap h x'
  have hu : IsUnit (toH x h) := isUnit_iff_ne_zero.2 (by
    rw [Ne, toH_eq_zero_iff]
    exact awayComap_val_ne_zero h x')
  let ψ : Localization.Away h →+* H x := IsLocalization.Away.lift h hu
  have hψ : ∀ c : B, ψ (algebraMap B _ c) = toH x c := IsLocalization.Away.lift_eq h hu
  let z : Berk k (Localization.Away h) := ⟨NormedField.valuation.comap ψ, fun c hc => by
    rw [Valuation.comap_apply, NormedField.valuation_apply,
      IsScalarTower.algebraMap_apply k B (Localization.Away h), hψ, nnnorm_toH,
      x.val_algebraMap c hc]⟩
  have hz : awayComap h z = awayComap h x' := ext_val fun a => by
    rw [awayComap_val_apply]
    change ‖ψ (algebraMap B _ a)‖₊ = _
    rw [hψ, nnnorm_toH]
  have hzx := awayComap_injective h hz
  refine ⟨ψ, hψ, fun c => ?_⟩
  change z.val c = x'.val c
  rw [hzx]

/-- **Norm identity at a point of a principal open where `A` is free.** If `B_h ⊗_B A` is free
over `B_h`, the norm form `P = ∑_α c_α X^α ∈ B_h[X]` of `∑_j X_j (1 ⊗ b_j)` satisfies, at every
`x' ∈ (Spec B_h)^an`,
`max_α |c_α|_{x'} r^α = ∏_{π(y) = x} (max_j |b_j|_y r_j)^{m_y(π)}`, `x` the image of `x'`. -/
theorem wgaussValuation_normForm_away [Infinite k] [Module.Finite B A] (h : B)
    [Module.Free (Localization.Away h) (Localization.Away h ⊗[B] A)] {σ : Type*} [Fintype σ]
    (b : σ → A) (r : σ → ℝ≥0) (x' : Berk k (Localization.Away h)) :
    wgaussValuation x'.val r
        (normForm (Localization.Away h) fun j => (1 : Localization.Away h) ⊗ₜ[B] b j) =
      ∏ y ∈ (finite_preimage_singleton (A := A) (awayComap h x')).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ flatFibreMult B y := by
  obtain ⟨ψ, hψ, hψv⟩ := exists_lift_toH_away h x'
  exact wgaussValuation_normForm_baseChange b r x' ψ hψ hψv

end Berk

end EnvelopeProperty
