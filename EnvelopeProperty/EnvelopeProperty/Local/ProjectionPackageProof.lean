/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.ProjectionExistence
import EnvelopeProperty.Local.ProjectionPackage
import EnvelopeProperty.AlgGeom.FiniteSeparation
import EnvelopeProperty.AlgGeom.GenericSmoothness
import EnvelopeProperty.AlgGeom.KrullDim
import EnvelopeProperty.AlgGeom.EtaleLocalization

/-!
# FHX Lemma 5.23 implies the algebraic-geometry package of Theorem 5.25

The proof of Fang–Han–Xia, *The envelope property for unibranch projective varieties*,
Theorem 5.25 (`thm:normal-local-regularization`) is formalized in
`EnvelopeProperty.Local.LocalRegularization` under the temporary hypothesis class
`ProjectionPackage k`, which bundles Lemma 5.23 (`lem:projection-existence`) with generic
smoothness, the choice of `g` and a partition of unity. This file proves

* `ProjectionExistence.toProjectionPackage`: `ProjectionExistence k → ProjectionPackage k`,

so that Theorem 5.25 depends on algebraic geometry only through Lemma 5.23 itself
(`ProjectionExistence k`).

## The argument (FHX, proof of Theorem 5.25)

Let `Y = Spec A` (`A` a finitely generated `k`-domain) and `W = V(I)` with `I` radical,
`I ≠ ⊥`, `I ≠ ⊤`.

1. *Generic smoothness* (`exists_isMaximal_isSmoothAt`): the reduced `W` has a closed point `z` at
   which it is smooth. The dimension `n = dim Y` is a natural number
   (`exists_ringKrullDim_eq_natCast`) and `n ≥ 1` (`⊥ ⊊ z` in the domain `A`).
2. *Lemma 5.23* (`ProjectionExistence`) gives an affine open `U ∋ z`, a principal open
   `S = D(h₀) ⊆ 𝔸ⁿ` and `π = Spec φ : U → S` finite, injective on rings, generically étale and
   restricting to a closed immersion on `W_U = W ∩ U`.
3. *`U` principal* (`ProjectionExistence.exists_principal`): by prime avoidance on the finite fibre
   over `π(z)` and lying over, some `S_b ∋ π(z)` has `π⁻¹(S_b)` inside a principal open `D(c) ⊆ U`
   of `Y`, so `π⁻¹(S_b)` is a principal open `D(a)` of `Y` (`exists_dvd_notMem_of_map_eq_top`,
   `IsAffineOpenImmersion.isLocalization_away`, `isLocalization_away_mul_of_dvd`).
4. *The choice of `g`* (`exists_separation`): there are `b ∈ k[S]` and `f₁ ∈ k[U]` with
   `W ∩ D(φ b) ≠ ∅`, `φ b - f₁ ∈ I k[U]` and `f₁` vanishing on `Z' = π⁻¹(π(W_U)) \ W_U`. The
   source argues by dimension; we use that the irreducible components of `W_U` are irreducible
   components of `π⁻¹(π(W_U))` (incomparability for the finite `π`), see
   `EnvelopeProperty.AlgGeom.FiniteSeparation`. Irreducibility of `W_U` is not needed.
5. *Shrinking* (in steps 3 and 4): `S₁ = S_b` and `U₁ = π⁻¹(S₁) = D(φ b)`; the localized map
   `k[S]_b → k[U]_{φ b}` is finite, injective, generically étale and a closed immersion on
   `W ∩ U₁` (`finite_away_map`, `injective_away_map`, `IsGenericallyEtale.awayMap`,
   `surjective_quotient_away_map`).
6. *Partition of unity*: `f₁ / φ b + (φ b - f₁) / φ b = 1` on `U₁`, with `(φ b - f₁) / φ b`
   vanishing on `W₁ = W ∩ U₁` and `f₁ / φ b` vanishing on `Z'₁ = Z' ∩ U₁`.
7. *Transport* (`exists_projection_away_of_algEquiv`, `ProjectionData.of_isLocalization`):
   `U₁ = D(a c)` with `φ b = c / a^m`, and `S₁ = D(h₀ b')` with `b = b' / h₀^m`; the data are
   transported along the isomorphisms `k[U]_{φ b} ≅ A_{a c}` and `k[S]_b ≅ k[x]_{h₀ b'}`.

## Main results

* `ProjectionExistence.exists_principal`: Lemma 5.23 with `U` a principal open of `Y`.
* `ProjectionExistence.nonempty_projectionData`: the data `ProjectionData k A I`.
* `ProjectionExistence.toProjectionPackage` (instance): `ProjectionExistence k` gives
  `ProjectionPackage k`, so FHX Theorem 5.25 (`IsRegularizable.of_isWeaklyPSHOn`) holds with
  `[ProjectionExistence k]` in place of `[ProjectionPackage k]`.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

universe u v

/-! ### Generic étaleness under localization and isomorphisms -/

section genericallyEtale

variable {A B : Type*} [CommRing A] [CommRing B]

/-- **Generic étaleness is preserved by isomorphisms** of source and target. -/
theorem IsGenericallyEtale.comp_ringEquiv {A' B' : Type*} [CommRing A'] [CommRing B']
    {φ : B →+* A} (hφ : IsGenericallyEtale φ) (e₁ : B' ≃+* B) (e₂ : A ≃+* A') :
    IsGenericallyEtale ((e₂ : A →+* A').comp (φ.comp (e₁ : B' →+* B))) := by
  obtain ⟨h, hh, het⟩ := hφ
  set φ' := (e₂ : A →+* A').comp (φ.comp (e₁ : B' →+* B))
  refine ⟨e₁.symm h, by simpa using hh, ?_⟩
  have H₁ : (Submonoid.powers (e₁.symm h)).map e₁.toMonoidHom = Submonoid.powers h := by
    rw [Submonoid.map_powers]; simp
  have H₂ : (Submonoid.powers (φ h)).map e₂.toMonoidHom = Submonoid.powers (φ' (e₁.symm h)) := by
    rw [Submonoid.map_powers]; simp [φ']
  let E₁ : Localization.Away (e₁.symm h) ≃+* Localization.Away h :=
    IsLocalization.ringEquivOfRingEquiv _ _ e₁ H₁
  let E₂ : Localization.Away (φ h) ≃+* Localization.Away (φ' (e₁.symm h)) :=
    IsLocalization.ringEquivOfRingEquiv _ _ e₂ H₂
  have key : Localization.awayMap φ' (e₁.symm h) =
      (E₂ : _ →+* _).comp ((Localization.awayMap φ h).comp (E₁ : _ →+* _)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (e₁.symm h)) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe, E₁, E₂,
      IsLocalization.ringEquivOfRingEquiv_eq]
    rw [Localization.awayMap, Localization.awayMap, away_map_algebraMap, away_map_algebraMap,
      IsLocalization.ringEquivOfRingEquiv_eq]
    rfl
  rw [key]
  exact ringHom_etale_comp_ringEquiv het E₁ E₂

/-- **Generic étaleness is preserved by localization**: if `π = Spec φ` is generically étale and
`b ≠ 0`, then `π⁻¹(S_b) → S_b` (the map `B_b → A_{φ b}`) is generically étale. -/
theorem IsGenericallyEtale.awayMap [IsDomain B] {φ : B →+* A} (hφ : IsGenericallyEtale φ)
    {b : B} (hb : b ≠ 0) : IsGenericallyEtale (Localization.awayMap φ b) := by
  obtain ⟨h, hh, het⟩ := hφ
  let Bb := Localization.Away b
  let Ab := Localization.Away (φ b)
  let φb : Bb →+* Ab := Localization.awayMap φ b
  have hinj : Function.Injective (algebraMap B Bb) :=
    IsLocalization.injective Bb (powers_le_nonZeroDivisors_of_noZeroDivisors hb)
  refine ⟨algebraMap B Bb h, (map_ne_zero_iff _ hinj).mpr hh, ?_⟩
  -- Model 1: localize the étale map `B_h → A_{φ h}` away from `b`.
  let R₀ := Localization.Away h
  let S₀ := Localization.Away (φ h)
  let f₀ : R₀ →+* S₀ := Localization.awayMap φ h
  let R' := Localization.Away (algebraMap B R₀ b)
  let S' := Localization.Away (f₀ (algebraMap B R₀ b))
  let ψ : R' →+* S' := IsLocalization.Away.map R' S' f₀ (algebraMap B R₀ b)
  have hψ : ψ.Etale := etale_away_map f₀ _ R' S' het
  have hf₀ : ∀ x, f₀ (algebraMap B R₀ x) = algebraMap A S₀ (φ x) := fun x =>
    away_map_algebraMap φ h R₀ S₀ x
  have : IsLocalization.Away (b * h) R' := IsLocalization.Away.mul R₀ R' h b
  have : IsLocalization.Away (algebraMap A S₀ (φ b)) S' := by
    rw [← hf₀]; infer_instance
  have : IsLocalization.Away (φ (b * h)) S' := by
    rw [map_mul]; exact IsLocalization.Away.mul S₀ S' (φ h) (φ b)
  -- Model 2: the map `(B_b)_h → (A_{φ b})_{φ h}`.
  let R₂ := Localization.Away (algebraMap B Bb h)
  let S₂ := Localization.Away (φb (algebraMap B Bb h))
  have hφb : ∀ x, φb (algebraMap B Bb x) = algebraMap A Ab (φ x) := fun x =>
    away_map_algebraMap φ b Bb Ab x
  have : IsLocalization.Away (b * h) R₂ := IsLocalization.Away.mul' Bb R₂ b h
  have : IsLocalization.Away (algebraMap A Ab (φ h)) S₂ := by
    rw [← hφb]; infer_instance
  have : IsLocalization.Away (φ (b * h)) S₂ := by
    rw [map_mul]; exact IsLocalization.Away.mul' Ab S₂ (φ b) (φ h)
  refine etale_of_isLocalization_away φ (b * h) R' S' R₂ S₂ ψ
    (Localization.awayMap φb (algebraMap B Bb h)) ?_ ?_ hψ
  · refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply B R₀ R', away_map_algebraMap, hf₀ x,
      ← IsScalarTower.algebraMap_apply]
  · refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply B Bb R₂, Localization.awayMap, away_map_algebraMap, hφb x,
      ← IsScalarTower.algebraMap_apply]

end genericallyEtale

/-! ### Transport of the data to `Localization.Away h` -/

section transport

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A] {I : Ideal A}

/-- An `A`-algebra isomorphism `e : A' ≃ₐ[A] A''` carries `I A'` onto `I A''`. -/
theorem map_map_algEquiv {A' A'' : Type*} [CommRing A'] [CommRing A''] [Algebra A A']
    [Algebra A A''] (e : A' ≃ₐ[A] A'') (I : Ideal A) :
    (I.map (algebraMap A A')).map (e : A' →+* A'') = I.map (algebraMap A A'') := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext fun x => e.commutes x

/-- **Transport of a projection along isomorphisms.** Let `eA : A' ≃ₐ[A] A_h` and
`eB : B' ≃ₐ[k] k[x]_{h₀}`. A finite injective generically étale `φ : B' → A'`, restricting to a
closed immersion on `V(I A')`, gives such a map `φ' : k[x]_{h₀} → A_h` with `φ' ∘ eB = eA ∘ φ`. -/
theorem exists_projection_away_of_algEquiv (I : Ideal A) (h : A)
    {A' : Type*} [CommRing A'] [Algebra A A'] [Algebra k A'] [IsScalarTower k A A']
    (eA : A' ≃ₐ[A] Localization.Away h) {n : ℕ} {h₀ : MvPolynomial (Fin n) k}
    {B' : Type*} [CommRing B'] [Algebra k B'] (eB : B' ≃ₐ[k] Localization.Away h₀)
    (φ : B' →ₐ[k] A') (hinj : Function.Injective φ) (hfin : (φ : B' →+* A').Finite)
    (het : IsGenericallyEtale (φ : B' →+* A'))
    (hsurj : Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap A A'))).comp (φ : B' →+* A'))) :
    ∃ φ' : Localization.Away h₀ →ₐ[k] Localization.Away h,
      (∀ x, φ' (eB x) = eA (φ x)) ∧
      Function.Injective φ' ∧
      (φ' : Localization.Away h₀ →+* Localization.Away h).Finite ∧
      IsGenericallyEtale (φ' : Localization.Away h₀ →+* Localization.Away h) ∧
      Function.Surjective ((Ideal.Quotient.mk (I.map (algebraMap A (Localization.Away h)))).comp
        (φ' : Localization.Away h₀ →+* Localization.Away h)) := by
  let eAk : A' ≃ₐ[k] Localization.Away h := eA.restrictScalars k
  let φ' : Localization.Away h₀ →ₐ[k] Localization.Away h :=
    (eAk : A' →ₐ[k] Localization.Away h).comp (φ.comp (eB.symm : Localization.Away h₀ →ₐ[k] B'))
  have hφ' : (φ' : Localization.Away h₀ →+* Localization.Away h) =
      (eAk.toRingEquiv : A' →+* Localization.Away h).comp
        ((φ : B' →+* A').comp (eB.symm.toRingEquiv : Localization.Away h₀ →+* B')) := rfl
  have hφ'x : ∀ x, φ' (eB x) = eA (φ x) := fun x => by
    simp [φ', eAk]
  have hmap := map_map_algEquiv eA I
  refine ⟨φ', hφ'x, eAk.injective.comp (hinj.comp eB.symm.injective), ?_, ?_, ?_⟩
  · rw [hφ']
    exact (RingHom.Finite.of_surjective _ eAk.surjective).comp
      (hfin.comp (RingHom.Finite.of_surjective _ eB.symm.surjective))
  · rw [hφ']
    exact het.comp_ringEquiv eB.symm.toRingEquiv eAk.toRingEquiv
  · intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨w, hw⟩ := hsurj (Ideal.Quotient.mk (I.map (algebraMap A A')) (eA.symm y))
    have hwx : φ w - eA.symm y ∈ I.map (algebraMap A A') := Ideal.Quotient.eq.mp hw
    refine ⟨eB w, ?_⟩
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [Ideal.Quotient.eq, hφ'x, ← hmap]
    have := Ideal.mem_map_of_mem (eA : A' →+* Localization.Away h) hwx
    have e1 : (eA : A' →+* Localization.Away h) (φ w - eA.symm y) = eA (φ w) - y := by simp
    rwa [e1] at this

/-- **Transport of the projection data.** Data `(φ, f₁, f₂)` over a localization `A'` of `A` away
from `h` and a `k`-algebra `B' ≅ k[x]_{h₀}` give `ProjectionData k A I`. -/
theorem ProjectionData.of_isLocalization (h : A) (hP : ∃ P : Ideal A, P.IsPrime ∧ I ≤ P ∧ h ∉ P)
    {A' : Type*} [CommRing A'] [Algebra A A'] [Algebra k A'] [IsScalarTower k A A']
    [IsLocalization.Away h A'] {n : ℕ} (hn : 1 ≤ n) {h₀ : MvPolynomial (Fin n) k} (hh₀ : h₀ ≠ 0)
    {B' : Type*} [CommRing B'] [Algebra k B'] (eB : B' ≃ₐ[k] Localization.Away h₀)
    (φ : B' →ₐ[k] A') (hinj : Function.Injective φ) (hfin : (φ : B' →+* A').Finite)
    (het : IsGenericallyEtale (φ : B' →+* A'))
    (hsurj : Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap A A'))).comp (φ : B' →+* A')))
    (f₁ f₂ : A') (hadd : f₁ + f₂ = 1) (hf₂ : f₂ ∈ (I.map (algebraMap A A')).radical)
    (hf₁ : ∀ Q Q₀ : Ideal A', Q.IsPrime → Q₀.IsPrime → I.map (algebraMap A A') ≤ Q₀ →
      ¬ I.map (algebraMap A A') ≤ Q → Q.comap (φ : B' →+* A') = Q₀.comap (φ : B' →+* A') →
      f₁ ∈ Q) :
    Nonempty (ProjectionData k A I) := by
  let eA : A' ≃ₐ[A] Localization.Away h :=
    IsLocalization.algEquiv (Submonoid.powers h) A' (Localization.Away h)
  obtain ⟨φ', hφ'x, hinj', hfin', het', hsurj'⟩ :=
    exists_projection_away_of_algEquiv I h eA eB φ hinj hfin het hsurj
  have hmap := map_map_algEquiv eA I
  refine ⟨{
    h := h
    exists_prime := hP
    n := n
    one_le := hn
    h₀ := h₀
    h₀_ne_zero := hh₀
    φ := φ'
    injective := hinj'
    finite := hfin'
    genericallyEtale := het'
    closedImmersion := hsurj'
    f₁ := eA f₁
    f₂ := eA f₂
    add_eq_one := by rw [← map_add, hadd, map_one]
    f₂_mem := ?_
    f₁_mem := ?_ }⟩
  · obtain ⟨m, hm⟩ := hf₂
    refine ⟨m, ?_⟩
    rw [← map_pow, ← hmap]
    exact Ideal.mem_map_of_mem _ hm
  · intro Q Q₀ hQ hQ₀ hIQ₀ hIQ hc
    have h1 : I.map (algebraMap A A') ≤ Q₀.comap (eA : A' →+* Localization.Away h) := by
      rw [← Ideal.map_le_iff_le_comap, hmap]; exact hIQ₀
    have h2 : ¬ I.map (algebraMap A A') ≤ Q.comap (eA : A' →+* Localization.Away h) := by
      rw [← Ideal.map_le_iff_le_comap, hmap]; exact hIQ
    have hcomp : (φ' : Localization.Away h₀ →+* Localization.Away h).comp
        (eB : B' →+* Localization.Away h₀) =
        (eA : A' →+* Localization.Away h).comp (φ : B' →+* A') := RingHom.ext hφ'x
    have h3 : (Q.comap (eA : A' →+* Localization.Away h)).comap (φ : B' →+* A') =
        (Q₀.comap (eA : A' →+* Localization.Away h)).comap (φ : B' →+* A') := by
      have := congrArg (Ideal.comap (eB : B' →+* Localization.Away h₀)) hc
      rwa [Ideal.comap_comap, Ideal.comap_comap, hcomp, ← Ideal.comap_comap,
        ← Ideal.comap_comap] at this
    exact hf₁ _ _ (Ideal.comap_isPrime _ _) (Ideal.comap_isPrime _ _) h1 h2 h3

end transport

/-! ### The reduction -/

section reduction

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **`U` may be taken principal** (FHX Lemma 5.23, end of the proof: "shrink the target to a
principal affine neighbourhood of the image of `z`"). From `ProjectionExistence`: there are a
principal open `D(a) ∋ z` of `Y`, a principal open `S = D(h₀) ⊆ 𝔸ⁿ` and a finite injective
generically étale `φ : k[x]_{h₀} → A_a` restricting to a closed immersion on `Z ∩ D(a)`.

Given `π = Spec φ : U → S` from `ProjectionExistence` with `U = Spec A'` covered by `D(a)`,
`a ∈ s`: by prime avoidance some `c` in the ideal generated by `s` lies in no prime of the finite
fibre `π⁻¹(π(z))`, and lying over gives `b ∈ k[S]`, `b ∉ π(z)`, with `c ∣ φ b`
(`exists_dvd_notMem_of_map_eq_top`). Then `D(c) ⊆ U` with `A'_c = A_c`
(`IsAffineOpenImmersion.isLocalization_away`), and `π⁻¹(S_b) = U_{φ b} ⊆ D(c)` is a principal
open `D(c d)` of `Y` (`isLocalization_away_mul_of_dvd`). The localized map
`k[S]_b → A'_{φ b}` keeps all properties, and `S_b = D(h₀ b')` is principal in `𝔸ⁿ`. -/
theorem ProjectionExistence.exists_principal [ProjectionExistence.{u, v} k]
    (A : Type v) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (n : ℕ)
    (hn : ringKrullDim A = n) (hn1 : 1 ≤ n) (I : Ideal A) (hrad : I.IsRadical) (hbot : I ≠ ⊥)
    (z : Ideal (A ⧸ I)) [z.IsMaximal] (hsm : Algebra.IsSmoothAt k z) :
    ∃ a : A, Ideal.Quotient.mk I a ∉ z ∧
    ∃ h₀ : MvPolynomial (Fin n) k, h₀ ≠ 0 ∧
    ∃ φ : Localization.Away h₀ →ₐ[k] Localization.Away a,
      Function.Injective φ ∧
      (φ : Localization.Away h₀ →+* Localization.Away a).Finite ∧
      IsGenericallyEtale (φ : Localization.Away h₀ →+* Localization.Away a) ∧
      Function.Surjective ((Ideal.Quotient.mk (I.map (algebraMap A (Localization.Away a)))).comp
        (φ : Localization.Away h₀ →+* Localization.Away a)) := by
  classical
  obtain ⟨A', _, _, _, _, ⟨s, hs, hloc⟩, ⟨z', hz', hz'c⟩, h₀, hh₀, φ, hinj, hfin, het, hsurj⟩ :=
    ProjectionExistence.exists_projection A n hn hn1 I hrad hbot z hsm
  let B := Localization.Away h₀
  have : IsDomain B := IsLocalization.Away.isDomain (S := B) hh₀
  have : IsNoetherianRing A' := by
    let := (φ : B →+* A').toAlgebra
    have : Algebra.FiniteType B A' := hfin.finiteType
    exact Algebra.FiniteType.isNoetherianRing B A'
  -- Shrinking around the fibre over `π(z)`.
  have hJ : (Ideal.span (s : Set A)).map (algebraMap A A') = ⊤ := by
    rw [Ideal.map_span]; exact hs
  obtain ⟨c, hcJ, b, hb𝔮, hdvd⟩ := exists_dvd_notMem_of_map_eq_top (φ : B →+* A')
    hfin.to_isIntegral (z'.comap (φ : B →+* A')) _ hJ
  have hbz' : φ b ∉ z' := hb𝔮
  have hb0 : b ≠ 0 := by
    rintro rfl; exact hbz' (by simp [z'.zero_mem])
  have : IsLocalization.Away c (Localization.Away (algebraMap A A' c)) :=
    IsAffineOpenImmersion.isLocalization_away hloc hcJ
  obtain ⟨d, hd⟩ := isLocalization_away_mul_of_dvd c hdvd
  -- The localized projection `k[S]_b → A'_{φ b}`.
  let B₁ := Localization.Away b
  let A₁ := Localization.Away (φ b)
  have : IsLocalization.Away ((φ : B →+* A') b) A₁ :=
    (inferInstance : IsLocalization.Away (φ b) A₁)
  have : IsLocalization.Away (c * d) A₁ := hd
  let φ₁ : B₁ →ₐ[k] A₁ := IsLocalization.Away.mapₐ B₁ A₁ φ b
  have hinj₁ : Function.Injective φ₁ := IsLocalization.Away.mapₐ_injective_of_injective b hinj
  have hfin₁ : (φ₁ : B₁ →+* A₁).Finite := finite_away_map (φ : B →+* A') b B₁ A₁ hfin
  have het₁ : IsGenericallyEtale (φ₁ : B₁ →+* A₁) := het.awayMap hb0
  have hsurj₁ : Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap A A₁))).comp (φ₁ : B₁ →+* A₁)) := by
    have h := surjective_quotient_away_map (φ : B →+* A') b B₁ A₁ _ hsurj
    rwa [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at h
  -- `S_b = D(h₀ b')`.
  obtain ⟨⟨b', ⟨_, m', rfl⟩⟩, hb'⟩ := IsLocalization.surj (Submonoid.powers h₀) b
  have hbB : Associated (algebraMap (MvPolynomial (Fin n) k) B b') b := by
    have hu : IsUnit (algebraMap (MvPolynomial (Fin n) k) B (h₀ ^ m')) :=
      IsLocalization.map_units B (⟨h₀ ^ m', m', rfl⟩ : Submonoid.powers h₀)
    exact ⟨hu.unit⁻¹, by
      simp only at hb'
      rw [← hb', mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
  have : IsLocalization.Away (h₀ * b') B₁ :=
    IsLocalization.Away.mul_of_associated (S := B) h₀ b' b hbB
  have hb'0 : b' ≠ 0 := by
    rintro rfl
    exact hb0 (hbB.eq_zero_iff.mp (map_zero _))
  let eB : B₁ ≃ₐ[k] Localization.Away (h₀ * b') :=
    (IsLocalization.algEquiv (Submonoid.powers (h₀ * b')) B₁
      (Localization.Away (h₀ * b'))).restrictScalars k
  obtain ⟨φ', -, hφ'⟩ := exists_projection_away_of_algEquiv I (c * d)
    (IsLocalization.algEquiv (Submonoid.powers (c * d)) A₁ (Localization.Away (c * d))) eB φ₁
    hinj₁ hfin₁ het₁ hsurj₁
  refine ⟨c * d, ?_, h₀ * b', mul_ne_zero hh₀ hb'0, φ', hφ'⟩
  -- `z ∈ D(c d)`: the prime `z' A'_{φ b}` does not contain the unit `c d`.
  intro hcd
  have hcd' : algebraMap A A' (c * d) ∈ z' := by
    rw [← Ideal.mem_comap, hz'c]; exact hcd
  have hdisj : Disjoint (Submonoid.powers (φ b) : Set A') z' := by
    rw [Ideal.disjoint_powers_iff_notMem _ hz'.isRadical]; exact hbz'
  have hP := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (φ b)) A₁ z' hz' hdisj
  have hmem : algebraMap A A₁ (c * d) ∈ z'.map (algebraMap A' A₁) := by
    rw [IsScalarTower.algebraMap_apply A A' A₁]; exact Ideal.mem_map_of_mem _ hcd'
  exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (IsLocalization.Away.algebraMap_isUnit _))

/-- **FHX Lemma 5.23 gives the projection data** of the proof of Theorem 5.25: for a finitely
generated domain `A` over `k` and a radical ideal `I` with `I ≠ ⊥`, `I ≠ ⊤`, there is a
`ProjectionData k A I`. See the module docstring for the argument. -/
theorem ProjectionExistence.nonempty_projectionData [ProjectionExistence.{u, v} k]
    (A : Type v) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (I : Ideal A)
    (hrad : I.IsRadical) (hbot : I ≠ ⊥) (htop : I ≠ ⊤) : Nonempty (ProjectionData k A I) := by
  classical
  -- Step 1: a smooth closed point of `W = V(I)`, and the dimension.
  have : IsReduced (A ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hrad
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr htop
  obtain ⟨z, hz, hsm⟩ := exists_isMaximal_isSmoothAt k (A ⧸ I)
  set zA := z.comap (Ideal.Quotient.mk I)
  have hzA_max : zA.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hIz : I ≤ zA := fun x hx => by
    simp [zA, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast k A
  have hn1 : 1 ≤ n := by
    have : (⊥ : Ideal A) < zA := lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr hbot) hIz
    have h1 := one_le_ringKrullDim_of_lt (P := ⊥) (Q := zA) this
    rw [hn] at h1
    exact_mod_cast h1
  -- Steps 2 and 3: Lemma 5.23, with `U = D(a)` principal.
  obtain ⟨a, haz, h₀, hh₀, φ, hinj, hfin, het, hsurj⟩ :=
    ProjectionExistence.exists_principal A n hn hn1 I hrad hbot z hsm
  let A₁ := Localization.Away a
  let B := Localization.Away h₀
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : IsDomain B := IsLocalization.Away.isDomain (S := B) hh₀
  have hdisj : Disjoint (Submonoid.powers a : Set A) zA := by
    rw [Ideal.disjoint_powers_iff_notMem _ hzA_max.isPrime.isRadical]; exact haz
  set J := I.map (algebraMap A A₁) with hJ
  have hJtop : J ≠ ⊤ := by
    have hP := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) A₁ zA
      hzA_max.isPrime hdisj
    exact ne_top_of_le_ne_top hP.ne_top (Ideal.map_mono hIz)
  -- Step 4: the choice of `g` (here `b`).
  obtain ⟨b, ⟨P, hP, hJP, hbP⟩, f₁, hf₁J, hf₁⟩ :=
    exists_separation (φ : B →+* A₁) hfin.to_isIntegral J hJtop hsurj
  have hb0 : b ≠ 0 := by
    rintro rfl; exact hbP (by simp [P.zero_mem])
  -- Step 5: shrinking to `S_b` and `U_{φ b}`.
  let B₂ := Localization.Away b
  let A₂ := Localization.Away (φ b)
  let φ₂ : B₂ →ₐ[k] A₂ := IsLocalization.Away.mapₐ B₂ A₂ φ b
  have : IsLocalization.Away ((φ : B →+* A₁) b) A₂ :=
    (inferInstance : IsLocalization.Away (φ b) A₂)
  have hφ₂x : ∀ x, φ₂ (algebraMap B B₂ x) = algebraMap A₁ A₂ (φ x) := fun x =>
    away_map_algebraMap (φ : B →+* A₁) b B₂ A₂ x
  have hJ₂ : J.map (algebraMap A₁ A₂) = I.map (algebraMap A A₂) := by
    rw [hJ, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  -- Step 7 (part): `U_{φ b} = D(a c)` and `S_b = D(h₀ b')`.
  obtain ⟨⟨c, ⟨_, m, rfl⟩⟩, hc⟩ := IsLocalization.surj (Submonoid.powers a) (φ b)
  have hcA : Associated (algebraMap A A₁ c) (φ b) := by
    have hu : IsUnit (algebraMap A A₁ (a ^ m)) :=
      IsLocalization.map_units A₁ (⟨a ^ m, m, rfl⟩ : Submonoid.powers a)
    exact ⟨hu.unit⁻¹, by
      simp only at hc
      rw [← hc, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
  have : IsLocalization.Away (a * c) A₂ :=
    IsLocalization.Away.mul_of_associated (S := A₁) a c (φ b) hcA
  obtain ⟨⟨b', ⟨_, m', rfl⟩⟩, hb'⟩ := IsLocalization.surj (Submonoid.powers h₀) b
  have hbB : Associated (algebraMap (MvPolynomial (Fin n) k) B b') b := by
    have hu : IsUnit (algebraMap (MvPolynomial (Fin n) k) B (h₀ ^ m')) :=
      IsLocalization.map_units B (⟨h₀ ^ m', m', rfl⟩ : Submonoid.powers h₀)
    exact ⟨hu.unit⁻¹, by
      simp only at hb'
      rw [← hb', mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
  have : IsLocalization.Away (h₀ * b') B₂ :=
    IsLocalization.Away.mul_of_associated (S := B) h₀ b' b hbB
  have hb'0 : b' ≠ 0 := by
    rintro rfl
    exact hb0 (hbB.eq_zero_iff.mp (map_zero _))
  let eB : B₂ ≃ₐ[k] Localization.Away (h₀ * b') :=
    (IsLocalization.algEquiv (Submonoid.powers (h₀ * b')) B₂
      (Localization.Away (h₀ * b'))).restrictScalars k
  -- Steps 5 and 6: the localized projection and the partition of unity.
  have hinj₂ : Function.Injective φ₂ := IsLocalization.Away.mapₐ_injective_of_injective b hinj
  have hfin₂ : (φ₂ : B₂ →+* A₂).Finite := finite_away_map (φ : B →+* A₁) b B₂ A₂ hfin
  have het₂ : IsGenericallyEtale (φ₂ : B₂ →+* A₂) := het.awayMap hb0
  have hsurj₂ : Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap A A₂))).comp (φ₂ : B₂ →+* A₂)) := by
    rw [← hJ₂]; exact surjective_quotient_away_map (φ : B →+* A₁) b B₂ A₂ J hsurj
  let w : A₂ := IsLocalization.Away.invSelf ((φ : B →+* A₁) b)
  have hw : algebraMap A₁ A₂ (φ b) * w = 1 := IsLocalization.Away.mul_invSelf _
  have hcomp : (algebraMap A₁ A₂).comp (φ : B →+* A₁) =
      (φ₂ : B₂ →+* A₂).comp (algebraMap B B₂) := RingHom.ext fun x => (hφ₂x x).symm
  refine ProjectionData.of_isLocalization (a * c)
    ⟨P.comap (algebraMap A A₁), Ideal.comap_isPrime _ _, Ideal.map_le_iff_le_comap.mp hJP, ?_⟩
    hn1 (mul_ne_zero hh₀ hb'0) eB φ₂ hinj₂ hfin₂ het₂ hsurj₂ (algebraMap A₁ A₂ f₁ * w)
    (algebraMap A₁ A₂ (φ b - f₁) * w) ?_ ?_ ?_
  · -- `a c ∉ P`: `a` is a unit in `A_a` and `c` is associated to `φ b ∉ P`.
    intro hac
    rw [Ideal.mem_comap, map_mul] at hac
    rcases hP.mem_or_mem hac with ha | hc'
    · exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ ha (IsLocalization.Away.algebraMap_isUnit a))
    · obtain ⟨v, hv⟩ := hcA
      exact hbP (hv ▸ Ideal.mul_mem_right _ _ hc')
  · rw [← add_mul, ← map_add, add_sub_cancel, hw]
  · refine Ideal.le_radical (Ideal.mul_mem_right _ _ ?_)
    rw [← hJ₂]
    exact Ideal.mem_map_of_mem _ hf₁J
  · intro Q Q₀ hQ hQ₀ hIQ₀ hIQ hc
    refine Ideal.mul_mem_right _ _ (show f₁ ∈ Q.comap (algebraMap A₁ A₂) from ?_)
    have hJQ₀ : J ≤ Q₀.comap (algebraMap A₁ A₂) := by
      rw [← Ideal.map_le_iff_le_comap, hJ₂]; exact hIQ₀
    have hJQ : ¬ J ≤ Q.comap (algebraMap A₁ A₂) := by
      rw [← Ideal.map_le_iff_le_comap, hJ₂]; exact hIQ
    have hc₁ : (Q.comap (algebraMap A₁ A₂)).comap (φ : B →+* A₁) =
        (Q₀.comap (algebraMap A₁ A₂)).comap (φ : B →+* A₁) := by
      rw [Ideal.comap_comap, Ideal.comap_comap, hcomp, ← Ideal.comap_comap,
        ← Ideal.comap_comap, hc]
    exact hf₁ _ (Ideal.comap_isPrime _ _) (hc₁ ▸ Ideal.comap_mono hJQ₀) hJQ

/-- **FHX Lemma 5.23 implies the algebraic-geometry package of Theorem 5.25.** Generic smoothness,
the choice of `g` and the partition of unity are proved
(`ProjectionExistence.nonempty_projectionData`); only Lemma 5.23 itself is assumed. -/
instance (priority := 100) ProjectionExistence.toProjectionPackage
    [ProjectionExistence.{u, v} k] : ProjectionPackage.{u, v} k where
  nonempty_projectionData A _ _ _ _ _ I hrad hbot htop :=
    ProjectionExistence.nonempty_projectionData A I hrad hbot htop

end reduction

end EnvelopeProperty
