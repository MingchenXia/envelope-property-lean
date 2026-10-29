/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Algebra.NonflatCharpoly
import EnvelopeProperty.Berkovich.NontrivialRigidField
import EnvelopeProperty.Berkovich.NonflatLineGeneric
import EnvelopeProperty.Berkovich.AffineLineScalarExtension
import EnvelopeProperty.Local.NonflatImport
import EnvelopeProperty.Berkovich.FlatFibre

/-!
# The good locus of a generically étale finite cover, and the rigid base change

This file formalizes `lem:nf-good-locus`, `lem:nf-rigid-fibre`(1) and `lem:nf-line-exists` of the
blueprint chapter `nonflat-route.tex`, the nonflat route to Fang–Han–Xia, *The envelope property
for unibranch projective varieties*, Proposition 5.22 (`prop:nonflat-norm`; Section 5, `sec:normal-local-regularization`; the proof
introduces the étale locus `S_0`, the rigid lift `ξ` over the completed algebraic closure `F` of
`ℋ(s)` and the lines through it).

## Setting (`conv:nf-setting`)

`k` is a field, `S = Spec B` with `B ≅ k[x]_{h_S}` (`IsAffineSpacePrincipalOpen k B n`),
`Y = Spec A` with `A` a domain, `φ: B → A` finite and injective, `π = Spec φ` generically étale
(`IsGenericallyEtale`), of degree `d = genericDegree φ = rank_B A`, and `Z = V(S) ⊊ Y`
for a finite set `S ⊆ A` containing a nonzero element.

## Main definitions and results

* `IsAffineSpacePrincipalOpen.isDomain`, `.isIntegrallyClosed`, `.isNoetherianRing`: `B` is an
  integrally closed noetherian domain; `.exists_ulift`: a presentation `B ≅ k[x]_{h_S}` with
  coordinates `ULift (Fin n)` in any universe (the author's line API has field, coordinates and
  algebra in one universe).
* `EnvelopeProperty.IsNonflatGoodLocus φ S h` (`lem:nf-good-locus`): `h ≠ 0`, `φ(h) ∈ (S)` (so that
  `Y_0 = Spec A_{φ(h)}` misses `Z`), and `B_h ⊗_B A` is a free étale `B_h`-algebra (finite if `φ`
  is). `exists_isNonflatGoodLocus` produces such `h = h₁ h₂ χ_f(0)` as in the blueprint proof, from
  generic étaleness (`h₁`), generic freeness (`h₂`, `nonflat_exists_free_localizationAway`) and the
  constant term of the characteristic polynomial of `0 ≠ f ∈ S` (`lem:nf-charpoly`,
  `dvd_algebraMap_coeff_zero_nonflatCharpoly`). Consequences:
  * `IsNonflatGoodLocus.exists_mem_ne_zero`: points of `Y^an` over `S_0^an` are off `Z^an`;
  * `IsNonflatGoodLocus.free_tensor`, `.etale_tensor`, `.finrank_tensor`: for every `B`-algebra `C` in
    which `h` is a unit, `C ⊗_B A` is free and étale over `C`, of rank `d` if `C ≠ 0`;
  * `IsNonflatGoodLocus.sum_flatFibreMult`: over `s ∈ S_0^an`, the multiplicities
    `Berk.flatFibreMult` of `π` add up to `d`;
  * `nonflat_awayMap_finite`, `IsNonflatGoodLocus.awayMap_etale`, `.awayMap_free`, `.isDomain_away`:
    the localized map `B_h → A_{φ(h)}` (`Localization.awayMap`) is finite free étale, through
    `nonflatAwayTensorEquiv: B_h ⊗_B A ≅ A_{φ(h)}`.
* `lem:nf-rigid-fibre`(1): for a field `F ⊇ k`, `nonflatBaseEquiv: F ⊗_k B ≅ F[x]_{h_S}`, so
  `F ⊗_k B` is an integrally closed domain (`nonflat_isDomain_baseChange_base`,
  `nonflat_isIntegrallyClosed_baseChange_base`); `F ⊗_k A` is a domain if `k` is algebraically closed
  (`tensorProduct_isDomain_of_algClosed`), finite over `F ⊗_k B` (`nonflat_baseChange_finite`), and
  `IsNonflatGoodLocus.finrank_baseChange`: its rank over `F ⊗_k B` is `d`.
* Coordinates (the interface with the author's line API and `Local/NonflatLineFibres`):
  `nonflatCoordMap F E φ: F[x]_{h_S} → F ⊗_k A` is `φ_F`; `nonflat_nonempty_coord_tensorEquiv`:
  `C ⊗_{B_F} A_F ≅ C ⊗_B A` for every `B_F`-algebra `C`; hence `IsNonflatGoodLocus.coord_etale`,
  `.coord_free` (the hypotheses `het`, `hfree` of `AffineLine.nonflatLine_lineWeights` for
  `h_F = ψ(1 ⊗ h)`) and `.finrank_coord` (`rank_{B_F} A_F = d`). `nonflatCharpoly_map_ringEquiv`
  transports characteristic polynomials along `F ⊗_k B ≅ F[x]_{h_S}`.
* `lem:nf-line-exists`: for an `F`-point `ξ` of `F ⊗_k B`, `nonflatLinePoint E ξ ∈ F^σ` are its
  coordinates; `nonflat_linePoint_eval_ne_zero` (`h_S(a) ≠ 0`), `nonflat_lineEval_comp` (the line
  `t ↦ a + t w` passes through `ξ` at `t = 0`) and `nonflat_exists_admissible_direction`: for
  `0 ≠ e ∈ B` there is a direction `w ≠ 0` with `ι(e) ≠ 0`; `nonflat_admissible_of_mul`.

## Comparison with the blueprint

* The good locus is recorded in tensor form (`B_h ⊗_B A` free and étale over `B_h`), the form that
  base changes along `B → C` for every `C` in which `h` is a unit; the localized form
  `B_h → A_{φ(h)}` is derived.
* The degree `d` of `lem:nf-rigid-fibre`(1) is stated as `rank_{F ⊗_k B} (F ⊗_k A) = d`, which is
  `dim_{Frac B_F} (Frac B_F ⊗_{B_F} A_F)` (`nonflat_finrank_fractionRing_tensor`); it is proved by base
  change from the free localization `B_h ⊗_B A`, as in the blueprint.
-/

open scoped NNReal ENNReal Topology TensorProduct nonZeroDivisors
open Polynomial

noncomputable section

universe w

namespace EnvelopeProperty

open Berk

/-! ### Principal opens of affine space -/

namespace IsAffineSpacePrincipalOpen

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {n : ℕ}

/-- A principal open of `𝔸ⁿ` is a domain. -/
theorem isDomain (hB : IsAffineSpacePrincipalOpen k B n) : IsDomain B := by
  obtain ⟨h, hh, ⟨E⟩⟩ := hB
  have : IsDomain (Localization.Away h) := IsLocalization.Away.isDomain _ hh
  exact Function.Injective.isDomain (E : B →+* Localization.Away h) E.injective

/-- A principal open of `𝔸ⁿ` is integrally closed (a localization of a factorial ring). -/
theorem isIntegrallyClosed (hB : IsAffineSpacePrincipalOpen k B n) : IsIntegrallyClosed B := by
  obtain ⟨h, hh, ⟨E⟩⟩ := hB
  have : IsIntegrallyClosed (Localization.Away h) :=
    isIntegrallyClosed_of_isLocalization (Localization.Away h) (Submonoid.powers h)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hh)
  exact IsIntegrallyClosed.of_equiv E.symm.toRingEquiv

/-- A principal open of `𝔸ⁿ` is noetherian. -/
theorem isNoetherianRing (hB : IsAffineSpacePrincipalOpen k B n) : IsNoetherianRing B :=
  have := hB.finiteType
  Algebra.FiniteType.isNoetherianRing k B

/-- A presentation of a principal open of `𝔸ⁿ` with coordinates in an arbitrary universe:
`B ≅ k[x_i : i ∈ ULift (Fin n)]_{h_S}` (the author's line API has coordinates, field and
algebra in one universe). -/
theorem exists_ulift (hB : IsAffineSpacePrincipalOpen k B n) :
    ∃ hS : MvPolynomial (ULift.{w} (Fin n)) k, hS ≠ 0 ∧
      Nonempty (B ≃ₐ[k] Localization.Away hS) := by
  obtain ⟨h, hh, ⟨E⟩⟩ := hB
  let R : MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (ULift.{w} (Fin n)) k :=
    MvPolynomial.renameEquiv k Equiv.ulift.symm
  refine ⟨R h, (map_ne_zero_iff _ R.injective).2 hh, ⟨E.trans ?_⟩⟩
  exact IsLocalization.algEquivOfAlgEquiv (Localization.Away h) (Localization.Away (R h)) R
    (Submonoid.map_powers R h)

end IsAffineSpacePrincipalOpen

/-! ### Localized algebras and tensor products -/

section Tensor

/-- If `T_f ⊗` is étale over `R_f` and `f` becomes a unit in `S`, then `S ⊗_R T` is étale over `S`
(base change along `R_f → S`). -/
theorem nonflat_etale_tensor_of_isUnit {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    {f : R} (het : Algebra.Etale (Localization.Away f) (Localization.Away f ⊗[R] T)) (S : Type*)
    [CommRing S] [Algebra R S] (hf : IsUnit (algebraMap R S f)) : Algebra.Etale S (S ⊗[R] T) := by
  let Rf := Localization.Away f
  let _ : Algebra Rf S := (IsLocalization.Away.lift f hf).toAlgebra
  have : IsScalarTower R Rf S := IsScalarTower.of_algebraMap_eq fun r =>
    (IsLocalization.Away.lift_eq f hf r).symm
  have : Algebra.Etale S (S ⊗[Rf] (Rf ⊗[R] T)) := Algebra.Etale.baseChange Rf (Rf ⊗[R] T) S
  exact Algebra.Etale.of_equiv (Algebra.TensorProduct.cancelBaseChange R Rf S S T)

/-- If `T_f` is free over `R_f` and `f` is a unit in the nontrivial `R`-algebra `S`, then
`rank_S (S ⊗_R T) = rank_{R_f} (R_f ⊗_R T)`. -/
theorem nonflat_finrank_tensor_of_isUnit {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    {f : R} (hfree : Module.Free (Localization.Away f) (Localization.Away f ⊗[R] T)) (S : Type*)
    [CommRing S] [Nontrivial S] [Algebra R S] (hf : IsUnit (algebraMap R S f)) :
    Module.finrank S (S ⊗[R] T) =
      Module.finrank (Localization.Away f) (Localization.Away f ⊗[R] T) := by
  let Rf := Localization.Away f
  let _ : Algebra Rf S := (IsLocalization.Away.lift f hf).toAlgebra
  have : IsScalarTower R Rf S := IsScalarTower.of_algebraMap_eq fun r =>
    (IsLocalization.Away.lift_eq f hf r).symm
  have : Nontrivial Rf := (algebraMap Rf S).domain_nontrivial
  rw [← (Algebra.TensorProduct.cancelBaseChange R Rf S S T).toLinearEquiv.finrank_eq]
  exact Module.finrank_baseChange

variable {A B : Type*} [CommRing A] [CommRing B]

/-- **The localized algebra as a base change**: `B_h ⊗_B A ≅ A_{φ(h)}` as `B_h`-algebras, with `A`
a `B`-algebra through `φ` and `A_{φ(h)}` a `B_h`-algebra through `Localization.awayMap φ h`. -/
def nonflatAwayTensorEquiv (φ : B →+* A) (h : B) :
    letI := φ.toAlgebra
    letI := (Localization.awayMap φ h).toAlgebra
    Localization.Away h ⊗[B] A ≃ₐ[Localization.Away h] Localization.Away (φ h) :=
  letI := φ.toAlgebra
  letI := (Localization.awayMap φ h).toAlgebra
  haveI : IsScalarTower B (Localization.Away h) (Localization.Away (φ h)) :=
    IsScalarTower.of_algebraMap_eq fun b => by
      change algebraMap A (Localization.Away (φ h)) (φ b) =
        Localization.awayMap φ h (algebraMap B (Localization.Away h) b)
      rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers h))
      (Localization.Away (φ h)) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact Localization.isLocalization
  haveI := (Algebra.isPushout_of_isLocalization (Submonoid.powers h) (Localization.Away h) A
    (Localization.Away (φ h))).symm
  Algebra.IsPushout.equiv B (Localization.Away h) A (Localization.Away (φ h))

@[simp]
theorem nonflatAwayTensorEquiv_tmul (φ : B →+* A) (h : B) (c : Localization.Away h) (a : A) :
    letI := φ.toAlgebra
    letI := (Localization.awayMap φ h).toAlgebra
    nonflatAwayTensorEquiv φ h (c ⊗ₜ a) =
      Localization.awayMap φ h c * algebraMap A (Localization.Away (φ h)) a := by
  let := φ.toAlgebra
  let := (Localization.awayMap φ h).toAlgebra
  rw [nonflatAwayTensorEquiv, Algebra.IsPushout.equiv_tmul]
  rfl

end Tensor

/-! ### The good locus (`lem:nf-good-locus`) -/

section GoodLocus

variable {k : Type*} [Field k] {A B : Type*} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

/-- **A good principal open of `S`** (`lem:nf-good-locus`): `h ≠ 0`, `φ(h)` lies in the ideal
`(S)` of `Z = V(S)` (so `Y_0 = Spec A_{φ(h)} = π⁻¹(S_h)` misses `Z`), and `B_h ⊗_B A` (that is,
`A_{φ(h)}`, `nonflatAwayTensorEquiv`) is a free étale `B_h`-algebra. -/
structure IsNonflatGoodLocus (φ : B →ₐ[k] A) (S : Finset A) (h : B) : Prop where
  /-- `h ≠ 0`. -/
  ne_zero : h ≠ 0
  /-- `φ(h)` vanishes on `Z = V(S)`. -/
  mem_span : φ h ∈ Ideal.span (S : Set A)
  /-- `B_h ⊗_B A` is free over `B_h`. -/
  free : letI := (φ : B →+* A).toAlgebra
    Module.Free (Localization.Away h) (Localization.Away h ⊗[B] A)
  /-- `B_h ⊗_B A` is étale over `B_h`. -/
  etale : letI := (φ : B →+* A).toAlgebra
    Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] A)

/-- **`lem:nf-good-locus`.** Let `B` be a principal open of `𝔸ⁿ`, `A` a domain and `φ : B → A`
finite, injective and generically étale, and let `S ⊆ A` contain a nonzero element `f`. There is
`h ∈ B` with `IsNonflatGoodLocus φ S h`: take `h = h₁ h₂ χ_f(0)` with `B_{h₁} → A_{φ(h₁)}` étale,
`A_{h₂}` free over `B_{h₂}` (generic freeness), and `χ_f(0) ≠ 0`, `f ∣ φ(χ_f(0))`
(`lem:nf-charpoly` for `B ⊆ A`). -/
theorem exists_isNonflatGoodLocus {n : ℕ} (hB : IsAffineSpacePrincipalOpen k B n) [IsDomain A]
    (φ : B →ₐ[k] A) (hinj : Function.Injective φ) (hfin : (φ : B →+* A).Finite)
    (het : IsGenericallyEtale (φ : B →+* A)) (S : Finset A) (hS : ∃ f ∈ S, f ≠ 0) :
    ∃ h : B, IsNonflatGoodLocus φ S h := by
  have := hB.isDomain
  have := hB.isIntegrallyClosed
  have := hB.isNoetherianRing
  let := (φ : B →+* A).toAlgebra
  have : Module.Finite B A := hfin
  have : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).2 hinj
  obtain ⟨h₁, hh₁, het₁⟩ := het
  obtain ⟨h₂, hh₂, hfree₂⟩ := nonflat_exists_free_localizationAway (R := B) (M := A)
  obtain ⟨f, hfS, hf0⟩ := hS
  set c := (nonflatCharpoly B A f).coeff 0 with hc
  have hc0 : c ≠ 0 := coeff_zero_nonflatCharpoly_ne_zero hf0
  have hcf : f ∣ φ c := dvd_algebraMap_coeff_zero_nonflatCharpoly f
  refine ⟨h₁ * (h₂ * c), mul_ne_zero hh₁ (mul_ne_zero hh₂ hc0), ?_, ?_, ?_⟩
  · rw [map_mul, map_mul]
    refine Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ?_)
    obtain ⟨a, ha⟩ := hcf
    rw [ha]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span hfS)
  · exact nonflat_free_away_of_dvd hfree₂ ⟨h₁ * c, by ring⟩
  · let := (Localization.awayMap (φ : B →+* A) h₁).toAlgebra
    have : Algebra.Etale (Localization.Away h₁) (Localization.Away ((φ : B →+* A) h₁)) := het₁
    have het₁' : Algebra.Etale (Localization.Away h₁) (Localization.Away h₁ ⊗[B] A) :=
      Algebra.Etale.of_equiv (nonflatAwayTensorEquiv (φ : B →+* A) h₁).symm
    refine nonflat_etale_tensor_of_isUnit het₁' _ ?_
    exact isUnit_of_mul_isUnit_left (by
      rw [← map_mul]
      exact IsLocalization.Away.algebraMap_isUnit (h₁ * (h₂ * c)))

namespace IsNonflatGoodLocus

variable {φ : B →ₐ[k] A} {S : Finset A} {h : B} (hh : IsNonflatGoodLocus φ S h)
include hh

/-- **`Y_0 ∩ Z = ∅`**: a point of `Y^an` over `S_0^an` (`|h| ≠ 0`) is off `Z^an`: some `f ∈ S`
does not vanish at it. -/
theorem exists_mem_ne_zero {y : Berk k A} (hy : (comap φ y).val h ≠ 0) :
    ∃ f ∈ S, y.val f ≠ 0 := by
  by_contra! h0
  apply hy
  rw [comap_val_apply, ← Valuation.mem_supp_iff]
  refine (Ideal.span_le.2 fun f hf => ?_) hh.mem_span
  exact (Valuation.mem_supp_iff _ _).2 (h0 f hf)

/-- For every `B`-algebra `C` in which `h` is a unit, `C ⊗_B A` is free over `C`. -/
theorem free_tensor (C : Type*) [CommRing C] [Algebra B C] (hC : IsUnit (algebraMap B C h)) :
    letI := (φ : B →+* A).toAlgebra
    Module.Free C (C ⊗[B] A) :=
  letI := (φ : B →+* A).toAlgebra
  nonflat_free_tensor_of_isUnit hh.free C hC

/-- For every `B`-algebra `C` in which `h` is a unit, `C ⊗_B A` is étale over `C`. -/
theorem etale_tensor (C : Type*) [CommRing C] [Algebra B C] (hC : IsUnit (algebraMap B C h)) :
    letI := (φ : B →+* A).toAlgebra
    Algebra.Etale C (C ⊗[B] A) :=
  letI := (φ : B →+* A).toAlgebra
  nonflat_etale_tensor_of_isUnit hh.etale C hC

/-- For every nontrivial `B`-algebra `C` in which `h` is a unit, `C ⊗_B A` has rank
`d = genericDegree φ` over `C`. -/
theorem finrank_tensor [IsDomain B] (C : Type*) [CommRing C] [Nontrivial C] [Algebra B C]
    (hC : IsUnit (algebraMap B C h)) :
    letI := (φ : B →+* A).toAlgebra
    Module.finrank C (C ⊗[B] A) = genericDegree (φ : B →+* A) := by
  let := (φ : B →+* A).toAlgebra
  rw [nonflat_finrank_tensor_of_isUnit hh.free C hC,
    nonflat_finrank_localizationAway_tensor hh.ne_zero (Localization.Away h)]
  rfl

/-- **The multiplicities over the good locus add up to the degree**: for `s ∈ S_0^an`
(`|h|_s ≠ 0`), `∑_{π(y) = s} m_y = d` with `m_y = Berk.flatFibreMult B y`
(`dim_{ℋ(s)} (ℋ(s) ⊗_B A) = d`, as `h` is a unit in `ℋ(s)`). -/
theorem sum_flatFibreMult [IsDomain B] (hfin : (φ : B →+* A).Finite) {s : Berk k B}
    (hs : s.val h ≠ 0) :
    letI := (φ : B →+* A).toAlgebra
    haveI : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    ∑ y ∈ (finite_preimage_comap_singleton φ hfin s).toFinset, flatFibreMult B y =
      genericDegree (φ : B →+* A) := by
  let := (φ : B →+* A).toAlgebra
  have : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have : Module.Finite B A := hfin
  rw [show (finite_preimage_comap_singleton φ hfin s).toFinset =
    (finite_preimage_singleton (A := A) s).toFinset from rfl, Berk.sum_flatFibreMult]
  refine hh.finrank_tensor (H s) (isUnit_iff_ne_zero.2 ?_)
  rw [algebraMap_H, Ne, toH_eq_zero_iff]
  exact hs

/-- The localized map `B_h → A_{φ(h)}` is étale. -/
theorem awayMap_etale : (Localization.awayMap (φ : B →+* A) h).Etale := by
  let := (φ : B →+* A).toAlgebra
  let := (Localization.awayMap (φ : B →+* A) h).toAlgebra
  have := hh.etale
  have : Algebra.Etale (Localization.Away h) (Localization.Away ((φ : B →+* A) h)) :=
    Algebra.Etale.of_equiv (nonflatAwayTensorEquiv (φ : B →+* A) h)
  exact this

/-- `A_{φ(h)}` is a free `B_h`-module. -/
theorem awayMap_free :
    letI := (Localization.awayMap (φ : B →+* A) h).toAlgebra
    Module.Free (Localization.Away h) (Localization.Away ((φ : B →+* A) h)) := by
  let := (φ : B →+* A).toAlgebra
  let := (Localization.awayMap (φ : B →+* A) h).toAlgebra
  have := hh.free
  exact Module.Free.of_equiv (nonflatAwayTensorEquiv (φ : B →+* A) h).toLinearEquiv

omit hh in
/-- The localized map `B_h → A_{φ(h)}` of a finite map is finite. -/
theorem _root_.EnvelopeProperty.nonflat_awayMap_finite (hfin : (φ : B →+* A).Finite) (h : B) :
    (Localization.awayMap (φ : B →+* A) h).Finite := by
  let := (φ : B →+* A).toAlgebra
  let := (Localization.awayMap (φ : B →+* A) h).toAlgebra
  have : Module.Finite B A := hfin
  have : Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] A) := inferInstance
  exact Module.Finite.equiv (nonflatAwayTensorEquiv (φ : B →+* A) h).toLinearEquiv

omit hh in
/-- The localized map `B_h → A_{φ(h)}` is finite. -/
theorem awayMap_finite (hfin : (φ : B →+* A).Finite) :
    (Localization.awayMap (φ : B →+* A) h).Finite :=
  nonflat_awayMap_finite hfin h

/-- `A_{φ(h)}` is a domain (for `A` a domain and `φ` injective). -/
theorem isDomain_away [IsDomain A] (hinj : Function.Injective φ) :
    IsDomain (Localization.Away ((φ : B →+* A) h)) :=
  IsLocalization.Away.isDomain (x := (φ : B →+* A) h) _
    ((map_ne_zero_iff (φ : B →+* A) hinj).2 hh.ne_zero)

end IsNonflatGoodLocus

end GoodLocus

/-! ### Rigid base change (`lem:nf-rigid-fibre` (1)) -/

section BaseChange

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] (F : Type*) [Field F]
  [Algebra k F] {σ : Type*} {hS : MvPolynomial σ k}

/-- **`B_F = F ⊗_k B ≅ F[x]_{h_S}`** for a presentation `E : B ≅ k[x]_{h_S}`
(`AffineLine.principalOpenTensorEquiv`). -/
def nonflatBaseEquiv (E : B ≃ₐ[k] Localization.Away hS) :
    F ⊗[k] B ≃ₐ[F] Localization.Away (MvPolynomial.map (algebraMap k F) hS) :=
  (Algebra.TensorProduct.congr AlgEquiv.refl E).trans (AffineLine.principalOpenTensorEquiv hS)

/-- `h_S ≠ 0` stays nonzero over `F`. -/
theorem nonflat_map_ne_zero (hS0 : hS ≠ 0) : MvPolynomial.map (algebraMap k F) hS ≠ 0 := by
  intro h0
  apply hS0
  apply MvPolynomial.map_injective _ (algebraMap k F).injective
  rw [h0, map_zero]

variable {F} in
/-- `F[x]_{h_S}` is a domain. -/
theorem nonflat_isDomain_localizationAway_map (hS0 : hS ≠ 0) :
    IsDomain (Localization.Away (MvPolynomial.map (algebraMap k F) hS)) :=
  IsLocalization.Away.isDomain _ (nonflat_map_ne_zero F hS0)

variable {F} in
/-- `F[x]_{h_S}` is integrally closed. -/
theorem nonflat_isIntegrallyClosed_localizationAway_map (hS0 : hS ≠ 0) :
    IsIntegrallyClosed (Localization.Away (MvPolynomial.map (algebraMap k F) hS)) :=
  isIntegrallyClosed_of_isLocalization
    (Localization.Away (MvPolynomial.map (algebraMap k F) hS))
    (Submonoid.powers (MvPolynomial.map (algebraMap k F) hS))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (nonflat_map_ne_zero F hS0))

/-- **`lem:nf-rigid-fibre` (1), the base.** `B_F = F ⊗_k B` is a domain. -/
theorem nonflat_isDomain_baseChange_base {n : ℕ} (hB : IsAffineSpacePrincipalOpen k B n) :
    IsDomain (F ⊗[k] B) := by
  obtain ⟨hS, hS0, ⟨E⟩⟩ := hB
  have := nonflat_isDomain_localizationAway_map (F := F) hS0
  exact Function.Injective.isDomain (nonflatBaseEquiv F E).toRingEquiv
    (nonflatBaseEquiv F E).toRingEquiv.injective

/-- **`lem:nf-rigid-fibre` (1), the base.** `B_F = F ⊗_k B` is integrally closed. -/
theorem nonflat_isIntegrallyClosed_baseChange_base {n : ℕ}
    (hB : IsAffineSpacePrincipalOpen k B n) : IsIntegrallyClosed (F ⊗[k] B) := by
  obtain ⟨hS, hS0, ⟨E⟩⟩ := hB
  have := nonflat_isIntegrallyClosed_localizationAway_map (F := F) hS0
  exact IsIntegrallyClosed.of_equiv (nonflatBaseEquiv F E).symm.toRingEquiv

end BaseChange

/-! ### Characteristic polynomials along an isomorphism of bases -/

/-- **Transport of `χ_b` along an isomorphism of integrally closed bases**: if `e : R ≅ R'` is
compatible with the algebra structures on `T`, then `nonflatCharpoly R' T b` is the image of
`nonflatCharpoly R T b` (the minimal polynomials and the ranks correspond). -/
theorem nonflatCharpoly_map_ringEquiv {R R' T : Type*} [CommRing R] [IsDomain R] [CommRing R']
    [IsDomain R'] [IsIntegrallyClosed R'] [CommRing T] [IsDomain T] [Algebra R T] [Algebra R' T]
    [Algebra.IsIntegral R T] [FaithfulSMul R' T] (e : R ≃+* R')
    (he : ∀ r, algebraMap R' T (e r) = algebraMap R T r) (b : T) :
    (nonflatCharpoly R T b).map (e : R →+* R') = nonflatCharpoly R' T b := by
  have hb : IsIntegral R b := Algebra.IsIntegral.isIntegral b
  have hcomp : (algebraMap R' T).comp (e : R →+* R') = algebraMap R T := RingHom.ext he
  have hcomp' : (algebraMap R T).comp (e.symm : R' →+* R) = algebraMap R' T := by
    ext r
    rw [RingHom.comp_apply, ← he, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  have hb' : IsIntegral R' b := by
    obtain ⟨p, hpm, hp⟩ := hb
    refine ⟨p.map (e : R →+* R'), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hcomp, hp]
  have hmin : (minpoly R b).map (e : R →+* R') = minpoly R' b := by
    refine minpoly.IsIntegrallyClosed.unique_of_degree_le_degree_minpoly ((minpoly.monic hb).map _) ?_ ?_
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def,
        minpoly.aeval]
    · rw [Polynomial.degree_map_eq_of_injective e.injective]
      refine minpoly.min R b ((minpoly.monic hb').map (e.symm : R' →+* R)) ?_ |>.trans ?_
      · rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp', ← Polynomial.aeval_def,
          minpoly.aeval]
      · rw [Polynomial.degree_map_eq_of_injective e.symm.injective]
  have hrank : Module.finrank R T = Module.finrank R' T :=
    Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl T) (by ext r; exact he r)
  rw [nonflatCharpoly_def, nonflatCharpoly_def, Polynomial.map_pow, hmin, hrank,
    ← hmin, (minpoly.monic hb).natDegree_map]

/-! ### Coordinates of the rigid base change -/

section Coordinates

variable {k : Type*} [Field k] {A B : Type*} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  (F : Type*) [Field F] [Algebra k F] {σ : Type*} {hS : MvPolynomial σ k}
  (E : B ≃ₐ[k] Localization.Away hS) (φ : B →ₐ[k] A)

/-- The base change `φ_F : B_F → A_F = F ⊗_k A` in the coordinates `B_F ≅ F[x]_{h_S}`
(`nonflatBaseEquiv`): the map `φ` of the author's line API. -/
def nonflatCoordMap : Localization.Away (MvPolynomial.map (algebraMap k F) hS) →ₐ[F] F ⊗[k] A :=
  (Algebra.TensorProduct.map (AlgHom.id F F) φ).comp (nonflatBaseEquiv F E).symm.toAlgHom

@[simp]
theorem nonflatCoordMap_nonflatBaseEquiv (q : F ⊗[k] B) :
    nonflatCoordMap F E φ (nonflatBaseEquiv F E q) =
      Algebra.TensorProduct.map (AlgHom.id F F) φ q := by
  simp [nonflatCoordMap]

/-- `φ_F` is finite if `φ` is. -/
theorem nonflatCoordMap_finite (hfin : (φ : B →+* A).Finite) :
    (nonflatCoordMap F E φ).toRingHom.Finite :=
  (nonflat_baseChange_finite F φ hfin).comp
    (RingHom.Finite.of_surjective _ (nonflatBaseEquiv F E).symm.surjective)

/-- `φ_F` is injective if `φ` is (`F` is flat over the field `k`). -/
theorem nonflatCoordMap_injective (hinj : Function.Injective φ) :
    Function.Injective (nonflatCoordMap F E φ) := by
  have hm : Function.Injective (Algebra.TensorProduct.map (AlgHom.id F F) φ) :=
    Module.Flat.lTensor_preserves_injective_linearMap φ.toLinearMap hinj
  exact hm.comp (nonflatBaseEquiv F E).symm.injective

/-- **`B_h`-base change in coordinates.** For every algebra `C` over
`B_F = F[x]_{h_S}`, `C ⊗_{B_F} A_F ≅ C ⊗_B A` (`A_F = F ⊗_k A` is the base change of `A` along
`B → B_F`, `ScalarExtension.equiv`). -/
theorem nonflat_nonempty_coord_tensorEquiv (C : Type*) [CommRing C]
    [Algebra (Localization.Away (MvPolynomial.map (algebraMap k F) hS)) C] :
    letI := (nonflatCoordMap F E φ).toRingHom.toAlgebra
    letI := (φ : B →+* A).toAlgebra
    letI : Algebra B C := ((algebraMap (Localization.Away (MvPolynomial.map (algebraMap k F) hS))
      C).comp ((nonflatBaseEquiv F E : F ⊗[k] B →+* _).comp
        Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
    Nonempty (C ⊗[Localization.Away (MvPolynomial.map (algebraMap k F) hS)] (F ⊗[k] A) ≃ₐ[C]
      C ⊗[B] A) := by
  set R₂ := Localization.Away (MvPolynomial.map (algebraMap k F) hS)
  set ψ := nonflatBaseEquiv F E
  let iT₂ : Algebra R₂ (F ⊗[k] A) := (nonflatCoordMap F E φ).toRingHom.toAlgebra
  let : Algebra B A := (φ : B →+* A).toAlgebra
  have : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  let iB₁ : Algebra B (F ⊗[k] B) := Algebra.TensorProduct.rightAlgebra
  let iC₁ : Algebra (F ⊗[k] B) C := ((algebraMap R₂ C).comp (ψ : F ⊗[k] B →+* R₂)).toAlgebra
  let iBC : Algebra B C := ((algebraMap R₂ C).comp ((ψ : F ⊗[k] B →+* R₂).comp
    Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
  let iT₁ : Algebra (F ⊗[k] B) (F ⊗[k] A) := ScalarExtension.algebra k F B A
  have : IsScalarTower B (F ⊗[k] B) C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hT : ∀ r : F ⊗[k] B, algebraMap R₂ (F ⊗[k] A) (ψ r) = algebraMap (F ⊗[k] B) (F ⊗[k] A) r :=
    fun r => nonflatCoordMap_nonflatBaseEquiv F E φ r
  have hC : ∀ (r : F ⊗[k] B) (c : C), ψ r • c = r • c := fun r c => by
    rw [Algebra.smul_def, Algebra.smul_def]
    rfl
  have hT' : ∀ (r : F ⊗[k] B) (t : F ⊗[k] A), ψ r • t = r • t := fun r t => by
    rw [Algebra.smul_def, Algebra.smul_def, hT]
  have : TensorProduct.CompatibleSMul (F ⊗[k] B) R₂ C (F ⊗[k] A) := ⟨fun r₂ c t => by
    obtain ⟨r, rfl⟩ := ψ.surjective r₂
    rw [hC, hT', TensorProduct.smul_tmul]⟩
  have : TensorProduct.CompatibleSMul R₂ (F ⊗[k] B) C (F ⊗[k] A) := ⟨fun r c t => by
    rw [← hC, ← hT', TensorProduct.smul_tmul]⟩
  have : SMulCommClass (F ⊗[k] B) R₂ C := ⟨fun r r₂ c => by
    rw [← hC, smul_comm, hC]⟩
  let e₀ : (F ⊗[k] B) ⊗[B] A ≃ₐ[F ⊗[k] B] F ⊗[k] A := ScalarExtension.equiv k F B A
  let e₂ : C ⊗[F ⊗[k] B] ((F ⊗[k] B) ⊗[B] A) ≃ₐ[C] C ⊗[B] A :=
    Algebra.TensorProduct.cancelBaseChange B (F ⊗[k] B) C C A
  let e₃ : C ⊗[F ⊗[k] B] (F ⊗[k] A) ≃ₐ[C] C ⊗[F ⊗[k] B] ((F ⊗[k] B) ⊗[B] A) :=
    Algebra.TensorProduct.congr AlgEquiv.refl e₀.symm
  let e₄ : C ⊗[R₂] (F ⊗[k] A) ≃ₐ[C] C ⊗[F ⊗[k] B] (F ⊗[k] A) :=
    Algebra.TensorProduct.equivOfCompatibleSMul (F ⊗[k] B) R₂ C C (F ⊗[k] A)
  exact ⟨e₄.trans (e₃.trans e₂)⟩

variable {F E φ}

/-- **The good locus in coordinates**: for `h_F = ψ(1 ⊗ h) ∈ B_F = F[x]_{h_S}`, the algebra
`(B_F)_{h_F} ⊗_{B_F} A_F` is étale over `(B_F)_{h_F}` (the hypothesis `het` of the author's line
API and of `AffineLine.nonflatLine_lineWeights`). -/
theorem IsNonflatGoodLocus.coord_etale {S : Finset A} {h : B} (hh : IsNonflatGoodLocus φ S h) :
    letI := (nonflatCoordMap F E φ).toRingHom.toAlgebra
    Algebra.Etale (Localization.Away (nonflatBaseEquiv F E (1 ⊗ₜ h)))
      (Localization.Away (nonflatBaseEquiv F E (1 ⊗ₜ h)) ⊗[Localization.Away
        (MvPolynomial.map (algebraMap k F) hS)] (F ⊗[k] A)) := by
  set C := Localization.Away (nonflatBaseEquiv F E (1 ⊗ₜ h))
  obtain ⟨e⟩ := nonflat_nonempty_coord_tensorEquiv F E φ C
  let := (nonflatCoordMap F E φ).toRingHom.toAlgebra
  let := (φ : B →+* A).toAlgebra
  let : Algebra B C := ((algebraMap (Localization.Away (MvPolynomial.map (algebraMap k F) hS))
      C).comp ((nonflatBaseEquiv F E : F ⊗[k] B →+* _).comp
        Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
  have := hh.etale_tensor C
    (by exact IsLocalization.Away.algebraMap_isUnit (nonflatBaseEquiv F E ((1 : F) ⊗ₜ[k] h)))
  exact Algebra.Etale.of_equiv e.symm

/-- **The good locus in coordinates**: `(B_F)_{h_F} ⊗_{B_F} A_F` is free over `(B_F)_{h_F}` (the
hypothesis `hfree` of `AffineLine.nonflatLine_lineWeights`). -/
theorem IsNonflatGoodLocus.coord_free {S : Finset A} {h : B} (hh : IsNonflatGoodLocus φ S h) :
    letI := (nonflatCoordMap F E φ).toRingHom.toAlgebra
    Module.Free (Localization.Away (nonflatBaseEquiv F E (1 ⊗ₜ h)))
      (Localization.Away (nonflatBaseEquiv F E (1 ⊗ₜ h)) ⊗[Localization.Away
        (MvPolynomial.map (algebraMap k F) hS)] (F ⊗[k] A)) := by
  set C := Localization.Away (nonflatBaseEquiv F E (1 ⊗ₜ h))
  obtain ⟨e⟩ := nonflat_nonempty_coord_tensorEquiv F E φ C
  let := (nonflatCoordMap F E φ).toRingHom.toAlgebra
  let := (φ : B →+* A).toAlgebra
  let : Algebra B C := ((algebraMap (Localization.Away (MvPolynomial.map (algebraMap k F) hS))
      C).comp ((nonflatBaseEquiv F E : F ⊗[k] B →+* _).comp
        Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
  have := hh.free_tensor C
    (by exact IsLocalization.Away.algebraMap_isUnit (nonflatBaseEquiv F E ((1 : F) ⊗ₜ[k] h)))
  exact Module.Free.of_equiv e.symm.toLinearEquiv

/-- `h_F = ψ(1 ⊗ h) ≠ 0` for `h ≠ 0`. -/
theorem nonflatBaseEquiv_one_tmul_ne_zero {h : B} (hh : h ≠ 0) :
    nonflatBaseEquiv F E ((1 : F) ⊗ₜ[k] h) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (nonflatBaseEquiv F E).injective]
  intro h0
  apply hh
  apply Algebra.TensorProduct.includeRight_injective (A := F) (algebraMap k F).injective
  rw [Algebra.TensorProduct.includeRight_apply, h0, map_zero]

/-- **The degree in coordinates** (`lem:nf-rigid-fibre` (1)): `rank_{B_F} A_F = d` for
`B_F = F[x]_{h_S}` acting on `A_F = F ⊗_k A` through `φ_F`. By base change from the free
localization `B_h ⊗_B A` of rank `d`: `(B_F)_{h_F} ⊗_{B_F} A_F ≅ (B_F)_{h_F} ⊗_B A`. -/
theorem IsNonflatGoodLocus.finrank_coord [IsDomain B] (hS0 : hS ≠ 0) {S : Finset A} {h : B}
    (hh : IsNonflatGoodLocus φ S h) :
    letI := (nonflatCoordMap F E φ).toRingHom.toAlgebra
    Module.finrank (Localization.Away (MvPolynomial.map (algebraMap k F) hS)) (F ⊗[k] A) =
      genericDegree (φ : B →+* A) := by
  set C := Localization.Away (nonflatBaseEquiv F E (1 ⊗ₜ h))
  obtain ⟨e⟩ := nonflat_nonempty_coord_tensorEquiv F E φ C
  let := (nonflatCoordMap F E φ).toRingHom.toAlgebra
  let := (φ : B →+* A).toAlgebra
  let : Algebra B C := ((algebraMap (Localization.Away (MvPolynomial.map (algebraMap k F) hS))
      C).comp ((nonflatBaseEquiv F E : F ⊗[k] B →+* _).comp
        Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
  have := nonflat_isDomain_localizationAway_map (F := F) hS0
  have hh0 := nonflatBaseEquiv_one_tmul_ne_zero (F := F) (E := E) hh.ne_zero
  have : IsDomain C := IsLocalization.Away.isDomain C hh0
  rw [← nonflat_finrank_localizationAway_tensor hh0 C, e.toLinearEquiv.finrank_eq]
  exact hh.finrank_tensor C
    (by exact IsLocalization.Away.algebraMap_isUnit (nonflatBaseEquiv F E ((1 : F) ⊗ₜ[k] h)))

end Coordinates

/-- **`lem:nf-rigid-fibre` (1), the degree.** For a field `F ⊇ k` and a good locus `h`, the rank of
`A_F = F ⊗_k A` over `B_F = F ⊗_k B` (through `F ⊗ φ`) is the degree `d` of `π`; equivalently
`dim_{Frac B_F} (Frac B_F ⊗_{B_F} A_F) = d` (`nonflat_finrank_fractionRing_tensor`). -/
theorem IsNonflatGoodLocus.finrank_baseChange {k : Type*} [Field k] {A B : Type*} [CommRing A]
    [Algebra k A] [CommRing B] [Algebra k B] (F : Type*) [Field F] [Algebra k F] {n : ℕ}
    (hB : IsAffineSpacePrincipalOpen k B n) {φ : B →ₐ[k] A} {S : Finset A} {h : B}
    (hh : IsNonflatGoodLocus φ S h) :
    letI := (Algebra.TensorProduct.map (AlgHom.id F F) φ).toRingHom.toAlgebra
    Module.finrank (F ⊗[k] B) (F ⊗[k] A) = genericDegree (φ : B →+* A) := by
  have := hB.isDomain
  obtain ⟨hS, hS0, ⟨E⟩⟩ := hB
  let := (Algebra.TensorProduct.map (AlgHom.id F F) φ).toRingHom.toAlgebra
  let := (nonflatCoordMap F E φ).toRingHom.toAlgebra
  rw [← hh.finrank_coord (F := F) (E := E) hS0]
  exact Algebra.finrank_eq_of_equiv_equiv (nonflatBaseEquiv F E).toRingEquiv (RingEquiv.refl _)
    (RingHom.ext fun r => nonflatCoordMap_nonflatBaseEquiv F E φ r)

/-! ### Lines through a rigid point (`lem:nf-line-exists`) -/

section Lines

open AffineLine

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {F : Type*} [Field F]
  [Algebra k F] {σ : Type*} {hS : MvPolynomial σ k} (E : B ≃ₐ[k] Localization.Away hS)
  (ξ : F ⊗[k] B →ₐ[F] F)

/-- The coordinates `a = (ξ(x_i))_i ∈ F^σ` of an `F`-point `ξ` of `B_F ≅ F[x]_{h_S}`
(`def:nf-line`: `ξ` is the point `a ∈ F^n`, `h_S(a) ≠ 0`). -/
def nonflatLinePoint : σ → F := fun i =>
  ξ ((nonflatBaseEquiv F E).symm (algebraMap (MvPolynomial σ F) _ (MvPolynomial.X i)))

/-- `ξ` on polynomials is evaluation at `a`. -/
theorem nonflat_eval_linePoint (q : MvPolynomial σ F) :
    ξ ((nonflatBaseEquiv F E).symm (algebraMap (MvPolynomial σ F)
        (Localization.Away (MvPolynomial.map (algebraMap k F) hS)) q)) =
      MvPolynomial.eval (nonflatLinePoint E ξ) q := by
  have h := MvPolynomial.algHom_ext (A := F)
    (f := (ξ.comp (nonflatBaseEquiv F E).symm.toAlgHom).comp
      (IsScalarTower.toAlgHom F (MvPolynomial σ F)
        (Localization.Away (MvPolynomial.map (algebraMap k F) hS))))
    (g := MvPolynomial.aeval (nonflatLinePoint E ξ)) fun i => by
      simp [nonflatLinePoint]
  have := congrArg (fun f => f q) h
  simpa [MvPolynomial.coe_aeval_eq_eval] using this

/-- `h_S(a) ≠ 0`: the coordinates of `ξ` lie in the principal open. -/
theorem nonflat_linePoint_eval_ne_zero :
    MvPolynomial.eval (nonflatLinePoint E ξ) (MvPolynomial.map (algebraMap k F) hS) ≠ 0 := by
  rw [← nonflat_eval_linePoint]
  exact ((IsLocalization.Away.algebraMap_isUnit _).map
    ((ξ.comp (nonflatBaseEquiv F E).symm.toAlgHom))).ne_zero

/-- `p(0) = h_S(a) ≠ 0` for the line `t ↦ a + t w`, `p(t) = h_S(a + t w)`. -/
theorem nonflat_eval_subst_zero_ne_zero (w : σ → F) :
    (subst (nonflatLinePoint E ξ) w (MvPolynomial.map (algebraMap k F) hS)).eval 0 ≠ 0 := by
  rw [eval_subst_zero]
  exact nonflat_linePoint_eval_ne_zero E ξ

/-- **The line passes through `ξ`** (`def:nf-line`): composing `ι : B_F → Q` with the evaluation
at `t = 0` gives `ξ` (in coordinates). -/
theorem nonflat_lineEval_comp (w : σ → F) :
    (openLineEval (subst (nonflatLinePoint E ξ) w (MvPolynomial.map (algebraMap k F) hS)) 0
        (nonflat_eval_subst_zero_ne_zero E ξ w)).comp
      (principalLineHom (nonflatLinePoint E ξ) w (MvPolynomial.map (algebraMap k F) hS)) =
      ξ.comp (nonflatBaseEquiv F E).symm.toAlgHom := by
  apply IsLocalization.algHom_ext (Submonoid.powers (MvPolynomial.map (algebraMap k F) hS))
  apply AlgHom.ext
  intro q
  change openLineEval _ 0 (nonflat_eval_subst_zero_ne_zero E ξ w)
      (principalLineHom _ w _ (algebraMap _ _ q)) =
    ξ ((nonflatBaseEquiv F E).symm (algebraMap _ _ q))
  rw [principalLineHom_algebraMap, openLineEval_algebraMap, eval_subst_zero,
    nonflat_eval_linePoint]

/-- **`lem:nf-line-exists`.** For every `0 ≠ e ∈ B` there is a direction `w ≠ 0` admissible for `e`:
`ι(e) ≠ 0` in `Q = F[t]_p`, where `ι = principalLineHom a w g` is the restriction to the line
`t ↦ a + t w` through `ξ`, `g = h_S` over `F`, and `e` is viewed in `B_F` as `ψ(1 ⊗ e)`. -/
theorem nonflat_exists_admissible_direction [Infinite F] [Nonempty σ] {e : B} (he : e ≠ 0) :
    ∃ w : σ → F, w ≠ 0 ∧
      subst (nonflatLinePoint E ξ) w (MvPolynomial.map (algebraMap k F) hS) ≠ 0 ∧
      principalLineHom (nonflatLinePoint E ξ) w (MvPolynomial.map (algebraMap k F) hS)
        (nonflatBaseEquiv F E ((1 : F) ⊗ₜ[k] e)) ≠ 0 :=
  exists_principal_open_line_localized _ (nonflat_linePoint_eval_ne_zero E ξ) _
    (nonflatBaseEquiv_one_tmul_ne_zero he)

/-- A direction admissible for a product `e₁ e₂` is admissible for both factors (`def:nf-line`;
e.g. a direction admissible for `h e_u` in `prop:nf-identification` is admissible for `h`). -/
theorem nonflat_admissible_of_mul (w : σ → F) {e₁ e₂ : B}
    (he : principalLineHom (nonflatLinePoint E ξ) w (MvPolynomial.map (algebraMap k F) hS)
      (nonflatBaseEquiv F E ((1 : F) ⊗ₜ[k] (e₁ * e₂))) ≠ 0) :
    principalLineHom (nonflatLinePoint E ξ) w (MvPolynomial.map (algebraMap k F) hS)
        (nonflatBaseEquiv F E ((1 : F) ⊗ₜ[k] e₁)) ≠ 0 ∧
      principalLineHom (nonflatLinePoint E ξ) w (MvPolynomial.map (algebraMap k F) hS)
        (nonflatBaseEquiv F E ((1 : F) ⊗ₜ[k] e₂)) ≠ 0 := by
  rw [← one_mul (1 : F), ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, map_mul] at he
  exact ⟨left_ne_zero_of_mul he, right_ne_zero_of_mul he⟩

end Lines

end EnvelopeProperty
