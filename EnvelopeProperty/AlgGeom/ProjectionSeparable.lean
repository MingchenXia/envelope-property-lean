/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Localization.Integral
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import EnvelopeProperty.AlgGeom.ProjectionCotangent
import EnvelopeProperty.AlgGeom.EtaleLocalization

/-!
# Generic étaleness of the projection

This file proves the generic étaleness part of the affine proof of Fang–Han–Xia, *The envelope
property for unibranch projective varieties*, Lemma 5.23 (`lem:projection-existence`), which FHX
add to Wu's Lemma 6.16 ("generically étale, which is needed in positive characteristic").

For the coordinates `yᵢ = tᵢ ^ fᵢ - aᵢ` of the projection, the characteristic divides `fᵢ`, so
`d yᵢ = - d aᵢ` in `Ω[L⁄k]` (`L = Frac A`); and the `aᵢ` are only prescribed modulo the ideal `I`
of `Z`. Since the differentials of `I ≠ 0` span `Ω[L⁄k]` (`span_D_image_ideal_eq_top`), the `aᵢ`
can be perturbed by elements of `I` so that their differentials span `Ω[L⁄k]`
(`exists_forall_mem_spanOrIndep`, `exists_mem_spanOrIndep_cons`, `span_eq_top_of_spanOrIndep`,
using that `Ω[L⁄k]` has dimension `trdeg L = n`, `k` perfect). Then:

* `formallyUnramified_of_span_D`, `formallyEtale_of_span_D`: `Ω[L⁄K] = 0` for `K = k(y)`, so the
  finite extension `L / K` is separable (in characteristic zero this is automatic);
* `exists_ne_zero_etale_awayMap`: a finite injective `B → A` of domains, generically separable, is
  étale over some `D(h)`, `h ≠ 0` (openness of the étale locus,
  `Algebra.exists_etale_of_isEtaleAt`).
-/

namespace EnvelopeProperty

open KaehlerDifferential

section span

variable {k A L : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Field L] [Algebra A L]
  [IsFractionRing A L] [Algebra k L] [IsScalarTower k A L]

/-- The differentials of the elements of a nonzero ideal `I` of `A` span `Ω[L⁄k]`, `L = Frac A`:
`ι d a = d(ι a) - a d ι` for `ι ∈ I`. -/
theorem span_D_image_ideal_eq_top (I : Ideal A) (hI : I ≠ ⊥) :
    Submodule.span L ((fun a => D k L (algebraMap A L a)) '' I) = ⊤ := by
  set V := Submodule.span L ((fun a => D k L (algebraMap A L a)) '' I)
  obtain ⟨ι₀, hι₀, hι₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hι₀L : algebraMap A L ι₀ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr hι₀0
  have hmemI : ∀ a ∈ I, D k L (algebraMap A L a) ∈ V := fun a ha =>
    Submodule.subset_span ⟨a, ha, rfl⟩
  have hA : ∀ a : A, D k L (algebraMap A L a) ∈ V := fun a => by
    have h1 := hmemI (ι₀ * a) (I.mul_mem_right a hι₀)
    rw [map_mul, Derivation.leibniz] at h1
    have h2 : algebraMap A L ι₀ • D k L (algebraMap A L a) ∈ V := by
      have := V.sub_mem h1 (V.smul_mem (algebraMap A L a) (hmemI ι₀ hι₀))
      simpa using this
    have := V.smul_mem (algebraMap A L ι₀)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hι₀L, one_smul] at this
  have hL : ∀ q : L, D k L q ∈ V := fun q => by
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) q
    have hs : algebraMap A L s ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr (nonZeroDivisors.ne_zero s.2)
    have hspec := IsLocalization.mk'_spec L a s
    have h1 : algebraMap A L s • D k L (IsLocalization.mk' L a s) ∈ V := by
      have h3 := congrArg (D k L) hspec
      rw [Derivation.leibniz] at h3
      have : algebraMap A L s • D k L (IsLocalization.mk' L a s) =
          D k L (algebraMap A L a) - IsLocalization.mk' L a s • D k L (algebraMap A L s) := by
        rw [← h3]; abel
      rw [this]
      exact V.sub_mem (hA a) (V.smul_mem _ (hA s))
    have := V.smul_mem (algebraMap A L s)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hs, one_smul] at this
  rw [eq_top_iff, ← span_range_derivation k L, Submodule.span_le]
  rintro _ ⟨q, rfl⟩
  exact hL q

/-- **The fraction field of an integral extension is algebraic over the coordinates.** If the domain
`A` is integral over `k[x₁, …, xₘ]`, then `L = Frac A` is algebraic over the subalgebra generated
by the images of the `xᵢ`. -/
theorem isAlgebraic_adjoin_range_fractionRing {m : ℕ} (x : Fin m → A)
    (hx : ∀ r : A, IsIntegral (Algebra.adjoin k (Set.range x)) r) :
    Algebra.IsAlgebraic (Algebra.adjoin k (Set.range fun i => algebraMap A L (x i))) L := by
  set F := Algebra.adjoin k (Set.range fun i => algebraMap A L (x i))
  have hmem : ∀ y ∈ Algebra.adjoin k (Set.range x), algebraMap A L y ∈ F := fun y hy => by
    have : (Algebra.adjoin k (Set.range x)).map (IsScalarTower.toAlgHom k A L) = F := by
      rw [AlgHom.map_adjoin, ← Set.range_comp]; rfl
    rw [← this]; exact Subalgebra.mem_map.mpr ⟨y, hy, rfl⟩
  let φ : Algebra.adjoin k (Set.range x) →+* F :=
    ((algebraMap A L).comp (algebraMap (Algebra.adjoin k (Set.range x)) A)).codRestrict F
      (fun y => hmem y y.2)
  have hint : ∀ a : A, IsAlgebraic F (algebraMap A L a) := fun a =>
    (IsIntegral.map_of_comp_eq φ (algebraMap A L) (RingHom.ext fun _ => rfl) (hx a)).isAlgebraic
  refine ⟨fun q => ?_⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) q
  have hs : algebraMap A L s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr (nonZeroDivisors.ne_zero s.2)
  change IsAlgebraic F (IsLocalization.mk' L a s)
  rw [show IsLocalization.mk' L a s = algebraMap A L a * (algebraMap A L s)⁻¹ by
    rw [eq_mul_inv_iff_mul_eq₀ hs]; exact IsLocalization.mk'_spec L a s]
  exact (hint a).mul (hint s).inv

end span

section linear

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The property maintained by the choice of the perturbations: the family spans, or is linearly
independent. -/
def SpanOrIndep {n : ℕ} (v : Fin n → M) : Prop :=
  Submodule.span K (Set.range v) = ⊤ ∨ LinearIndependent K v

/-- One step of the choice: given `v` with `SpanOrIndep`, a vector `w` and a set `E` spanning `M`
and containing `0`, some `w + e`, `e ∈ E`, can be put in front of `v` keeping `SpanOrIndep`. -/
theorem exists_spanOrIndep_cons {n : ℕ} (v : Fin n → M) (hv : SpanOrIndep (K := K) v) (w : M)
    (E : Set M) (hE0 : (0 : M) ∈ E) (hE : Submodule.span K E = ⊤) :
    ∃ e ∈ E, SpanOrIndep (K := K) (Fin.cons (w + e) v : Fin (n + 1) → M) := by
  by_cases htop : Submodule.span K (Set.range v) = ⊤
  · refine ⟨0, hE0, Or.inl (eq_top_iff.mpr (htop ▸ Submodule.span_mono ?_))⟩
    rw [Fin.range_cons]; exact Set.subset_insert _ _
  · have hli := hv.resolve_left htop
    by_cases hw : w ∈ Submodule.span K (Set.range v)
    · -- some `e ∈ E` lies outside the span
      have : ¬ E ⊆ Submodule.span K (Set.range v) := fun h =>
        htop (eq_top_iff.mpr (hE ▸ Submodule.span_le.mpr h))
      obtain ⟨e, heE, he⟩ := Set.not_subset.mp this
      refine ⟨e, heE, Or.inr (linearIndependent_finCons.mpr ⟨hli, fun h => he ?_⟩)⟩
      simpa using Submodule.sub_mem _ h hw
    · exact ⟨0, hE0, Or.inr (linearIndependent_finCons.mpr ⟨hli, by simpa using hw⟩)⟩

/-- A family with `SpanOrIndep` of length at least the dimension spans. -/
theorem span_eq_top_of_spanOrIndep [FiniteDimensional K M] {n : ℕ} (v : Fin n → M)
    (hv : SpanOrIndep (K := K) v) (hn : Module.finrank K M ≤ n) :
    Submodule.span K (Set.range v) = ⊤ := by
  rcases hv with h | h
  · exact h
  · have := h.fintype_card_le_finrank
    rw [Fintype.card_fin] at this
    exact h.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin]; omega)

end linear

section choice

variable {k A L : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Field L] [Algebra A L]
  [IsFractionRing A L] [Algebra k L] [IsScalarTower k A L]

/-- **Perturbing by elements of `I` to make differentials independent, one step.** -/
theorem exists_mem_spanOrIndep_cons (I : Ideal A) (hI : I ≠ ⊥) {m : ℕ} (v : Fin m → Ω[L⁄k])
    (hv : SpanOrIndep (K := L) v) (a : A) :
    ∃ ι ∈ I, SpanOrIndep (K := L)
      (Fin.cons (D k L (algebraMap A L (a + ι))) v : Fin (m + 1) → Ω[L⁄k]) := by
  obtain ⟨e, ⟨ι, hι, rfl⟩, he⟩ := exists_spanOrIndep_cons v hv (D k L (algebraMap A L a))
    ((fun a => D k L (algebraMap A L a)) '' I) ⟨0, I.zero_mem, by simp⟩
    (span_D_image_ideal_eq_top I hI)
  exact ⟨ι, hι, by simpa [map_add] using he⟩

/-- **Perturbing by elements of `I` to make differentials independent.** For `b₁, …, bₘ ∈ A` there
are `ι₁, …, ιₘ ∈ I` such that the differentials `d(bᵢ + ιᵢ)` in `Ω[L⁄k]` span or are linearly
independent. -/
theorem exists_forall_mem_spanOrIndep (I : Ideal A) (hI : I ≠ ⊥) {m : ℕ} (b : Fin m → A) :
    ∃ ι : Fin m → A, (∀ i, ι i ∈ I) ∧
      SpanOrIndep (K := L) (fun i => D k L (algebraMap A L (b i + ι i))) := by
  induction m with
  | zero => exact ⟨fun _ => 0, fun _ => I.zero_mem, Or.inr (linearIndependent_empty_type)⟩
  | succ m ih =>
    obtain ⟨ι', hι', hv⟩ := ih (Fin.tail b)
    obtain ⟨ι₀, hι₀, h⟩ := exists_mem_spanOrIndep_cons I hI _ hv (b 0)
    refine ⟨Fin.cons ι₀ ι', fun i => ?_, ?_⟩
    · cases i using Fin.cases with
      | zero => simpa using hι₀
      | succ j => simpa using hι' j
    · convert h using 1
      funext i
      cases i using Fin.cases with
      | zero => simp
      | succ j => simp [Fin.tail]

end choice

section unramified

/-- If the differentials of elements of `K` span `Ω[L⁄k]`, then `Ω[L⁄K] = 0`: `L` is formally
unramified over `K`. -/
theorem formallyUnramified_of_span_D (k K L : Type*) [Field k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] (S : Set K)
    (hS : Submodule.span L ((fun y => D k L (algebraMap K L y)) '' S) = ⊤) :
    Algebra.FormallyUnramified K L := by
  constructor
  have hrange : LinearMap.range (KaehlerDifferential.map k K L L) = ⊥ := by
    rw [LinearMap.range_eq_map, ← hS, Submodule.map_span, Submodule.span_eq_bot]
    rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    simp [map_D]
  have hsurj := KaehlerDifferential.map_surjective k K L
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := hsurj a
  obtain ⟨b, rfl⟩ := hsurj b
  have ha : KaehlerDifferential.map k K L L a ∈ LinearMap.range (KaehlerDifferential.map k K L L) :=
    ⟨a, rfl⟩
  have hb : KaehlerDifferential.map k K L L b ∈ LinearMap.range (KaehlerDifferential.map k K L L) :=
    ⟨b, rfl⟩
  rw [hrange, Submodule.mem_bot] at ha hb
  rw [ha, hb]

end unramified

section etale

/-- **Generic étaleness of a finite map.** Let `φ : B → A` be a finite injective map of domains,
`B` noetherian, such that `Frac A` is formally étale (i.e. finite separable) over `Frac B`. Then
`B_h → A_{φ h}` is étale for some `h ≠ 0`.

`A` is étale over `B` at its generic point, hence on a principal open `D(f)`, `f ≠ 0`
(`Algebra.exists_etale_of_isEtaleAt`, openness of the étale locus); `D(φ h) ⊆ D(f)` for a nonzero
`h ∈ B ∩ f A` (`Ideal.comap_ne_bot_of_integral_mem`). -/
theorem exists_ne_zero_etale_awayMap {B A : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [CommRing A] [IsDomain A] (φ : B →+* A) (hfin : φ.Finite)
    (K L : Type*) [Field K] [Field L] [Algebra B K] [IsFractionRing B K] [Algebra A L]
    [IsFractionRing A L] [Algebra K L]
    (hKL : ∀ b, algebraMap K L (algebraMap B K b) = algebraMap A L (φ b))
    [Algebra.FormallyEtale K L] :
    ∃ h : B, h ≠ 0 ∧ (Localization.awayMap φ h).Etale := by
  algebraize [φ]
  let : Algebra B L := ((algebraMap A L).comp φ).toAlgebra
  have : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower B K L := IsScalarTower.of_algebraMap_eq fun b => (hKL b).symm
  have : Algebra.FormallyEtale B K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  have : Algebra.FormallyEtale B L := Algebra.FormallyEtale.comp B K L
  -- `L` is the localization of `A` at the prime `0`
  have hcompl : (⊥ : Ideal A).primeCompl = nonZeroDivisors A := by
    ext x; simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  have : IsLocalization (⊥ : Ideal A).primeCompl L := by rw [hcompl]; infer_instance
  let e : Localization.AtPrime (⊥ : Ideal A) ≃ₐ[A] L :=
    IsLocalization.algEquiv (⊥ : Ideal A).primeCompl _ L
  have : Algebra.IsEtaleAt B (⊥ : Ideal A) :=
    Algebra.FormallyEtale.of_equiv (e.restrictScalars B).symm
  have : Module.Finite B A := hfin
  have : Algebra.FinitePresentation B A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨f, hf0, hfet⟩ := Algebra.exists_etale_of_isEtaleAt (R := B) (⊥ : Ideal A)
  have hf0' : f ≠ 0 := by simpa using hf0
  have hcomap : (Ideal.span {f}).comap (algebraMap B A) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hf0' (Ideal.mem_span_singleton_self f)
      (Algebra.IsIntegral.isIntegral f)
  obtain ⟨h, hh, hh0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcomap
  refine ⟨h, hh0, ?_⟩
  -- `A_{φ h}` is étale over `B`
  have hsub : ↑(PrimeSpectrum.basicOpen (φ h)) ⊆ Algebra.etaleLocus B A := by
    refine subset_trans ?_ (Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr hfet)
    intro p hp
    simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hp ⊢
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hh)
    exact fun hfp => hp (hc ▸ p.asIdeal.mul_mem_left c hfp)
  have hAh : Algebra.Etale B (Localization.Away (φ h)) :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.mp hsub
  -- localize the base
  let ψ := Localization.awayMap φ h
  let := ψ.toAlgebra
  have hψ : ∀ b : B, ψ (algebraMap B (Localization.Away h) b) =
      algebraMap A (Localization.Away (φ h)) (φ b) := fun b =>
    away_map_algebraMap φ h _ _ b
  have : IsScalarTower B (Localization.Away h) (Localization.Away (φ h)) :=
    IsScalarTower.of_algebraMap_eq fun b => by
      rw [IsScalarTower.algebraMap_apply B A (Localization.Away (φ h))]
      exact (hψ b).symm
  have : Algebra.FormallyEtale (Localization.Away h) (Localization.Away (φ h)) :=
    Algebra.FormallyEtale.localization_base (Submonoid.powers h)
  have : Algebra.FinitePresentation (Localization.Away h) (Localization.Away (φ h)) := by
    have h₃ : Algebra.FiniteType B (Localization.Away h) :=
      have := IsLocalization.Away.finitePresentation (R := B) (S := Localization.Away h) h
      .of_finitePresentation
    have : (ψ.comp (algebraMap B (Localization.Away h))).FinitePresentation := by
      rw [show ψ.comp (algebraMap B (Localization.Away h)) =
          algebraMap B (Localization.Away (φ h)) from
        RingHom.ext fun b => by
          rw [RingHom.comp_apply, hψ, IsScalarTower.algebraMap_apply B A (Localization.Away (φ h))]
          rfl]
      exact RingHom.finitePresentation_algebraMap.mpr inferInstance
    exact RingHom.FinitePresentation.of_comp_finiteType (algebraMap B (Localization.Away h)) this
      (RingHom.finiteType_algebraMap.mpr h₃)
  exact Algebra.Etale.mk

/-- **Generic separability.** Let `φ : B → A` be a finite map of domains, `K = Frac B`,
`L = Frac A`, everything over a field `k`. If `k` has characteristic zero, or if the differentials
of the `φ b`, `b ∈ S`, span `Ω[L⁄k]`, then `L` is formally étale (finite separable) over `K`. -/
theorem formallyEtale_of_span_D (k : Type*) [Field k] {B A K L : Type*} [CommRing B] [IsDomain B]
    [CommRing A] [IsDomain A] [Field K] [Field L] [Algebra B K] [IsFractionRing B K] [Algebra A L]
    [IsFractionRing A L] [Algebra K L] [Algebra k K] [Algebra k L] [IsScalarTower k K L]
    (φ : B →+* A) (hfin : φ.Finite)
    (hKL : ∀ b, algebraMap K L (algebraMap B K b) = algebraMap A L (φ b)) (S : Set B)
    (hsep : CharZero k ∨
      Submodule.span L ((fun b => KaehlerDifferential.D k L (algebraMap A L (φ b))) '' S) = ⊤) :
    Algebra.FormallyEtale K L := by
  algebraize [φ]
  let : Algebra B L := ((algebraMap A L).comp φ).toAlgebra
  have : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower B K L := IsScalarTower.of_algebraMap_eq fun b => (hKL b).symm
  have : Module.Finite B A := hfin
  have : Algebra.EssFiniteType A L := .of_isLocalization L (nonZeroDivisors A)
  have : Algebra.EssFiniteType B L := .comp B A L
  have : Algebra.EssFiniteType K L := .of_comp B K L
  rcases hsep with h0 | hspan
  · have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    have hB : Algebra.IsAlgebraic B L := ⟨fun q => by
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) q
      have hs : algebraMap A L s ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr (nonZeroDivisors.ne_zero s.2)
      have hint : ∀ x : A, IsAlgebraic B (algebraMap A L x) := fun x =>
        ((Algebra.IsIntegral.isIntegral x).map (IsScalarTower.toAlgHom B A L)).isAlgebraic
      change IsAlgebraic B (IsLocalization.mk' L a s)
      rw [show IsLocalization.mk' L a s = algebraMap A L a * (algebraMap A L s)⁻¹ by
        rw [eq_mul_inv_iff_mul_eq₀ hs]; exact IsLocalization.mk'_spec L a s]
      exact (hint a).mul (hint s).inv⟩
    have : Algebra.IsAlgebraic K L := (IsFractionRing.comap_isAlgebraic_iff (A := B)).mp hB
    exact Algebra.FormallyEtale.of_isSeparable K L
  · have : Algebra.FormallyUnramified K L := by
      refine formallyUnramified_of_span_D k K L (algebraMap B K '' S) ?_
      rw [← hspan, Set.image_image]
      simp_rw [hKL]
    exact Algebra.FormallyEtale.of_formallyUnramified_of_field K L

end etale

end EnvelopeProperty
