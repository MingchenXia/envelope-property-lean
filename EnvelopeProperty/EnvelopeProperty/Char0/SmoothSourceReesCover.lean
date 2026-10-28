/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.LeafJacobianCoordinates
import EnvelopeProperty.Char0.FinitePrincipalRefinement
import EnvelopeProperty.Char0.SNCCharts
import Hironaka.Scheme.Snc.EmptyFamily
import Hironaka.Resolution.Algebraic.Kol07.Thm36.RelativeDimensionConstancy

/-!
# Actual source etale coordinates on finite principal Rees refinements

The actual smooth source produces its own finite source-coordinate cover,
while every literal chart retains the original subalgebra inclusion.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory
open scoped Classical

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- A literal unit-generating Rees chart is the actual principal localization under its
original inclusion algebra map. -/
theorem isLocalization_principalReesChart (C : Subalgebra k K) {m : ℕ}
    (g : Fin m → C) (hg : Ideal.span (Set.range g) = ⊤) (i : Fin m) (hi : g i ≠ 0) :
    letI : Algebra C (reesTreeChart C g i) := (reesTreeChartIncl C g i).toAlgebra
    IsLocalization.Away (g i) (reesTreeChart C g i) := by
  let _ : Algebra C (reesTreeChart C g i) := (reesTreeChartIncl C g i).toAlgebra
  let e : Localization.Away (g i) ≃ₐ[C] reesTreeChart C g i :=
    { principalCoverLocalizationEquiv C g hg i hi with
      commutes' := principalCoverLocalizationEquiv_algebraMap C g hg i hi }
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (g i)) e

/-- Actual smooth source geometry constructs a finite unit Rees cover whose literal chart
rings have actual etale image coordinates, without any global source-coordinate input. -/
theorem exists_smooth_source_principal_rees_etale_cover [PerfectField k]
    (C : Subalgebra k K) (n : ℕ)
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap k C)))] :
    ∃ (m : ℕ) (g : Fin m → C), Ideal.span (Set.range g) = ⊤ ∧ (∃ i, g i ≠ 0) ∧
      ∀ i : {i : Fin m // g i ≠ 0}, ∃ z : Fin n → reesTreeChart C g i,
        (MvPolynomial.aeval (R := k) z).toRingHom.Etale := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨t, hcover, hcharts⟩ := exists_finite_snc_etale_cover f n (isSnc_empty_of_smooth f)
  let U : t → (Spec (.of C)).Opens := fun V => V.1.1
  have hU : ∀ x : Spec (.of C), ∃ V, x ∈ U V := by
    intro x
    obtain ⟨V, hVt, hxV⟩ := hcover x
    exact ⟨⟨V, hVt⟩, hxV⟩
  obtain ⟨m, g, hg, hg0, hsub⟩ := exists_finite_principal_rees_refinement C U hU
  refine ⟨m, g, hg, hg0, ?_⟩
  intro i
  obtain ⟨V, hiV⟩ := hsub i
  obtain ⟨_, v, _, _, hv, _⟩ := hcharts V V.2
  let D := reesTreeChart C g i
  let α : Spec (.of D) ⟶ Spec (.of C) := subalgebraSpecMap (le_reesTreeChart C g i)
  have : IsOpenImmersion α := isOpenImmersion_principalReesChartMap C g hg i i.2
  have hαV : Set.range α ⊆ (V.1.1 : Set (Spec (.of C))) := hiV
  let _ : Algebra C D := (reesTreeChartIncl C g i).toAlgebra
  have : IsScalarTower k C D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hπ : α ≫ 𝟙 (Spec (.of C)) = Spec.map (CommRingCat.ofHom (algebraMap C D)) := by
    rw [Category.comp_id]
    rfl
  let f' := 𝟙 (Spec (.of C)) ≫ f
  let _ := f'.sectionsAlgebra V.1.1
  let φ := affineOpenChartRingHom α V.1 hαV
  let _ : Algebra Γ(Spec (.of C), V.1.1) D := φ.toAlgebra
  have : IsScalarTower k Γ(Spec (.of C), V.1.1) D :=
    isScalarTower_field_affineOpenChartRingHom (k := k) (𝟙 _) α V.1 hαV hπ
  have hφ : (algebraMap Γ(Spec (.of C), V.1.1) D).Etale :=
    etale_affineOpenChartRingHom α V.1 hαV
  have hv' : Etale (toAffineSpace f' V.1.1 v) := by simpa only [f', Category.id_comp] using hv
  have hV : IsAffineOpen V.1.1 := V.1.2
  have hvR := (etale_toAffineSpace_iff f' hV v).mp hv'
  exact ⟨fun j => algebraMap Γ(Spec (.of C), V.1.1) D (v j), etale_aeval_algebraMap v hvR hφ⟩

/-- A smooth literal affine domain is internally of one pure dimension, so its finite
source-coordinate Rees cover needs no separate dimension or global-coordinate input. -/
theorem exists_smooth_source_unit_rees_etale_cover [PerfectField k]
    (C : Subalgebra k K) [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))] :
    ∃ (n m : ℕ) (g : Fin m → C), Ideal.span (Set.range g) = ⊤ ∧ (∃ i, g i ≠ 0) ∧
      ∀ i : {i : Fin m // g i ≠ 0}, ∃ z : Fin n → reesTreeChart C g i,
        (MvPolynomial.aeval (R := k) z).toRingHom.Etale := by
  obtain ⟨n, hn⟩ := Hironaka.Resolution.exists_smoothOfRelativeDimension_of_irreducibleSpace
    (Spec.map (CommRingCat.ofHom (algebraMap k C)))
  obtain ⟨m, g, hg, hg0, hz⟩ := @exists_smooth_source_principal_rees_etale_cover
    k K _ _ _ _ C n hn
  exact ⟨n, m, g, hg, hg0, hz⟩

end EnvelopeProperty.Char0
