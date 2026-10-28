/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SNCFactors
import EnvelopeProperty.Char0.SNCCharts
import Hironaka.Scheme.Snc.SpreadSnc
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Scheme.Smooth.EtaleLocal

/-!
# Affine étale neighbourhoods for factors of an SNC product

The monomial stalk identity produced in `SNCFactors` spreads to an actual affine neighbourhood
with actual étale coordinates. The finite-generation spreading theorem and the étale-coordinate
producer are both applied internally, with no added chart-existence assumption.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal
open scoped Classical

universe u

variable {X : Scheme.{u}}

/-- The monomial factor stalk identity is independent of the chosen generators of the component
ideals. In particular it transfers to the germs of the actual adapted chart functions. -/
theorem exists_factor_stalk_monomial_in_component_sections {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] {A B : X.IdealSheafData}
    {F : Scheme.DivisorFamily X} (hF : F.IsSnc) (e : F.ι → ℕ)
    (hprod : A * B = ∏ i, F.component i ^ e i) {x : X}
    (U : X.affineOpens) (hxU : x ∈ U.1) {n : ℕ} (v : Fin n → Γ(X, U.1))
    (c : {i : F.ι // x ∈ (F.component i).support} → Fin n)
    (hc : ∀ i, (F.component i.1).ideal U = span {v (c i)}) :
    ∃ a : {i : F.ι // x ∈ (F.component i).support} → ℕ, (∀ i, a i ≤ e i.1) ∧
      A.stalkIdeal x = span ((X.presheaf.germ U.1 x hxU).hom '' {∏ i, v (c i) ^ a i}) := by
  obtain ⟨m, z, _, c₀, _, hc₀, a, ha, hA⟩ := exists_stalk_monomial_factor f hF e hprod x
  have hcompg (i : {i : F.ι // x ∈ (F.component i).support}) :
      (F.component i.1).stalkIdeal x = span {X.presheaf.germ U.1 x hxU (v (c i))} := by
    rw [Scheme.IdealSheafData.stalkIdeal_eq_map_germ _ U hxU, hc i,
      Ideal.map_span, Set.image_singleton]
  refine ⟨a, ha, ?_⟩
  calc A.stalkIdeal x = span {∏ i, z (c₀ i) ^ a i} := hA
    _ = ∏ i, span {z (c₀ i) ^ a i} := (Ideal.prod_span_singleton _ _).symm
    _ = ∏ i, span {(X.presheaf.germ U.1 x hxU (v (c i))) ^ a i} := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← Ideal.span_singleton_pow, ← hc₀ i, hcompg i, Ideal.span_singleton_pow]
    _ = span {∏ i, (X.presheaf.germ U.1 x hxU (v (c i))) ^ a i} :=
      Ideal.prod_span_singleton _ _
    _ = span ((X.presheaf.germ U.1 x hxU).hom '' {∏ i, v (c i) ^ a i}) := by
      rw [Set.image_singleton, map_prod]
      simp only [map_pow]

/-- A factor of the SNC total product is a coordinate monomial on an actual affine étale
neighbourhood of each closed point. The chosen coordinates also cut out the original boundary. -/
theorem exists_snc_etale_chart_monomial_factor {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {A B : X.IdealSheafData} {F : Scheme.DivisorFamily X} (hF : F.IsSnc) (e : F.ι → ℕ)
    (hprod : A * B = ∏ i, F.component i ^ e i) {x : X} (hx : IsClosed ({x} : Set X)) :
    ∃ (U : X.affineOpens) (v : Fin n → Γ(X, U.1)), x ∈ U.1 ∧
      Etale (toAffineSpace f U.1 v) ∧
      ∃ c : {i : F.ι // x ∈ (F.component i).support} → Fin n,
        Function.Injective c ∧
        (∀ i, (F.component i.1).ideal U = span {v (c i)}) ∧
        (∀ i, x ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤) ∧
        ∃ a : {i : F.ι // x ∈ (F.component i).support} → ℕ,
          (∀ i, a i ≤ e i.1) ∧ A.ideal U = span {∏ i, v (c i) ^ a i} := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨V, v, hxV, het, c, hcinj, hcomp, habsent⟩ :=
    exists_snc_etale_chart_at_closed f n hF hx
  obtain ⟨a, ha, hA⟩ :=
    exists_factor_stalk_monomial_in_component_sections f hF e hprod V hxV v c hcomp
  have : IsNoetherianRing Γ(X, V.1) := by
    let _ := f.sectionsAlgebra V.1
    have : Algebra.FiniteType k Γ(X, V.1) := f.finiteType_sectionsAlgebra V.2
    exact Algebra.FiniteType.isNoetherianRing k Γ(X, V.1)
  obtain ⟨t, hxt, ht⟩ := exists_basicOpen_ideal_eq_span A V hxV
    {∏ i, v (c i) ^ a i} (Set.finite_singleton _) hA
  let U : X.affineOpens := X.affineBasicOpen t
  have hUV : U.1 ≤ V.1 := X.basicOpen_le t
  let w : Fin n → Γ(X, U.1) := fun j => X.presheaf.map (homOfLE hUV).op (v j)
  refine ⟨U, w, hxt, ?_, c, hcinj, ?_, ?_, a, ha, ?_⟩
  · have : Etale (toAffineSpace f V.1 v) := het
    exact etale_toAffineSpace_restrict f hUV v
  · intro i
    change (F.component i.1).ideal U =
      span {(X.presheaf.map (homOfLE hUV).op).hom (v (c i))}
    rw [← (F.component i.1).map_ideal hUV, hcomp i, Ideal.map_span, Set.image_singleton]
    rfl
  · intro i hi
    rw [← X.homOfLE_ι hUV, Scheme.IdealSheafData.comap_comp, habsent i hi,
      Scheme.IdealSheafData.comap_top]
  · change A.ideal ⟨X.basicOpen t, V.2.basicOpen t⟩ =
      span {∏ i, (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom (v (c i)) ^ a i}
    simpa only [Set.image_singleton, map_prod, map_pow] using ht

/-- Finitely many factors of the total transform are simultaneously monomial in the same actual
étale coordinates, after one principal-open shrinking. -/
theorem exists_snc_etale_chart_monomial_family {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {κ : Type*} [Fintype κ] (A : κ → X.IdealSheafData)
    {F : Scheme.DivisorFamily X} (hF : F.IsSnc) (e : F.ι → ℕ)
    (hprod : ∏ j, A j = ∏ i, F.component i ^ e i) {x : X} (hx : IsClosed ({x} : Set X)) :
    ∃ (U : X.affineOpens) (v : Fin n → Γ(X, U.1)), x ∈ U.1 ∧
      Etale (toAffineSpace f U.1 v) ∧
      ∃ c : {i : F.ι // x ∈ (F.component i).support} → Fin n,
        Function.Injective c ∧
        (∀ i, (F.component i.1).ideal U = span {v (c i)}) ∧
        (∀ i, x ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤) ∧
        ∃ a : κ → {i : F.ι // x ∈ (F.component i).support} → ℕ,
          (∀ j i, a j i ≤ e i.1) ∧ ∀ j, (A j).ideal U = span {∏ i, v (c i) ^ a j i} := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨V, v, hxV, het, c, hcinj, hcomp, habsent⟩ :=
    exists_snc_etale_chart_at_closed f n hF hx
  have hfactor (j : κ) : A j * (∏ j' ∈ Finset.univ.erase j, A j') =
      ∏ i, F.component i ^ e i :=
    (Finset.mul_prod_erase Finset.univ A (Finset.mem_univ j)).trans hprod
  choose a ha hA using fun j => exists_factor_stalk_monomial_in_component_sections
    f hF e (hfactor j) V hxV v c hcomp
  have : IsNoetherianRing Γ(X, V.1) := by
    let _ := f.sectionsAlgebra V.1
    have : Algebra.FiniteType k Γ(X, V.1) := f.finiteType_sectionsAlgebra V.2
    exact Algebra.FiniteType.isNoetherianRing k Γ(X, V.1)
  obtain ⟨t, hxt, ht⟩ := exists_basicOpen_forall_ideal_eq_span A V hxV
    (fun j => {∏ i, v (c i) ^ a j i}) (fun _ => Set.finite_singleton _) hA
  let U : X.affineOpens := X.affineBasicOpen t
  have hUV : U.1 ≤ V.1 := X.basicOpen_le t
  let w : Fin n → Γ(X, U.1) := fun j => X.presheaf.map (homOfLE hUV).op (v j)
  refine ⟨U, w, hxt, ?_, c, hcinj, ?_, ?_, a, ha, ?_⟩
  · have : Etale (toAffineSpace f V.1 v) := het
    exact etale_toAffineSpace_restrict f hUV v
  · intro i
    change (F.component i.1).ideal U =
      span {(X.presheaf.map (homOfLE hUV).op).hom (v (c i))}
    rw [← (F.component i.1).map_ideal hUV, hcomp i, Ideal.map_span, Set.image_singleton]
    rfl
  · intro i hi
    rw [← X.homOfLE_ι hUV, Scheme.IdealSheafData.comap_comp, habsent i hi,
      Scheme.IdealSheafData.comap_top]
  · intro j
    change (A j).ideal ⟨X.basicOpen t, V.2.basicOpen t⟩ =
      span {∏ i, (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom (v (c i)) ^ a j i}
    simpa only [Set.image_singleton, map_prod, map_pow] using ht j

/-- A quasi-compact smooth scheme has a finite actual affine étale cover simultaneously
monomializing every factor of the SNC total product. -/
theorem exists_finite_snc_etale_monomial_cover {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] [CompactSpace X]
    {κ : Type*} [Fintype κ] (A : κ → X.IdealSheafData)
    {F : Scheme.DivisorFamily X} (hF : F.IsSnc) (e : F.ι → ℕ)
    (hprod : ∏ j, A j = ∏ i, F.component i ^ e i) :
    ∃ t : Finset X.affineOpens, (∀ x : X, ∃ U ∈ t, x ∈ U.1) ∧
      ∀ U ∈ t, ∃ (x : X) (v : Fin n → Γ(X, U.1)), IsClosed ({x} : Set X) ∧
        x ∈ U.1 ∧ Etale (toAffineSpace f U.1 v) ∧
        ∃ c : {i : F.ι // x ∈ (F.component i).support} → Fin n,
          Function.Injective c ∧
          (∀ i, (F.component i.1).ideal U = span {v (c i)}) ∧
          (∀ i, x ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤) ∧
          ∃ a : κ → {i : F.ι // x ∈ (F.component i).support} → ℕ,
            (∀ j i, a j i ≤ e i.1) ∧ ∀ j, (A j).ideal U = span {∏ i, v (c i) ^ a j i} := by
  choose U v hmem het c hcinj hideal habsent a ha hA using
    fun p : {x : X // IsClosed ({x} : Set X)} =>
      exists_snc_etale_chart_monomial_family f n A hF e hprod p.2
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hcover : (Set.univ : Set X) ⊆ ⋃ p, ((U p).1 : Set X) := by
    intro x _
    obtain ⟨p, hp, _, hxp⟩ :=
      exists_isClosed_singleton_mem_specializes isClosed_univ (Set.mem_univ x)
    exact Set.mem_iUnion.mpr
      ⟨⟨p, hp⟩, hxp.mem_open (U ⟨p, hp⟩).1.isOpen (hmem ⟨p, hp⟩)⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun p => ((U p).1 : Set X)) (fun p => (U p).1.isOpen) hcover
  refine ⟨s.image U, ?_, ?_⟩
  · intro x
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
    obtain ⟨hps, hxp⟩ := Set.mem_iUnion.mp hp
    exact ⟨U p, Finset.mem_image.mpr ⟨p, hps, rfl⟩, hxp⟩
  · intro V hV
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hV
    exact ⟨p.1, v p, p.2, hmem p, het p, c p, hcinj p, hideal p, habsent p,
      a p, ha p, hA p⟩

end EnvelopeProperty.Char0
