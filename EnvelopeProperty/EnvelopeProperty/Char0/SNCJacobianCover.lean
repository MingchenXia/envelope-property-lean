/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SNCJacobianNeighborhoods
import EnvelopeProperty.Char0.SNCAffineFactors

/-!
# Actual SNC Jacobian neighborhoods cover the whole scheme

Choose and shrink a chart at every closed point first; only then use Jacobson
specializations and compactness. This preserves a genuine cover after shrinking.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory Module Ideal
open scoped Classical

universe u

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] {Y : Scheme.{u}} {n : ℕ}

/-- Literal actual affine coordinate, boundary, transform and Jacobian data on a principal
neighborhood of the specified point. This is existential geometric data, not a typeclass. -/
def SNCJacobianNeighbourhood (π : Y ⟶ Spec (.of R)) (F : Scheme.DivisorFamily Y)
    (n : ℕ) (J : (Spec (.of R)).IdealSheafData) (x : Y) (W : Y.affineOpens) : Prop :=
  ∃ (U : Y.affineOpens) (v : Fin n → Γ(Y, U.1)), x ∈ U.1 ∧
    ∃ hv : Etale (toAffineSpace
        (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) U.1 v),
      ∃ c : {i : F.ι // x ∈ (F.component i).support} → Fin n,
        Function.Injective c ∧
        (∀ i, (F.component i.1).ideal U = span {v (c i)}) ∧
        (∀ i, x ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤) ∧
        ∃ e : {i : F.ι // x ∈ (F.component i).support} → ℕ,
          (J.comap π).ideal U = span {∏ i, v (c i) ^ e i} ∧
          ∃ s : Γ(Y, U.1), W = Y.affineBasicOpen s ∧ x ∈ W.1 ∧
            (letI := (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))).sectionsAlgebra U.1
             letI : Algebra R Γ(Y, U.1) := (sectionsHom π U.1).toAlgebra
             letI := isScalarTower_base_resolutionSections (k := k) π U.1
             ∃ a : {i : F.ι // x ∈ (F.component i).support} → ℕ,
               ∀ (T : Type u) [CommRing T] [Algebra Γ(Y, U.1) T] [IsLocalization.Away s T],
                 (affineRelativeJacobianIdeal (R := R)
                   (schemeEtaleDifferentialBasis
                     (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) U v hv)).map
                     (algebraMap Γ(Y, U.1) T) =
                   span {∏ i, algebraMap Γ(Y, U.1) T (v (c i)) ^ a i})

/-- At every closed point actual SNC geometry and an actual source coordinate map produce
an adapted principal neighborhood with a genuine monomial Jacobian identity. -/
theorem exists_snc_jacobian_neighbourhood_at_closed [PerfectField k]
    (π : Y ⟶ Spec (.of R))
    [SmoothOfRelativeDimension n (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))]
    (J : (Spec (.of R)).IdealSheafData) [IsIso (π ∣_ J.support.compl)]
    (F : Scheme.DivisorFamily Y) (hF : F.IsSnc) (e : F.ι → ℕ)
    (hJ : J.comap π = ∏ i, F.component i ^ e i)
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    {x : Y} (hx : IsClosed ({x} : Set Y)) :
    ∃ W : Y.affineOpens, x ∈ W.1 ∧ SNCJacobianNeighbourhood (k := k) π F n J x W := by
  let f := π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))
  have hprod : J.comap π * ⊤ = ∏ i, F.component i ^ e i := by simpa using hJ
  obtain ⟨U, v, hxU, hv, c, hcinj, hc, habsent, a, _, hmon⟩ :=
    exists_snc_etale_chart_monomial_factor f n hF e hprod hx
  let _ := f.sectionsAlgebra U.1
  let _ : Algebra R Γ(Y, U.1) := (sectionsHom π U.1).toAlgebra
  have := isScalarTower_base_resolutionSections (k := k) π U.1
  obtain ⟨s, hxs, b, hb⟩ := exists_principal_monomial_jacobian_neighbourhood
    π J F hF U x hxU v hv c hc a hmon z hz
  refine ⟨Y.affineBasicOpen s, hxs, U, v, hxU, hv, c, hcinj, hc, habsent, a, hmon,
    s, rfl, hxs, b, hb⟩

/-- Choose and shrink at all closed points before compactness: these actual principal
neighborhoods cover the whole smooth scheme and have a finite subcover. -/
theorem exists_finite_snc_jacobian_neighbourhood_cover [PerfectField k] [CompactSpace Y]
    (π : Y ⟶ Spec (.of R))
    [SmoothOfRelativeDimension n (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))]
    (J : (Spec (.of R)).IdealSheafData) [IsIso (π ∣_ J.support.compl)]
    (F : Scheme.DivisorFamily Y) (hF : F.IsSnc) (e : F.ι → ℕ)
    (hJ : J.comap π = ∏ i, F.component i ^ e i)
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    ∃ t : Finset Y.affineOpens, (∀ y : Y, ∃ W ∈ t, y ∈ W.1) ∧
      ∀ W ∈ t, ∃ x : Y, IsClosed ({x} : Set Y) ∧
        SNCJacobianNeighbourhood (k := k) π F n J x W := by
  choose W hmem hW using fun p : {x : Y // IsClosed ({x} : Set Y)} =>
    exists_snc_jacobian_neighbourhood_at_closed π J F hF e hJ z hz p.2
  let f := π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace f
  have hcover : (Set.univ : Set Y) ⊆ ⋃ p, ((W p).1 : Set Y) := by
    intro y _
    obtain ⟨x, hx, _, hyx⟩ :=
      exists_isClosed_singleton_mem_specializes isClosed_univ (Set.mem_univ y)
    exact Set.mem_iUnion.mpr
      ⟨⟨x, hx⟩, hyx.mem_open (W ⟨x, hx⟩).1.isOpen (hmem ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun p => ((W p).1 : Set Y)) (fun p => (W p).1.isOpen) hcover
  refine ⟨s.image W, ?_, ?_⟩
  · intro y
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ y))
    obtain ⟨hps, hyp⟩ := Set.mem_iUnion.mp hp
    exact ⟨W p, Finset.mem_image.mpr ⟨p, hps, rfl⟩, hyp⟩
  · intro V hV
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hV
    exact ⟨p.1, p.2, hW p⟩

end EnvelopeProperty.Char0
