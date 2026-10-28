/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SNCJacobianCover
import EnvelopeProperty.Char0.SNCAffineFactors

/-!
# Actual simultaneous family monomials in genuine Jacobian neighborhoods

Every factor and the total-transform Jacobian use the same actual adapted
boundary coordinates, with genuine coverage after principal shrinking.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory Module Ideal
open scoped Classical

universe u

/-- Evaluation on an actual affine open preserves the multiplicative ideal structure. -/
def nativeIdealMonoidHom {Y : Scheme.{u}} (U : Y.affineOpens) :
    Y.IdealSheafData →* Ideal Γ(Y, U.1) where
  toFun J := J.ideal U
  map_one' := by simp
  map_mul' _ _ := rfl

/-- The native ideal of the actual finite family product is the product of its native ideals. -/
theorem nativeIdeal_fintype_prod {Y : Scheme.{u}} (U : Y.affineOpens)
    {κ : Type*} [Fintype κ] (A : κ → Y.IdealSheafData) :
    (∏ j, A j).ideal U = ∏ j, (A j).ideal U :=
  map_prod (nativeIdealMonoidHom U) A Finset.univ

/-- A finite product of actual coordinate monomial ideals adds the exponents. -/
theorem prod_span_monomial_family {R : Type u} [CommRing R]
    {κ ι : Type*} [Fintype κ] [Fintype ι] (p : ι → R) (a : κ → ι → ℕ) :
    (∏ j, span {∏ i, p i ^ a j i}) = span {∏ i, p i ^ (∑ j, a j i)} := by
  rw [Ideal.prod_span_singleton]
  congr 1
  congr 1
  rw [Finset.prod_comm]
  simp only [Finset.prod_pow_eq_pow_sum]

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] {Y : Scheme.{u}} {κ : Type*}

/-- Literal common adapted coordinates for every family factor and the genuine localized
Jacobian. This is actual existential geometric data, not an assumption class. -/
def SNCFamilyJacobianNeighbourhood (π : Y ⟶ Spec (.of R)) (F : Scheme.DivisorFamily Y)
    (n : ℕ) (J : (Spec (.of R)).IdealSheafData) (A : κ → Y.IdealSheafData)
    (x : Y) (W : Y.affineOpens) : Prop :=
  ∃ (U : Y.affineOpens) (v : Fin n → Γ(Y, U.1)), x ∈ U.1 ∧
    ∃ hv : Etale (toAffineSpace
        (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) U.1 v),
      ∃ c : {i : F.ι // x ∈ (F.component i).support} → Fin n,
        Function.Injective c ∧
        (∀ i, (F.component i.1).ideal U = span {v (c i)}) ∧
        (∀ i, x ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤) ∧
        ∃ d : κ → {i : F.ι // x ∈ (F.component i).support} → ℕ,
          (∀ j, (A j).ideal U = span {∏ i, v (c i) ^ d j i}) ∧
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

/-- Forgetting the family retains exactly the actual total-transform Jacobian neighborhood. -/
theorem SNCFamilyJacobianNeighbourhood.toSNCJacobianNeighbourhood
    (π : Y ⟶ Spec (.of R)) (F : Scheme.DivisorFamily Y) (n : ℕ)
    (J : (Spec (.of R)).IdealSheafData) (A : κ → Y.IdealSheafData) (x : Y) (W : Y.affineOpens)
    (h : SNCFamilyJacobianNeighbourhood (k := k) π F n J A x W) :
    SNCJacobianNeighbourhood (k := k) π F n J x W := by
  obtain ⟨U, v, hxU, hv, c, hcinj, hc, habsent, _, _, e, hJ, s, hW, hxs, hJac⟩ := h
  exact ⟨U, v, hxU, hv, c, hcinj, hc, habsent, e, hJ, s, hW, hxs, hJac⟩

variable [Fintype κ]

/-- Actual simultaneous SNC factor coordinates also give the total-transform monomial and
therefore produce the genuine Jacobian principal neighborhood in those same coordinates. -/
theorem exists_snc_family_jacobian_neighbourhood_at_closed [PerfectField k]
    (π : Y ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))]
    (J : (Spec (.of R)).IdealSheafData) [IsIso (π ∣_ J.support.compl)]
    (F : Scheme.DivisorFamily Y) (hF : F.IsSnc) (e : F.ι → ℕ)
    (hJ : J.comap π = ∏ i, F.component i ^ e i)
    (A : κ → Y.IdealSheafData) (hAprod : ∏ j, A j = J.comap π)
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    {x : Y} (hx : IsClosed ({x} : Set Y)) :
    ∃ W : Y.affineOpens, x ∈ W.1 ∧ SNCFamilyJacobianNeighbourhood (k := k) π F n J A x W := by
  let f := π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))
  obtain ⟨U, v, hxU, hv, c, hcinj, hc, habsent, d, _, hA⟩ :=
    exists_snc_etale_chart_monomial_family f n A hF e (hAprod.trans hJ) hx
  have hJchart : (J.comap π).ideal U = span {∏ i, v (c i) ^ (∑ j, d j i)} := by
    rw [← hAprod, nativeIdeal_fintype_prod]
    simp_rw [hA]
    exact prod_span_monomial_family (fun i => v (c i)) d
  let _ := f.sectionsAlgebra U.1
  let _ : Algebra R Γ(Y, U.1) := (sectionsHom π U.1).toAlgebra
  have := isScalarTower_base_resolutionSections (k := k) π U.1
  obtain ⟨s, hxs, a, hJac⟩ := exists_principal_monomial_jacobian_neighbourhood (k := k)
    π J F hF U x hxU v hv c hc (fun i => ∑ j, d j i) hJchart z hz
  exact ⟨Y.affineBasicOpen s, hxs, U, v, hxU, hv, c, hcinj, hc, habsent, d, hA,
    (fun i => ∑ j, d j i), hJchart, s, rfl, hxs, a, hJac⟩

/-- The actually shrunk simultaneous family neighborhoods cover all points, and compactness
selects a genuine finite subcover after shrinking. -/
theorem exists_finite_snc_family_jacobian_neighbourhood_cover [PerfectField k] [CompactSpace Y]
    (π : Y ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))]
    (J : (Spec (.of R)).IdealSheafData) [IsIso (π ∣_ J.support.compl)]
    (F : Scheme.DivisorFamily Y) (hF : F.IsSnc) (e : F.ι → ℕ)
    (hJ : J.comap π = ∏ i, F.component i ^ e i)
    (A : κ → Y.IdealSheafData) (hAprod : ∏ j, A j = J.comap π)
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    ∃ t : Finset Y.affineOpens, (∀ y : Y, ∃ W ∈ t, y ∈ W.1) ∧
      ∀ W ∈ t, ∃ x : Y, IsClosed ({x} : Set Y) ∧
        SNCFamilyJacobianNeighbourhood (k := k) π F n J A x W := by
  choose W hmem hW using fun p : {x : Y // IsClosed ({x} : Set Y)} =>
    exists_snc_family_jacobian_neighbourhood_at_closed π n J F hF e hJ A hAprod z hz p.2
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
