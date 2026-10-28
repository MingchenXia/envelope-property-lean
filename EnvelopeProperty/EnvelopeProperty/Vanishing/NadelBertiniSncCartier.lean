import Hironaka.Algebra.Local.QuotientParameters
import Hironaka.Scheme.IdealSheaf.Invertible
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.Smooth.SubschemeStalk
import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Scheme.Snc.Coordinates

/-! # Genuine regular Cartier equations have nonzero cotangent classes

Regularity of the zero subscheme alone is insufficient. The actual nonzero
Cartier equation is retained in the native regular-quotient parameter theorem.
This gives the real codimension-one input needed for original SNC transversality.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniSncCartier

/-- A nonzero ORIGINAL principal equation with regular ORIGINAL quotient cannot
lie in the original maximal-ideal square. -/
theorem equation_notMem_sq_of_regular_quotient {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (h : R) (hh : h ≠ 0)
    [IsRegularLocalRing (R ⧸ Ideal.span {h})] : h ∉ maximalIdeal R ^ 2 := by
  intro hbad
  obtain ⟨n, c, z, hcn, hnd, hz, hI⟩ :=
    IsRegularLocalRing.exists_span_eq_maximalIdeal_and_eq_span_image_lt
      (Ideal.span {h})
  have hc : c = 0 := by
    by_contra hc
    have hcpos : 0 < c := Nat.pos_of_ne_zero hc
    let j : Fin n := ⟨0, lt_of_lt_of_le hcpos hcn⟩
    have hj : z j ∈ Ideal.span {h} := by
      rw [hI]
      exact Ideal.subset_span ⟨j, hcpos, rfl⟩
    exact notMem_sq_of_span_eq z hz hnd j
      ((Ideal.span_singleton_le_iff_mem _).mpr hbad hj)
  subst c
  have hzero : Ideal.span ({h} : Set R) = ⊥ := by simpa using hI
  have hmem : h ∈ Ideal.span ({h} : Set R) := Ideal.mem_span_singleton_self h
  rw [hzero, Ideal.mem_bot] at hmem
  exact hh hmem

/-- An ORIGINAL effective Cartier hypersurface with regular actual zero scheme
is a genuine smooth divisor of the original regular scheme. -/
theorem isSmoothDivisor_of_cartier_regular {X : Scheme.{u}} [IsRegular X]
    (H : X.IdealSheafData) (hH : H.IsInvertible) (hreg : IsRegular H.subscheme) :
    IsSmoothDivisor H := by
  refine ⟨hreg, fun x hx => ?_⟩
  obtain ⟨h, hh, he⟩ := hH.exists_ne_zero_stalkIdeal_eq_span x
  have hm : h ∈ maximalIdeal (X.presheaf.stalk x) :=
    (Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal H x).mp hx
      (he.symm ▸ Ideal.mem_span_singleton_self h)
  let : IsRegularLocalRing (X.presheaf.stalk x) := IsRegular.isRegularAt x
  have hquot : IsRegularLocalRing (X.presheaf.stalk x ⧸ H.stalkIdeal x) := by
    obtain ⟨w, rfl⟩ := H.exists_subschemeι_eq hx
    let : IsRegularLocalRing (H.subscheme.presheaf.stalk w) := hreg.isRegularAt w
    exact IsRegularLocalRing.of_ringEquiv (H.stalkQuotientEquiv w).symm
  let : IsRegularLocalRing (X.presheaf.stalk x ⧸ Ideal.span {h}) := he ▸ hquot
  exact ⟨h, hm, equation_notMem_sq_of_regular_quotient h hh, he⟩

/-- A genuine smooth divisor avoids any original regular point whose actual
local dimension is zero; identically-zero sections cannot pass this test. -/
theorem smoothDivisor_avoids_dimZero_point {X : Scheme.{u}} [IsRegular X]
    (H : X.IdealSheafData) (hH : IsSmoothDivisor H) (x : X)
    (hdim : ringKrullDim (X.presheaf.stalk x) = 0) : x ∉ H.support := by
  intro hx
  let : IsRegularLocalRing (X.presheaf.stalk x) := IsRegular.isRegularAt x
  obtain ⟨n, z, hz, hnd⟩ := exists_fin_span_eq_maximalIdeal (X.presheaf.stalk x)
  have hn : n = 0 := by
    have h := hnd.trans hdim
    exact_mod_cast h
  subst n
  have hm : maximalIdeal (X.presheaf.stalk x) = ⊥ := by
    rw [← hz]
    simp
  obtain ⟨h, hh, hh2, _⟩ := hH.2 x hx
  have hh0 : h = 0 := by simpa only [hm, Ideal.mem_bot] using hh
  exact hh2 (hh0 ▸ Ideal.zero_mem _)

end EnvelopeProperty.Vanishing.NadelBertiniSncCartier
