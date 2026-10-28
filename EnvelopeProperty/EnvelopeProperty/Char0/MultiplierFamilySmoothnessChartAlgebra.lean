import EnvelopeProperty.Projective.SmoothCone
import EnvelopeProperty.Projective.NativeQuotientAlgebra
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Whole original quotient charts and true native coordinate algebras -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
universe u
namespace EnvelopeProperty.Char0.MultiplierFamilySmoothness
open ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {M : ℕ}

/-- Rename the actual original standard affine variables by their actual complementary coordinates. -/
def chartCoordinateEquiv (j : Fin (M + 1)) :
    chartAlg (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) 1 ≃ₐ[k] CoordinateRing k j :=
  (chartEquiv j).trans (MvPolynomial.renameEquiv k (finSuccAboveEquiv j))

/-- The entire original polynomial map is precisely the actual native dehomogenization. -/
theorem rename_dehom (j : Fin (M + 1)) (F : MvPolynomial (Fin (M + 1)) k) :
    (MvPolynomial.renameEquiv k (finSuccAboveEquiv j)) (dehom j F) = coordinateDehom j F := by
  have he : (MvPolynomial.renameEquiv k (finSuccAboveEquiv j)).toAlgHom.comp (dehom j) =
      coordinateDehom j := by
    apply MvPolynomial.algHom_ext
    intro a
    rcases Fin.eq_self_or_eq_succAbove j a with rfl | ⟨b, rfl⟩
    · simp [dehom, coordinateDehom, coordinateDehomCoord]
    · simp [dehom, coordinateDehom, coordinateDehomCoord, Fin.succAbove_ne, finSuccAboveEquiv_apply]
  exact AlgHom.congr_fun he F

/-- EVERY original homogeneous fraction retains its original coordinate polynomial. -/
theorem chartCoordinateEquiv_chartMk (j : Fin (M + 1)) {d : ℕ}
    {F : MvPolynomial (Fin (M + 1)) k} (hF : F.IsHomogeneous d) :
    chartCoordinateEquiv j (chartMk (MvPolynomial.X j) 1 d F) = coordinateDehom j F := by
  change (MvPolynomial.renameEquiv k (finSuccAboveEquiv j))
    (chartDehom j (chartMk (MvPolynomial.X j) 1 d F)) = _
  rw [chartDehom_chartMk_of_isHomogeneous j hF, rename_dehom]

/-- The actual coordinate comparison retains the ENTIRE original homogeneous ideal on a relevant chart. -/
theorem chartIdeal_map_eq (X : ProjSubvariety k M) (j : Fin (M + 1))
    (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal) :
    (chartIdeal X.ideal (MvPolynomial.X j) 1).map (chartCoordinateEquiv j).toRingHom =
      X.ideal.map (coordinateDehom j).toRingHom := by
  let : X.ideal.IsPrime := X.isPrime
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change chartCoordinateEquiv j a ∈ X.ideal.map (coordinateDehom j).toRingHom
    obtain ⟨d, F, hF, hFI, rfl⟩ :=
      (mem_chartIdeal_iff (MvPolynomial.isHomogeneous_X k j) hj).mp ha
    rw [chartCoordinateEquiv_chartMk j (by simpa using hF)]
    exact Ideal.mem_map_of_mem _ hFI
  · rw [Ideal.map_le_iff_le_comap]
    intro F hF
    change coordinateDehom j F ∈ (chartIdeal X.ideal (MvPolynomial.X j) 1).map
      (chartCoordinateEquiv j).toRingHom
    rw [← MvPolynomial.sum_homogeneousComponent F, map_sum]
    apply Ideal.sum_mem
    intro d _
    have hd : MvPolynomial.homogeneousComponent d F ∈ X.ideal :=
      MvPolynomial.homogeneousComponent_mem_of_mem
        ((isHomogeneousIdeal_iff_isHomogeneous X.ideal).mp X.isHomogeneousIdeal) hF d
    have hmem := chartMk_mem_chartIdeal (I := X.ideal) (σ := MvPolynomial.X j) (d := 1)
      (show (MvPolynomial.homogeneousComponent d F).IsHomogeneous (d * 1) by
        simpa using MvPolynomial.homogeneousComponent_isHomogeneous d F) hd
    have hm := Ideal.mem_map_of_mem (chartCoordinateEquiv j).toRingHom hmem
    change chartCoordinateEquiv j (chartMk (MvPolynomial.X j) 1 d (MvPolynomial.homogeneousComponent d F)) ∈
      (chartIdeal X.ideal (MvPolynomial.X j) 1).map (chartCoordinateEquiv j).toRingHom at hm
    rwa [chartCoordinateEquiv_chartMk j (MvPolynomial.homogeneousComponent_isHomogeneous d F)] at hm

private def quotientEquivReverse {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (I : Ideal A) (J : Ideal B) (e : A ≃ₐ[k] B)
    (h : J = I.map e.toRingHom) : (B ⧸ J) ≃ₐ[k] (A ⧸ I) :=
  (Ideal.quotientEquivAlg I J e h).symm

/-- The whole actual native coordinate quotient is the SAME original algebra used by HasSmoothCharts. -/
def coordinateQuotientEquiv (X : ProjSubvariety k M) (j : Fin (M + 1))
    (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal) :
    (CoordinateRing k j ⧸ (X.ideal.map (coordinateDehom j).toRingHom)) ≃ₐ[k] QuotChartAlg X.ideal (MvPolynomial.X j) 1 :=
  quotientEquivReverse (chartIdeal X.ideal (MvPolynomial.X j) 1)
    (X.ideal.map (coordinateDehom j).toRingHom) (chartCoordinateEquiv j) (chartIdeal_map_eq X j hj).symm

end EnvelopeProperty.Char0.MultiplierFamilySmoothness
