import EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomialLaurent
import EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomialCoefficients

/-! # Original coordinate-localization maps retain actual original Laurent values

Only the coordinate index is universe-lifted in the target Laurent algebra.
The actual polynomial ring and original coefficient ring are retained by the
literal variable-renaming map; the geometric projective scheme is unchanged.
-/

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial HomogeneousLocalization
noncomputable section
universe u
namespace EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomial
open DeJongAlterations.Geometry.ProperSteinProjectiveCech
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual original Laurent algebra, with only its finite coordinate index universe-lifted. -/
abbrev originalLaurent := projectiveLaurentAlgebra R (ULift.{u} σ)

/-- Original polynomials enter Laurent coordinates by actual variable renaming; their coefficients stay in R. -/
def originalPolynomialToLaurent : MvPolynomial σ R →ₐ[R] originalLaurent (R := R) (σ := σ) :=
  (polynomialToProjectiveLaurent (K := R) (I := ULift.{u} σ)).comp
    (MvPolynomial.rename ULift.up)

/-- Every original chart coordinate is a genuine unit in the actual target Laurent algebra. -/
theorem originalPolynomialToLaurent_X_isUnit (i : σ) :
    IsUnit (originalPolynomialToLaurent (R := R) (X i)) := by
  simpa only [originalPolynomialToLaurent, AlgHom.comp_apply, MvPolynomial.rename_X] using
    polynomialToProjectiveLaurent_X_isUnit (K := R) (I := ULift.{u} σ) (ULift.up i)

/-- Native localization of the ORIGINAL polynomial ring into the original Laurent algebra. -/
def originalLocalizationToLaurent (f : MvPolynomial σ R)
    (hf : IsUnit (originalPolynomialToLaurent f)) :
    Localization.Away f →ₐ[R] originalLaurent (R := R) (σ := σ) :=
  IsLocalization.Away.liftAlgHom _ hf

/-- Original numerator coefficients are unchanged by the actual localization map. -/
theorem originalLocalizationToLaurent_algebraMap (f : MvPolynomial σ R)
    (hf : IsUnit (originalPolynomialToLaurent f)) (F : MvPolynomial σ R) :
    originalLocalizationToLaurent f hf (algebraMap _ (Localization.Away f) F) =
      originalPolynomialToLaurent F := IsLocalization.Away.lift_eq _ hf F

/-- The SAME native homogeneous Away element is mapped by its actual ordinary fraction value. -/
def originalAwayToLaurent (f : MvPolynomial σ R)
    (hf : IsUnit (originalPolynomialToLaurent f)) :
    Away (homogeneousSubmodule σ R) f →+* originalLaurent (R := R) (σ := σ) :=
  (originalLocalizationToLaurent f hf).toRingHom.comp
    (algebraMap (Away (homogeneousSubmodule σ R) f) (Localization.Away f))

/-- Actual original homogeneous fractions satisfy their literal denominator-clearing identity in the same Laurent algebra. -/
theorem originalAwayToLaurent_mk_clear (f : MvPolynomial σ R)
    (hf : IsUnit (originalPolynomialToLaurent f)) {d : ℕ}
    (hfd : f ∈ homogeneousSubmodule σ R d) (n : ℕ)
    (F : MvPolynomial σ R) (hF : F ∈ homogeneousSubmodule σ R (n • d)) :
    originalAwayToLaurent f hf (Away.mk (homogeneousSubmodule σ R) hfd n F hF) *
      originalPolynomialToLaurent f ^ n = originalPolynomialToLaurent F := by
  have he : Localization.mk F (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) *
      algebraMap (MvPolynomial σ R) (Localization.Away f) (f ^ n) =
      algebraMap (MvPolynomial σ R) (Localization.Away f) F := by
    simpa only [Localization.mk_eq_mk'] using
      IsLocalization.mk'_spec (Localization.Away f) F (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f)
  have h := congrArg (originalLocalizationToLaurent f hf) he
  change originalLocalizationToLaurent f hf
    (Localization.mk F (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f)) *
      originalPolynomialToLaurent f ^ n = originalPolynomialToLaurent F
  simpa only [map_mul, originalLocalizationToLaurent_algebraMap, map_pow] using h

/-- The actual native homogeneous-coordinate restriction preserves the SAME original Laurent fraction. -/
theorem originalAwayToLaurent_awayMap {f g x : MvPolynomial σ R} {d a : ℕ}
    (hfd : f ∈ homogeneousSubmodule σ R d) (hga : g ∈ homogeneousSubmodule σ R a)
    (hf : IsUnit (originalPolynomialToLaurent f)) (hg : IsUnit (originalPolynomialToLaurent g))
    (hx : x = f * g) (z : Away (homogeneousSubmodule σ R) f) :
    originalAwayToLaurent x (by rw [hx, map_mul]; exact hf.mul hg)
      (awayMap (homogeneousSubmodule σ R) hga hx z) = originalAwayToLaurent f hf z := by
  subst x
  obtain ⟨n, F, hF, rfl⟩ := Away.mk_surjective (homogeneousSubmodule σ R) hfd z
  rw [awayMap_mk]
  apply ((hf.mul hg).pow n).mul_right_cancel
  change _ * (originalPolynomialToLaurent f * originalPolynomialToLaurent g) ^ n =
    _ * (originalPolynomialToLaurent f * originalPolynomialToLaurent g) ^ n
  have hc := originalAwayToLaurent_mk_clear (f * g) (by rw [map_mul]; exact hf.mul hg)
    (SetLike.mul_mem_graded hfd hga) n (F * g ^ n) (by
      rw [smul_add]
      exact SetLike.mul_mem_graded hF (SetLike.pow_mem_graded n hga))
  simp only [map_mul] at hc
  rw [hc, map_pow]
  rw [mul_pow, ← mul_assoc, originalAwayToLaurent_mk_clear f hf hfd n F hF]

end EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomial
