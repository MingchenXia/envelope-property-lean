import EnvelopeProperty.Char0.AffineSpecRoundedCanonicalKernel

/-! # SAME original native affine quotient kernel and ENTIRE canonical factorization -/

open CategoryTheory AlgebraicGeometry Opposite
open EnvelopeProperty.CanonicalGeometry
namespace EnvelopeProperty.Char0.RoundedCanonicalModule
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- EVERY original spectrum quotient kernel member is exactly an ENTIRE
original scalar canonical map factorization through SAME rounded inclusion. -/
theorem mem_specQuotientKernel_iff_factorization
    {k : Type u} [Field k] (A B : CommRingCat.{u}) [Algebra k A] [Algebra k B]
    (φ : A →ₐ[k] B) {n : ℕ} (z : Fin n → A)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    [SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ affineStructuralMap k A)]
    (J : (Spec B).IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) (a : B) :
    let f := affineStructuralMap k A
    let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
    letI : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
    a ∈ specQuotientKernel A B φ z hz J hJ q ↔
      ∃ θ : (Scheme.Modules.pullback g).obj (canonicalLineSheaf f n) ⟶ absolute (g ≫ f) n J hJ q,
        θ ≫ absoluteRoundedInclusion (g ≫ f) n J hJ q =
          SchemeUnitScalarAction.globalScalarAction _ ((Scheme.ΓSpecIso B).inv.hom a) ≫
            exteriorCotangentSheafPullbackMap f g n := by
  let f := affineStructuralMap k A
  let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  exact (mem_specQuotientKernel_iff A B φ z hz J hJ q a).trans
    (quotientDifferentialSection_apply_eq_zero_iff_factorization f g n J hJ q
      ((Scheme.ΓSpecIso B).inv.hom a))

end
end EnvelopeProperty.Char0.RoundedCanonicalModule
