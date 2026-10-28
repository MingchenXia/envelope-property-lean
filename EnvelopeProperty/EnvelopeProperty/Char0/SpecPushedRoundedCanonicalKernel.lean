import EnvelopeProperty.Char0.AffineSpecRoundedCanonicalKernel
import EnvelopeProperty.Char0.RoundedCanonicalQuotientOpenCover

/-! # The SAME entire actual geometric pushed quotient kernel in original coefficients -/

open CategoryTheory AlgebraicGeometry Opposite
open EnvelopeProperty.CanonicalGeometry
namespace EnvelopeProperty.Char0.RoundedCanonicalModule
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem wholePushedIdealMapEquivMem {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (a : S) : a ∈ I.map e.toRingHom ↔ e.symm a ∈ I := by
  have hmap := Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective (I := I) (y := a)
  constructor
  · intro ha
    obtain ⟨b, hb, hba⟩ := hmap.mp ha
    have heq : b = e.symm a := e.injective (hba.trans (e.apply_symm_apply a).symm)
    exact heq ▸ hb
  · intro ha
    exact hmap.mpr ⟨e.symm a, ha, e.apply_symm_apply a⟩

variable {k : Type u} [Field k] (A : CommRingCat.{u}) [Algebra k A]
    {Y : Scheme.{u}} (g : Y ⟶ Spec A) {n : ℕ}
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)

/-- The ENTIRE actual original pushed quotient-section kernel in the SAME
original source ring, using literally the original whole pushed map. -/
def specPushedQuotientKernel : Ideal A := by
  let f := affineStructuralMap k A
  letI : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  exact (Scheme.Modules.unitMapKernelIdeal (pushedQuotientDifferentialSection f g n J hJ q)
    ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso A).hom.hom

/-- EVERY original coefficient belongs exactly when SAME entire original
quotient kills its SAME genuine original pulled function on ALL of original Y. -/
theorem mem_specPushedQuotientKernel_iff (a : A) :
    let f := affineStructuralMap k A
    letI : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
    a ∈ specPushedQuotientKernel A g z hz J hJ q ↔
      (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤)
        (g.appTop ((Scheme.ΓSpecIso A).inv.hom a)) = 0 := by
  let f := affineStructuralMap k A
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  have hmem := wholePushedIdealMapEquivMem (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv
    (Scheme.Modules.unitMapKernelIdeal (pushedQuotientDifferentialSection f g n J hJ q)
      ⟨⊤, isAffineOpen_top _⟩) a
  refine hmem.trans ?_
  exact Iff.of_eq (congrArg (fun t => t = 0)
    (pushedQuotientDifferentialSection_app f g n J hJ q ⊤ ((Scheme.ΓSpecIso A).inv.hom a)))

/-- It is the SAME whole original geometric pushed kernel ideal sheaf's
original affine ideal; actual compact denominator clearing is already derived. -/
theorem specPushedQuotientKernel_eq_idealOf
    [QuasiCompact g]
    [SmoothOfRelativeDimension n (g ≫ affineStructuralMap k A)] :
    letI : SmoothOfRelativeDimension n (affineStructuralMap k A) :=
      smoothOfRelativeDimension_of_etale_coordinates z hz
    specPushedQuotientKernel A g z hz J hJ q =
      idealOfSpecSheaf (roundedCanonicalKernelIdeal (affineStructuralMap k A) g n J hJ q) := by
  rfl

end
end EnvelopeProperty.Char0.RoundedCanonicalModule
