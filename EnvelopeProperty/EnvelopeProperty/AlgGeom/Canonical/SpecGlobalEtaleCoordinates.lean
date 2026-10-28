import EnvelopeProperty.AlgGeom.Canonical.AffineCanonicalFrame
import EnvelopeProperty.Char0.EtaleDifferentials

/-! # The SAME original affine coordinate ring in its original spectrum sections -/

open CategoryTheory AlgebraicGeometry Opposite

namespace EnvelopeProperty.CanonicalGeometry

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (k : Type u) [Field k] (A : CommRingCat.{u}) [Algebra k A]

/-- The SAME actual native ΓSpec isomorphism is an actual algebra
isomorphism for the ORIGINAL structural scheme map's actual section algebra. -/
def affineGammaSpecAlgEquiv :
    letI := affineChartAlgebra (affineStructuralMap k A) ⊤
    A ≃ₐ[k] Γ(Spec A, ⊤) := by
  letI := affineChartAlgebra (affineStructuralMap k A) ⊤
  refine { (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro a
  change (Scheme.ΓSpecIso A).inv.hom (algebraMap k A a) =
    ((schemeConstantPresheafMap (affineStructuralMap k A)).app (.op ⊤)).hom a
  have hmap : affineCoordinateMap A (.op ⊤) = (Scheme.ΓSpecIso A).inv := by
    unfold affineCoordinateMap
    rw [show (⊤ : (Spec A).Opens).leTop = 𝟙 ⊤ from Subsingleton.elim _ _,
      op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  have hs : affineBaseRingMap k A ≫ (Scheme.ΓSpecIso A).inv =
      (schemeConstantPresheafMap (affineStructuralMap k A)).app (.op ⊤) := by
    rw [← hmap]
    exact affineBaseRingMap_coordinateMap k A (.op ⊤)
  exact congrArg (fun m => m.hom a) hs

/-- Actual original etale coordinates remain genuinely etale in the SAME
original spectrum section ring, with its original structural algebra. -/
theorem affineGammaSpec_etaleCoordinates {n : ℕ} (v : Fin n → A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    letI := affineChartAlgebra (affineStructuralMap k A) ⊤
    (MvPolynomial.aeval (R := k) (fun i => affineGammaSpecAlgEquiv k A (v i))).toRingHom.Etale := by
  let := affineChartAlgebra (affineStructuralMap k A) ⊤
  let e := affineGammaSpecAlgEquiv k A
  have he : e.toRingHom.Etale := RingHom.Etale.of_bijective e.bijective
  have hcomp : (MvPolynomial.aeval (R := k) (fun i => e (v i))).toRingHom =
      e.toRingHom.comp (MvPolynomial.aeval (R := k) v).toRingHom := by
    exact congrArg AlgHom.toRingHom (MvPolynomial.comp_aeval v e.toAlgHom).symm
  rw [hcomp]
  exact RingHom.Etale.stableUnderComposition _ _ hv he

/-- The ORIGINAL etale coordinate map DERIVES the genuine original
cotangent basis on the SAME actual whole spectrum section ring. -/
def affineGammaSpecEtaleBasis {n : ℕ} (v : Fin n → A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    letI := affineChartAlgebra (affineStructuralMap k A) ⊤
    Module.Basis (Fin n) Γ(Spec A, ⊤) (KaehlerDifferential k Γ(Spec A, ⊤)) :=
  letI := affineChartAlgebra (affineStructuralMap k A) ⊤
  Char0.etaleDifferentialBasis (fun i => affineGammaSpecAlgEquiv k A (v i))
    (affineGammaSpec_etaleCoordinates k A v hv)

/-- Every original coordinate differential is retained under the SAME
original ΓSpec coefficient map; no basis matching premise. -/
theorem affineGammaSpecEtaleBasis_apply {n : ℕ} (v : Fin n → A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (i : Fin n) :
    letI := affineChartAlgebra (affineStructuralMap k A) ⊤
    affineGammaSpecEtaleBasis k A v hv i =
      KaehlerDifferential.D k Γ(Spec A, ⊤) (affineGammaSpecAlgEquiv k A (v i)) :=
  by
    let := affineChartAlgebra (affineStructuralMap k A) ⊤
    exact Char0.etaleDifferentialBasis_apply _ _ i

end
end EnvelopeProperty.CanonicalGeometry
