import EnvelopeProperty.AlgGeom.SchemeResidueCoefficientTowers
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-! # Actual original trait-center residue transcendence -/
open AlgebraicGeometry CategoryTheory IsLocalRing Algebra
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeTraitCenterTranscendence
variable {E V : Type u} [Field E] [CommRing V] [IsLocalRing V] [Algebra E V]
  {Y Z : Scheme.{u}} (p : Y ⟶ Z) (f : Z ⟶ Spec (.of E)) (q : Spec (.of V) ⟶ Y)
  (hq : (q ≫ p) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap E V)))

include hq in
/-- The SAME original center residue field has the actual outer transcendence degree,
using the native residue maps and the whole original trait coefficient square. -/
theorem trdeg_eq (d : Cardinal.{u})
    (hZ : letI := SchemePointClosureCurve.residueAlgebra (p (q (closedPoint V))) f
      Algebra.trdeg E (Z.residueField (p (q (closedPoint V)))) = d)
    (hV : Algebra.trdeg E (ResidueField V) = d) :
    letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (p ≫ f)
    Algebra.trdeg E (Y.residueField (q (closedPoint V))) = d := by
  let := SchemePointClosureCurve.residueAlgebra (p (q (closedPoint V))) f
  let := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (p ≫ f)
  let γ := SchemeResidueCoefficientTowers.residueFieldMapAlgHom p f (q (closedPoint V))
  let δ := SchemeLocalResidueCoefficients.residueAlgHom (p ≫ f) q
    (by simpa only [Category.assoc] using hq)
  apply le_antisymm
  · exact (trdeg_le_of_injective δ δ.injective).trans_eq hV
  · exact hZ.symm.trans_le (trdeg_le_of_injective γ γ.injective)

end EnvelopeProperty.SchemeTraitCenterTranscendence
