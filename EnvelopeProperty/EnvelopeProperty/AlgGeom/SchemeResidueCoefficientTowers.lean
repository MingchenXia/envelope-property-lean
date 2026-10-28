import EnvelopeProperty.AlgGeom.SchemeLocalResidueCoefficients

/-! # Actual original stalk and residue maps retain the whole coefficient tower -/
open AlgebraicGeometry CategoryTheory IsLocalRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeResidueCoefficientTowers
variable {R : Type u} [CommRing R] {Y Z : Scheme.{u}}
  (p : Y ⟶ Z) (f : Z ⟶ Spec (.of R)) (z : Y)

/-- The SAME native original stalk map preserves EVERY original base coefficient. -/
theorem stalkMap_coefficients :
    (p.stalkMap z).hom.comp (SchemeStalkCoefficients.coefficientMap f (p z)) =
      SchemeStalkCoefficients.coefficientMap (p ≫ f) z := by
  have hc : CommRingCat.ofHom (SchemeStalkCoefficients.coefficientMap f (p z)) ≫
      p.stalkMap z = CommRingCat.ofHom (SchemeStalkCoefficients.coefficientMap (p ≫ f) z) := by
    apply Spec.map_injective
    rw [Spec.map_comp,← SchemeStalkCoefficients.fromSpecStalk_structureMap,
      Scheme.SpecMap_stalkMap_fromSpecStalk_assoc,
      SchemeStalkCoefficients.fromSpecStalk_structureMap]
  exact congrArg CommRingCat.Hom.hom hc

/-- The SAME native residue map with the actual original structure-stalk scalar actions. -/
def residueFieldMapAlgHom :
    letI := SchemePointClosureCurve.residueAlgebra (p z) f
    letI := SchemePointClosureCurve.residueAlgebra z (p ≫ f)
    Z.residueField (p z) →ₐ[R] Y.residueField z := by
  let := SchemePointClosureCurve.residueAlgebra (p z) f
  let := SchemePointClosureCurve.residueAlgebra z (p ≫ f)
  refine { (p.residueFieldMap z).hom with commutes' := ?_ }
  intro c
  change residue _ ((p.stalkMap z) (SchemeStalkCoefficients.coefficientMap f (p z) c)) =
    residue _ (SchemeStalkCoefficients.coefficientMap (p ≫ f) z c)
  exact congrArg (residue _) (RingHom.congr_fun (stalkMap_coefficients p f z) c)

/-- The genuine original trait residue tower commutes with the SAME original
projection and all original base coefficients, as actual algebra maps. -/
theorem traitResidue_comp {V : Type u} [CommRing V] [IsLocalRing V] [Algebra R V]
    (q : Spec (.of V) ⟶ Y)
    (h : (q ≫ p) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R V))) :
    letI := SchemePointClosureCurve.residueAlgebra ((q ≫ p) (closedPoint V)) f
    letI := SchemePointClosureCurve.residueAlgebra (p (q (closedPoint V))) f
    letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (p ≫ f)
    SchemeLocalResidueCoefficients.residueAlgHom f (q ≫ p) h =
      (SchemeLocalResidueCoefficients.residueAlgHom (p ≫ f) q
        (by simpa only [Category.assoc] using h)).comp
        (residueFieldMapAlgHom p f (q (closedPoint V))) := by
  let := SchemePointClosureCurve.residueAlgebra ((q ≫ p) (closedPoint V)) f
  let := SchemePointClosureCurve.residueAlgebra (p (q (closedPoint V))) f
  let := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (p ≫ f)
  ext s
  exact RingHom.congr_fun (SchemeLocalResidueCoefficients.residueAlgHom_comp q p f h) s

end EnvelopeProperty.SchemeResidueCoefficientTowers
