import EnvelopeProperty.AlgGeom.SchemeResidueCoefficientTowers
import EnvelopeProperty.Algebra.RelativeBasisCenterFinite

/-! # True finite residue comparison for an original local trait and its center -/
open AlgebraicGeometry CategoryTheory IsLocalRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeTraitResidueFinite
variable {k V : Type u} [Field k] [CommRing V] [IsLocalRing V] [Algebra k V]
  {Y Z : Scheme.{u}}

/-- Actual whole coefficient maps force their original residues into the
SAME actual trait-center residue image; no coefficient-field lift is supplied. -/
theorem coefficient_residue_mem_range (f : Y ⟶ Spec (.of k))
    (q : Spec (.of V) ⟶ Y)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k V)))
    {E : Type u} [CommRing E] (g : Y ⟶ Spec (.of E)) (ρ : E →+* V)
    (hg : q ≫ g = Spec.map (CommRingCat.ofHom ρ)) (e : E) :
    letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) f
    residue V (ρ e) ∈ Set.range (SchemeLocalResidueCoefficients.residueAlgHom f q hq) := by
  let := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) f
  refine ⟨Y.residue _ (SchemeStalkCoefficients.coefficientMap g (q (closedPoint V)) e),?_⟩
  rw [SchemeLocalResidueCoefficients.residueAlgHom_residue]
  exact congrArg (residue V)
    (RingHom.congr_fun (SchemeLocalResidueCoefficients.stalkClosedPointTo_coefficients g q ρ hg) e)

/-- A true relative basis contained in the actual center residue image
makes the SAME original trait residue extension genuinely finite. -/
theorem finite_of_relativeBasis_in_range [Algebra.EssFiniteType k V]
    (p : Y ⟶ Z) (f : Z ⟶ Spec (.of k)) (q : Spec (.of V) ⟶ Y)
    (h : (q ≫ p) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k V)))
    {ι : Type u} (u : ι → ResidueField V)
    (hu : letI := SchemePointClosureCurve.residueAlgebra ((q ≫ p) (closedPoint V)) f
      letI := (SchemeLocalResidueCoefficients.residueAlgHom f (q ≫ p) h).toAlgebra
      IsTranscendenceBasis (Z.residueField ((q ≫ p) (closedPoint V))) u)
    (hrange : letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (p ≫ f)
      ∀ i, u i ∈ Set.range (SchemeLocalResidueCoefficients.residueAlgHom (p ≫ f) q
        (by simpa only [Category.assoc] using h))) :
    letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (p ≫ f)
    letI := (SchemeLocalResidueCoefficients.residueAlgHom (p ≫ f) q
      (by simpa only [Category.assoc] using h)).toAlgebra
    FiniteDimensional (Y.residueField (q (closedPoint V))) (ResidueField V) := by
  let := SchemePointClosureCurve.residueAlgebra ((q ≫ p) (closedPoint V)) f
  let := SchemePointClosureCurve.residueAlgebra (p (q (closedPoint V))) f
  let := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (p ≫ f)
  let α : Z.residueField (p (q (closedPoint V))) →ₐ[k] ResidueField V :=
    SchemeLocalResidueCoefficients.residueAlgHom f (q ≫ p) h
  let γ : Y.residueField (q (closedPoint V)) →ₐ[k] ResidueField V :=
    SchemeLocalResidueCoefficients.residueAlgHom (p ≫ f) q
    (by simpa only [Category.assoc] using h)
  let β : Z.residueField (p (q (closedPoint V))) →ₐ[k] Y.residueField (q (closedPoint V)) :=
    SchemeResidueCoefficientTowers.residueFieldMapAlgHom p f (q (closedPoint V))
  let := α.toAlgebra
  let := β.toAlgebra
  let := γ.toAlgebra
  let : IsScalarTower k (Z.residueField (p (q (closedPoint V)))) (ResidueField V) :=
    IsScalarTower.of_algebraMap_eq fun c => (α.commutes c).symm
  let : IsScalarTower (Z.residueField (p (q (closedPoint V))))
      (Y.residueField (q (closedPoint V))) (ResidueField V) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      AlgHom.congr_fun (SchemeResidueCoefficientTowers.traitResidue_comp p f q h) c
  let : Algebra.EssFiniteType k (ResidueField V) :=
    inferInstanceAs (Algebra.EssFiniteType k (V ⧸ maximalIdeal V))
  let : Algebra.EssFiniteType (Z.residueField (p (q (closedPoint V)))) (ResidueField V) :=
    Algebra.EssFiniteType.of_comp k _ _
  exact RelativeBasisCenterFinite.finite_of_relativeBasis_in_range
    (L := Z.residueField (p (q (closedPoint V))))
    (M := Y.residueField (q (closedPoint V))) (N := ResidueField V) u hu hrange

end EnvelopeProperty.SchemeTraitResidueFinite
