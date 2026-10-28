import EnvelopeProperty.Projective.NativeBaseChange
import EnvelopeProperty.AlgGeom.ReesFormalRestriction
import ModularCurves.ForMathlib.ProjectiveFactorization

/-! # Genuine projective factorizations of the actual schematic Rees family -/

open CategoryTheory AlgebraicGeometry Limits
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.FormalFunctionsProjectiveFamily

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} {d : ℕ}
variable (i : X ⟶ ProjBerk.NativeProjectiveScheme R d)

/-- The actual original projective embedding after genuine Rees coefficient
base change and the actual polynomial-projective scalar isomorphism. -/
def ambientEmbedding :
    FcReesFormalFamily.ambient I (i ≫ ProjBerk.nativeStructureMap (R := R) (n := d)) ⟶
      ProjBerk.NativeProjectiveScheme (reesAlgebra I) d :=
  FcReesFormalRestriction.ambientMap I (ProjBerk.nativeStructureMap (R := R) (n := d)) i ≫
    (ProjBerk.isPullback_nativeCoefficientBaseChange (n := d)
      (algebraMap R (reesAlgebra I))).isoPullback.inv

/-- The constructed ambient map is a genuine closed immersion whenever
the same original projective embedding is a closed immersion. -/
instance ambientEmbedding_isClosedImmersion [IsClosedImmersion i] :
    IsClosedImmersion (ambientEmbedding I i) := by
  have : IsClosedImmersion
      (FcReesFormalRestriction.ambientMap I (ProjBerk.nativeStructureMap (R := R) (n := d)) i) :=
    MorphismProperty.of_isPullback
      (FcReesFormalRestriction.ambientMap_isPullback I
        (ProjBerk.nativeStructureMap (R := R) (n := d)) i) inferInstance
  unfold ambientEmbedding
  infer_instance

/-- The entire coefficient projection is the SAME original Rees-base projection. -/
theorem ambientEmbedding_projection :
    ambientEmbedding I i ≫ ProjBerk.nativeStructureMap (R := reesAlgebra I) (n := d) =
      FcReesFormalFamily.ambientProjection I
        (i ≫ ProjBerk.nativeStructureMap (R := R) (n := d)) := by
  let hP := ProjBerk.isPullback_nativeCoefficientBaseChange (n := d)
    (algebraMap R (reesAlgebra I))
  let E := hP.isoPullback
  have hE : E.inv ≫ ProjBerk.nativeStructureMap (R := reesAlgebra I) (n := d) =
      pullback.snd (ProjBerk.nativeStructureMap (R := R) (n := d))
        (FcReesFormalFamily.reesBase I) := by
    apply (cancel_epi E.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact hP.isoPullback_hom_snd.symm
  change (FcReesFormalRestriction.ambientMap I
      (ProjBerk.nativeStructureMap (R := R) (n := d)) i ≫ E.inv) ≫ _ = _
  rw [Category.assoc, hE]
  exact FcReesFormalRestriction.ambientMap_projection I
    (ProjBerk.nativeStructureMap (R := R) (n := d)) i

/-- The actual schematic Rees family is projectively factored because the
original morphism is projectively factored; no projectivity of the family is assumed. -/
theorem family_isProjectiveFactorization (f : X ⟶ Spec (.of R))
    (hf : IsProjectiveFactorization f) :
    IsProjectiveFactorization (FcReesFormalFamily.familyProjection I f) := by
  obtain ⟨d, i, hi, hif⟩ := hf
  let i' : X ⟶ ProjBerk.NativeProjectiveScheme R d := i
  let : IsClosedImmersion i' := hi
  have hif' : i' ≫ ProjBerk.nativeStructureMap (R := R) (n := d) = f := hif
  rw [← hif']
  have hAmb : IsClosedImmersion (ambientEmbedding I i') := inferInstance
  have hFam : IsClosedImmersion (FcReesFormalFamily.familyImmersion I
    (i' ≫ ProjBerk.nativeStructureMap (R := R) (n := d))) := inferInstance
  refine ⟨d, FcReesFormalFamily.familyImmersion I
    (i' ≫ ProjBerk.nativeStructureMap (R := R) (n := d)) ≫ ambientEmbedding I i',
      @IsClosedImmersion.comp _ _ _ _ _ hFam hAmb, ?_⟩
  change (_ ≫ ambientEmbedding I i') ≫
    ProjBerk.nativeStructureMap (R := reesAlgebra I) (n := d) = _
  rw [Category.assoc, ambientEmbedding_projection]
  rfl

end EnvelopeProperty.FormalFunctionsProjectiveFamily
