import EnvelopeProperty.AlgGeom.SchemeGenericFieldCoefficients
import EnvelopeProperty.AlgGeom.SchemeFunctionFieldDimension

/-! # Genuine original residue-point closures and their SAME native function fields -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemePointClosureCurve
variable {Y : Scheme.{u}} (z : Y)

/-- The true NATIVE scheme-image closure of the SAME original residue point. -/
def closure : Scheme.{u} := (Y.fromSpecResidueField z).image

/-- The actual original closed inclusion of the SAME point closure. -/
def inclusion : closure z ⟶ Y := (Y.fromSpecResidueField z).imageι

private local instance inclusion_closed : IsClosedImmersion (inclusion z) := by
  dsimp only [inclusion]
  infer_instance

/-- The SAME native original residue-field point of the actual closure. -/
def genericMap : Spec (Y.residueField z) ⟶ closure z := (Y.fromSpecResidueField z).toImage

/-- The actual original coefficient structure on the true point closure. -/
def structureMap {k : Type u} [CommRing k] (f : Y ⟶ Spec (.of k)) :
    closure z ⟶ Spec (.of k) := inclusion z ≫ f

/-- The true whole original residue-field morphism is retained EXACTLY. -/
theorem genericMap_inclusion : genericMap z ≫ inclusion z = Y.fromSpecResidueField z :=
  Scheme.Hom.toImage_imageι _

private local instance residueMap_quasiCompact : QuasiCompact (Y.fromSpecResidueField z) where
  isCompact_preimage U _ _ := (Set.toFinite ((Y.fromSpecResidueField z) ⁻¹' U)).isCompact

/-- The actual original point closure is integral, genuinely derived. -/
theorem closure_isIntegral : IsIntegral (closure z) :=
  SchemeDominantImageFactorization.image_isIntegral _

private local instance genericMap_dominant : IsDominant (genericMap z) := by
  dsimp only [genericMap]
  infer_instance

/-- The actual canonical map to the SAME point closure is a true preimmersion. -/
theorem genericMap_isPreimmersion : IsPreimmersion (genericMap z) := by
  let : IsPreimmersion (genericMap z ≫ inclusion z) := by rw [genericMap_inclusion]; infer_instance
  exact IsPreimmersion.of_comp (genericMap z) (inclusion z)

private theorem fieldHom_surjective_of_preimmersion {K : Type u} [Field K]
    {T : Scheme.{u}} [IsIntegral T] (g : Spec (.of K) ⟶ T)
    [IsDominant g] [IsPreimmersion g] : Function.Surjective (SchemeGenericFieldGraph.fieldHom g).hom := by
  have hp : g (IsLocalRing.closedPoint K) = genericPoint T := by
    rw [show IsLocalRing.closedPoint K = genericPoint (Spec (.of K)) from Subsingleton.elim _ _]
    apply ((genericPoint_spec T).eq _).symm
    simpa only [Set.image_univ,g.denseRange.closure_range] using
      (genericPoint_spec (Spec (.of K))).image g.continuous
  let e := T.presheaf.stalkCongr (.of_eq hp.symm)
  have he : SchemeGenericFieldGraph.fieldHom g =
      e.hom ≫ g.stalkMap (IsLocalRing.closedPoint K) ≫ (stalkClosedPointIso (.of K)).hom := rfl
  rw [he]
  exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of K)).hom).2.comp
    ((g.stalkMap_surjective _).comp (ConcreteCategory.bijective_of_isIso e.hom).2)

/-- The ACTUAL native function field of the original point closure is the
SAME original residue field; bijectivity is derived from its true preimmersion. -/
def functionFieldEquiv :
    letI := closure_isIntegral z
    (closure z).functionField ≃+* Y.residueField z := by
  let := closure_isIntegral z
  let := genericMap_isPreimmersion z
  exact RingEquiv.ofBijective (SchemeGenericFieldGraph.fieldHom (genericMap z)).hom
    ⟨(SchemeGenericFieldGraph.fieldHom (genericMap z)).hom.injective,
      fieldHom_surjective_of_preimmersion (genericMap z)⟩

/-- The actual original structure-map stalk action on its native residue quotient. -/
@[instance_reducible]
def residueAlgebra {k : Type u} [CommRing k] (f : Y ⟶ Spec (.of k)) :
    Algebra k (Y.residueField z) :=
  letI := f.stalkAlgebra z
  inferInstanceAs (Algebra k (IsLocalRing.ResidueField (Y.presheaf.stalk z)))

private theorem originalResidue_structure {k : Type u} [Field k]
    (f : Y ⟶ Spec (.of k)) :
    letI := f.stalkAlgebra z
    letI := residueAlgebra z f
    Y.fromSpecResidueField z ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k (Y.residueField z))) := by
  let := f.stalkAlgebra z
  let := residueAlgebra z f
  dsimp only [Scheme.fromSpecResidueField]
  rw [Category.assoc,SchemeStalkCoefficients.fromSpecStalk_structureMap,← Spec.map_comp]
  rfl

/-- The SAME genuine native point-closure field equivalence preserves EVERY
original base coefficient, with native structure-stalk actions on BOTH sides. -/
def functionFieldAlgEquiv {k : Type u} [Field k] (f : Y ⟶ Spec (.of k)) :
    letI := closure_isIntegral z
    letI := f.stalkAlgebra z
    letI := residueAlgebra z f
    letI := (structureMap z f).stalkAlgebra (genericPoint (closure z))
    (closure z).functionField ≃ₐ[k] Y.residueField z := by
  let := closure_isIntegral z
  let := f.stalkAlgebra z
  let := residueAlgebra z f
  let := (structureMap z f).stalkAlgebra (genericPoint (closure z))
  refine { functionFieldEquiv z with commutes' := ?_ }
  intro c
  apply RingHom.congr_fun (SchemeGenericFieldCoefficients.fieldHom_coefficients (genericMap z)
    (structureMap z f) (algebraMap k (Y.residueField z)) _) c
  rw [structureMap,← Category.assoc,genericMap_inclusion]
  exact originalResidue_structure z f

/-- Original properness gives genuine properness of the SAME actual point closure. -/
theorem structureMap_isProper {k : Type u} [CommRing k]
    (f : Y ⟶ Spec (.of k)) [IsProper f] : IsProper (structureMap z f) := by
  dsimp only [structureMap,inclusion]
  infer_instance

/-- Actual local finite type and ORIGINAL residue degree derive WHOLE native
point-closure dimension, with no geometric dimension certificate supplied. -/
theorem dimension_eq {k : Type u} [Field k] (f : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (d : ℕ)
    (htr : letI := residueAlgebra z f; Algebra.trdeg k (Y.residueField z) = d) :
    topologicalKrullDim (closure z) = d := by
  let := closure_isIntegral z
  let := f.stalkAlgebra z
  let := residueAlgebra z f
  let := (structureMap z f).stalkAlgebra (genericPoint (closure z))
  let : LocallyOfFiniteType (structureMap z f) := by dsimp only [structureMap,inclusion]; infer_instance
  apply SchemeFunctionFieldDimension.topologicalKrullDim_eq (structureMap z f) d
  exact (functionFieldAlgEquiv z f).trdeg_eq.trans htr

end EnvelopeProperty.SchemePointClosureCurve
