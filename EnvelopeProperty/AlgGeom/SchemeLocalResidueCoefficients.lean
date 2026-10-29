import EnvelopeProperty.AlgGeom.SchemePointClosureCurve

/-! # Genuine original local-trait center residue coefficient maps -/
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeLocalResidueCoefficients
variable {R V : Type u} [CommRing R] [CommRing V] [IsLocalRing V]
  {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)) (q : Spec (.of V) ⟶ Y)

/-- EVERY original local-trait center coefficient agrees with the whole
original base diagram, with the SAME native stalk map. -/
theorem stalkClosedPointTo_coefficients (α : R →+* V)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom α)) :
    (Scheme.stalkClosedPointTo q).hom.comp
      (SchemeStalkCoefficients.coefficientMap f (q (closedPoint V))) = α := by
  have hc : CommRingCat.ofHom (SchemeStalkCoefficients.coefficientMap f (q (closedPoint V))) ≫
      Scheme.stalkClosedPointTo q = CommRingCat.ofHom α := by
    apply Spec.map_injective
    rw [Spec.map_comp,← SchemeStalkCoefficients.fromSpecStalk_structureMap,
      ← Category.assoc,Scheme.Spec_stalkClosedPointTo_fromSpecStalk,hq]
  exact congrArg CommRingCat.Hom.hom hc

variable [Algebra R V]
  (hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R V)))

/-- The SAME genuine native center-stalk local map preserves all original R-scalars. -/
def stalkClosedPointToAlgHom :
    letI := f.stalkAlgebra (q (closedPoint V))
    Y.presheaf.stalk (q (closedPoint V)) →ₐ[R] V := by
  let := f.stalkAlgebra (q (closedPoint V))
  refine { (Scheme.stalkClosedPointTo q).hom with commutes' := ?_ }
  intro c
  exact RingHom.congr_fun (stalkClosedPointTo_coefficients f q (algebraMap R V) hq) c

/-- The SAME actual native center residue-field map is an R-algebra map,
retaining both actual original quotient actions. -/
def residueAlgHom :
    letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) f
    Y.residueField (q (closedPoint V)) →ₐ[R] ResidueField V := by
  let := f.stalkAlgebra (q (closedPoint V))
  let : IsLocalHom (stalkClosedPointToAlgHom f q hq) :=
    ⟨fun a ha => IsLocalHom.map_nonunit (f := (Scheme.stalkClosedPointTo q).hom) a ha⟩
  exact ResidueField.mapAlgHom (stalkClosedPointToAlgHom f q hq)

/-- EVERY SAME original local stalk element retains its actual original residue value. -/
theorem residueAlgHom_residue (s : Y.presheaf.stalk (q (closedPoint V))) :
    letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) f
    residueAlgHom f q hq (Y.residue _ s) = residue V ((Scheme.stalkClosedPointTo q) s) := rfl

/-- The whole actual generic residue-point map is exactly the native
quotient of the SAME original entire trait diagram. -/
theorem residueAlgHom_fromSpecResidueField :
    letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) f
    Spec.map (CommRingCat.ofHom (residueAlgHom f q hq).toRingHom) ≫
      Y.fromSpecResidueField (q (closedPoint V)) =
    Spec.map (CommRingCat.ofHom (residue V)) ≫ q := by
  let := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) f
  have hc : Y.residue (q (closedPoint V)) ≫
      CommRingCat.ofHom (residueAlgHom f q hq).toRingHom =
      Scheme.stalkClosedPointTo q ≫ CommRingCat.ofHom (residue V) := by
    apply CommRingCat.hom_ext
    rfl
  dsimp only [Scheme.fromSpecResidueField]
  rw [← Spec.map_comp_assoc,hc,Spec.map_comp,Category.assoc,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

/-- Native original center residue maps compose with the SAME original whole
scheme projection, preserving the actual center and all original coefficients. -/
theorem residueAlgHom_comp {Z : Scheme.{u}} (p : Y ⟶ Z) (fZ : Z ⟶ Spec (.of R))
    (h : (q ≫ p) ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R V))) :
    letI := SchemePointClosureCurve.residueAlgebra ((q ≫ p) (closedPoint V)) fZ
    letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (p ≫ fZ)
    (residueAlgHom fZ (q ≫ p) h).toRingHom =
      (residueAlgHom (p ≫ fZ) q (by simpa only [Category.assoc] using h)).toRingHom.comp
        (p.residueFieldMap (q (closedPoint V))).hom := by
  let := SchemePointClosureCurve.residueAlgebra ((q ≫ p) (closedPoint V)) fZ
  let := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (p ≫ fZ)
  ext s
  obtain ⟨a,rfl⟩ := residue_surjective (R := Z.presheaf.stalk ((q ≫ p) (closedPoint V))) s
  change residue V ((Scheme.stalkClosedPointTo (q ≫ p)) a) =
    residue V ((Scheme.stalkClosedPointTo q) ((p.stalkMap (q (closedPoint V))) a))
  exact congrArg (fun h : Z.presheaf.stalk (p (q (closedPoint V))) ⟶ CommRingCat.of V =>
    residue V (h a)) (Scheme.stalkClosedPointTo_comp q p)

end EnvelopeProperty.SchemeLocalResidueCoefficients
