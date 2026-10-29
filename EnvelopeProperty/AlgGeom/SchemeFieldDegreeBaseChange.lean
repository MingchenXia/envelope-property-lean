import EnvelopeProperty.AffineGlobalSections
import EnvelopeProperty.AlgGeom.FiniteClosedIdealLocalDegrees

/-! # Actual whole finite-scheme field degrees under original scalar base change -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeFieldDegreeBaseChange
open FlatGlobalSections FiniteClosedIdealLocalDegrees SchemeCoherentEulerIndex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k E : Type u} [Field k] [Field E] [Algebra k E]

/-- A whole original scheme isomorphism over the SAME field retains literal original section scalars. -/
def structureSectionsIsoOver {X Y : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (q : Y ⟶ Spec (.of k)) (e : X ≅ Y) (he : e.hom ≫ q = p) :
    letI := structureSectionsAlgebra p
    letI := structureSectionsAlgebra q
    Γ(X, ⊤) ≃ₐ[k] Γ(Y, ⊤) := by
  letI := structureSectionsAlgebra p
  letI := structureSectionsAlgebra q
  refine { (Scheme.Γ.mapIso e.symm.op).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro r
  have hi : e.inv ≫ p = q := by rw [← he, Iso.inv_hom_id_assoc]
  have h := congrArg (fun f : Y ⟶ Spec (.of k) => f.appTop (baseScalar r)) hi
  exact h

/-- Entire original structure-section field ranks agree under the actual whole structure triangle. -/
theorem finrank_sections_isoOver {X Y : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (q : Y ⟶ Spec (.of k)) (e : X ≅ Y) (he : e.hom ≫ q = p) :
    letI := structureSectionsAlgebra p
    letI := structureSectionsAlgebra q
    Module.finrank k Γ(X, ⊤) = Module.finrank k Γ(Y, ⊤) := by
  let := structureSectionsAlgebra p
  let := structureSectionsAlgebra q
  exact (structureSectionsIsoOver p q e he).toLinearEquiv.finrank_eq

/-- TRUE whole original section rank is preserved by ANY original field extension. -/
theorem finrank_sections_baseChange {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [QuasiCompact p] [QuasiSeparated p] :
    letI := structureSectionsAlgebra p
    letI := structureSectionsAlgebra (structureMap (S := E) p)
    Module.finrank E Γ(baseChange (S := E) p, ⊤) = Module.finrank k Γ(X, ⊤) := by
  let := structureSectionsAlgebra p
  let := structureSectionsAlgebra (structureMap (S := E) p)
  rw [← (fieldTensorEquiv (L := E) p).toLinearEquiv.finrank_eq]
  exact Module.finrank_baseChange

/-- The SAME original field-linear structure-module sections retain their true degree after base change. -/
theorem finrank_fieldSections_baseChange {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [QuasiCompact p] [QuasiSeparated p] :
    Module.finrank E (fieldSections (structureMap (S := E) p) (unitObj _)) =
      Module.finrank k (fieldSections p (unitObj X)) := by
  let := structureSectionsAlgebra p
  let := structureSectionsAlgebra (structureMap (S := E) p)
  rw [(structureFieldSectionsIso (structureMap (S := E) p)).toLinearEquiv.finrank_eq,
    (structureFieldSectionsIso p).toLinearEquiv.finrank_eq]
  exact finrank_sections_baseChange p

/-- The original geometric comap closed scheme is the WHOLE scalar pullback of the SAME original closed scheme. -/
def comapSubschemeIso {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) (I : X.IdealSheafData) :
    (I.comap (firstProjection (S := E) p)).subscheme ≅
      baseChange (S := E) (I.subschemeι ≫ p) :=
  I.comapIso (firstProjection (S := E) p) ≪≫
    pullbackSymmetry _ _ ≪≫
      pullbackRightPullbackFstIso p (Spec.map (CommRingCat.ofHom (algebraMap k E))) I.subschemeι

/-- The entire genuine closed-subscheme isomorphism retains the SAME original new-field structure. -/
theorem comapSubschemeIso_structure {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) :
    (comapSubschemeIso (E := E) p I).hom ≫ structureMap (S := E) (I.subschemeι ≫ p) =
      (I.comap (firstProjection (S := E) p)).subschemeι ≫ structureMap (S := E) p := by
  simp only [comapSubschemeIso, Iso.trans_hom, Category.assoc,
    structureMap, pullbackRightPullbackFstIso_hom_snd,
    pullbackSymmetry_hom_comp_snd_assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc]

/-- A SAME actual finite closed subscheme retains its TRUE original whole field degree after scalar pullback. -/
theorem finrank_comapSubscheme {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) [IsFinite (I.subschemeι ≫ p)] :
    letI := structureSectionsAlgebra
      ((I.comap (firstProjection (S := E) p)).subschemeι ≫ structureMap (S := E) p)
    letI := structureSectionsAlgebra (I.subschemeι ≫ p)
    Module.finrank E Γ((I.comap (firstProjection (S := E) p)).subscheme, ⊤) =
      Module.finrank k Γ(I.subscheme, ⊤) := by
  rw [finrank_sections_isoOver _ _ (comapSubschemeIso p I)
    (comapSubschemeIso_structure p I), finrank_sections_baseChange]

/-- The same actual comap closed subscheme is genuinely finite over the new field. -/
theorem comapSubscheme_isFinite {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) [IsFinite (I.subschemeι ≫ p)] :
    IsFinite ((I.comap (firstProjection (S := E) p)).subschemeι ≫ structureMap (S := E) p) := by
  have h : IsFinite ((comapSubschemeIso (E := E) p I).hom ≫
      structureMap (S := E) (I.subschemeι ≫ p)) := inferInstance
  rw [comapSubschemeIso_structure] at h
  exact h

/-- Entire actual structure-module field degree of the SAME comap closed subscheme is preserved. -/
theorem finrank_fieldSections_comapSubscheme {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) [IsFinite (I.subschemeι ≫ p)] :
    Module.finrank E (fieldSections
      ((I.comap (firstProjection (S := E) p)).subschemeι ≫ structureMap (S := E) p)
      (unitObj _)) = Module.finrank k (fieldSections (I.subschemeι ≫ p) (unitObj _)) := by
  let := structureSectionsAlgebra (I.subschemeι ≫ p)
  let := structureSectionsAlgebra
    ((I.comap (firstProjection (S := E) p)).subschemeι ≫ structureMap (S := E) p)
  rw [(structureFieldSectionsIso
      ((I.comap (firstProjection (S := E) p)).subschemeι ≫ structureMap (S := E) p)).toLinearEquiv.finrank_eq,
    (structureFieldSectionsIso (I.subschemeι ≫ p)).toLinearEquiv.finrank_eq]
  exact finrank_comapSubscheme p I

end EnvelopeProperty.SchemeFieldDegreeBaseChange
