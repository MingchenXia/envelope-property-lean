import EnvelopeProperty.AlgGeom.SymmetricProjectiveEmbedding
import Hironaka.Scheme.ProjectiveBundle.Defs
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # The entire original projective bundle over an affine base -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.AffineProjectiveBundleComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def topAffine (X : Scheme.{u}) [IsAffine X] : X.affineOpens :=
  ⟨⊤, isAffineOpen_top X⟩

private def topAffine_isTerminal (X : Scheme.{u}) [IsAffine X] :
    IsTerminal (topAffine X) :=
  IsTerminal.ofUniqueHom (fun U => homOfLE (show U ≤ topAffine X from (show (U : X.Opens) ≤ ⊤ from le_top)))
    (fun _ _ => Subsingleton.elim _ _)

variable {X : Scheme.{u}} [IsAffine X] (E : X.Modules) [E.IsQuasicoherent]

private instance diagram_locallyDirected :
    ((projectiveBundleGluingData E).functor ⋙ Scheme.forget).IsLocallyDirected := inferInstance

private instance diagram_hasColimit : HasColimit (projectiveBundleGluingData E).functor :=
  ⟨_, Scheme.IsLocallyDirected.isColimit (projectiveBundleGluingData E).functor⟩

/-- The actual original global-section symmetric projective bundle is the
WHOLE original glued projective bundle, by the terminal original affine open. -/
def wholeIso : affineProjectiveBundle Γ(X, ⊤) Γ(E, ⊤) ≅ E.projectiveBundle := by
  letI : HasColimit (projectiveBundleGluingData E).functor := diagram_hasColimit E
  letI := isIso_ι_of_isTerminal (topAffine_isTerminal X) (projectiveBundleGluingData E).functor
  exact asIso (colimit.ι (projectiveBundleGluingData E).functor (topAffine X))

/-- The actual whole-bundle comparison preserves the original projection to
the original affine scheme, as an equality of ENTIRE native morphisms. -/
theorem wholeIso_structure :
    (wholeIso E).hom ≫ E.projectiveBundleπ =
      affineProjectiveBundle.π Γ(X, ⊤) Γ(E, ⊤) ≫ X.isoSpec.inv := by
  let : HasColimit (projectiveBundleGluingData E).functor := diagram_hasColimit E
  change colimit.ι (projectiveBundleGluingData E).functor (topAffine X) ≫
      (projectiveBundleGluingData E).toBase = _
  rw [(projectiveBundleGluingData E).ι_toBase]
  change (affineProjectiveBundle.π Γ(X, ⊤) Γ(E, ⊤) ≫
      (isAffineOpen_top X).isoSpec.inv) ≫ (⊤ : X.Opens).ι = _
  rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.fromSpec_top]

/-- The inverse whole-bundle comparison retains the original coefficient
projection to the actual global coefficient spectrum. -/
theorem wholeIso_inv_structure :
    (wholeIso E).inv ≫ affineProjectiveBundle.π Γ(X, ⊤) Γ(E, ⊤) =
      E.projectiveBundleπ ≫ X.isoSpec.hom := by
  apply (cancel_epi (wholeIso E).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, wholeIso_structure, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The original finite quasicoherent whole projective bundle admits a
constructed finite polynomial projective factorization over the actual global base ring. -/
theorem wholeBundle_isProjectiveFactorization [E.IsFiniteType] :
    IsProjectiveFactorization (E.projectiveBundleπ ≫ X.isoSpec.hom) := by
  let : Module.Finite Γ(X, ⊤) Γ(E, ⊤) :=
    Scheme.Modules.globalSections_module_finite_of_isFiniteType_of_isAffine E
  have h := SymmetricProjectiveEmbedding.isProjectiveFactorization
    (R := Γ(X, ⊤)) (M := Γ(E, ⊤))
  have h' := h.comp_isClosedImmersion (wholeIso E).inv inferInstance
  exact (wholeIso_inv_structure E) ▸ h'

/-- Actual original projectivity in the finite quasicoherent bundle sense
implies an ACTUAL finite polynomial factorization over the canonical affine coefficient ring. -/
theorem isProjectiveFactorization_of_isProjective {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsProjective f] : IsProjectiveFactorization (f ≫ X.isoSpec.hom) := by
  obtain ⟨E, hE, hEt, i, hi, hif⟩ := (inferInstance : IsProjective f).exists_isClosedImmersion
  let := hE
  let := hEt
  have h := (wholeBundle_isProjectiveFactorization E).comp_isClosedImmersion i hi
  rw [← Category.assoc, hif] at h
  exact h

end EnvelopeProperty.AffineProjectiveBundleComparison
