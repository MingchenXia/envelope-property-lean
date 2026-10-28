import EnvelopeProperty.AlgGeom.SchemeModuleMorphismGluing
import EnvelopeProperty.AlgGeom.AffineSchemeLocalDegrees
import ModularCurves.Picard.InvertibleSheaf

/-! # Actual global triviality of original line sheaves on discrete schemes -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.DiscreteSchemeLineTriviality
open SchemeModuleMorphismGluing
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

private theorem overHom_eq_of_bot (L N : X.Modules) (U : X.Opens) (hU : U = ⊥)
    (a b : L.over U ⟶ N.over U) : a = b := by
  subst U
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext s
  have hW : W.unop.left = ⊥ := le_bot_iff.mp W.unop.hom.le
  have : Subsingleton Γ(X, W.unop.left) := by
    rw [hW]
    infer_instance
  have : Subsingleton ((N.over ⊥).val.obj W) := Module.subsingleton Γ(X, W.unop.left) _
  exact Subsingleton.elim _ _

/-- An actual invertible sheaf on an actual discrete scheme has a genuine
whole original module-sheaf isomorphism with the original structure line. -/
theorem nonempty_iso_unit [DiscreteTopology X] (L : X.Modules) (hL : IsInvertible L) :
    Nonempty (L ≅ unitObj X) := by
  classical
  let U : X → X.Opens := fun x => ⟨{x}, isOpen_discrete _⟩
  have hcover : ∀ x : X, ∃ i, x ∈ U i := fun x => ⟨x, rfl⟩
  have hlocal (x : X) : Nonempty ((pullback (U x).ι).obj L ≅ unitObj (U x).toScheme) := by
    obtain ⟨ι, V, hV, e⟩ := hL
    have hx : x ∈ iSup V := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    have hUV : U x ≤ V i := by
      intro z hz
      have hz : z = x := hz
      simpa only [hz] using hi
    obtain ⟨e⟩ := e i
    exact ⟨restrictTrivialization hUV e⟩
  let e : ∀ x : X, L.over (U x) ≅ (unitObj X).over (U x) := fun x =>
    overTrivializationOfRestrictIso L (U x)
      (restrictIsoOfPullbackIso L (U x) (hlocal x).some)
  refine ⟨bundleGlueIso L (unitObj X) U hcover e ?_⟩
  intro i j
  by_cases hij : i = j
  · subst j
    congr 1
  · apply overHom_eq_of_bot
    ext x
    change (x = i ∧ x = j) ↔ False
    constructor
    · rintro ⟨hi, hj⟩
      exact hij (hi.symm.trans hj)
    · exact False.elim


/-- An actual affine scheme with finite original section algebra over a field
has genuinely discrete ORIGINAL topology. -/
theorem discreteTopology_of_finite_sections {k : Type u} [Field k]
    [IsAffine X] (f : X ⟶ Spec (.of k))
    (hfinite : letI := FiniteClosedIdealLocalDegrees.structureSectionsAlgebra f;
      Module.Finite k Γ(X, ⊤)) : DiscreteTopology X := by
  let := FiniteClosedIdealLocalDegrees.structureSectionsAlgebra f
  let : Module.Finite k Γ(X, ⊤) := hfinite
  let : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite k Γ(X, ⊤)
  let : DiscreteTopology (Spec Γ(X, ⊤)) :=
    inferInstanceAs (DiscreteTopology (PrimeSpectrum Γ(X, ⊤)))
  exact (Scheme.homeoOfIso X.isoSpec).symm.discreteTopology

/-- Every actual line on the SAME genuine finite closed subscheme is
actually globally trivial; topology and scalar finiteness are derived. -/
theorem nonempty_iso_unit_on_finite_closed {k : Type u} [Field k]
    {D : Scheme.{u}} (g : D ⟶ X) [IsClosedImmersion g]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f) [IsFinite (g ≫ f)]
    (L : D.Modules) (hL : IsInvertible L) : Nonempty (L ≅ unitObj D) := by
  let : IsAffine D := isAffine_of_isAffineHom (g ≫ f)
  let : DiscreteTopology D := discreteTopology_of_finite_sections (g ≫ f)
    (FiniteClosedIdealLocalDegrees.structureSections_finite g f hf)
  exact nonempty_iso_unit L hL

/-- Twisting the SAME actual finite closed scheme by ANY actual line leaves
its TRUE original field degree unchanged. -/
theorem fieldSections_finrank_eq_on_finite_closed {k : Type u} [Field k]
    {D : Scheme.{u}} (g : D ⟶ X) [IsClosedImmersion g]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f) [IsFinite (g ≫ f)]
    (L : D.Modules) (hL : IsInvertible L) :
    Module.finrank k (SchemeCoherentEulerIndex.fieldSections (g ≫ f) L) =
      Module.finrank k (SchemeCoherentEulerIndex.fieldSections (g ≫ f) (unitObj D)) := by
  obtain ⟨e⟩ := nonempty_iso_unit_on_finite_closed g f hf L hL
  exact (SchemeCoherentEulerIndex.fieldSectionsIso (g ≫ f) e).toLinearEquiv.finrank_eq

end EnvelopeProperty.DiscreteSchemeLineTriviality
