import EnvelopeProperty.AlgGeom.SchemeModuleOpenCoverFactorization
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorEquivalence
import EnvelopeProperty.AlgGeom.SchemeTensorIdealPullback

/-! # Whole native Cartier factorizations from an actual point-cover of open charts -/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules

noncomputable section
universe u v

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalGluingDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- The actual ideal inclusion tensored with an actual original line is
monic, by the genuine invertible-tensor equivalence. -/
theorem tensorIdealMap_mono {X : Scheme.{u}} (B : X.Modules) (hB : IsInvertible B)
    (I : X.IdealSheafData) :
    Mono (SchemeTensorObjMorphisms.tensorObjIdealMap B I.toModules I.toModulesInclusion) := by
  let := SchemeTensorObjMorphisms.mono_tensorObjMap_left B hB I.toModulesInclusion
  unfold SchemeTensorObjMorphisms.tensorObjIdealMap
  infer_instance

/-- Actual native open pullback preserves every original whole module mono,
through the genuine restriction comparison. -/
theorem pullback_open_mono {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N) [Mono f] : Mono ((pullback j).map f) := by
  let e := restrictFunctorIsoPullback j
  have hmono : Mono f.val := CategoryTheory.preserves_mono_of_preservesLimit
    (SheafOfModules.forget X.ringCatSheaf) f
  have hrestrict : Mono ((restrictFunctor j).map f) := by
    apply (SheafOfModules.forget Y.ringCatSheaf).mono_of_mono_map
    exact PresheafOfModules.mono_of_injective (fun {U} =>
      PresheafOfModules.injective_of_mono f.val (op (j ''ᵁ U.unop)))
  have hm : Mono ((restrictFunctor j).map f ≫ e.hom.app N) := by infer_instance
  rw [e.hom.naturality f] at hm
  exact (mono_comp_iff_of_isIso (e.hom.app M) _).mp hm

variable {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u})
    (j : (i : ι) → Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), j i y = x)

include hcover

/-- Genuine original native point-cover pullbacks detect whole module
isomorphisms; no affine, quasicoherence or exactness premise is supplied. -/
theorem isIso_of_open_cover {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ i, IsIso ((pullback (j i)).map f)) : IsIso f := by
  have : Mono f := by
    constructor
    intro Z a b hab
    apply SchemeModuleOpenCoverDetection.hom_ext Y j hcover
    intro i
    let F := pullback (j i)
    let := hf i
    apply (cancel_mono (F.map f)).mp
    rw [← F.map_comp, ← F.map_comp, hab]
  have : Epi f := by
    constructor
    intro Z a b hab
    apply SchemeModuleOpenCoverDetection.hom_ext Y j hcover
    intro i
    let F := pullback (j i)
    let := hf i
    apply (cancel_epi (F.map f)).mp
    rw [← F.map_comp, ← F.map_comp, hab]
  exact isIso_of_mono_of_epi f

/-- Actual local isomorphism factorizations of the SAME original whole map
through the SAME actual original monomorphism construct a genuine whole
isomorphism. Matching is derived from the original inclusion, never input. -/
theorem exists_iso_of_local_factors {A B I : X.Modules} (inc : I ⟶ B) [Mono inc]
    (δ : A ⟶ B)
    (hloc : ∀ i, ∃ e : (pullback (j i)).obj A ≅ (pullback (j i)).obj I,
      e.hom ≫ (pullback (j i)).map inc = (pullback (j i)).map δ) :
    ∃ e : A ≅ I, e.hom ≫ inc = δ := by
  obtain ⟨θ, hθ⟩ := (SchemeModuleOpenCoverDetection.factorization_iff Y j hcover inc δ).mpr
    (by intro i; obtain ⟨e, he⟩ := hloc i; exact ⟨e.hom, he⟩)
  have hθiso : IsIso θ := by
    apply isIso_of_open_cover Y j hcover
    intro i
    obtain ⟨e, he⟩ := hloc i
    let F := pullback (j i)
    let := pullback_open_mono (j i) inc
    have h : F.map θ = e.hom := by
      apply (cancel_mono (F.map inc)).mp
      rw [← F.map_comp, hθ, he]
    rw [h]
    infer_instance
  let := hθiso
  exact ⟨asIso θ, hθ⟩

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalGluingDescent
