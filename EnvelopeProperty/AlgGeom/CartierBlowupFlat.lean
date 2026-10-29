/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Algebra.DedekindBlowupChartFlat
import Hironaka.Scheme.BlowUp.Glue.Global
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Actual whole blowup flatness over the original Dedekind spectrum -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.IdealSheafData.blowUp
variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable {X : Scheme.{u}} (I : X.IdealSheafData) (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]

/-- Every actual global blowup chart is flat over the same original Dedekind base. -/
theorem chart_flat_over_dedekind (U : X.affineOpens) (a : I.ideal U) :
    Flat (chart I U a ≫ I.blowUpπ ≫ f) := by
  let A := Γ(X, U)
  let φ : CommRingCat.of R ⟶ CommRingCat.of A :=
    (Scheme.Spec.preimage (U.2.fromSpec ≫ f)).unop
  have hφ : Spec.map φ = U.2.fromSpec ≫ f := Scheme.Spec.map_preimage _
  let := φ.hom.toAlgebra
  have hφflat : Flat (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : Module.Flat R A := RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hφflat)
  have : Module.Flat R (affineBlowUpAlgebra (I.ideal U) a) :=
    EnvelopeProperty.affineBlowUpAlgebra_flat_over_dedekind (I.ideal U) a
  have hc : Flat (Spec.map (CommRingCat.ofHom
      (algebraMap R (affineBlowUpAlgebra (I.ideal U) a)))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have he : chart I U a ≫ I.blowUpπ ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (affineBlowUpAlgebra (I.ideal U) a))) := by
    rw [← Category.assoc, chart_π, Category.assoc, Category.assoc,
      IsAffineOpen.isoSpec_inv_ι_assoc, ← hφ, ← Spec.map_comp]
    rfl
  exact he.symm ▸ hc

/-- The entire original blowup of any ideal on a flat original scheme is
flat over the same Dedekind spectrum, with no domain or reduction assumption. -/
theorem flat_over_dedekind : Flat (I.blowUpπ ≫ f) := by
  let C := fun i : Σ U : X.affineOpens, I.ideal U => (chart I i.1 i.2).opensRange
  have hC : iSup C = ⊤ := by
    apply top_unique
    intro b _hb
    obtain ⟨U, hU⟩ := exists_affineOpens_mem (I.blowUpπ b)
    have hmem : b ∈ ⨆ a : I.ideal U, (chart I U a).opensRange := by
      rw [iSup_opensRange_chart]
      exact hU
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hmem
    exact Opens.mem_iSup.mpr ⟨⟨U, a⟩, ha⟩
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Flat) C hC
  intro i
  let j := chart I i.1 i.2
  change Flat (j.opensRange.ι ≫ I.blowUpπ ≫ f)
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac j (Scheme.Opens.ι j.opensRange)
    (congr_arg Opens.carrier (Scheme.Opens.opensRange_ι j.opensRange).symm), Category.assoc]
  have : IsIso (IsOpenImmersion.isoOfRangeEq j (Scheme.Opens.ι j.opensRange)
    (congr_arg Opens.carrier (Scheme.Opens.opensRange_ι j.opensRange).symm)).inv := inferInstance
  have : Flat (j ≫ I.blowUpπ ≫ f) := chart_flat_over_dedekind I f i.1 i.2
  infer_instance

end AlgebraicGeometry.Scheme.IdealSheafData.blowUp
