import EnvelopeProperty.AlgGeom.SchemeInvertibleHomSectionNaturality
import EnvelopeProperty.AlgGeom.SchemeTensorIdealShuffle

/-! # Original tensor-ideal section lifts and whole-map factorization -/

open CategoryTheory AlgebraicGeometry

namespace EnvelopeProperty.SchemeInvertibleHomSection

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

/-- An actual lift of the SAME original Hom-section into the ENTIRE
original tensor ideal is equivalent to factorization of the ENTIRE
original map through the SAME original target tensor ideal. -/
theorem equiv_ideal_lift_iff (A : X.Modules) (hA : Scheme.Modules.IsInvertible A)
    (B I : X.Modules) (i : I ⟶ Scheme.Modules.unitObj X) (φ : A ⟶ B) :
    (∃ s : Scheme.Modules.unitObj X ⟶
        Scheme.Modules.tensorObj (Scheme.Modules.tensorObj B (Scheme.Modules.dualObj A)) I,
      s ≫ SchemeTensorObjMorphisms.tensorObjIdealMap
        (Scheme.Modules.tensorObj B (Scheme.Modules.dualObj A)) I i = equiv A hA B φ) ↔
      ∃ θ : A ⟶ Scheme.Modules.tensorObj B I,
        θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap B I i = φ := by
  let e := SchemeTensorObjMorphisms.tensorObjIdealShuffleIso B I (Scheme.Modules.dualObj A)
  have he := equiv_lift_iff A hA φ (SchemeTensorObjMorphisms.tensorObjIdealMap B I i)
  have hh := SchemeTensorObjMorphisms.tensorObjIdealShuffleIso_inclusion B I (Scheme.Modules.dualObj A) i
  constructor
  · rintro ⟨s, hs⟩
    apply he.mp
    refine ⟨s ≫ e.inv, ?_⟩
    rw [hh]
    change (s ≫ e.inv) ≫ (e.hom ≫ _) = _
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hs
  · intro h
    obtain ⟨s, hs⟩ := he.mpr h
    refine ⟨s ≫ e.hom, ?_⟩
    rw [Category.assoc]
    exact (congrArg (fun t ↦ s ≫ t) hh).symm.trans hs

end
end EnvelopeProperty.SchemeInvertibleHomSection
