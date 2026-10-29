import EnvelopeProperty.Vanishing.RelativeNadelCoverExceptionalAmple
import EnvelopeProperty.Vanishing.NadelOriginalBlowupWeightedExceptionalCons
import EnvelopeProperty.AlgGeom.AmpleTensorLines

/-! # Actual positive exceptional weights over the original relative base -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.MonoidalCategory
open Scheme.Modules Scheme.IdealSheafData Scheme.BlowUpSequence
universe u
namespace EnvelopeProperty.Vanishing.RelativeNadelCoverWeightedAmple
open CanonicalGeometry NadelOriginalBlowupWeightedExceptionalCons
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Constructor induction internally produces every positive exceptional
weight and original ample exponent over the SAME arbitrary R.  Only the
original field finite type and coefficient square are retained. -/
theorem exists_positive_weights_isAmple {k R : Type u}
    [Field k] [CommRing R] [Algebra k R] {X : Scheme.{u}} (S : X.BlowUpSequence) :
    ∀ (p : X ⟶ Spec (.of k)) [FiniteType p] (π : X ⟶ Spec (.of R))
      (_hπ : π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = p) (C : X.Modules),
      SchemeLineAmpleness.IsAmple π C →
      ∃ (w : Fin S.length → ℕ) (r : ℕ), (∀ i, 0 < w i) ∧ 0 < r ∧
        SchemeLineAmpleness.IsAmple (S.composite ≫ π)
          ((sequenceWeightedIdeal S w).toModules ⊗
            (pullback S.composite).obj (bundleTensorPower C r)) := by
  induction S with
  | nil Y =>
      intro p hp π hπ C hC
      let w : Fin (nil Y).length → ℕ := fun i => i.elim0
      refine ⟨w, 1, (fun i => i.elim0), Nat.zero_lt_one, ?_⟩
      have hJ : sequenceWeightedIdeal (nil Y) w = ⊤ := by
        simp [sequenceWeightedIdeal, length]
      let T := (sequenceWeightedIdeal (nil Y) w).toModules ⊗
        (pullback (nil Y).composite).obj (bundleTensorPower C 1)
      let e : T ≅ C :=
        (eqToIso (congrArg Scheme.IdealSheafData.toModules hJ) ⊗ᵢ
          (pullbackId Y).app (bundleTensorPower C 1)) ≪≫
        (((NadelBlowupCanonicalIdealPowers.unitIdealModuleIso (X := Y)).symm ≪≫
          (ModularCurves.monoidalUnitObjIso Y).symm) ⊗ᵢ Iso.refl _) ≪≫
        λ_ (bundleTensorPower C 1) ≪≫ bundleTensorLeftUnitIso C
      change SchemeLineAmpleness.IsAmple (𝟙 Y ≫ π) T
      rw [Category.id_comp]
      exact AmpleTensorLines.ample_of_iso hC e.symm
  | cons Y D rest ih =>
      intro p hp π hπ C hC
      let : IsLocallyNoetherian Y := p.isLocallyNoetherian_of_field
      obtain ⟨r, hr, hC₁⟩ :=
        RelativeNadelCoverExceptionalAmple.exists_positive_isAmple_exceptional_tensor_pullback
          p π hπ D C hC
      let p₁ := D.blowUpπ ≫ p
      let π₁ := D.blowUpπ ≫ π
      let C₁ := D.exceptionalDivisor.toModules ⊗ (pullback D.blowUpπ).obj (bundleTensorPower C r)
      let : IsProper π := hC.isProjectiveFactorization.isProper
      let : IsProper (D.blowUpπ ≫ π) := hC₁.isProjectiveFactorization.isProper
      let : IsProper D.blowUpπ := IsProper.of_comp D.blowUpπ π
      let : FiniteType p₁ := inferInstance
      have hπ₁ : π₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = p₁ := by
        dsimp only [π₁, p₁]
        rw [Category.assoc, hπ]
      obtain ⟨w, s, hw, hs, htail⟩ := ih p₁ π₁ hπ₁ C₁ hC₁
      let wFull : Fin (rest.length + 1) → ℕ := Fin.cons s w
      have hweights : ∀ i : Fin (rest.length + 1), 0 < wFull i := by
        intro i
        exact Fin.cases hs hw i
      refine ⟨wFull, r * s, hweights, Nat.mul_pos hr hs, ?_⟩
      have h := AmpleTensorLines.ample_of_iso htail (consTwistIso D rest C r s w)
      change SchemeLineAmpleness.IsAmple ((rest.composite ≫ D.blowUpπ) ≫ π)
        ((sequenceWeightedIdeal (cons Y D rest) (Fin.cons s w)).toModules ⊗
          (pullback (cons Y D rest).composite).obj (bundleTensorPower C (r * s)))
      simpa only [π₁, Category.assoc] using h

end EnvelopeProperty.Vanishing.RelativeNadelCoverWeightedAmple
