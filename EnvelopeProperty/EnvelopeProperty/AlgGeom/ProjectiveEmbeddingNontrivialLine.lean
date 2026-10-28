import EnvelopeProperty.AlgGeom.ProjectiveGeneratedIdeals
import EnvelopeProperty.AlgGeom.PositivePowerProjectiveGeneration
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness

/-! # The actual embedding line on an original positive-dimensional integral projective scheme -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace MvPolynomial
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveEmbeddingNontrivialLine
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra

private def unitPowerIso (X : Scheme.{u}) : (d : ℕ) →
    CanonicalGeometry.bundleTensorPower (unitObj X) d ≅ unitObj X
  | 0 => Iso.refl _
  | d + 1 => CanonicalGeometry.bundleTensorIso (unitPowerIso X d) (Iso.refl _) ≪≫
      CanonicalGeometry.bundleTensorLeftUnitIso (unitObj X)

private def pulledTwistUnitIso {k : Type u} [Field k] {X : Scheme.{u}} {n : ℕ}
    (i : X ⟶ DeJongAlterations.projectiveSpace k n)
    (e : (Scheme.Modules.pullback i).obj
      (coordinateHyperplaneTwist (R := k) (0 : Fin (n + 1)) 1) ≅ unitObj X) (d : ℕ) :
    (Scheme.Modules.pullback i).obj
      (coordinateHyperplaneTwist (R := k) (0 : Fin (n + 1)) (d : ℤ)) ≅ unitObj X :=
  (Scheme.Modules.pullback i).mapIso
    (PositivePowerProjectiveGeneration.twistPowerIso (0 : Fin (n + 1)) d).symm ≪≫
    BundleTensorPowerPullback.pullbackIso i
      (coordinateHyperplaneTwist (R := k) (0 : Fin (n + 1)) 1) d ≪≫
        BundleTensorPowerPullback.powerIso e d ≪≫ unitPowerIso X d

/-- Triviality of the SAME actual embedding line internally generates every
original ideal, hence makes every such ideal zero or unit. -/
theorem ideal_eq_bot_or_top_of_trivial {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] (p : X ⟶ Spec (.of k)) (h : SchemeLineAmpleness.IsVeryAmple p (unitObj X))
    (I : X.IdealSheafData) : I = ⊥ ∨ I = ⊤ := by
  have hp := h.isProjectiveFactorization
  let : IsProper p := hp.isProper
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : I.toModules.IsFinitePresentation := I.isFinitePresentation_toModules
  let : I.toModules.IsQuasicoherent := inferInstance
  let : I.toModules.IsFiniteType := inferInstance
  obtain ⟨n, i, hi, _hp, ⟨e⟩⟩ := h
  let : IsClosedImmersion i := hi
  obtain ⟨N, hN⟩ := ClosedProjectiveGlobalGeneration.exists_eventual_generatingSections
    i I.toModules (0 : Fin (n + 1))
  obtain ⟨G, _hG⟩ := hN N le_rfl
  let E : I.toModules ⊗ (Scheme.Modules.pullback i).obj
      (coordinateHyperplaneTwist (R := k) (0 : Fin (n + 1)) (N : ℤ)) ≅ I.toModules :=
    (Iso.refl I.toModules ⊗ᵢ
      (pulledTwistUnitIso i e N ≪≫ (ModularCurves.monoidalUnitObjIso X).symm)) ≪≫ ρ_ I.toModules
  exact ProjectiveGeneratedIdeals.eq_bot_or_top_of_generatingSections p hp I (G.ofEpi E.hom)

/-- A genuinely trivial original projective embedding line forces the SAME
original integral scheme to have dimension at most zero. -/
theorem dimension_le_zero_of_trivial {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] (p : X ⟶ Spec (.of k)) (h : SchemeLineAmpleness.IsVeryAmple p (unitObj X)) :
    topologicalKrullDim X ≤ 0 := by
  have hcl (x : X) : closure ({x} : Set X) = Set.univ := by
    let Z : Closeds X := ⟨closure ({x} : Set X), isClosed_closure⟩
    let I := Scheme.IdealSheafData.vanishingIdeal Z
    have hs : (I.support : Set X) = closure ({x} : Set X) :=
      Scheme.IdealSheafData.coe_support_vanishingIdeal Z
    rcases ideal_eq_bot_or_top_of_trivial p h I with hb | ht
    · rw [← hs, hb]
      rfl
    · have hx : x ∈ (I.support : Set X) := hs.symm ▸ subset_closure (Set.mem_singleton x)
      rw [ht] at hx
      exact hx.elim
  let : Subsingleton X := ⟨fun x y => (show IsGenericPoint x Set.univ from hcl x).eq
    (show IsGenericPoint y Set.univ from hcl y)⟩
  exact topologicalKrullDim_zero_of_discreteTopology X

/-- On ANY original integral positive-dimensional scheme the actual original
very-ample embedding line is nontrivial. -/
theorem nontrivial_of_isVeryAmple {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] (p : X ⟶ Spec (.of k)) (L : X.Modules)
    (h : SchemeLineAmpleness.IsVeryAmple p L) (hdim : 0 < topologicalKrullDim X) :
    ¬ Nonempty (L ≅ unitObj X) := by
  rintro ⟨e⟩
  have hu : SchemeLineAmpleness.IsVeryAmple p (unitObj X) := by
    obtain ⟨n, i, hi, hp, ⟨E⟩⟩ := h
    exact ⟨n, i, hi, hp, ⟨E ≪≫ e⟩⟩
  exact (not_lt_of_ge (dimension_le_zero_of_trivial p hu)) hdim
end EnvelopeProperty.ProjectiveEmbeddingNontrivialLine
