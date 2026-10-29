import EnvelopeProperty.AlgGeom.IdealModuleFunctorial

/-! # Actual whole ideal restriction detected by its original module inclusion -/
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.IdealModuleRestrictionUnit

/-- A true whole restricted original ideal inclusion isomorphism DERIVES
the whole original geometric unit ideal on that same open. -/
theorem comap_eq_top_of_isIso_restrict {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.Opens)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map I.toModulesInclusion)] :
    I.comap U.ι = ⊤ := by
  apply top_le_iff.mp
  intro V a _ha
  rw [I.ideal_comap_of_isOpenImmersion]
  let W : X.affineOpens := ⟨U.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.ι⟩
  let q := (Scheme.Modules.restrictFunctor U.ι).map I.toModulesInclusion
  obtain ⟨s, hs⟩ := (ConcreteCategory.bijective_of_isIso (q.app V.1)).2
    (show Γ(X, U.ι ''ᵁ V.1) from 1)
  change s.val = (1 : Γ(X, U.ι ''ᵁ V.1)) at hs
  have hm : (1 : Γ(X, W.1)) ∈ I.ideal W :=
    (I.isLocallyMem_iff W 1).mp (hs ▸ s.property)
  have ht : I.ideal W = ⊤ := (Ideal.eq_top_iff_one _).mpr hm
  change a ∈ (I.ideal W).comap _
  rw [ht]
  trivial

end EnvelopeProperty.IdealModuleRestrictionUnit
