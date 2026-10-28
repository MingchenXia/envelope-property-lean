import EnvelopeProperty.Vanishing.NadelAffineCounitCore

/-! # Actual affine pushforward detects maps out of a coherent module -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelAffineCounitDetection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- All original affine inverse images detect the entire original maps from
a finite-type quasicoherent module.  The target module is arbitrary. -/
theorem hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    {M N : X.Modules} [M.IsQuasicoherent] [M.IsFiniteType]
    {a b : M ⟶ N} (h : (pushforward f).map a = (pushforward f).map b) : a = b := by
  let V (U : Y.affineOpens) : X.Opens := f ⁻¹ᵁ U.1
  have hVa (U : Y.affineOpens) : IsAffineOpen (V U) := U.2.preimage f
  let W (U : Y.affineOpens) : Scheme.{u} := (V U).toScheme
  let j (U : Y.affineOpens) : W U ⟶ X := (V U).ι
  have hcover : ∀ x : X, ∃ (U : Y.affineOpens) (y : W U), j U y = x := by
    intro x
    have hx : f x ∈ ⨆ U : Y.affineOpens, U.1 := by
      rw [iSup_affineOpens_eq_top Y]
      trivial
    obtain ⟨U, hxU⟩ := Opens.mem_iSup.mp hx
    exact ⟨U, ⟨x, hxU⟩, rfl⟩
  apply SchemeModuleOpenCoverDetection.hom_ext W j hcover
  intro U
  have hr : (restrictFunctor (j U)).map a = (restrictFunctor (j U)).map b := by
    obtain ⟨G, _hG⟩ := exists_generatingSections_restrict_of_isFiniteType_of_isAffineOpen
      M ⟨V U, hVa U⟩
    apply NadelAffineCounitCore.hom_ext_of_generators G
    have hU : a.app (V U) = b.app (V U) :=
      congrArg (fun q => q.app U.1) h
    have he : j U ''ᵁ (⊤ : (W U).Opens) = V U := by
      ext x
      constructor
      · rintro ⟨y, _hy, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    have hI : a.app (j U ''ᵁ (⊤ : (W U).Opens)) =
        b.app (j U ''ᵁ (⊤ : (W U).Opens)) := by
      rw [he]
      exact hU
    apply ConcreteCategory.hom_ext
    intro s
    exact ConcreteCategory.congr_hom hI s
  let C := restrictFunctorIsoPullback (j U)
  apply (cancel_epi (C.hom.app M)).mp
  rw [← C.hom.naturality a, ← C.hom.naturality b, hr]

end EnvelopeProperty.Vanishing.NadelAffineCounitDetection
