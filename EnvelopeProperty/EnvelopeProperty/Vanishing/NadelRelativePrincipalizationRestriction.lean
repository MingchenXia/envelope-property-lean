import EnvelopeProperty.Vanishing.NadelRelativePrincipalization
import EnvelopeProperty.Vanishing.NadelPrincipalizationRestriction

/-! # Relative global BP on the same original affine charts

Only the global algebraic triple is generalized from projective-over-k to
separated finite type over k. The original affine triples, BP sequences,
function-field coefficients, ideal comparisons and generic pullback geometry
are reused unchanged. No properness over k or local resolution is an input.
-/
open AlgebraicGeometry CategoryTheory Scheme.BlowUpSequence
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelRelativePrincipalizationRestriction
open NadelPrincipalizationRestriction (affineTriple affineSequence)
set_option backward.isDefEq.respectTransparency false

run_cmd
  let source := `EnvelopeProperty.Vanishing.NadelPrincipalizationRestriction
  for short in [`pullbackIso_triangle, `pullbackIso_isPullback,
      `structure_triangle, `ideal_comap_square, `last_transport] do
    let full := `EnvelopeProperty.Vanishing.NadelPrincipalizationRestriction ++ short
    let original := Lean.mkPrivateNameCore source full
    unless (← Lean.getEnv).contains original do throwError "missing original generic restriction law"
    Lean.Elab.Command.modifyScope fun scope =>
      {scope with openDecls := Lean.OpenDecl.explicit short original :: scope.openDecls}

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [FiniteType f] [IsSeparated f]
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (U : X.affineOpens) [Nonempty U.1]

omit [CharZero k] in
/-- The WHOLE actual chart triple carries the precise original pullback data. -/
theorem affineTriple_isPullbackOf :
    (affineTriple f n I hI U).IsPullbackOf (NadelRelativePrincipalization.originalTriple f n I hI)
      (NadelPrincipalizationAffineChart.map f U) := by
  refine ⟨?_, ?_, ?_⟩
  · change NadelPrincipalizationAffineChart.map f U ≫ f =
      NadelPrincipalizationAffineChart.structureMap f U
    exact NadelPrincipalizationAffineChart.map_structure f U
  · change specIdealSheaf (NadelPrincipalizationAffineChart.ideal f I U) =
      I.comap (NadelPrincipalizationAffineChart.map f U)
    exact (NadelPrincipalizationAffineChart.comap_ideal f I U).symm
  · change Scheme.DivisorFamily.empty _ =
      (Scheme.DivisorFamily.empty X).comap (NadelPrincipalizationAffineChart.map f U)
    exact (empty_comap (NadelPrincipalizationAffineChart.map f U)).symm

/-- Actual BP functoriality on the original open chart retains deletion of
empty blow-ups; no local resolution or comparison hypothesis is supplied. -/
theorem affineSequence_eq_pullback_eraseEmpty :
    affineSequence f n I hI U =
      ((NadelRelativePrincipalization.sequence f n I hI).pullback
        (NadelPrincipalizationAffineChart.map f U)).eraseEmpty :=
  Hironaka.Sequence.BP_pullback_eraseEmpty (NadelRelativePrincipalization.originalTriple f n I hI)
    (affineTriple f n I hI U) (NadelPrincipalizationAffineChart.map f U)
    (affineTriple_isPullbackOf f n I hI U)

/-- The actual affine BP last scheme is the actual categorical restriction
of the SAME original global BP composite. -/
def lastIso : (affineSequence f n I hI U).last ≅
    CategoryTheory.Limits.pullback (NadelRelativePrincipalization.sequence f n I hI).composite
      (NadelPrincipalizationAffineChart.map f U) :=
  eqToIso (congrArg Scheme.BlowUpSequence.last
      (affineSequence_eq_pullback_eraseEmpty f n I hI U)) ≪≫
    NadelPrincipalizationRestrictionCore.erasedPullbackLastIso
      (NadelRelativePrincipalization.sequence f n I hI) (NadelPrincipalizationAffineChart.map f U)

/-- The whole native affine projection is the SAME original affine BP composite. -/
theorem lastIso_snd :
    (lastIso f n I hI U).hom ≫ CategoryTheory.Limits.pullback.snd _ _ =
      (affineSequence f n I hI U).composite := by
  rw [lastIso, Iso.trans_hom, Category.assoc,
    NadelPrincipalizationRestrictionCore.erasedPullbackLastIso_snd]
  exact last_transport (affineSequence_eq_pullback_eraseEmpty f n I hI U)

/-- The actual affine BP enters the last scheme of the original global BP. -/
def lastMap : (affineSequence f n I hI U).last ⟶
    (NadelRelativePrincipalization.sequence f n I hI).last :=
  (lastIso f n I hI U).hom ≫ CategoryTheory.Limits.pullback.fst _ _

/-- The whole actual diagram retains the original global and affine BP composites. -/
theorem lastMap_composite :
    lastMap f n I hI U ≫ (NadelRelativePrincipalization.sequence f n I hI).composite =
      (affineSequence f n I hI U).composite ≫ NadelPrincipalizationAffineChart.map f U :=
  pullbackIso_triangle (NadelRelativePrincipalization.sequence f n I hI).composite
    (NadelPrincipalizationAffineChart.map f U) (lastIso f n I hI U)
    (affineSequence f n I hI U).composite (lastIso_snd f n I hI U)

/-- The actual local/global BP diagram is cartesian on the whole original chart. -/
theorem last_isPullback :
    IsPullback (lastMap f n I hI U) (affineSequence f n I hI U).composite
      (NadelRelativePrincipalization.sequence f n I hI).composite
      (NadelPrincipalizationAffineChart.map f U) :=
  pullbackIso_isPullback (NadelRelativePrincipalization.sequence f n I hI).composite
    (NadelPrincipalizationAffineChart.map f U) (lastIso f n I hI U)
    (affineSequence f n I hI U).composite (lastIso_snd f n I hI U)

/-- The same actual affine BP chart is an open subscheme of the global BP last scheme. -/
theorem lastMap_isOpenImmersion : IsOpenImmersion (lastMap f n I hI U) := by
  dsimp only [lastMap]
  infer_instance

/-- Both original field structures are retained by the whole last-stage comparison. -/
theorem lastMap_structure :
    lastMap f n I hI U ≫ (NadelRelativePrincipalization.sequence f n I hI).composite ≫ f =
      (affineSequence f n I hI U).composite ≫
        NadelPrincipalizationAffineChart.structureMap f U :=
  structure_triangle (lastMap f n I hI U) (NadelRelativePrincipalization.sequence f n I hI).composite
    (affineSequence f n I hI U).composite (NadelPrincipalizationAffineChart.map f U) f
    (NadelPrincipalizationAffineChart.structureMap f U)
    (lastMap_composite f n I hI U) (NadelPrincipalizationAffineChart.map_structure f U)

/-- The SAME original full total-transform ideal restricts to the SAME
original affine total transform, through the actual last-stage map. -/
theorem totalTransform_comap :
    (I.comap (NadelRelativePrincipalization.sequence f n I hI).composite).comap
        (lastMap f n I hI U) =
      (specIdealSheaf (NadelPrincipalizationAffineChart.ideal f I U)).comap
        (affineSequence f n I hI U).composite :=
  ideal_comap_square I (specIdealSheaf (NadelPrincipalizationAffineChart.ideal f I U))
    (lastMap f n I hI U) (NadelRelativePrincipalization.sequence f n I hI).composite
    (affineSequence f n I hI U).composite (NadelPrincipalizationAffineChart.map f U)
    (lastMap_composite f n I hI U) (NadelPrincipalizationAffineChart.comap_ideal f I U)

end EnvelopeProperty.Vanishing.NadelRelativePrincipalizationRestriction
