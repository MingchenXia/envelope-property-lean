import EnvelopeProperty.Vanishing.NadelPrincipalizationMultiplierChart
import EnvelopeProperty.Vanishing.NadelPrincipalizationRestrictionCore

/-! # The original global BP on its actual function-field affine chart

Both principalization triples and the full original ideal pullback are
constructed internally. Native BP functoriality, empty-blow-up deletion,
and the actual last-stage pullback square give the whole comparison.
-/

open AlgebraicGeometry CategoryTheory Scheme.BlowUpSequence

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelPrincipalizationRestriction

set_option backward.isDefEq.respectTransparency false

private theorem pullbackIso_triangle {A B C D : Scheme.{u}}
    (p : B ⟶ D) (g : C ⟶ D)
    (e : A ≅ CategoryTheory.Limits.pullback p g) (q : A ⟶ C)
    (he : e.hom ≫ CategoryTheory.Limits.pullback.snd p g = q) :
    (e.hom ≫ CategoryTheory.Limits.pullback.fst p g) ≫ p = q ≫ g := by
  rw [Category.assoc, CategoryTheory.Limits.pullback.condition, ← Category.assoc, he]

private theorem pullbackIso_isPullback {A B C D : Scheme.{u}}
    (p : B ⟶ D) (g : C ⟶ D)
    (e : A ≅ CategoryTheory.Limits.pullback p g) (q : A ⟶ C)
    (he : e.hom ≫ CategoryTheory.Limits.pullback.snd p g = q) :
    IsPullback (e.hom ≫ CategoryTheory.Limits.pullback.fst p g) q p g := by
  apply (IsPullback.of_hasPullback p g).of_iso'
    e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id] using he
  · simp
  · simp

private theorem structure_triangle {A B C D E : Scheme.{u}}
    (a : A ⟶ B) (p : B ⟶ D) (q : A ⟶ C) (g : C ⟶ D)
    (f : D ⟶ E) (fC : C ⟶ E) (ha : a ≫ p = q ≫ g) (hg : g ≫ f = fC) :
    a ≫ p ≫ f = q ≫ fC := by
  rw [← Category.assoc, ha, Category.assoc, hg]

private theorem ideal_comap_square {A B C D : Scheme.{u}}
    (I : D.IdealSheafData) (J : C.IdealSheafData)
    (a : A ⟶ B) (p : B ⟶ D) (q : A ⟶ C) (g : C ⟶ D)
    (ha : a ≫ p = q ≫ g) (hI : I.comap g = J) :
    (I.comap p).comap a = J.comap q := by
  rw [← Scheme.IdealSheafData.comap_comp, ha, Scheme.IdealSheafData.comap_comp, hI]

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (U : X.affineOpens) [Nonempty U.1]

/-- The actual affine triple of the original function-field chart and ideal. -/
def affineTriple : Triple k := by
  let := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
  exact Char0.affinePrincipalizationTriple
    (NadelPrincipalizationAffineChart.structureMap f U) n
    (NadelPrincipalizationAffineChart.ideal f I U)
    (NadelPrincipalizationAffineChart.ideal_ne_bot f I hI U)

/-- The native BP of the SAME actual chart triple; it is not supplied as local data. -/
def affineSequence : (Spec (.of (NadelPrincipalizationAffineChart.algebra f U))).BlowUpSequence :=
  Hironaka.Sequence.BP (affineTriple f n I hI U)

omit [CharZero k] in
/-- The WHOLE actual chart triple carries the precise original pullback data. -/
theorem affineTriple_isPullbackOf :
    (affineTriple f n I hI U).IsPullbackOf (NadelPrincipalization.originalTriple f hp n I hI)
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
      ((NadelPrincipalization.sequence f hp n I hI).pullback
        (NadelPrincipalizationAffineChart.map f U)).eraseEmpty :=
  Hironaka.Sequence.BP_pullback_eraseEmpty (NadelPrincipalization.originalTriple f hp n I hI)
    (affineTriple f n I hI U) (NadelPrincipalizationAffineChart.map f U)
    (affineTriple_isPullbackOf f hp n I hI U)

private theorem last_transport {Z : Scheme.{u}} {S T : Z.BlowUpSequence} (he : S = T) :
    (eqToIso (congrArg Scheme.BlowUpSequence.last he)).hom ≫ T.composite = S.composite := by
  subst T
  simp

/-- The actual affine BP last scheme is the actual categorical restriction
of the SAME original global BP composite. -/
def lastIso : (affineSequence f n I hI U).last ≅
    CategoryTheory.Limits.pullback (NadelPrincipalization.sequence f hp n I hI).composite
      (NadelPrincipalizationAffineChart.map f U) :=
  eqToIso (congrArg Scheme.BlowUpSequence.last
      (affineSequence_eq_pullback_eraseEmpty f hp n I hI U)) ≪≫
    NadelPrincipalizationRestrictionCore.erasedPullbackLastIso
      (NadelPrincipalization.sequence f hp n I hI) (NadelPrincipalizationAffineChart.map f U)

/-- The whole native affine projection is the SAME original affine BP composite. -/
theorem lastIso_snd :
    (lastIso f hp n I hI U).hom ≫ CategoryTheory.Limits.pullback.snd _ _ =
      (affineSequence f n I hI U).composite := by
  rw [lastIso, Iso.trans_hom, Category.assoc,
    NadelPrincipalizationRestrictionCore.erasedPullbackLastIso_snd]
  exact last_transport (affineSequence_eq_pullback_eraseEmpty f hp n I hI U)

/-- The actual affine BP enters the last scheme of the original global BP. -/
def lastMap : (affineSequence f n I hI U).last ⟶
    (NadelPrincipalization.sequence f hp n I hI).last :=
  (lastIso f hp n I hI U).hom ≫ CategoryTheory.Limits.pullback.fst _ _

/-- The whole actual diagram retains the original global and affine BP composites. -/
theorem lastMap_composite :
    lastMap f hp n I hI U ≫ (NadelPrincipalization.sequence f hp n I hI).composite =
      (affineSequence f n I hI U).composite ≫ NadelPrincipalizationAffineChart.map f U :=
  pullbackIso_triangle (NadelPrincipalization.sequence f hp n I hI).composite
    (NadelPrincipalizationAffineChart.map f U) (lastIso f hp n I hI U)
    (affineSequence f n I hI U).composite (lastIso_snd f hp n I hI U)

/-- The actual local/global BP diagram is cartesian on the whole original chart. -/
theorem last_isPullback :
    IsPullback (lastMap f hp n I hI U) (affineSequence f n I hI U).composite
      (NadelPrincipalization.sequence f hp n I hI).composite
      (NadelPrincipalizationAffineChart.map f U) :=
  pullbackIso_isPullback (NadelPrincipalization.sequence f hp n I hI).composite
    (NadelPrincipalizationAffineChart.map f U) (lastIso f hp n I hI U)
    (affineSequence f n I hI U).composite (lastIso_snd f hp n I hI U)

/-- The same actual affine BP chart is an open subscheme of the global BP last scheme. -/
theorem lastMap_isOpenImmersion : IsOpenImmersion (lastMap f hp n I hI U) := by
  dsimp only [lastMap]
  infer_instance

/-- Both original field structures are retained by the whole last-stage comparison. -/
theorem lastMap_structure :
    lastMap f hp n I hI U ≫ (NadelPrincipalization.sequence f hp n I hI).composite ≫ f =
      (affineSequence f n I hI U).composite ≫
        NadelPrincipalizationAffineChart.structureMap f U :=
  structure_triangle (lastMap f hp n I hI U) (NadelPrincipalization.sequence f hp n I hI).composite
    (affineSequence f n I hI U).composite (NadelPrincipalizationAffineChart.map f U) f
    (NadelPrincipalizationAffineChart.structureMap f U)
    (lastMap_composite f hp n I hI U) (NadelPrincipalizationAffineChart.map_structure f U)

/-- The SAME original full total-transform ideal restricts to the SAME
original affine total transform, through the actual last-stage map. -/
theorem totalTransform_comap :
    (I.comap (NadelPrincipalization.sequence f hp n I hI).composite).comap
        (lastMap f hp n I hI U) =
      (specIdealSheaf (NadelPrincipalizationAffineChart.ideal f I U)).comap
        (affineSequence f n I hI U).composite :=
  ideal_comap_square I (specIdealSheaf (NadelPrincipalizationAffineChart.ideal f I U))
    (lastMap f hp n I hI U) (NadelPrincipalization.sequence f hp n I hI).composite
    (affineSequence f n I hI U).composite (NadelPrincipalizationAffineChart.map f U)
    (lastMap_composite f hp n I hI U) (NadelPrincipalizationAffineChart.comap_ideal f I U)

end EnvelopeProperty.Vanishing.NadelPrincipalizationRestriction
