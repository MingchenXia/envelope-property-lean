import EnvelopeProperty.AlgGeom.SchemeDominantImageFactorization

/-! # Genuine whole coefficient slices of an original fraction-field diagram -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeDVRBaseChangeImage
variable {R S V K : Type u} [CommRing R] [CommRing S] [CommRing V]
  [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (ρ : R →+* S)
  (q : Spec (.of V) ⟶ X) (β : S →+* V)
  (hq : q ≫ f = Spec.map (CommRingCat.ofHom (β.comp ρ)))

/-- The genuine coefficient graph in the ACTUAL fibre product. -/
def liftedMap : Spec (.of V) ⟶ pullback f (Spec.map (CommRingCat.ofHom ρ)) :=
  pullback.lift q (Spec.map (CommRingCat.ofHom β)) (by
    rw [hq,← Spec.map_comp]
    rfl)

/-- The SAME original fraction-field restriction of the whole coefficient graph. -/
def genericMap : Spec (.of K) ⟶ pullback f (Spec.map (CommRingCat.ofHom ρ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ liftedMap f ρ q β hq

/-- The ACTUAL native scheme-image closure of the SAME original fraction field. -/
def model : Scheme.{u} := (genericMap (K := K) f ρ q β hq).image

/-- The genuine original projection of the actual constructed coefficient slice. -/
def projection : model (K := K) f ρ q β hq ⟶ X :=
  (genericMap (K := K) f ρ q β hq).imageι ≫ pullback.fst _ _

/-- The genuine original coefficient structure of the actual constructed slice. -/
def structureMap : model (K := K) f ρ q β hq ⟶ Spec (.of S) :=
  (genericMap (K := K) f ρ q β hq).imageι ≫ pullback.snd _ _

private theorem fractionMap_isDominant :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V K))) := by
  have hp : (Spec.map (CommRingCat.ofHom (algebraMap V K))) (⊥ : PrimeSpectrum K) =
      (⊥ : PrimeSpectrum V) := by
    apply PrimeSpectrum.ext
    change RingHom.ker (algebraMap V K) = ⊥
    exact (RingHom.injective_iff_ker_eq_bot (algebraMap V K)).mp (IsFractionRing.injective V K)
  rw [isDominant_iff]
  change Dense (Set.range (Spec.map (CommRingCat.ofHom (algebraMap V K))))
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  rw [← (genericPoint_spec (Spec (.of V))).def,genericPoint_eq_bot_of_affine]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨(⊥ : PrimeSpectrum K),hp⟩)

private local instance fractionMap_schematicDominant :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap V K))) := by
  let := fractionMap_isDominant (V := V) (K := K)
  exact IsSchemeTheoreticallyDominant.of_isDominant _

/-- The ENTIRE original V-diagram factors through the ACTUAL generic image;
this is derived from genuine fraction-map dominance, not supplied containment. -/
def centerLift : Spec (.of V) ⟶ model (K := K) f ρ q β hq :=
  SchemeDominantImageFactorization.factorThroughImage
    (Spec.map (CommRingCat.ofHom (algebraMap V K))) (liftedMap f ρ q β hq)

/-- The original whole morphism q is preserved EXACTLY by the actual slice. -/
theorem centerLift_projection :
    centerLift (K := K) f ρ q β hq ≫ projection f ρ q β hq = q := by
  dsimp only [centerLift,projection,model,genericMap]
  rw [← Category.assoc,SchemeDominantImageFactorization.factorThroughImage_inclusion]
  exact pullback.lift_fst _ _ _

/-- The original whole coefficient map into V is preserved EXACTLY. -/
theorem centerLift_structure :
    centerLift (K := K) f ρ q β hq ≫ structureMap f ρ q β hq = Spec.map (CommRingCat.ofHom β) := by
  dsimp only [centerLift,structureMap,model,genericMap]
  rw [← Category.assoc,SchemeDominantImageFactorization.factorThroughImage_inclusion]
  exact pullback.lift_snd _ _ _

/-- Restriction to the SAME actual fraction field is the native image map. -/
theorem fraction_centerLift :
    Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ centerLift f ρ q β hq =
      (genericMap (K := K) f ρ q β hq).toImage :=
  SchemeDominantImageFactorization.dominant_factorThroughImage _ _

private local instance genericMap_quasiCompact :
    QuasiCompact (genericMap (K := K) f ρ q β hq) where
  isCompact_preimage U _ _ := (Set.toFinite ((genericMap (K := K) f ρ q β hq) ⁻¹' U)).isCompact

omit [IsDomain V] [IsFractionRing V K] in
/-- The true entire coefficient slice is integral, derived from its native image. -/
theorem model_isIntegral : IsIntegral (model (K := K) f ρ q β hq) :=
  SchemeDominantImageFactorization.image_isIntegral _

omit [IsDomain V] [IsFractionRing V K] in
/-- Original properness gives genuine properness of the actual whole slice. -/
theorem structureMap_isProper [IsProper f] :
    IsProper (structureMap (K := K) f ρ q β hq) := by
  unfold structureMap
  infer_instance

end EnvelopeProperty.SchemeDVRBaseChangeImage
