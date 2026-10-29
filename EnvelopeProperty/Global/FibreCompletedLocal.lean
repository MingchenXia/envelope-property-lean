import EnvelopeProperty.AlgGeom.FlatLocalFieldLift
import EnvelopeProperty.InfinitesimalSchemes
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Original field fibres as literal complete-local closed fibres

The original residue quotient and actual pullback pasting identify the WHOLE
original field-valued fibre with the order-one maximal-ideal fibre of its
actual complete flat local pullback. No closed-fibre connectedness or
formal-functions comparison is assumed or asserted here.
-/

open CategoryTheory AlgebraicGeometry Limits
noncomputable section
universe u

namespace EnvelopeProperty.FibreCompletedLocal

section Residue

variable {B K : Type u} [CommRing B] [IsLocalRing B] [Field K]
    (γ : B →+* K) (hγs : Function.Surjective γ)
    (hγk : RingHom.ker γ = IsLocalRing.maximalIdeal B)

/-- The actual order-one quotient is the SAME original residue field. -/
def residueEquiv : B ⧸ (IsLocalRing.maximalIdeal B)^1 ≃+* K :=
  (Ideal.quotEquivOfEq (by rw [pow_one]; exact hγk.symm)).trans
    (RingHom.quotientKerEquivOfSurjective hγs)

/-- Every original quotient coefficient retains its entire given residue value. -/
theorem residueEquiv_mk (b : B) :
    residueEquiv γ hγs hγk (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal B)^1) b) = γ b := by
  simp only [residueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- The inverse retains the WHOLE original coefficient quotient map. -/
theorem residueEquiv_symm_comp :
    (residueEquiv γ hγs hγk).symm.toRingHom.comp γ =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal B)^1) := by
  ext b
  apply (residueEquiv γ hγs hγk).injective
  change (residueEquiv γ hγs hγk) ((residueEquiv γ hγs hγk).symm (γ b)) =
    residueEquiv γ hγs hγk (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal B)^1) b)
  rw [RingEquiv.apply_symm_apply, residueEquiv_mk]

/-- The genuine whole affine residue-scheme isomorphism. -/
def residueSpecIso :
    Spec (.of (B ⧸ (IsLocalRing.maximalIdeal B)^1)) ≅ Spec (.of K) :=
  Scheme.Spec.mapIso (residueEquiv γ hγs hγk).symm.toCommRingCatIso.op

/-- The actual residue-scheme isomorphism preserves the ENTIRE coefficient morphism. -/
theorem residueSpecIso_coefficient :
    (residueSpecIso γ hγs hγk).hom ≫ Spec.map (CommRingCat.ofHom γ) =
      InfinitesimalSchemes.coefficientScheme (IsLocalRing.maximalIdeal B) 1 := by
  change Spec.map (CommRingCat.ofHom (residueEquiv γ hγs hγk).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom γ) = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((residueEquiv γ hγs hγk).symm.toRingHom.comp γ)) = _
  rw [residueEquiv_symm_comp]

variable {Y : Scheme.{u}} (g : Y ⟶ Spec (.of B))

/-- Base change of the actual residue isomorphism compares the WHOLE nonreduced fibres. -/
def residuePullbackIso :
    InfinitesimalSchemes.model (IsLocalRing.maximalIdeal B) g 1 ≅
      pullback g (Spec.map (CommRingCat.ofHom γ)) := by
  let e := residueSpecIso γ hγs hγk
  let a := pullback.map g (InfinitesimalSchemes.coefficientScheme (IsLocalRing.maximalIdeal B) 1)
    g (Spec.map (CommRingCat.ofHom γ)) (𝟙 Y) e.hom (𝟙 _)
    (by simp) (by simpa only [Category.comp_id] using (residueSpecIso_coefficient γ hγs hγk).symm)
  exact asIso a

/-- The residue pullback comparison preserves the whole total-scheme projection. -/
theorem residuePullbackIso_projection :
    (residuePullbackIso γ hγs hγk g).hom ≫ pullback.fst _ _ =
      InfinitesimalSchemes.projection (IsLocalRing.maximalIdeal B) g 1 := by
  simp only [residuePullbackIso, InfinitesimalSchemes.projection, asIso_hom,
    pullback.map, pullback.lift_fst, Category.comp_id]

/-- The residue pullback comparison retains the entire original field structure. -/
theorem residuePullbackIso_structure :
    (residuePullbackIso γ hγs hγk g).hom ≫ pullback.snd _ _ =
      InfinitesimalSchemes.structureMap (IsLocalRing.maximalIdeal B) g 1 ≫
        (residueSpecIso γ hγs hγk).hom := by
  simp only [residuePullbackIso, InfinitesimalSchemes.structureMap, asIso_hom,
    pullback.map, pullback.lift_snd]

end Residue

section Tower

variable {A B K : Type u} [CommRing A] [CommRing B] [IsLocalRing B] [Field K]
    [Algebra A B] (w : A →+* K) (γ : B →+* K)
    (hγs : Function.Surjective γ) (hγk : RingHom.ker γ = IsLocalRing.maximalIdeal B)
    (hγw : γ.comp (algebraMap A B) = w)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

omit [IsLocalRing B] in
include hγw in
/-- The entire original A/B/K coefficient triangle gives the exact scheme triangle. -/
theorem coefficientSpec_comp :
    Spec.map (CommRingCat.ofHom γ) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom w) := by
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (γ.comp (algebraMap A B))) = _
  rw [hγw]

/-- The literal completed-local order-one fibre is the WHOLE original field-valued fibre. -/
def closedFibreIso :
    InfinitesimalSchemes.model (IsLocalRing.maximalIdeal B)
      (FlatGlobalSections.structureMap (S := B) f) 1 ≅
        pullback f (Spec.map (CommRingCat.ofHom w)) :=
  residuePullbackIso γ hγs hγk (FlatGlobalSections.structureMap (S := B) f) ≪≫
    pullbackLeftPullbackSndIso f
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) (Spec.map (CommRingCat.ofHom γ)) ≪≫
        pullback.congrHom rfl (coefficientSpec_comp w γ hγw)

/-- The whole closed-fibre isomorphism preserves the original projection to X. -/
theorem closedFibreIso_projection :
    (closedFibreIso w γ hγs hγk hγw f).hom ≫ pullback.fst _ _ =
      InfinitesimalSchemes.projection (IsLocalRing.maximalIdeal B)
        (FlatGlobalSections.structureMap (S := B) f) 1 ≫
          FlatGlobalSections.firstProjection (S := B) f := by
  simp only [closedFibreIso, Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
    pullback.map, pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
  rw [← Category.assoc, residuePullbackIso_projection]

/-- The same whole isomorphism retains the exact original residue-field structure map. -/
theorem closedFibreIso_structure :
    (closedFibreIso w γ hγs hγk hγw f).hom ≫ pullback.snd _ _ =
      InfinitesimalSchemes.structureMap (IsLocalRing.maximalIdeal B)
        (FlatGlobalSections.structureMap (S := B) f) 1 ≫
          (residueSpecIso γ hγs hγk).hom := by
  simp only [closedFibreIso, Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
    pullback.map, pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  exact residuePullbackIso_structure γ hγs hγk _

end Tower

section Presentation

variable {F A K : Type u} [Field F] [CommRing A] [Field K]
    [Algebra F A] [Algebra F K] [Algebra.FiniteType F A]
    (w : A →ₐ[F] K) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- Every original field fibre has an INTERNALLY CONSTRUCTED complete flat
local presentation, with its entire original projection and field structure. -/
theorem exists_completedLocalPresentation :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B)
      (_ : IsLocalRing B), Module.Flat A B ∧
      IsAdicComplete (IsLocalRing.maximalIdeal B) B ∧
      ∃ γ : B →+* K, Function.Surjective γ ∧
        RingHom.ker γ = IsLocalRing.maximalIdeal B ∧
        γ.comp (algebraMap A B) = w.toRingHom ∧
        ∃ e : InfinitesimalSchemes.model (IsLocalRing.maximalIdeal B)
            (FlatGlobalSections.structureMap (S := B) f) 1 ≅
              pullback f (Spec.map (CommRingCat.ofHom w.toRingHom)),
          e.hom ≫ pullback.fst _ _ =
            InfinitesimalSchemes.projection (IsLocalRing.maximalIdeal B)
              (FlatGlobalSections.structureMap (S := B) f) 1 ≫
                FlatGlobalSections.firstProjection (S := B) f := by
  obtain ⟨R, hRing, hAlg, hNoeth, hLocal, hFlat, β, hβs, hβk, hβw,
    hFlatB, hComplete, γ, hγs, hγk, hγw⟩ :=
      FcFlatLocalFieldLift.exists_completed_flat_local_lift w
  let B := AdicCompletion (IsLocalRing.maximalIdeal R) R
  refine ⟨B, inferInstance, inferInstance, inferInstance,
    hFlatB, hComplete, γ, hγs, hγk, hγw,
    closedFibreIso w.toRingHom γ hγs hγk hγw f, ?_⟩
  exact closedFibreIso_projection w.toRingHom γ hγs hγk hγw f

variable [IsDomain A] [IsIntegrallyClosed A] [IsReduced X] [IsProper f]
    (h : Scheme.BirationalOver f (𝟙 (Spec (.of A))))

include h in
/-- Normal proper-birational geometry constructs the SAME complete flat local
total model with actual whole coefficient bijection and connected total space.
Its literal closed fibre is the ENTIRE original prescribed-field fibre. -/
theorem exists_completedLocalBirationalPresentation :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B)
      (_ : IsLocalRing B), Module.Flat A B ∧
      IsAdicComplete (IsLocalRing.maximalIdeal B) B ∧
      Function.Bijective (ProperBirationalSections.coefficientMap
        (FlatGlobalSections.structureMap (S := B) f)) ∧
      ConnectedSpace (FlatGlobalSections.baseChange (S := B) f) ∧
      ∃ γ : B →+* K, Function.Surjective γ ∧
        RingHom.ker γ = IsLocalRing.maximalIdeal B ∧
        γ.comp (algebraMap A B) = w.toRingHom ∧
        ∃ e : InfinitesimalSchemes.model (IsLocalRing.maximalIdeal B)
            (FlatGlobalSections.structureMap (S := B) f) 1 ≅
              pullback f (Spec.map (CommRingCat.ofHom w.toRingHom)),
          e.hom ≫ pullback.fst _ _ =
            InfinitesimalSchemes.projection (IsLocalRing.maximalIdeal B)
              (FlatGlobalSections.structureMap (S := B) f) 1 ≫
                FlatGlobalSections.firstProjection (S := B) f := by
  obtain ⟨B, hRing, hAlg, hLocal, hFlat, hComplete, γ, hγs, hγk, hγw, e, he⟩ :=
    exists_completedLocalPresentation w f
  let : Module.Flat A B := hFlat
  exact ⟨B, hRing, hAlg, hLocal, hFlat, hComplete,
    FcProperBirationalFlatSections.coefficientMap_flat_bijective f h,
    FcProperBirationalFlatSections.connectedSpace_flatBaseChange f h,
    γ, hγs, hγk, hγw, e, he⟩

end Presentation

end EnvelopeProperty.FibreCompletedLocal
