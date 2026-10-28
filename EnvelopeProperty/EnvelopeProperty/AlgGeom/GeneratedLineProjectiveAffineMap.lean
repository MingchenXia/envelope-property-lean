import EnvelopeProperty.AlgGeom.SchemeGeneratedLineCoefficients
import EnvelopeProperty.AlgGeom.FiniteProjectivePort.FiniteProjectiveAffineMap

/-! # The actual projective map of a finite original affine framed generating family -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
namespace EnvelopeProperty.GeneratedLineProjectiveAffineMap
open SchemeGeneratedLineCoefficients
open DeJongAlterations.Geometry.FiniteProjective DeJongAlterations.Geometry.BlowupProjectiveEmbedding
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {X Y : Scheme.{u}} {L : X.Modules}

private instance pullbackIndexFintype (f : Y ⟶ X)
    (G : L.GeneratingSections) [Fintype G.I] :
    Fintype (ClosedProjectiveGlobalGeneration.pullback_generatingSections f G).I :=
  (inferInstance : Fintype G.I)

/-- The literal actual original coefficient map of the original structure morphism. -/
def baseCoefficients (p : X ⟶ Spec (.of R)) : R →+* Γ(X, ⊤) :=
  p.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

/-- Original whole coefficient maps retain EVERY original affine-source morphism. -/
theorem baseCoefficients_naturality (f : Y ⟶ X) (p : X ⟶ Spec (.of R)) :
    baseCoefficients (f ≫ p) = f.appTop.hom.comp (baseCoefficients p) := rfl

/-- The actual affine-spectrum coefficient map is exactly the original structure map. -/
theorem baseCoefficients_structure [IsAffine X] (p : X ⟶ Spec (.of R)) :
    X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (baseCoefficients p)) = p := by
  have h : CommRingCat.ofHom (baseCoefficients p) =
      (Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop := rfl
  rw [h, Spec.map_comp]
  change X.toSpecΓ ≫ (Spec.map p.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of R)).inv) = p
  rw [← Category.assoc, ← Scheme.toSpecΓ_naturality p, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The genuine whole affine projective morphism of the SAME original
finite generating family, with a derived whole unit-ideal coefficient tuple. -/
def affineMap [IsAffine X] (p : X ⟶ Spec (.of R))
    (G : L.GeneratingSections) [Fintype G.I] (e : L ≅ unitObj X) :
    X ⟶ DeJongAlterations.projectiveSpace R (Fintype.card G.I) :=
  X.isoSpec.hom ≫ affineTupleMap (baseCoefficients p)
    (paddedCoefficients (coefficient G e))
    (span_paddedCoefficients_eq_top _ (span_coefficients_eq_top G e))

/-- This actual whole native projective map preserves the literal original structure morphism. -/
@[reassoc] theorem affineMap_structure [IsAffine X] (p : X ⟶ Spec (.of R))
    (G : L.GeneratingSections) [Fintype G.I] (e : L ≅ unitObj X) :
    affineMap p G e ≫ DeJongAlterations.projectiveSpaceStructure R (Fintype.card G.I) = p := by
  rw [affineMap, Category.assoc, affineTupleMap_structure]
  exact baseCoefficients_structure p

/-- Changing the ACTUAL original whole frame preserves the ENTIRE native
projective morphism; its actual unit-transition is derived internally. -/
theorem affineMap_frame_independent [IsAffine X] (p : X ⟶ Spec (.of R))
    (G : L.GeneratingSections) [Fintype G.I] (e e' : L ≅ unitObj X) :
    affineMap p G e' = affineMap p G e := by
  obtain ⟨v, hv⟩ := exists_unit_coefficient_transition G e e'
  have hc : paddedCoefficients (coefficient G e') =
      fun j => (v : Γ(X, ⊤)) * paddedCoefficients (coefficient G e) j :=
    (congrArg paddedCoefficients (funext hv)).trans (paddedCoefficients_unit _ v)
  let a := paddedCoefficients (coefficient G e)
  let ha : Ideal.span (Set.range a) = ⊤ :=
    span_paddedCoefficients_eq_top _ (span_coefficients_eq_top G e)
  have h := (affineTupleMap_congr (rfl : baseCoefficients p = baseCoefficients p) hc
    (span_paddedCoefficients_eq_top _ (span_coefficients_eq_top G e'))
    (generator_span_unit ⊤ a ha v)).trans (affineTupleMap_unit _ a ha v)
  exact congrArg (fun q => X.isoSpec.hom ≫ q) h

/-- The SAME actual original affine-source morphism commutes with the
whole projective map of its genuine pulled generators and true pulled frame. -/
theorem affineMap_naturality [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections) [Fintype G.I] (e : L ≅ unitObj X) :
    f ≫ affineMap p G e =
      affineMap (f ≫ p) (ClosedProjectiveGlobalGeneration.pullback_generatingSections f G)
        ((Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f) := by
  let a := paddedCoefficients (coefficient G e)
  let ha : Ideal.span (Set.range a) = ⊤ :=
    span_paddedCoefficients_eq_top _ (span_coefficients_eq_top G e)
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections f G
  let E := (Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f
  have hc : paddedCoefficients (coefficient H E) = fun j => f.appTop.hom (a j) :=
    (congrArg paddedCoefficients (funext (coefficient_pullback f G e))).trans
      (paddedCoefficients_map (coefficient G e) f.appTop.hom)
  have hb : Ideal.span (Set.range (fun j => f.appTop.hom (a j))) = ⊤ := by
    rw [← hc]
    exact span_paddedCoefficients_eq_top _ (span_coefficients_eq_top H E)
  have hn := affineTupleMap_naturality (baseCoefficients p) a ha f.appTop.hom hb
  rw [CommRingCat.ofHom_hom] at hn
  change f ≫ (X.isoSpec.hom ≫ affineTupleMap (baseCoefficients p) a ha) = _
  rw [← Category.assoc, ← Scheme.isoSpec_hom_naturality f, Category.assoc, hn]
  exact congrArg (fun q => Y.isoSpec.hom ≫ q)
    (affineTupleMap_congr (baseCoefficients_naturality f p).symm hc.symm hb
      (span_paddedCoefficients_eq_top _ (span_coefficients_eq_top H E)))

end EnvelopeProperty.GeneratedLineProjectiveAffineMap
