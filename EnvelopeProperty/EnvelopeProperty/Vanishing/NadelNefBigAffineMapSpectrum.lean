import EnvelopeProperty.AlgGeom.GeneratedLineProjectiveAffineMap
noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelNefBigAffineMapSpectrum
open GeneratedLineProjectiveAffineMap SchemeGeneratedLineCoefficients
open DeJongAlterations.Geometry.FiniteProjective
variable {R A : Type u} [CommRing R] [CommRing A]

theorem baseCoefficients_spec (r : R →+* A) :
    (Scheme.ΓSpecIso (.of A)).hom.hom.comp
      (baseCoefficients (Spec.map (CommRingCat.ofHom r))) = r := by
  apply RingHom.ext
  intro x
  change (Scheme.ΓSpecIso (.of A)).hom.hom
    ((Spec.map (CommRingCat.ofHom r)).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom x)) = r x
  have h := congrArg (fun f => f.hom x)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom r))
  exact (congrArg (Scheme.ΓSpecIso (.of A)).hom.hom h.symm).trans
    ((Scheme.ΓSpecIso (.of A)).inv_hom_id_apply (r x))

theorem affineMap_spec {M : (Spec (.of A)).Modules} (r : R →+* A)
    (G : M.GeneratingSections) [Fintype G.I] (e : M ≅ unitObj (Spec (.of A))) :
    affineMap (Spec.map (CommRingCat.ofHom r)) G e =
      affineTupleMap r (paddedCoefficients (fun i => (Scheme.ΓSpecIso (.of A)).hom.hom
        (coefficient G e i))) (by
          rw [paddedCoefficients_map]
          have h := congrArg (Ideal.map (Scheme.ΓSpecIso (.of A)).hom.hom)
            (span_paddedCoefficients_eq_top _ (span_coefficients_eq_top G e))
          rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
          exact h) := by
  let a := paddedCoefficients (coefficient G e)
  let ha := span_paddedCoefficients_eq_top _ (span_coefficients_eq_top G e)
  have hb : Ideal.span (Set.range (fun i => (Scheme.ΓSpecIso (.of A)).hom.hom (a i))) = ⊤ := by
    have h := congrArg (Ideal.map (Scheme.ΓSpecIso (.of A)).hom.hom) ha
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    exact h
  have h := affineTupleMap_naturality (baseCoefficients (Spec.map (CommRingCat.ofHom r))) a ha
    (Scheme.ΓSpecIso (.of A)).hom.hom hb
  rw [CommRingCat.ofHom_hom] at h
  change (Spec (.of A)).isoSpec.hom ≫ _ = _
  rw [Scheme.isoSpec_Spec_hom]
  exact h.trans (affineTupleMap_congr (baseCoefficients_spec r)
    (paddedCoefficients_map (coefficient G e) (Scheme.ΓSpecIso (.of A)).hom.hom).symm _ _)
end EnvelopeProperty.Vanishing.NadelNefBigAffineMapSpectrum
