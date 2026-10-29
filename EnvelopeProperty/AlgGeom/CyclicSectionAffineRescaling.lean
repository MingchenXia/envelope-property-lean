import EnvelopeProperty.AlgGeom.CyclicSectionAffineCover

/-! # Original affine cyclic frame isomorphisms over their base

The whole rescaling cocycle and coefficient square are transported through the
native contravariant spectrum functor, including the original structure maps.
-/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.CyclicSectionAffineRescaling
open CyclicSectionAlgebra CyclicSectionBaseChange CyclicSectionAffineCover
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Actual frame rescaling between the SAME original affine cyclic covers. -/
def rescaleSpecIso (n : ℕ) (a b : R) (v : Rˣ) (h : b = (v : R) ^ n * a) :
    Spec (.of (RootRing n a)) ≅ Spec (.of (RootRing n b)) :=
  Scheme.Spec.mapIso (rescaleEquiv n a b v h).toRingEquiv.toCommRingCatIso.op

/-- The original frame isomorphism is over the SAME original base spectrum. -/
theorem rescaleSpecIso_structure (n : ℕ) (a b : R) (v : Rˣ)
    (h : b = (v : R) ^ n * a) :
    (rescaleSpecIso n a b v h).hom ≫ structureMap n b = structureMap n a := by
  change Spec.map (CommRingCat.ofHom (rescaleEquiv n a b v h).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (RootRing n b))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun r => (rescaleEquiv n a b v h).commutes r)

/-- Identity frame change is the WHOLE identity affine scheme isomorphism. -/
theorem rescaleSpecIso_one (n : ℕ) (a : R) :
    rescaleSpecIso n a a 1 (by simp) = Iso.refl _ := by
  unfold rescaleSpecIso
  rw [rescaleEquiv_one]
  apply Iso.ext
  exact Spec.map_id _

/-- Original affine frame changes satisfy the WHOLE original scheme cocycle. -/
theorem rescaleSpecIso_trans (n : ℕ) (a b c : R) (v w : Rˣ)
    (hb : b = (v : R) ^ n * a) (hc : c = (w : R) ^ n * b) :
    rescaleSpecIso n a b v hb ≪≫ rescaleSpecIso n b c w hc =
      rescaleSpecIso n a c (w * v)
        (by rw [hc, hb]; simp only [Units.val_mul, mul_pow, mul_assoc]) := by
  apply Iso.ext
  change Spec.map (CommRingCat.ofHom (rescaleEquiv n a b v hb).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (rescaleEquiv n b c w hc).toRingHom) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg (fun e : RootRing n c ≃ₐ[R] RootRing n a => e.toAlgHom.toRingHom)
    (rescaleEquiv_trans n a b c v w hb hc)

/-- The WHOLE original affine coefficient square commutes with frame rescaling. -/
theorem coefficientSpecMap_rescale (n : ℕ) (a b : R) (c d : S) (v : Rˣ)
    (h : b = (v : R) ^ n * a) (hc : c = algebraMap R S a) (hd : d = algebraMap R S b) :
    coefficientSpecMap n a c hc ≫ (rescaleSpecIso n a b v h).hom =
      (rescaleSpecIso n c d (Units.map (algebraMap R S).toMonoidHom v) (by
        change d = (algebraMap R S (v : R)) ^ n * c
        rw [hd, h, map_mul, map_pow, ← hc])).hom ≫ coefficientSpecMap n b d hd := by
  change Spec.map (CommRingCat.ofHom (coefficientMap n a c hc).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (rescaleEquiv n a b v h).toRingHom) =
    Spec.map (CommRingCat.ofHom (rescaleEquiv n c d
      (Units.map (algebraMap R S).toMonoidHom v) (by
        change d = (algebraMap R S (v : R)) ^ n * c
        rw [hd, h, map_mul, map_pow, ← hc])).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (coefficientMap n b d hd).toRingHom)
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (coefficientMap_rescale n a b c d v h hc hd)

end EnvelopeProperty.CyclicSectionAffineRescaling
