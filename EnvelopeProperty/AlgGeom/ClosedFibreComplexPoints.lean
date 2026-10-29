import EnvelopeProperty.AlgGeom.ClosedFibreLocalRing
import EnvelopeProperty.AlgGeom.ProperLocalSectionDetection
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Actual algebraically closed field points on the original closed coefficient fibre

The actual residue map supplies an actual closed fibre. Every closed original
point on it is realized by an actual field-valued point with the SAME residue
coefficient triangle. On an affine tensor chart the ENTIRE resulting ring map
is the original point tensor map, with no point-cover certificate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u

namespace EnvelopeProperty.ClosedFibreComplexPoints

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

section ResiduePoint

variable {S K : Type u} [CommRing S] [IsLocalRing S] [Field K]
  (β : S →+* K) (hβ : Function.Surjective β)

include hβ

/-- The actual surjective residue map sends the unique field point to the actual local closed point. -/
theorem spec_residueMap_closedPoint :
    Spec.map (CommRingCat.ofHom β) (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint S := by
  let : IsLocalHom β := IsLocalHom.of_surjective β hβ
  exact Spec_closedPoint

/-- The actual closed fibre uses the SAME residue map, whose image is exactly the closed point. -/
theorem range_spec_residueMap :
    Set.range (Spec.map (CommRingCat.ofHom β)) = {IsLocalRing.closedPoint S} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change Spec.map (CommRingCat.ofHom β) z = IsLocalRing.closedPoint S
    rw [Subsingleton.elim z (IsLocalRing.closedPoint K)]
    exact spec_residueMap_closedPoint β hβ
  · rintro rfl
    exact ⟨IsLocalRing.closedPoint K, spec_residueMap_closedPoint β hβ⟩

/-- Every actual closed point of the original closed fibre is covered by its actual field point with the exact original residue triangle. -/
theorem exists_point_over_residueMap_of_isClosed [IsAlgClosed K]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of S)) [LocallyOfFiniteType q]
    (y : Y) (hyc : IsClosed ({y} : Set Y)) (hy : q y = IsLocalRing.closedPoint S) :
    ∃ p : Spec (.of K) ⟶ Y,
      p ≫ q = Spec.map (CommRingCat.ofHom β) ∧ p (IsLocalRing.closedPoint K) = y := by
  let b := Spec.map (CommRingCat.ofHom β)
  let : IsClosedImmersion b := IsClosedImmersion.spec_of_surjective _ hβ
  let j := pullback.fst q b
  let f := pullback.snd q b
  let : LocallyOfFiniteType f := inferInstanceAs (LocallyOfFiniteType (pullback.snd q b))
  have hyr : y ∈ Set.range j := by
    change y ∈ Set.range (pullback.fst q b)
    rw [Scheme.Pullback.range_fst, range_spec_residueMap β hβ]
    exact hy
  obtain ⟨v, hv⟩ := hyr
  have hpre : j ⁻¹' ({y} : Set Y) = {v} := by
    ext w
    change j w = y ↔ w = v
    rw [← hv]
    exact j.isEmbedding.injective.eq_iff
  have hvc : IsClosed ({v} : Set (↑(pullback q b : Scheme.{u}))) := by
    rw [← hpre]
    exact hyc.preimage j.continuous
  refine ⟨pointOfClosedPoint f v hvc ≫ j, ?_, ?_⟩
  · change (pointOfClosedPoint f v hvc ≫ pullback.fst q b) ≫ q = b
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      pointOfClosedPoint_comp, Category.id_comp]
  · change j (pointOfClosedPoint f v hvc (IsLocalRing.closedPoint K)) = y
    rw [pointOfClosedPoint_apply]
    exact hv

end ResiduePoint

section TensorPoint

variable {R A S K : Type u} [CommRing R] [CommRing A] [CommRing S] [Field K]
  [Algebra R A] [Algebra R S] [Algebra R K]
  (β : S →ₐ[R] K) (h : Spec (.of K) ⟶ Spec (.of (A ⊗[R] S)))
  (hh : h ≫ Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S).toRingHom) =
      Spec.map (CommRingCat.ofHom β.toRingHom))

include hh

/-- The literal original ring map of the actual tensor-chart point has the SAME whole residue coefficient map. -/
theorem affinePoint_right :
    (Spec.preimage h).hom.comp
      (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S).toRingHom = β.toRingHom := by
  have he : CommRingCat.ofHom ((Spec.preimage h).hom.comp
      (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S).toRingHom) =
      CommRingCat.ofHom β.toRingHom := by
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S).toRingHom ≫
        Spec.preimage h) = _
    rw [Spec.map_comp, Spec.map_preimage]
    exact hh
  exact congrArg CommRingCat.Hom.hom he

/-- Restriction to the SAME original affine chart is an actual original R-algebra point. -/
def affinePoint_original : A →ₐ[R] K where
  __ := (Spec.preimage h).hom.comp
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] S).toRingHom
  commutes' r := by
    change (Spec.preimage h).hom (algebraMap R (A ⊗[R] S) r) = algebraMap R K r
    have hr := RingHom.congr_fun (affinePoint_right β h hh) (algebraMap R S r)
    simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes] using hr

/-- The ENTIRE actual tensor-chart point map equals the original tensor point map. -/
theorem affinePoint_eq_pointTensorMap :
    (Spec.preimage h).hom =
      (ClosedFibreLocalRing.pointTensorMap β (affinePoint_original β h hh)).toRingHom := by
  apply Algebra.TensorProduct.ringHom_ext
  · ext a
    change (Spec.preimage h).hom
      ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] S) a) =
      ClosedFibreLocalRing.pointTensorMap β (affinePoint_original β h hh)
        ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] S) a)
    rw [ClosedFibreLocalRing.pointTensorMap_includeLeft]
    rfl
  · ext s
    change (Spec.preimage h).hom
      ((Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S) s) =
      ClosedFibreLocalRing.pointTensorMap β (affinePoint_original β h hh)
        ((Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S) s)
    rw [show ClosedFibreLocalRing.pointTensorMap β (affinePoint_original β h hh)
      ((Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S) s) = β s by
        change affinePoint_original β h hh 1 * β s = β s
        rw [map_one, one_mul]]
    exact RingHom.congr_fun (affinePoint_right β h hh) s

end TensorPoint

section ClosedTensorPoint

variable {R A S K : Type u} [CommRing R] [CommRing A] [CommRing S] [Field K]
  [Algebra R A] [Algebra R S] [Algebra R K] [IsLocalRing S] [IsAlgClosed K]
  (β : S →ₐ[R] K)

/-- Every actual closed tensor-chart point over the local closed point has a SAME original surjective point and its ENTIRE original tensor point ideal. -/
theorem exists_surjective_original_tensorPoint
    [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S).toRingHom))]
    (hβ : Function.Surjective β) (hR : Function.Surjective (algebraMap R K))
    (y : Spec (.of (A ⊗[R] S))) (hyc : IsClosed ({y} : Set (Spec (.of (A ⊗[R] S)))))
    (hy : Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S).toRingHom) y =
        IsLocalRing.closedPoint S) :
    ∃ p : A →ₐ[R] K, Function.Surjective p ∧
      y.asIdeal = RingHom.ker (ClosedFibreLocalRing.pointTensorMap β p).toRingHom := by
  obtain ⟨h, hh, hyh⟩ := exists_point_over_residueMap_of_isClosed β.toRingHom hβ
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S).toRingHom)) y hyc hy
  let p := affinePoint_original β h hh
  have hp : Function.Surjective p := by
    intro c
    obtain ⟨r, hr⟩ := hR c
    exact ⟨algebraMap R A r, (p.commutes r).trans hr⟩
  refine ⟨p, hp, ?_⟩
  have hy0 : h (⊥ : PrimeSpectrum K) = y :=
    (congrArg h (Subsingleton.elim _ (IsLocalRing.closedPoint K))).trans hyh
  have he := congrArg PrimeSpectrum.asIdeal hy0
  rw [← Spec.map_preimage h, Spec.map_apply] at he
  change RingHom.ker (Spec.preimage h).hom = y.asIdeal at he
  change y.asIdeal =
    RingHom.ker (ClosedFibreLocalRing.pointTensorMap β (affinePoint_original β h hh)).toRingHom
  rw [← affinePoint_eq_pointTensorMap β h hh]
  exact he.symm

end ClosedTensorPoint

section SectionDetection

variable {S K : Type u} [CommRing S] [IsLocalRing S] [Field K] [IsAlgClosed K]
  (β : S →+* K) (hβ : Function.Surjective β)
  {Y : Scheme.{u}} (q : Y ⟶ Spec (.of S)) [UniversallyClosed q] [LocallyOfFiniteType q]
  (M : Y.Modules) [M.IsQuasicoherent]

include hβ in
/-- The WHOLE original section is detected by actual field points over the SAME original residue map. -/
theorem section_eq_zero_iff_residueFieldPoints (m : Γ(M, ⊤)) :
    m = 0 ↔ ∀ p : Spec (.of K) ⟶ Y, p ≫ q = Spec.map (CommRingCat.ofHom β) →
      M.presheaf.germ ⊤ (p (IsLocalRing.closedPoint K)) trivial m = 0 := by
  constructor
  · rintro rfl p _
    exact map_zero _
  · intro h
    apply ProperLocalSectionDetection.section_eq_zero_of_closedPoint_closedFiber_germs q M m
    intro y hyc hy
    obtain ⟨p, hp, hpy⟩ := exists_point_over_residueMap_of_isClosed β hβ q y hyc hy
    subst y
    exact h p hp

end SectionDetection

end EnvelopeProperty.ClosedFibreComplexPoints
