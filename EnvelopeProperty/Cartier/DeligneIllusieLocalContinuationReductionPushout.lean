import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCotangentKernel

/-! # The actual compatible reduction square is a ring pushout

The universal scalar-extension property is constructed from the two original
surjective p-quotient maps. No ring-pushout or cotangent comparison is an input.
-/

noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationReductionPushout

open FrobeniusLiftDifference

universe u v w z
variable {p : ℕ} {C : Type u} {K : Type v} {S : Type w} {B : Type v}
  [CommRing C] [CommRing K] [CommRing S] [CommRing B]
  [Algebra C K] [Algebra C S] [Algebra S B] [Algebra K B] [Algebra C B]
  [IsScalarTower C S B] [IsScalarTower C K B]

/-- Two actual compatible p-quotients DERIVE the scalar-extension universal property. -/
theorem reduction_isBaseChange (c : Reduction p C K) (b : Reduction p S B)
    (hc : algebraMap C K = c.map) (hb : algebraMap S B = b.map) :
    IsBaseChange K (IsScalarTower.toAlgHom C S B).toLinearMap := by
  classical
  have hp : algebraMap C K (p : C) = 0 := by
    rw [hc, c.kernel_iff]
    exact ⟨1, mul_one _⟩
  have hscalar (r : C) (s : S) : b.map (r • s) = c.map r • b.map s := by
    rw [← hc, ← hb]
    simp only [Algebra.smul_def, map_mul]
    rw [← IsScalarTower.algebraMap_apply C S B, ← IsScalarTower.algebraMap_apply C K B]
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ g
  have hgzero (s : S) : g ((p : S) * s) = 0 := by
    have hs : (p : S) * s = (p : C) • s := by
      simp only [Algebra.smul_def, map_natCast]
    rw [hs, map_smul, ← IsScalarTower.algebraMap_smul K, hp, zero_smul]
  have hgeq (s t : S) (hst : b.map s = b.map t) : g s = g t := by
    have hz : b.map (s - t) = 0 := by rw [map_sub, hst, sub_self]
    obtain ⟨u, hu⟩ := (b.kernel_iff (s - t)).mp hz
    have hs : s = t + (p : S) * u := by rw [hu]; abel
    rw [hs, map_add, hgzero, add_zero]
  let d : B → Q := fun y => g (Classical.choose (b.surjective y))
  have hd (s : S) : d (b.map s) = g s :=
    hgeq _ _ (Classical.choose_spec (b.surjective (b.map s)))
  let G : B →ₗ[K] Q :=
    { toFun := d
      map_add' := by
        intro y z
        obtain ⟨s, rfl⟩ := b.surjective y
        obtain ⟨t, rfl⟩ := b.surjective z
        rw [← map_add, hd, hd, hd, map_add]
      map_smul' := by
        intro k y
        obtain ⟨r, rfl⟩ := c.surjective k
        obtain ⟨s, rfl⟩ := b.surjective y
        rw [← hscalar, hd, hd, map_smul, ← hc]
        exact (IsScalarTower.algebraMap_smul K r (g s)).symm }
  refine ⟨G, ?_, ?_⟩
  · ext s
    change d (algebraMap S B s) = g s
    rw [hb, hd]
  · intro G' hG'
    ext y
    obtain ⟨s, rfl⟩ := b.surjective y
    have h := LinearMap.congr_fun hG' s
    change G' (algebraMap S B s) = g s at h
    change G' (b.map s) = d (b.map s)
    rw [hb] at h
    rw [h, hd]

/-- The actual ring pushout is derived from the two original quotient reductions. -/
theorem reduction_isPushout (c : Reduction p C K) (b : Reduction p S B)
    (hc : algebraMap C K = c.map) (hb : algebraMap S B = b.map) :
    Algebra.IsPushout C K S B :=
  ⟨reduction_isBaseChange c b hc hb⟩

variable [SMulCommClass K S B]

/-- Original cotangent divisibility follows from genuine quotient geometry alone. -/
theorem cotangent_reduction_eq_zero_iff (c : Reduction p C K) (b : Reduction p S B)
    (hc : algebraMap C K = c.map) (hb : algebraMap S B = b.map)
    (ω : KaehlerDifferential C S) :
    DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K ω = 0 ↔
      ∃ η : KaehlerDifferential C S, (p : S) • η = ω := by
  let := reduction_isPushout c b hc hb
  exact DeligneIllusieLocalContinuationCotangentKernel.cotangent_reduction_eq_zero_iff
    C K b hb ω

variable [Fact p.Prime] [CharP K p] [CharP B p] {R : Type z} [CommRing R]

/-- Actual individual Frobenius divisors with NO supplied pushout or Ω comparison. -/
theorem exists_individual_relativeFrobenius_divisor
    (c : Reduction p C K)
    (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p))
    (b : Reduction p S B) (hc : algebraMap C K = c.map) (hb : algebraMap S B = b.map)
    (f : R →+* S) (hf : ∀ x, b.map (f x) =
      (RelativeFrobenius.map (algebraMap K B) p).hom (a.map x)) (x : R) :
    ∃ η : KaehlerDifferential C S, (p : S) • η = KaehlerDifferential.D C S (f x) := by
  let := reduction_isPushout c b hc hb
  exact DeligneIllusieLocalContinuationCotangentKernel.exists_individual_relativeFrobenius_divisor
    C K a b hb f hf x

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationReductionPushout
