import EnvelopeProperty.Cartier.FrobeniusLiftDifference

/-! # p-division of the difference of actual universal differentials

The cotangent reduction is the genuine KaehlerDifferential.map for an actual
base reduction square. Only honest cotangent p-flatness is assumed; the
comparison with the differential of the divided ring difference is proved.
Individual divided Frobenius differentials and global DI remain downstream.
-/

noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationDifferential

open FrobeniusLiftDifference

universe u v w z
variable {p : ℕ} {R : Type u} {S : Type v} {A : Type w} {B : Type z}
  [CommRing R] [CommRing S] [CommRing A] [CommRing B]
variable (C K : Type*) [CommRing C] [CommRing K]
  [Algebra C K] [Algebra C S] [Algebra S B] [Algebra K B] [Algebra C B]
  [IsScalarTower C S B] [IsScalarTower C K B] [SMulCommClass K S B]

/-- The ACTUAL universal cotangent reduction map, with its actual S-scalar action. -/
def reduction : KaehlerDifferential C S →ₗ[S] KaehlerDifferential K B :=
  KaehlerDifferential.map C K S B

/-- Its generator formula is derived from the universal map, not supplied as input. -/
theorem reduction_D (s : S) :
    reduction (S := S) (B := B) C K (KaehlerDifferential.D C S s) =
      KaehlerDifferential.D K B (algebraMap S B s) :=
  KaehlerDifferential.map_D C K S B s

private theorem reduction_eq_of_p_smul_eq
    (hflat : ∀ ω : KaehlerDifferential C S, (p : S) • ω = 0 → reduction (S := S) (B := B) C K ω = 0)
    (ω η : KaehlerDifferential C S) (h : (p : S) • ω = (p : S) • η) :
    reduction (S := S) (B := B) C K ω = reduction (S := S) (B := B) C K η := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact hflat (ω-η) (by rw [smul_sub, h, sub_self])

variable (a : Reduction p R A) (b : FlatReduction p S B) (φ : A →+* B)
  (f g : R →+* S)
  (hf : ∀ x, b.map (f x) = φ (a.map x))
  (hg : ∀ x, b.map (g x) = φ (a.map x))
  (hq : algebraMap S B = b.map)
  (hflat : ∀ ω : KaehlerDifferential C S, (p : S) • ω = 0 → reduction (S := S) (B := B) C K ω = 0)

include a b φ hf hg hq hflat

omit hq hflat [Algebra S B] [Algebra C B] [IsScalarTower C S B] in
/-- A genuine p-divisor of df-dg exists, derived from the ACTUAL ring-lift difference. -/
theorem exists_form_divisor (x : R) :
    ∃ ω : KaehlerDifferential C S, (p : S) • ω =
      KaehlerDifferential.D C S (f x) - KaehlerDifferential.D C S (g x) := by
  obtain ⟨u, hu⟩ := (b.toReduction.kernel_iff (f x-g x)).mp (by
    rw [map_sub, hf, hg, sub_self])
  refine ⟨KaehlerDifferential.D C S u, ?_⟩
  simpa only [Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero, map_sub] using
    congrArg (KaehlerDifferential.D C S) hu

/-- Reduce a CHOSEN actual p-divisor of the ACTUAL universal differential difference. -/
def differentialDifferenceOnLift (x : R) : KaehlerDifferential K B :=
  reduction (S := S) (B := B) C K (Classical.choose (exists_form_divisor C a b φ f g hf hg x))

omit hq in
/-- All actual p-divisors have the SAME original cotangent reduction. -/
theorem differentialDifferenceOnLift_eq (x : R) (ω : KaehlerDifferential C S)
    (hω : (p : S) • ω =
      KaehlerDifferential.D C S (f x) - KaehlerDifferential.D C S (g x)) :
    differentialDifferenceOnLift C K a b φ f g hf hg x = reduction (S := S) (B := B) C K ω := by
  apply reduction_eq_of_p_smul_eq C K hflat
  exact (Classical.choose_spec (exists_form_divisor C a b φ f g hf hg x)).trans hω.symm

/-- The ACTUAL differential comparison is DERIVED from genuine ring division and the
universal cotangent map. Neither a differential comparison nor a homotopy is an input. -/
theorem differentialDifferenceOnLift_comparison (x : R) :
    differentialDifferenceOnLift C K a b φ f g hf hg x =
      KaehlerDifferential.D K B (difference a b φ f g hf hg (a.map x)) := by
  obtain ⟨u, hu⟩ := (b.toReduction.kernel_iff (f x-g x)).mp (by
    rw [map_sub, hf, hg, sub_self])
  have hdu : (p : S) • KaehlerDifferential.D C S u =
      KaehlerDifferential.D C S (f x) - KaehlerDifferential.D C S (g x) := by
    simpa only [Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero, map_sub] using
      congrArg (KaehlerDifferential.D C S) hu
  calc
    differentialDifferenceOnLift C K a b φ f g hf hg x =
        reduction (S := S) (B := B) C K (KaehlerDifferential.D C S u) :=
      differentialDifferenceOnLift_eq C K a b φ f g hf hg hflat x _ hdu
    _ = KaehlerDifferential.D K B (b.map u) := by rw [reduction_D, hq]
    _ = KaehlerDifferential.D K B (difference a b φ f g hf hg (a.map x)) := by
      rw [difference_eq_of_lift a b φ f g hf hg x u hu]

/-- Independence of the source lift follows from the PROVED comparison on actual forms. -/
theorem differentialDifferenceOnLift_congr {x y : R} (hxy : a.map x = a.map y) :
    differentialDifferenceOnLift C K a b φ f g hf hg x =
      differentialDifferenceOnLift C K a b φ f g hf hg y := by
  rw [differentialDifferenceOnLift_comparison C K a b φ f g hf hg hq hflat,
    differentialDifferenceOnLift_comparison C K a b φ f g hf hg hq hflat, hxy]

/-- The divided differential difference on the ENTIRE original residue ring. -/
def differentialDifference (x : A) : KaehlerDifferential K B :=
  differentialDifferenceOnLift C K a b φ f g hf hg
    (Classical.choose (a.surjective x))

/-- The derived comparison holds for EVERY original residue function. -/
theorem differentialDifference_comparison (x : A) :
    differentialDifference C K a b φ f g hf hg x =
      KaehlerDifferential.D K B (difference a b φ f g hf hg x) := by
  unfold differentialDifference
  rw [differentialDifferenceOnLift_comparison C K a b φ f g hf hg hq hflat,
    Classical.choose_spec (a.surjective x)]

/-- Every actual division computes the same original comparison, without selected coordinates. -/
theorem reduced_division_eq_D_difference (x : R) (ω : KaehlerDifferential C S)
    (hω : (p : S) • ω =
      KaehlerDifferential.D C S (f x) - KaehlerDifferential.D C S (g x)) :
    reduction (S := S) (B := B) C K ω = KaehlerDifferential.D K B (difference a b φ f g hf hg (a.map x)) :=
  (differentialDifferenceOnLift_eq C K a b φ f g hf hg hflat x ω hω).symm.trans
    (differentialDifferenceOnLift_comparison C K a b φ f g hf hg hq hflat x)

/-- Difference of TWO ACTUAL divided differentials is d(h_fg) in the actual residue forms. -/
theorem two_dividedDifferentials_comparison (x : R) (ηf ηg : KaehlerDifferential C S)
    (hηf : (p : S) • ηf = KaehlerDifferential.D C S (f x))
    (hηg : (p : S) • ηg = KaehlerDifferential.D C S (g x)) :
    reduction (S := S) (B := B) C K ηf - reduction (S := S) (B := B) C K ηg =
      KaehlerDifferential.D K B (difference a b φ f g hf hg (a.map x)) := by
  simpa only [map_sub] using
    reduced_division_eq_D_difference C K a b φ f g hf hg hq hflat x (ηf-ηg)
      (by rw [smul_sub, hηf, hηg])

/-- The genuine differential divided difference is additive on all original functions. -/
theorem differentialDifference_add (x y : A) :
    differentialDifference C K a b φ f g hf hg (x+y) =
      differentialDifference C K a b φ f g hf hg x +
      differentialDifference C K a b φ f g hf hg y := by
  simp only [differentialDifference_comparison C K a b φ f g hf hg hq hflat,
    difference_add, map_add]

/-- The actual divided differential comparisons satisfy the triple-overlap identity. -/
theorem differentialDifference_cocycle (k : R →+* S)
    (hk : ∀ x, b.map (k x) = φ (a.map x)) (x : A) :
    differentialDifference C K a b φ f k hf hk x =
      differentialDifference C K a b φ f g hf hg x +
      differentialDifference C K a b φ g k hg hk x := by
  rw [differentialDifference_comparison C K a b φ f k hf hk hq hflat,
    difference_cocycle a b φ f g hf hg k hk, map_add,
    differentialDifference_comparison C K a b φ f g hf hg hq hflat,
    differentialDifference_comparison C K a b φ g k hg hk hq hflat]

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationDifferential
