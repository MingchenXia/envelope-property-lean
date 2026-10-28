import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationReductionPushout

/-! # The actual individual divided relative Frobenius differential

Existence, independence, additivity and relative linearity are derived from actual
ring lifts and quotient geometry. The target retains its native Kähler module and
K- and B-actions; the source twist acts through the genuine relative Frobenius.
-/

noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationDividedFrobenius

open FrobeniusLiftDifference CategoryTheory

universe u v w z
variable {p : ℕ} {C : Type u} {K : Type v} {S : Type w} {B : Type v}
  [CommRing C] [CommRing K] [CommRing S] [CommRing B]
  [Algebra C K] [Algebra C S] [Algebra S B] [Algebra K B] [Algebra C B]
  [IsScalarTower C S B] [IsScalarTower C K B] [SMulCommClass K S B]
  [Algebra.FormallySmooth C S]


/-- Smoothness and genuine scalar flat reduction derive uniqueness of reduced divisors. -/
theorem reduction_eq_of_p_smul_eq (b : FlatReduction p S B)
    (hb : algebraMap S B = b.map) (η ζ : KaehlerDifferential C S)
    (h : (p : S) • η = (p : S) • ζ) : (DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K) η = (DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K) ζ := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply DeligneIllusieLocalContinuationFlatCotangent.cotangent_annihilator_of_formallySmooth
    C K b hb
  rw [smul_sub, h, sub_self]

variable [Fact p.Prime] [CharP K p] [CharP B p]

/-- The original coefficient inclusion supplies the actual K-algebra on the genuine twist. -/
abbrev coefficientAlgebra : Algebra K (RelativeFrobenius.twist (algebraMap K B) p) :=
  (RelativeFrobenius.coefficientMap (algebraMap K B) p).hom.toAlgebra

attribute [local instance] coefficientAlgebra

/-- The actual relative Frobenius preserves every original base coefficient. -/
theorem frobenius_algebraMap (k : K) : (RelativeFrobenius.map (algebraMap K B) p).hom (algebraMap K (RelativeFrobenius.twist (algebraMap K B) p) k) = algebraMap K B k := by
  change (RelativeFrobenius.map (algebraMap K B) p).hom ((RelativeFrobenius.coefficientMap (algebraMap K B) p).hom k) = _
  exact congrArg (fun h : CommRingCat.of K ⟶ CommRingCat.of B => h.hom k)
    (RelativeFrobenius.coefficientMap_map (algebraMap K B) p)

private theorem target_scalarTower :
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
    IsScalarTower K (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
  apply IsScalarTower.of_algebraMap_smul
  intro k ω
  change (RelativeFrobenius.map (algebraMap K B) p).hom (algebraMap K (RelativeFrobenius.twist (algebraMap K B) p) k) • ω = k • ω
  rw [frobenius_algebraMap]
  exact IsScalarTower.algebraMap_smul B k ω

variable {R : Type z} [CommRing R]
  (c : Reduction p C K) (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p)) (b : FlatReduction p S B)
  (hc : algebraMap C K = c.map) (hb : algebraMap S B = b.map) (f : R →+* S)
  (hf : ∀ x, b.map (f x) = (RelativeFrobenius.map (algebraMap K B) p).hom (a.map x))

include c a b hc hb f hf

/-- Reduce an actual divisor, produced internally from the genuine quotient square. -/
def dividedOnLift (x : R) : KaehlerDifferential K B :=
  (DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K) (Classical.choose
    (DeligneIllusieLocalContinuationReductionPushout.exists_individual_relativeFrobenius_divisor
      c a b.toReduction hc hb f hf x))

/-- Every actual divisor computes the same original reduced value. -/
theorem dividedOnLift_eq (x : R) (η : KaehlerDifferential C S)
    (hη : (p : S) • η = KaehlerDifferential.D C S (f x)) :
    dividedOnLift c a b hc hb f hf x = (DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K) η := by
  apply reduction_eq_of_p_smul_eq b hb
  exact (Classical.choose_spec
    (DeligneIllusieLocalContinuationReductionPushout.exists_individual_relativeFrobenius_divisor
      c a b.toReduction hc hb f hf x)).trans hη.symm

/-- The original residue representative does not affect the individual divided differential. -/
theorem dividedOnLift_congr {x y : R} (hxy : a.map x = a.map y) :
    dividedOnLift c a b hc hb f hf x = dividedOnLift c a b hc hb f hf y := by
  obtain ⟨t, ht⟩ := (a.kernel_iff (x-y)).mp (by rw [map_sub, hxy, sub_self])
  obtain ⟨η, hη⟩ :=
    DeligneIllusieLocalContinuationReductionPushout.exists_individual_relativeFrobenius_divisor
      c a b.toReduction hc hb f hf y
  have hdt : (p : S) • KaehlerDifferential.D C S (f t) =
      KaehlerDifferential.D C S (f x) - KaehlerDifferential.D C S (f y) := by
    simpa only [map_mul, map_natCast, map_sub, Derivation.leibniz, Derivation.map_natCast,
      smul_zero, add_zero] using congrArg (fun r => KaehlerDifferential.D C S (f r)) ht
  have hηx : (p : S) • (η + KaehlerDifferential.D C S (f t)) =
      KaehlerDifferential.D C S (f x) := by
    rw [smul_add, hη, hdt]
    abel
  rw [dividedOnLift_eq c a b hc hb f hf x _ hηx, map_add,
    DeligneIllusieLocalContinuationDifferential.reduction_D, hb, hf,
    RelativeFrobeniusCoefficient.D_map_eq_zero, add_zero]
  exact (dividedOnLift_eq c a b hc hb f hf y η hη).symm

/-- The individual divided differential on EVERY original element of the genuine residue twist. -/
def divided (x : (RelativeFrobenius.twist (algebraMap K B) p)) : KaehlerDifferential K B :=
  dividedOnLift c a b hc hb f hf (Classical.choose (a.surjective x))

/-- Every original source lift and every actual divisor give the same residue value. -/
theorem divided_eq_of_lift (x : R) (η : KaehlerDifferential C S)
    (hη : (p : S) • η = KaehlerDifferential.D C S (f x)) :
    divided c a b hc hb f hf (a.map x) = (DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K) η :=
  (dividedOnLift_congr c a b hc hb f hf
    (Classical.choose_spec (a.surjective (a.map x)))).trans
      (dividedOnLift_eq c a b hc hb f hf x η hη)

/-- Actual individual division is additive on the entire original residue ring. -/
theorem divided_add (x y : (RelativeFrobenius.twist (algebraMap K B) p)) :
    divided c a b hc hb f hf (x+y) =
      divided c a b hc hb f hf x + divided c a b hc hb f hf y := by
  obtain ⟨r, rfl⟩ := a.surjective x
  obtain ⟨s, rfl⟩ := a.surjective y
  obtain ⟨η, hη⟩ :=
    DeligneIllusieLocalContinuationReductionPushout.exists_individual_relativeFrobenius_divisor
      c a b.toReduction hc hb f hf r
  obtain ⟨ζ, hζ⟩ :=
    DeligneIllusieLocalContinuationReductionPushout.exists_individual_relativeFrobenius_divisor
      c a b.toReduction hc hb f hf s
  rw [← map_add, divided_eq_of_lift c a b hc hb f hf (r+s) (η+ζ) (by
    rw [smul_add, hη, hζ, map_add, map_add]), map_add,
    divided_eq_of_lift c a b hc hb f hf r η hη,
    divided_eq_of_lift c a b hc hb f hf s ζ hζ]

/-- The original zero function has zero divided differential. -/
theorem divided_zero : divided c a b hc hb f hf 0 = 0 := by
  have h := divided_eq_of_lift c a b hc hb f hf 0 0 (by simp)
  simpa only [map_zero] using h

/-- The original unit function has zero divided differential. -/
theorem divided_one : divided c a b hc hb f hf 1 = 0 := by
  have h := divided_eq_of_lift c a b hc hb f hf 1 0 (by simp)
  simpa only [map_one, map_zero] using h

/-- The actual Leibniz coefficients are the original relative Frobenius images. -/
theorem divided_mul (x y : (RelativeFrobenius.twist (algebraMap K B) p)) :
    divided c a b hc hb f hf (x*y) =
      (RelativeFrobenius.map (algebraMap K B) p).hom x • divided c a b hc hb f hf y + (RelativeFrobenius.map (algebraMap K B) p).hom y • divided c a b hc hb f hf x := by
  obtain ⟨r, rfl⟩ := a.surjective x
  obtain ⟨s, rfl⟩ := a.surjective y
  obtain ⟨η, hη⟩ :=
    DeligneIllusieLocalContinuationReductionPushout.exists_individual_relativeFrobenius_divisor
      c a b.toReduction hc hb f hf r
  obtain ⟨ζ, hζ⟩ :=
    DeligneIllusieLocalContinuationReductionPushout.exists_individual_relativeFrobenius_divisor
      c a b.toReduction hc hb f hf s
  have hrs : (p : S) • (f r • ζ + f s • η) = KaehlerDifferential.D C S (f (r*s)) := by
    rw [smul_add, smul_comm (p : S) (f r), smul_comm (p : S) (f s), hη, hζ,
      map_mul, Derivation.leibniz]
  rw [← map_mul, divided_eq_of_lift c a b hc hb f hf (r*s) _ hrs,
    map_add, map_smul, map_smul,
    divided_eq_of_lift c a b hc hb f hf r η hη,
    divided_eq_of_lift c a b hc hb f hf s ζ hζ,
    ← IsScalarTower.algebraMap_smul B (f r), ← IsScalarTower.algebraMap_smul B (f s),
    hb, hf, hf]

section RelativeBase
variable (ι : C →+* R)
  (hι : ∀ r, a.map (ι r) = algebraMap K (RelativeFrobenius.twist (algebraMap K B) p) (c.map r))
  (hbase : ∀ r, f (ι r) = algebraMap C S r)

include ι hι hbase

/-- Genuine compatible base lifts force the divided differential of every base coefficient to vanish. -/
theorem divided_algebraMap (k : K) : divided c a b hc hb f hf (algebraMap K (RelativeFrobenius.twist (algebraMap K B) p) k) = 0 := by
  obtain ⟨r, rfl⟩ := c.surjective k
  have h := divided_eq_of_lift c a b hc hb f hf (ι r) 0 (by
    rw [hbase, Derivation.map_algebraMap, smul_zero])
  simpa only [hι, map_zero] using h

/-- Base-linearity uses the SAME native K-action on the original target cotangent module. -/
theorem divided_smul (k : K) (x : (RelativeFrobenius.twist (algebraMap K B) p)) :
    divided c a b hc hb f hf (k • x) = k • divided c a b hc hb f hf x := by
  rw [Algebra.smul_def, divided_mul, divided_algebraMap c a b hc hb f hf ι hι hbase,
    smul_zero, add_zero, frobenius_algebraMap]
  exact IsScalarTower.algebraMap_smul B k _

/-- The genuine K-relative derivation; only the (RelativeFrobenius.twist (algebraMap K B) p)-action is restriction along actual relative Frobenius. -/
def derivation :
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
    Derivation K (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
  exact
    { toFun := divided c a b hc hb f hf
      map_add' := divided_add c a b hc hb f hf
      map_smul' := divided_smul c a b hc hb f hf ι hι hbase
      map_one_eq_zero' := divided_one c a b hc hb f hf
      leibniz' := divided_mul c a b hc hb f hf }

/-- The ACTUAL individual divided map on the entire original relative cotangent module. -/
def cotangentMap :
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
    KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p) →ₗ[(RelativeFrobenius.twist (algebraMap K B) p)] KaehlerDifferential K B := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
  let := target_scalarTower (K := K) (B := B) (p := p)
  exact (derivation c a b hc hb f hf ι hι hbase).liftKaehlerDifferential

/-- Every original universal differential has its genuine reduced divided value. -/
theorem cotangentMap_D (x : (RelativeFrobenius.twist (algebraMap K B) p)) :
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
    cotangentMap c a b hc hb f hf ι hι hbase (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p) x) =
      divided c a b hc hb f hf x := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
  let := target_scalarTower (K := K) (B := B) (p := p)
  exact Derivation.liftKaehlerDifferential_comp_D (derivation c a b hc hb f hf ι hι hbase) x

/-- The whole cotangent map computes EVERY actual lift and EVERY actual individual divisor. -/
theorem cotangentMap_D_of_lift (x : R) (η : KaehlerDifferential C S)
    (hη : (p : S) • η = KaehlerDifferential.D C S (f x)) :
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
    cotangentMap c a b hc hb f hf ι hι hbase (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p) (a.map x)) = (DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K) η := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
  rw [cotangentMap_D, divided_eq_of_lift c a b hc hb f hf x η hη]

end RelativeBase
end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationDividedFrobenius
