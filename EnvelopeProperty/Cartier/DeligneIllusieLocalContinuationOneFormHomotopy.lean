import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationDividedFrobenius

/-! # Whole one-form homotopy and cocycle for actual relative Frobenius lifts -/

noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationOneFormHomotopy

open FrobeniusLiftDifference

universe u v w z
variable {p : ℕ} {K B : Type v} [CommRing K] [CommRing B] [Algebra K B]
  [Fact p.Prime] [CharP K p] [CharP B p]

attribute [local instance] DeligneIllusieLocalContinuationDividedFrobenius.coefficientAlgebra

/-- The original K-relative D is linear for the ORIGINAL twist action, derived from D(Fa)=0. -/
def relativeDifferential :
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) B := Module.compHom B (RelativeFrobenius.map (algebraMap K B) p).hom
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
    B →ₗ[(RelativeFrobenius.twist (algebraMap K B) p)] KaehlerDifferential K B := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) B := Module.compHom B (RelativeFrobenius.map (algebraMap K B) p).hom
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
  exact
    { toFun := KaehlerDifferential.D K B
      map_add' := (KaehlerDifferential.D K B).map_add
      map_smul' := fun a b => by
        change KaehlerDifferential.D K B ((RelativeFrobenius.map (algebraMap K B) p).hom a * b) =
          (RelativeFrobenius.map (algebraMap K B) p).hom a • KaehlerDifferential.D K B b
        rw [Derivation.leibniz, RelativeFrobeniusCoefficient.D_map_eq_zero,
          smul_zero, add_zero] }

/-- Its value is exactly the original universal differential on every original function. -/
theorem relativeDifferential_apply (b : B) :
    relativeDifferential (K := K) (B := B) (p := p) b = KaehlerDifferential.D K B b := rfl

private theorem target_scalarTower :
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
    IsScalarTower K (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
  apply IsScalarTower.of_algebraMap_smul
  intro k ω
  change (RelativeFrobenius.map (algebraMap K B) p).hom (algebraMap K (RelativeFrobenius.twist (algebraMap K B) p) k) • ω = k • ω
  rw [DeligneIllusieLocalContinuationDividedFrobenius.frobenius_algebraMap]
  exact IsScalarTower.algebraMap_smul B k ω

variable {C : Type u} {S : Type w} {R : Type z}
  [CommRing C] [CommRing S] [CommRing R]
  [Algebra C K] [Algebra C S] [Algebra S B] [Algebra C B]
  [IsScalarTower C S B] [IsScalarTower C K B] [SMulCommClass K S B]
  [Algebra.FormallySmooth C S]
  (c : Reduction p C K) (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p)) (b : FlatReduction p S B)
  (hc : algebraMap C K = c.map) (hb : algebraMap S B = b.map)
  (f g : R →+* S) (hf : ∀ x, b.map (f x) = (RelativeFrobenius.map (algebraMap K B) p).hom (a.map x))
  (hg : ∀ x, b.map (g x) = (RelativeFrobenius.map (algebraMap K B) p).hom (a.map x))

/-- The actual individual comparison on EVERY original function, using internally produced divisors. -/
theorem divided_sub (x : (RelativeFrobenius.twist (algebraMap K B) p)) :
    DeligneIllusieLocalContinuationDividedFrobenius.divided c a b hc hb f hf x - DeligneIllusieLocalContinuationDividedFrobenius.divided c a b hc hb g hg x =
      KaehlerDifferential.D K B (difference a b (RelativeFrobenius.map (algebraMap K B) p).hom f g hf hg x) := by
  obtain ⟨r, rfl⟩ := a.surjective x
  obtain ⟨ηf, hηf⟩ :=
    DeligneIllusieLocalContinuationReductionPushout.exists_individual_relativeFrobenius_divisor
      c a b.toReduction hc hb f hf r
  obtain ⟨ηg, hηg⟩ :=
    DeligneIllusieLocalContinuationReductionPushout.exists_individual_relativeFrobenius_divisor
      c a b.toReduction hc hb g hg r
  rw [DeligneIllusieLocalContinuationDividedFrobenius.divided_eq_of_lift c a b hc hb f hf r ηf hηf,
    DeligneIllusieLocalContinuationDividedFrobenius.divided_eq_of_lift c a b hc hb g hg r ηg hηg]
  exact DeligneIllusieLocalContinuationFlatCotangent.two_dividedDifferentials_comparison_of_formallySmooth
    C K a b (RelativeFrobenius.map (algebraMap K B) p).hom f g hf hg hb r ηf ηg hηf hηg

variable (ι : C →+* R) (hι : ∀ r, a.map (ι r) = algebraMap K (RelativeFrobenius.twist (algebraMap K B) p) (c.map r))
  (hbasef : ∀ r, f (ι r) = algebraMap C S r)
  (hbaseg : ∀ r, g (ι r) = algebraMap C S r)

/-- The actual H_fg cotangent map, constructed from ring differences and genuine base agreement. -/
def homotopyTerm :
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) B := Module.compHom B (RelativeFrobenius.map (algebraMap K B) p).hom
    KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p) →ₗ[(RelativeFrobenius.twist (algebraMap K B) p)] B :=
  FrobeniusLiftDifference.cotangentMap a b (RelativeFrobenius.map (algebraMap K B) p).hom f g hf hg c.map c.surjective ι hι
    (fun r => (hbasef r).trans (hbaseg r).symm)

omit [Algebra C K] [Algebra S B] [Algebra C B]
  [IsScalarTower C S B] [IsScalarTower C K B]
  [SMulCommClass K S B] [Algebra.FormallySmooth C S] in
/-- Every original da has its actual divided ring-difference value. -/
theorem homotopyTerm_D (x : (RelativeFrobenius.twist (algebraMap K B) p)) :
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) B := Module.compHom B (RelativeFrobenius.map (algebraMap K B) p).hom
    homotopyTerm c a b f g hf hg ι hι hbasef hbaseg (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p) x) =
      difference a b (RelativeFrobenius.map (algebraMap K B) p).hom f g hf hg x := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) B := Module.compHom B (RelativeFrobenius.map (algebraMap K B) p).hom
  exact FrobeniusLiftDifference.cotangentMap_D a b (RelativeFrobenius.map (algebraMap K B) p).hom f g hf hg c.map c.surjective ι hι
    (fun r => (hbasef r).trans (hbaseg r).symm) x

/-- The local homotopy identity holds on the ENTIRE actual native cotangent module. -/
theorem cotangentMap_sub :
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) B := Module.compHom B (RelativeFrobenius.map (algebraMap K B) p).hom
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
    DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc hb f hf ι hι hbasef -
        DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc hb g hg ι hι hbaseg =
      (relativeDifferential (K := K) (B := B) (p := p)).comp
        (homotopyTerm c a b f g hf hg ι hι hbasef hbaseg) := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) B := Module.compHom B (RelativeFrobenius.map (algebraMap K B) p).hom
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) := Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
  let := target_scalarTower (K := K) (B := B) (p := p)
  apply Derivation.liftKaehlerDifferential_unique
  ext x
  change DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc hb f hf ι hι hbasef (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p) x) -
      DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc hb g hg ι hι hbaseg (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p) x) =
    KaehlerDifferential.D K B
      (homotopyTerm c a b f g hf hg ι hι hbasef hbaseg (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p) x))
  rw [DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap_D, DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap_D, homotopyTerm_D]
  exact divided_sub c a b hc hb f g hf hg x

omit [Algebra C K] [Algebra S B] [Algebra C B]
  [IsScalarTower C S B] [IsScalarTower C K B]
  [SMulCommClass K S B] [Algebra.FormallySmooth C S] in
/-- Actual triple-overlap homotopies satisfy their cocycle on ALL original one-forms. -/
theorem homotopyTerm_cocycle (k : R →+* S) (hk : ∀ x, b.map (k x) = (RelativeFrobenius.map (algebraMap K B) p).hom (a.map x))
    (hbasek : ∀ r, k (ι r) = algebraMap C S r) :
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) B := Module.compHom B (RelativeFrobenius.map (algebraMap K B) p).hom
    homotopyTerm c a b f k hf hk ι hι hbasef hbasek =
      homotopyTerm c a b f g hf hg ι hι hbasef hbaseg +
        homotopyTerm c a b g k hg hk ι hι hbaseg hbasek := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) B := Module.compHom B (RelativeFrobenius.map (algebraMap K B) p).hom
  let : IsScalarTower K (RelativeFrobenius.twist (algebraMap K B) p) B := by
    apply IsScalarTower.of_algebraMap_smul
    intro k y
    change (RelativeFrobenius.map (algebraMap K B) p).hom (algebraMap K (RelativeFrobenius.twist (algebraMap K B) p) k) • y = k • y
    rw [DeligneIllusieLocalContinuationDividedFrobenius.frobenius_algebraMap]
    exact IsScalarTower.algebraMap_smul B k y
  apply Derivation.liftKaehlerDifferential_unique
  ext x
  change homotopyTerm c a b f k hf hk ι hι hbasef hbasek (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p) x) =
      homotopyTerm c a b f g hf hg ι hι hbasef hbaseg (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p) x) +
        homotopyTerm c a b g k hg hk ι hι hbaseg hbasek (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p) x)
  rw [homotopyTerm_D, homotopyTerm_D, homotopyTerm_D]
  exact difference_cocycle a b (RelativeFrobenius.map (algebraMap K B) p).hom f g hf hg k hk x

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationOneFormHomotopy
