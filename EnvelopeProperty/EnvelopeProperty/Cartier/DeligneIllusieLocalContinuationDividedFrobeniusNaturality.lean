import EnvelopeProperty.Cartier.FrobeniusLiftDifferenceCotangentNaturality

/-! # Genuine cotangent p-divisors derive actual individual divided-Frobenius restriction -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationDividedFrobeniusNaturality
open FrobeniusLiftDifference
universe u
attribute [local instance] DeligneIllusieLocalContinuationDividedFrobenius.coefficientAlgebra

private theorem algHom_tower {K A A' : Type u} [CommRing K] [CommRing A] [CommRing A']
    [Algebra K A] [Algebra K A'] (α₀ : A →ₐ[K] A') :
    letI : Algebra A A' := α₀.toRingHom.toAlgebra
    IsScalarTower K A A' := by
  let : Algebra A A' := α₀.toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun k => (α₀.commutes k).symm)

variable {C K S S' B B' : Type u}
  [CommRing C] [CommRing K] [CommRing S] [CommRing S'] [CommRing B] [CommRing B']
  [Algebra C K] [Algebra C S] [Algebra C S']
  [Algebra S B] [Algebra S' B'] [Algebra K B] [Algebra K B'] [Algebra C B] [Algebra C B']
  [IsScalarTower C S B] [IsScalarTower C S' B']
  [IsScalarTower C K B] [IsScalarTower C K B'] [SMulCommClass K S B] [SMulCommClass K S' B']
  (β : S →ₐ[C] S') (ψ : B →ₐ[K] B')

include β ψ in
/-- The ENTIRE actual cross-base native cotangent-reduction square follows from the genuine ORIGINAL ring square. -/
theorem reduction_naturality (hred : ∀ s, ψ (algebraMap S B s) = algebraMap S' B' (β s)) :
    letI : Algebra S S' := β.toRingHom.toAlgebra
    letI : IsScalarTower C S S' := algHom_tower β
    letI : Algebra B B' := ψ.toRingHom.toAlgebra
    letI : IsScalarTower K B B' := algHom_tower ψ
    EtaleDifferentialNaturality.cotangentSemilinearMap (R := K) (A := B) (B := B') ∘
        DeligneIllusieLocalContinuationClosedness.reductionSemilinear (C := C) (K := K) (S := S) (B := B) =
      DeligneIllusieLocalContinuationClosedness.reductionSemilinear (C := C) (K := K) (S := S') (B := B') ∘
        EtaleDifferentialNaturality.cotangentSemilinearMap (R := C) (A := S) (B := S') := by
  let : Algebra S S' := β.toRingHom.toAlgebra
  let : IsScalarTower C S S' := algHom_tower β
  let : Algebra B B' := ψ.toRingHom.toAlgebra
  let : IsScalarTower K B B' := algHom_tower ψ
  let ρS := EtaleDifferentialNaturality.cotangentSemilinearMap (R := C) (A := S) (B := S')
  let ρB := EtaleDifferentialNaturality.cotangentSemilinearMap (R := K) (A := B) (B := B')
  let red := DeligneIllusieLocalContinuationClosedness.reductionSemilinear (C := C) (K := K) (S := S) (B := B)
  let red' := DeligneIllusieLocalContinuationClosedness.reductionSemilinear (C := C) (K := K) (S := S') (B := B')
  funext η
  change ρB (red η) = red' (ρS η)
  have hη : η ∈ Submodule.span S (Set.range (KaehlerDifferential.D C S)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hη
  · rintro _ ⟨s, rfl⟩
    have hS : ρS (KaehlerDifferential.D C S s) = KaehlerDifferential.D C S' (β s) :=
      KaehlerDifferential.map_D C C S S' s
    have hB : ρB (KaehlerDifferential.D K B (algebraMap S B s)) =
        KaehlerDifferential.D K B' (ψ (algebraMap S B s)) :=
      KaehlerDifferential.map_D K K B B' _
    rw [DeligneIllusieLocalContinuationClosedness.reductionSemilinear_D, hB, hS,
      DeligneIllusieLocalContinuationClosedness.reductionSemilinear_D]
    exact congrArg (KaehlerDifferential.D K B') (hred s)
  · rw [map_zero, map_zero, map_zero, map_zero]
  · intro x y _ _ hx hy
    rw [map_add, map_add, map_add, map_add, hx, hy]
  · intro s x _ hx
    rw [map_smulₛₗ red s x, map_smulₛₗ ρB (algebraMap S B s) (red x),
      map_smulₛₗ ρS s x, map_smulₛₗ red' (algebraMap S S' s) (ρS x)]
    change ψ (algebraMap S B s) • ρB (red x) = algebraMap S' B' (β s) • red' (ρS x)
    rw [hred, hx]

variable {p : ℕ} {R R' : Type u} [CommRing R] [CommRing R']
  [Fact p.Prime] [CharP K p] [CharP B p] [CharP B' p]
  [Algebra.FormallySmooth C S] [Algebra.FormallySmooth C S']
  (c : Reduction p C K)
  (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p)) (b : FlatReduction p S B)
  (a' : Reduction p R' (RelativeFrobenius.twist (algebraMap K B') p)) (b' : FlatReduction p S' B')
  (hc : algebraMap C K = c.map) (hb : algebraMap S B = b.map) (hb' : algebraMap S' B' = b'.map)
  (f : R →+* S) (f' : R' →+* S')
  (hf : ∀ r, b.map (f r) = (RelativeFrobenius.map (algebraMap K B) p).hom (a.map r))
  (hf' : ∀ r, b'.map (f' r) = (RelativeFrobenius.map (algebraMap K B') p).hom (a'.map r))
  (α : R →+* R')
  (α₀ : RelativeFrobenius.twist (algebraMap K B) p →ₐ[K] RelativeFrobenius.twist (algebraMap K B') p)
  (ha : ∀ r, a'.map (α r) = α₀ (a.map r))
  (hbr : ∀ s, b'.map (β s) = ψ (b.map s)) (hff : ∀ r, β (f r) = f' (α r))

include ha hbr hff in
/-- ENTIRE actual individual divided Frobenius restriction is DERIVED by transporting INTERNALLY PRODUCED p-divisors. -/
theorem divided_naturality :
    letI : Algebra B B' := ψ.toRingHom.toAlgebra
    letI : IsScalarTower K B B' := algHom_tower ψ
    EtaleDifferentialNaturality.cotangentSemilinearMap (R := K) (A := B) (B := B') ∘
        DeligneIllusieLocalContinuationDividedFrobenius.divided c a b hc hb f hf =
      DeligneIllusieLocalContinuationDividedFrobenius.divided c a' b' hc hb' f' hf' ∘ α₀ := by
  let : Algebra S S' := β.toRingHom.toAlgebra
  let : IsScalarTower C S S' := algHom_tower β
  let : Algebra B B' := ψ.toRingHom.toAlgebra
  let : IsScalarTower K B B' := algHom_tower ψ
  let ρS := EtaleDifferentialNaturality.cotangentSemilinearMap (R := C) (A := S) (B := S')
  let ρB := EtaleDifferentialNaturality.cotangentSemilinearMap (R := K) (A := B) (B := B')
  have hred : ∀ s, ψ (algebraMap S B s) = algebraMap S' B' (β s) := by
    intro s
    rw [hb, hb']
    exact (hbr s).symm
  funext x
  obtain ⟨r, rfl⟩ := a.surjective x
  obtain ⟨η, hη⟩ := DeligneIllusieLocalContinuationReductionPushout.exists_individual_relativeFrobenius_divisor
    c a b.toReduction hc hb f hf r
  have hη' : (p : S') • ρS η = KaehlerDifferential.D C S' (f' (α r)) := by
    calc
      (p : S') • ρS η = (algebraMap S S' (p : S)) • ρS η := by rw [map_natCast]
      _ = ρS ((p : S) • η) := (map_smulₛₗ ρS (p : S) η).symm
      _ = ρS (KaehlerDifferential.D C S (f r)) := congrArg ρS hη
      _ = KaehlerDifferential.D C S' (β (f r)) := KaehlerDifferential.map_D C C S S' _
      _ = KaehlerDifferential.D C S' (f' (α r)) := congrArg (KaehlerDifferential.D C S') (hff r)
  change ρB (DeligneIllusieLocalContinuationDividedFrobenius.divided c a b hc hb f hf (a.map r)) =
    DeligneIllusieLocalContinuationDividedFrobenius.divided c a' b' hc hb' f' hf' (α₀ (a.map r))
  rw [DeligneIllusieLocalContinuationDividedFrobenius.divided_eq_of_lift c a b hc hb f hf r η hη,
    ← ha r,
    DeligneIllusieLocalContinuationDividedFrobenius.divided_eq_of_lift c a' b' hc hb' f' hf' (α r) (ρS η) hη']
  exact congrFun (reduction_naturality β ψ hred) η

variable (ι : C →+* R) (ι' : C →+* R')
  (hι : ∀ r, a.map (ι r) = algebraMap K (RelativeFrobenius.twist (algebraMap K B) p) (c.map r))
  (hι' : ∀ r, a'.map (ι' r) = algebraMap K (RelativeFrobenius.twist (algebraMap K B') p) (c.map r))
  (hbasef : ∀ r, f (ι r) = algebraMap C S r) (hbasef' : ∀ r, f' (ι' r) = algebraMap C S' r)

include ha hbr hff in
/-- ENTIRE actual individual cotangent map restriction on EVERY original form, with DERIVED coefficient actions. -/
theorem cotangentMap_naturality :
    letI : Algebra (RelativeFrobenius.twist (algebraMap K B) p)
        (RelativeFrobenius.twist (algebraMap K B') p) := α₀.toRingHom.toAlgebra
    letI : IsScalarTower K (RelativeFrobenius.twist (algebraMap K B) p)
        (RelativeFrobenius.twist (algebraMap K B') p) := algHom_tower α₀
    letI : Algebra B B' := ψ.toRingHom.toAlgebra
    letI : IsScalarTower K B B' := algHom_tower ψ
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) :=
      Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
    letI : Module (RelativeFrobenius.twist (algebraMap K B') p) (KaehlerDifferential K B') :=
      Module.compHom _ (RelativeFrobenius.map (algebraMap K B') p).hom
    EtaleDifferentialNaturality.cotangentSemilinearMap (R := K) (A := B) (B := B') ∘
        DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc hb f hf ι hι hbasef =
      DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a' b' hc hb' f' hf' ι' hι' hbasef' ∘
        EtaleDifferentialNaturality.cotangentSemilinearMap (R := K)
          (A := RelativeFrobenius.twist (algebraMap K B) p)
          (B := RelativeFrobenius.twist (algebraMap K B') p) := by
  let : Algebra (RelativeFrobenius.twist (algebraMap K B) p)
      (RelativeFrobenius.twist (algebraMap K B') p) := α₀.toRingHom.toAlgebra
  let : IsScalarTower K (RelativeFrobenius.twist (algebraMap K B) p)
      (RelativeFrobenius.twist (algebraMap K B') p) := algHom_tower α₀
  let : Algebra B B' := ψ.toRingHom.toAlgebra
  let : IsScalarTower K B B' := algHom_tower ψ
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) :=
    Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
  let : Module (RelativeFrobenius.twist (algebraMap K B') p) (KaehlerDifferential K B') :=
    Module.compHom _ (RelativeFrobenius.map (algebraMap K B') p).hom
  let X := DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc hb f hf ι hι hbasef
  let X' := DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a' b' hc hb' f' hf' ι' hι' hbasef'
  let ρA := EtaleDifferentialNaturality.cotangentSemilinearMap (R := K)
    (A := RelativeFrobenius.twist (algebraMap K B) p) (B := RelativeFrobenius.twist (algebraMap K B') p)
  let ρB := EtaleDifferentialNaturality.cotangentSemilinearMap (R := K) (A := B) (B := B')
  have hφ := FrobeniusLiftDifferenceNaturality.residueMapSquare a b a' b'
    (RelativeFrobenius.map (algebraMap K B) p).hom (RelativeFrobenius.map (algebraMap K B') p).hom
    f f' hf hf' α β.toRingHom α₀.toRingHom ψ.toRingHom ha hbr hff
  have hξ := divided_naturality β ψ c a b a' b' hc hb hb' f f' hf hf' α α₀ ha hbr hff
  funext ω
  change ρB (X ω) = X' (ρA ω)
  have hω : ω ∈ Submodule.span (RelativeFrobenius.twist (algebraMap K B) p)
      (Set.range (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hω
  · rintro _ ⟨x, rfl⟩
    have hA : ρA (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p) x) =
        KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B') p) (α₀ x) :=
      KaehlerDifferential.map_D K K _ _ x
    rw [hA, DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap_D,
      DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap_D]
    exact congrFun hξ x
  · rw [map_zero, map_zero, map_zero, map_zero]
  · intro x y _ _ hx hy
    rw [map_add, map_add, map_add, map_add, hx, hy]
  · intro r x _ hx
    rw [X.map_smul r x]
    change ρB ((RelativeFrobenius.map (algebraMap K B) p).hom r • X x) = X' (ρA (r • x))
    rw [map_smulₛₗ ρB ((RelativeFrobenius.map (algebraMap K B) p).hom r) (X x),
      map_smulₛₗ ρA r x, X'.map_smul]
    change ψ ((RelativeFrobenius.map (algebraMap K B) p).hom r) • ρB (X x) =
      (RelativeFrobenius.map (algebraMap K B') p).hom (α₀ r) • X' (ρA x)
    rw [hx]
    exact congrArg (fun z : B' => z • X' (ρA x))
      (congrArg (fun h : RelativeFrobenius.twist (algebraMap K B) p →+* B' => h r) hφ)

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationDividedFrobeniusNaturality
