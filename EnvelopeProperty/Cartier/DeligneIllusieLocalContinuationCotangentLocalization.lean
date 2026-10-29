import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationDifferenceLocalization

/-! # Genuine relative cotangent difference terms on actual principal models -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCotangentLocalization
open FrobeniusLiftDifference
open DeligneIllusieLocalContinuationFlatReductionLocalization
open DeligneIllusieLocalContinuationRelativeLiftLocalization
open DeligneIllusieLocalContinuationSameReductionLocalization
open DeligneIllusieLocalContinuationDifferenceLocalization
universe u v w z t k
variable {C : Type t} {K : Type k} {R : Type u} {S : Type v} {A : Type w} {B : Type z}
  [CommRing C] [CommRing K] [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra C K] [Algebra C R] [Algebra C S] [Algebra K A] [Algebra C A] [Algebra R A]
  [IsScalarTower C K A] [IsScalarTower C R A] {p : ℕ}
  (c : Reduction p C K) (a : Reduction p R A) (b : FlatReduction p S B)
  (f g : R →ₐ[C] S) (φ : A →+* B)
  (hf : b.map.comp f.toRingHom = φ.comp a.map)
  (hg : b.map.comp g.toRingHom = φ.comp a.map)
  (ha : algebraMap R A = a.map) (hc : algebraMap C K = c.map)

include ha hc in
private theorem source_base (x : C) :
    a.map (algebraMap C R x) = algebraMap K A (c.map x) := by
  rw [← ha, ← IsScalarTower.algebraMap_apply C R A, ← hc,
    ← IsScalarTower.algebraMap_apply C K A]

private theorem lifts_base (x : C) :
    f (algebraMap C R x) = g (algebraMap C R x) :=
  (f.commutes x).trans (g.commutes x).symm

include ha hc in
private theorem localized_source_base (r : R) (x : C) :
    (awayReduction a r).map (algebraMap C (Localization.Away r) x) =
      algebraMap K (Localization.Away (a.map r)) (c.map x) := by
  calc
    (awayReduction a r).map (algebraMap C (Localization.Away r) x) =
        (awayReduction a r).map (algebraMap R (Localization.Away r) (algebraMap C R x)) := by
      rw [← IsScalarTower.algebraMap_apply C R (Localization.Away r)]
    _ = algebraMap A (Localization.Away (a.map r)) (a.map (algebraMap C R x)) :=
      RingHom.congr_fun (awayReduction_triangle a r) (algebraMap C R x)
    _ = algebraMap A (Localization.Away (a.map r)) (algebraMap K A (c.map x)) :=
      congrArg _ (source_base (c := c) (a := a) (ha := ha) (hc := hc) x)
    _ = algebraMap K (Localization.Away (a.map r)) (c.map x) :=
      (IsScalarTower.algebraMap_apply K A (Localization.Away (a.map r)) (c.map x)).symm

omit [Algebra C A] [Algebra R A] [IsScalarTower C R A] in
private theorem localized_lifts_base (r : R) (x : C) :
    localizedLift f r (algebraMap C (Localization.Away r) x) =
      localizedSecondLift b f g (hf.trans hg.symm) r (algebraMap C (Localization.Away r) x) :=
  ((localizedLift f r).commutes x).trans
    ((localizedSecondLift b f g (hf.trans hg.symm) r).commutes x).symm

/-- ORIGINAL relative cotangent term; original base equations are DERIVED from actual towers/maps. -/
def cotangentTerm :
    letI : Module A B := Module.compHom B φ
    KaehlerDifferential K A →ₗ[A] B :=
  FrobeniusLiftDifference.cotangentMap a b φ f.toRingHom g.toRingHom
    (fun x => RingHom.congr_fun hf x) (fun x => RingHom.congr_fun hg x)
    c.map c.surjective (algebraMap C R)
    (fun x => source_base (c := c) (a := a) (ha := ha) (hc := hc) x)
    (fun x => lifts_base (f := f) (g := g) x)

/-- SAME original canonical relative term on the ACTUAL common localized target model. -/
def localizedCotangentTerm (r : R) :
    letI : Module (Localization.Away (a.map r)) (Localization.Away (b.map (f r))) :=
      Module.compHom _ (localizedResidue a b f.toRingHom φ hf r)
    KaehlerDifferential K (Localization.Away (a.map r)) →ₗ[Localization.Away (a.map r)]
      Localization.Away (b.map (f r)) :=
  FrobeniusLiftDifference.cotangentMap (awayReduction a r) (awayFlatReduction b (f r))
    (localizedResidue a b f.toRingHom φ hf r)
    (localizedLift f r).toRingHom (localizedSecondLift b f g (hf.trans hg.symm) r).toRingHom
    (fun x => RingHom.congr_fun (localizedReduction_square a b f φ hf r) x)
    (fun x => RingHom.congr_fun (localizedSecondLift_reduction a b f g φ hf hg r) x)
    c.map c.surjective (algebraMap C (Localization.Away r))
    (fun x => localized_source_base (c := c) (a := a) (ha := ha) (hc := hc) r x)
    (fun x => localized_lifts_base (a := a) (φ := φ) (b := b) (f := f) (g := g) (hf := hf) (hg := hg) r x)

/-- ENTIRE original relative cotangent-term restriction, with actual native Kaehler map/actions. -/
theorem cotangentTerm_localization (r : R) :
    letI : Module A B := Module.compHom B φ
    letI : Module (Localization.Away (a.map r)) (Localization.Away (b.map (f r))) :=
      Module.compHom _ (localizedResidue a b f.toRingHom φ hf r)
    (algebraMap B (Localization.Away (b.map (f r)))) ∘ cotangentTerm c a b f g φ hf hg ha hc =
      localizedCotangentTerm c a b f g φ hf hg ha hc r ∘
        KaehlerDifferential.map K K A (Localization.Away (a.map r)) := by
  let : Module A B := Module.compHom B φ
  let φ' := localizedResidue a b f.toRingHom φ hf r
  let : Module (Localization.Away (a.map r)) (Localization.Away (b.map (f r))) := Module.compHom _ φ'
  let H := cotangentTerm c a b f g φ hf hg ha hc
  let H' := localizedCotangentTerm c a b f g φ hf hg ha hc r
  let ρ := KaehlerDifferential.map K K A (Localization.Away (a.map r))
  have hφ (x : A) : φ' (algebraMap A (Localization.Away (a.map r)) x) =
      algebraMap B (Localization.Away (b.map (f r))) (φ x) := by
    dsimp only [φ', localizedResidue]
    apply IsLocalization.map_eq
  funext ω
  change algebraMap B (Localization.Away (b.map (f r))) (H ω) = H' (ρ ω)
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D K A)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hω
  · rintro _ ⟨x, rfl⟩
    have hD : ρ (KaehlerDifferential.D K A x) =
        KaehlerDifferential.D K (Localization.Away (a.map r))
          (algebraMap A (Localization.Away (a.map r)) x) := KaehlerDifferential.map_D K K A _ x
    rw [hD]
    change algebraMap B (Localization.Away (b.map (f r)))
        (FrobeniusLiftDifference.cotangentMap a b φ f.toRingHom g.toRingHom
          (fun x => RingHom.congr_fun hf x) (fun x => RingHom.congr_fun hg x)
          c.map c.surjective (algebraMap C R)
          (fun x => source_base (c := c) (a := a) (ha := ha) (hc := hc) x)
          (fun x => lifts_base (f := f) (g := g) x) (KaehlerDifferential.D K A x)) = _
    rw [FrobeniusLiftDifference.cotangentMap_D]
    change _ = FrobeniusLiftDifference.cotangentMap (awayReduction a r) (awayFlatReduction b (f r))
      φ' (localizedLift f r).toRingHom (localizedSecondLift b f g (hf.trans hg.symm) r).toRingHom
      (fun x => RingHom.congr_fun (localizedReduction_square a b f φ hf r) x)
      (fun x => RingHom.congr_fun (localizedSecondLift_reduction a b f g φ hf hg r) x)
      c.map c.surjective (algebraMap C (Localization.Away r))
      (fun x => localized_source_base (c := c) (a := a) (ha := ha) (hc := hc) r x)
      (fun x => localized_lifts_base (a := a) (φ := φ) (b := b) (f := f) (g := g) (hf := hf) (hg := hg) r x)
      (KaehlerDifferential.D K (Localization.Away (a.map r))
        (algebraMap A (Localization.Away (a.map r)) x))
    rw [FrobeniusLiftDifference.cotangentMap_D]
    exact congrFun (difference_localization a b f g φ hf hg r) x
  · rw [map_zero, map_zero, map_zero, map_zero]
  · intro x y _ _ hx hy
    rw [map_add, map_add, map_add, map_add, hx, hy]
  · intro s x _ hx
    rw [H.map_smul s x, ρ.map_smul s x]
    rw [← IsScalarTower.algebraMap_smul (Localization.Away (a.map r)) s (ρ x), H'.map_smul]
    change algebraMap B (Localization.Away (b.map (f r))) (φ s * H x) =
      φ' (algebraMap A (Localization.Away (a.map r)) s) * H' (ρ x)
    rw [map_mul, hx, hφ]
end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCotangentLocalization
