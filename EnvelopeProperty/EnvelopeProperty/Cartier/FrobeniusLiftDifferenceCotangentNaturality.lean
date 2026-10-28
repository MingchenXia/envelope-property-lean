import EnvelopeProperty.Cartier.FrobeniusLiftDifferenceNaturality
import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationNativeHomotopy
import EnvelopeProperty.Cartier.EtaleDifferentialNaturality

/-! # Canonical actual one-form homotopies restrict under genuine lift diagrams -/
noncomputable section
namespace EnvelopeProperty.Cartier.FrobeniusLiftDifferenceCotangentNaturality
open FrobeniusLiftDifference
universe u
attribute [local instance] DeligneIllusieLocalContinuationDividedFrobenius.coefficientAlgebra

private theorem algHom_tower {K A A' : Type u} [CommRing K] [CommRing A] [CommRing A']
    [Algebra K A] [Algebra K A'] (α₀ : A →ₐ[K] A') :
    letI : Algebra A A' := α₀.toRingHom.toAlgebra
    IsScalarTower K A A' := by
  let : Algebra A A' := α₀.toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun k => (α₀.commutes k).symm)

private theorem canonical_zero_apply {K B B' : Type u} [CommRing K] [CommRing B] [CommRing B']
    [Algebra K B] [Algebra K B'] (ψ : B →ₐ[K] B') (z : B) :
    letI : Algebra B B' := ψ.toRingHom.toAlgebra
    letI : IsScalarTower K B B' := algHom_tower ψ
    Char0.canonicalDifferentialLinearMap (k := K) (R := B) (A := B') 0
      ((exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm z) =
        (exteriorPower.zeroEquiv B' (KaehlerDifferential K B')).symm (ψ z) := by
  let : Algebra B B' := ψ.toRingHom.toAlgebra
  let : IsScalarTower K B B' := algHom_tower ψ
  rw [exteriorPower.zeroEquiv_symm_apply, map_smul,
    Char0.canonicalDifferentialLinearMap_wedge, exteriorPower.zeroEquiv_symm_apply,
    ← IsScalarTower.algebraMap_smul B' z]
  apply congrArg (fun ω : ⋀[B']^0 (KaehlerDifferential K B') => ψ z • ω)
  exact congrArg (exteriorPower.ιMulti B' 0) (Subsingleton.elim _ _)

variable {p : ℕ} {K B B' C R S R' S' : Type u}
  [CommRing K] [CommRing B] [CommRing B'] [CommRing C]
  [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
  [Algebra K B] [Algebra K B'] [Algebra C S] [Algebra C S']
  [Fact p.Prime] [CharP K p] [CharP B p] [CharP B' p]
  (c : Reduction p C K)
  (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p)) (b : FlatReduction p S B)
  (a' : Reduction p R' (RelativeFrobenius.twist (algebraMap K B') p)) (b' : FlatReduction p S' B')
  (f g : R →+* S) (f' g' : R' →+* S')
  (hf : ∀ r, b.map (f r) = (RelativeFrobenius.map (algebraMap K B) p).hom (a.map r))
  (hg : ∀ r, b.map (g r) = (RelativeFrobenius.map (algebraMap K B) p).hom (a.map r))
  (hf' : ∀ r, b'.map (f' r) = (RelativeFrobenius.map (algebraMap K B') p).hom (a'.map r))
  (hg' : ∀ r, b'.map (g' r) = (RelativeFrobenius.map (algebraMap K B') p).hom (a'.map r))
  (ι : C →+* R) (ι' : C →+* R')
  (hι : ∀ r, a.map (ι r) = algebraMap K (RelativeFrobenius.twist (algebraMap K B) p) (c.map r))
  (hι' : ∀ r, a'.map (ι' r) = algebraMap K (RelativeFrobenius.twist (algebraMap K B') p) (c.map r))
  (hbasef : ∀ r, f (ι r) = algebraMap C S r) (hbaseg : ∀ r, g (ι r) = algebraMap C S r)
  (hbasef' : ∀ r, f' (ι' r) = algebraMap C S' r) (hbaseg' : ∀ r, g' (ι' r) = algebraMap C S' r)
  (α : R →+* R') (β : S →+* S')
  (α₀ : RelativeFrobenius.twist (algebraMap K B) p →ₐ[K] RelativeFrobenius.twist (algebraMap K B') p)
  (ψ : B →ₐ[K] B')
  (ha : ∀ r, a'.map (α r) = α₀ (a.map r))
  (hb : ∀ s, b'.map (β s) = ψ (b.map s))
  (hff : ∀ r, β (f r) = f' (α r)) (hgg : ∀ r, β (g r) = g' (α r))

include ha hb hff hgg in
/-- ENTIRE canonical OLD cotangent homotopy naturality for ACTUAL maps and genuine lift/reduction squares. -/
theorem homotopyTerm_naturality :
    letI : Algebra (RelativeFrobenius.twist (algebraMap K B) p)
        (RelativeFrobenius.twist (algebraMap K B') p) := α₀.toRingHom.toAlgebra
    letI : IsScalarTower K (RelativeFrobenius.twist (algebraMap K B) p)
        (RelativeFrobenius.twist (algebraMap K B') p) := algHom_tower α₀
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) B :=
      Module.compHom B (RelativeFrobenius.map (algebraMap K B) p).hom
    letI : Module (RelativeFrobenius.twist (algebraMap K B') p) B' :=
      Module.compHom B' (RelativeFrobenius.map (algebraMap K B') p).hom
    ψ ∘ DeligneIllusieLocalContinuationOneFormHomotopy.homotopyTerm
        c a b f g hf hg ι hι hbasef hbaseg =
      DeligneIllusieLocalContinuationOneFormHomotopy.homotopyTerm
        c a' b' f' g' hf' hg' ι' hι' hbasef' hbaseg' ∘
        EtaleDifferentialNaturality.cotangentSemilinearMap (R := K)
          (A := RelativeFrobenius.twist (algebraMap K B) p)
          (B := RelativeFrobenius.twist (algebraMap K B') p) := by
  let : Algebra (RelativeFrobenius.twist (algebraMap K B) p)
      (RelativeFrobenius.twist (algebraMap K B') p) := α₀.toRingHom.toAlgebra
  let : IsScalarTower K (RelativeFrobenius.twist (algebraMap K B) p)
      (RelativeFrobenius.twist (algebraMap K B') p) := algHom_tower α₀
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) B :=
    Module.compHom B (RelativeFrobenius.map (algebraMap K B) p).hom
  let : Module (RelativeFrobenius.twist (algebraMap K B') p) B' :=
    Module.compHom B' (RelativeFrobenius.map (algebraMap K B') p).hom
  let H := DeligneIllusieLocalContinuationOneFormHomotopy.homotopyTerm c a b f g hf hg ι hι hbasef hbaseg
  let H' := DeligneIllusieLocalContinuationOneFormHomotopy.homotopyTerm c a' b' f' g' hf' hg' ι' hι' hbasef' hbaseg'
  let ρ := EtaleDifferentialNaturality.cotangentSemilinearMap (R := K)
    (A := RelativeFrobenius.twist (algebraMap K B) p) (B := RelativeFrobenius.twist (algebraMap K B') p)
  have hφ := FrobeniusLiftDifferenceNaturality.residueMapSquare a b a' b'
    (RelativeFrobenius.map (algebraMap K B) p).hom (RelativeFrobenius.map (algebraMap K B') p).hom
    f f' hf hf' α β α₀.toRingHom ψ.toRingHom ha hb hff
  have hδ := FrobeniusLiftDifferenceNaturality.difference_naturality a b a' b'
    (RelativeFrobenius.map (algebraMap K B) p).hom (RelativeFrobenius.map (algebraMap K B') p).hom
    f g f' g' hf hg hf' hg' α β α₀.toRingHom ψ.toRingHom ha hb hff hgg
  funext ω
  change ψ (H ω) = H' (ρ ω)
  have hω : ω ∈ Submodule.span (RelativeFrobenius.twist (algebraMap K B) p)
      (Set.range (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hω
  · rintro _ ⟨x, rfl⟩
    have hρ : ρ (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p) x) =
        KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B') p) (α₀ x) :=
      KaehlerDifferential.map_D K K _ _ x
    rw [hρ, DeligneIllusieLocalContinuationOneFormHomotopy.homotopyTerm_D,
      DeligneIllusieLocalContinuationOneFormHomotopy.homotopyTerm_D]
    exact congrFun hδ x
  · rw [map_zero, map_zero, map_zero, map_zero]
  · intro x y _ _ hx hy
    rw [map_add, map_add, map_add, map_add, hx, hy]
  · intro r x _ hx
    rw [H.map_smul r x, map_smulₛₗ ρ r x, H'.map_smul]
    change ψ ((RelativeFrobenius.map (algebraMap K B) p).hom r * H x) =
      (RelativeFrobenius.map (algebraMap K B') p).hom (α₀ r) * H' (ρ x)
    rw [map_mul, hx]
    exact congrArg (fun z : B' => z * H' (ρ x))
      (congrArg (fun h : RelativeFrobenius.twist (algebraMap K B) p →+* B' => h r) hφ)

include ha hb hff hgg in
/-- ENTIRE canonical OLD native zero-form homotopy restriction under the SAME actual canonical degree-zero map. -/
theorem zeroFormHomotopy_naturality :
    letI : Algebra (RelativeFrobenius.twist (algebraMap K B) p)
        (RelativeFrobenius.twist (algebraMap K B') p) := α₀.toRingHom.toAlgebra
    letI : IsScalarTower K (RelativeFrobenius.twist (algebraMap K B) p)
        (RelativeFrobenius.twist (algebraMap K B') p) := algHom_tower α₀
    letI : Algebra B B' := ψ.toRingHom.toAlgebra
    letI : IsScalarTower K B B' := algHom_tower ψ
    (fun ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p) =>
      Char0.canonicalDifferentialLinearMap (k := K) (R := B) (A := B') 0
        (DeligneIllusieLocalContinuationNativeHomotopy.zeroFormHomotopy c a b f g hf hg ι hι hbasef hbaseg ω)) =
      (fun ω => DeligneIllusieLocalContinuationNativeHomotopy.zeroFormHomotopy
        c a' b' f' g' hf' hg' ι' hι' hbasef' hbaseg'
        (EtaleDifferentialNaturality.cotangentSemilinearMap (R := K)
          (A := RelativeFrobenius.twist (algebraMap K B) p)
          (B := RelativeFrobenius.twist (algebraMap K B') p) ω)) := by
  let : Algebra (RelativeFrobenius.twist (algebraMap K B) p)
      (RelativeFrobenius.twist (algebraMap K B') p) := α₀.toRingHom.toAlgebra
  let : IsScalarTower K (RelativeFrobenius.twist (algebraMap K B) p)
      (RelativeFrobenius.twist (algebraMap K B') p) := algHom_tower α₀
  let : Algebra B B' := ψ.toRingHom.toAlgebra
  let : IsScalarTower K B B' := algHom_tower ψ
  funext ω
  rw [DeligneIllusieLocalContinuationNativeHomotopy.zeroFormHomotopy_apply,
    canonical_zero_apply ψ,
    DeligneIllusieLocalContinuationNativeHomotopy.zeroFormHomotopy_apply]
  exact congrArg (exteriorPower.zeroEquiv B' (KaehlerDifferential K B')).symm
    (congrFun (homotopyTerm_naturality c a b a' b' f g f' g' hf hg hf' hg' ι ι' hι hι'
      hbasef hbaseg hbasef' hbaseg' α β α₀ ψ ha hb hff hgg) ω)

end EnvelopeProperty.Cartier.FrobeniusLiftDifferenceCotangentNaturality
