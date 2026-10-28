import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistZeroFormTerm

/-! # Strict cocycles for the actual true-twist zero-form homotopy terms -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistZeroFormCocycle
open AlgebraicGeometry CategoryTheory Limits Opposite FrobeniusLiftDifference
universe u v w z t k

section Generic
variable {C : Type t} {K : Type k} {R : Type u} {S : Type v} {A : Type w} {B : Type z}
  [CommRing C] [CommRing K] [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra C K] [Algebra C R] [Algebra C S] [Algebra K A] [Algebra C A] [Algebra R A]
  [IsScalarTower C K A] [IsScalarTower C R A] {p : ℕ}
  (c : Reduction p C K) (a : Reduction p R A) (b : FlatReduction p S B)
  (F G J : R →ₐ[C] S) (φ : A →+* B)
  (hF : b.map.comp F.toRingHom = φ.comp a.map)
  (hG : b.map.comp G.toRingHom = φ.comp a.map)
  (hJ : b.map.comp J.toRingHom = φ.comp a.map)
  (ha : algebraMap R A = a.map) (hc : algebraMap C K = c.map)

/-- The SAME canonical relative cotangent terms satisfy the entire strict triple identity. -/
theorem cotangentTerm_cocycle :
    letI : Module A B := Module.compHom B φ
    DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm c a b F J φ hF hJ ha hc =
      DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm c a b F G φ hF hG ha hc +
        DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm c a b G J φ hG hJ ha hc := by
  let : Module A B := Module.compHom B φ
  let HFG := DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm c a b F G φ hF hG ha hc
  let HGJ := DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm c a b G J φ hG hJ ha hc
  let HFJ := DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm c a b F J φ hF hJ ha hc
  apply LinearMap.ext
  intro ω
  change HFJ ω = HFG ω + HGJ ω
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D K A)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hω
  · rintro _ ⟨x, rfl⟩
    dsimp only [HFJ, HFG, HGJ, DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm]
    rw [FrobeniusLiftDifference.cotangentMap_D, FrobeniusLiftDifference.cotangentMap_D,
      FrobeniusLiftDifference.cotangentMap_D]
    exact difference_cocycle a b φ F.toRingHom G.toRingHom
      (fun x => RingHom.congr_fun hF x) (fun x => RingHom.congr_fun hG x)
      J.toRingHom (fun x => RingHom.congr_fun hJ x) x
  · rw [map_zero, map_zero, map_zero, add_zero]
  · intro x y _ _ hx hy
    rw [map_add, map_add, map_add, hx, hy]
    ac_rfl
  · intro s x _ hx
    rw [map_smul, map_smul, map_smul, hx, smul_add]
end Generic

section Affine
variable {K B : Type u} [Field K] [CommRing B] [Algebra K B]
  {C : Type v} {R : Type w} {S : Type z}
  [CommRing C] [CommRing R] [CommRing S] [Algebra C K] [Algebra C R] [Algebra C S]
  (p : ℕ) [Fact p.Prime] [CharP K p]

private abbrev coefficientAlgebra : Algebra K (RelativeFrobenius.twist (algebraMap K B) p) :=
  (RelativeFrobenius.coefficientMap (algebraMap K B) p).hom.toAlgebra
attribute [local instance] coefficientAlgebra
private abbrev coefficientCAlgebra : Algebra C (RelativeFrobenius.twist (algebraMap K B) p) :=
  ((RelativeFrobenius.coefficientMap (algebraMap K B) p).hom.comp (algebraMap C K)).toAlgebra
attribute [local instance] coefficientCAlgebra
private instance coefficientTower : IsScalarTower C K (RelativeFrobenius.twist (algebraMap K B) p) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

variable [Algebra R (RelativeFrobenius.twist (algebraMap K B) p)]
  [IsScalarTower C R (RelativeFrobenius.twist (algebraMap K B) p)]
  (c : Reduction p C K) (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p))
  (b : FlatReduction p S B) (F G J : R →ₐ[C] S)
  (hF : b.map.comp F.toRingHom = (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)
  (hG : b.map.comp G.toRingHom = (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)
  (hJ : b.map.comp J.toRingHom = (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)
  (ha : algebraMap R (RelativeFrobenius.twist (algebraMap K B) p) = a.map)
  (hc : algebraMap C K = c.map)

/-- SAME actual geometric-beta zero-form terms satisfy the entire T-linear triple cocycle. -/
theorem nativeZeroFormTerm_cocycle :
    DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.nativeZeroFormTerm p c a b F J hF hJ ha hc =
      DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.nativeZeroFormTerm p c a b F G hF hG ha hc +
        DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.nativeZeroFormTerm p c a b G J hG hJ ha hc := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) B :=
    Module.compHom B (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom
  apply LinearMap.ext
  intro ω
  change (exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm
      (DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm c a b F J
        (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom hF hJ ha hc ω) =
    (exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm
      (DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm c a b F G
        (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom hF hG ha hc ω) +
    (exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm
      (DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm c a b G J
        (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom hG hJ ha hc ω)
  rw [cotangentTerm_cocycle c a b F G J _ hF hG hJ ha hc, LinearMap.add_apply, map_add]

variable {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := K) v).toRingHom.Etale)

/-- Strict cocycle in ACTUAL affine pushed zero-form sheaves, obtained by additive tilde. -/
theorem affineSheafTerm_cocycle :
    DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.affineSheafTerm p c a b F J hF hJ ha hc v hv =
      DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.affineSheafTerm p c a b F G hF hG ha hc v hv +
        DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.affineSheafTerm p c a b G J hG hJ ha hc v hv := by
  simp only [DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.affineSheafTerm,
    nativeZeroFormTerm_cocycle p c a b F G J hF hG hJ ha hc,
    ModuleCat.ofHom_add, Functor.map_add]
  exact Preadditive.add_comp _ _ _ _ _ _
end Affine

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistZeroFormCocycle
