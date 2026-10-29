import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCotangentLocalization
import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineSheafComplex
import EnvelopeProperty.Cartier.RelativeCartierContinuationTwistedAffineCotangentSheaves
import EnvelopeProperty.Cartier.RelativeCartierContinuationTwistedAffinePushforward

/-! # Actual true-twist degree-zero homotopy terms, including zero residue rings -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistZeroFormTerm
open AlgebraicGeometry CategoryTheory Limits Opposite FrobeniusLiftDifference
universe u v w z

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
  (b : FlatReduction p S B) (F G : R →ₐ[C] S)
  (hF : b.map.comp F.toRingHom = (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)
  (hG : b.map.comp G.toRingHom = (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)
  (ha : algebraMap R (RelativeFrobenius.twist (algebraMap K B) p) = a.map)
  (hc : algebraMap C K = c.map)

/-- Actual T-linear ZERO-FORM homotopy TERM with SAME original geometric beta action. -/
def nativeZeroFormTerm :
    KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p) →ₗ[RelativeFrobenius.twist (algebraMap K B) p]
      SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p 0 := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) B :=
    Module.compHom B (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom
  let H := DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm c a b F G
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom hF hG ha hc
  exact
    { toFun := fun ω => (exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm (H ω)
      map_add' := fun η ζ => by rw [map_add, map_add]; rfl
      map_smul' := fun t η => by
        change (exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm (H (t • η)) =
          (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom t •
            (exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm (H η)
        rw [H.map_smul]
        exact map_smul (exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm _ _ }

/-- EVERY actual form retains its ENTIRE original exterior-degree-zero value. -/
theorem nativeZeroFormTerm_apply (ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    (show ⋀[B]^0 (KaehlerDifferential K B) from nativeZeroFormTerm p c a b F G hF hG ha hc ω) =
      (exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm
        (DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm c a b F G
          (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom hF hG ha hc ω) := rfl

variable {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := K) v).toRingHom.Etale)

/-- Native associated-sheaf morphism into the ACTUAL original affine pushed zero-form sheaf. -/
def affineSheafTerm :
    tilde (ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
      (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p))) ⟶
      (Scheme.Modules.pushforward (SchemeRelativeFrobeniusAffineMap.affineMap (algebraMap K B) p)).obj
        (CanonicalGeometry.exteriorCotangentSheaf (CanonicalGeometry.affineStructuralMap K (CommRingCat.of B)) 0) :=
  (tilde.functor (RelativeFrobenius.twist (algebraMap K B) p)).map
      (ModuleCat.ofHom
        (X := ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
          (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)))
        (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p 0)
        (nativeZeroFormTerm p c a b F G hF hG ha hc)) ≫
    (SchemeRelativeFrobeniusAffineSheafDeRham.formIso p v hv 0).inv
end Affine

section Chart
variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of K))
  (p : ℕ) [Fact p.Prime] [CharP K p] (U : X.Opens) (hU : IsAffineOpen U)
  {C : Type v} {R : Type w} {S : Type z} [CommRing C] [CommRing R] [CommRing S]
  [Algebra C K] [Algebra C R] [Algebra C S]
private def chartStructuralRingMap : K →+* Γ(X, U) :=
  ((CanonicalGeometry.schemeConstantPresheafMap π).app (op U)).hom
private abbrev chartCoefficientAlgebra : Algebra K (RelativeFrobenius.twist (chartStructuralRingMap π U) p) :=
  (RelativeFrobenius.coefficientMap (chartStructuralRingMap π U) p).hom.toAlgebra
attribute [local instance] chartCoefficientAlgebra
private abbrev chartCoefficientCAlgebra : Algebra C (RelativeFrobenius.twist (chartStructuralRingMap π U) p) :=
  ((RelativeFrobenius.coefficientMap (chartStructuralRingMap π U) p).hom.comp (algebraMap C K)).toAlgebra
attribute [local instance] chartCoefficientCAlgebra
private instance chartCoefficientTower : IsScalarTower C K (RelativeFrobenius.twist (chartStructuralRingMap π U) p) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
variable [Algebra R (RelativeFrobenius.twist (chartStructuralRingMap π U) p)]
  [IsScalarTower C R (RelativeFrobenius.twist (chartStructuralRingMap π U) p)]
  (c : Reduction p C K) (a : Reduction p R (RelativeFrobenius.twist (chartStructuralRingMap π U) p))
  (b : FlatReduction p S Γ(X, U)) (F G : R →ₐ[C] S)
  (hF : b.map.comp F.toRingHom = (SchemeRelativeFrobeniusAffineMap.ringMap (chartStructuralRingMap π U) p).hom.comp a.map)
  (hG : b.map.comp G.toRingHom = (SchemeRelativeFrobeniusAffineMap.ringMap (chartStructuralRingMap π U) p).hom.comp a.map)
  (ha : algebraMap R (RelativeFrobenius.twist (chartStructuralRingMap π U) p) = a.map)
  (hc : algebraMap C K = c.map) {n : ℕ} (v : Fin n → Γ(X, U))
  (hv : letI := CanonicalGeometry.cotangentOpenAlgebra π U
    (MvPolynomial.aeval (R := K) v).toRingHom.Etale)

/-- Actual true-Y cotangent chart restriction -> SAME original global pushed zero-form object.
This is a degree-zero HOMOTOPY TERM, with no differential or gluing assertion. -/
def chartSheafTerm :
    (Scheme.Modules.restrictFunctor (RelativeTwistedAffineFrobenius.chartMap π p U hU)).obj
        (CanonicalGeometry.cotangentSheaf (pullback.snd π (SchemeRelativeFrobenius.baseMap (k := K) p))) ⟶
      (SchemeRelativeFrobeniusDeRham.formModule π p 0).restrict
        (RelativeTwistedAffineFrobenius.chartMap π p U hU) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra π U
  letI : Algebra K (RelativeFrobenius.twist (algebraMap K Γ(X, U)) p) :=
    coefficientAlgebra (K := K) (B := Γ(X, U)) p
  letI : Algebra C (RelativeFrobenius.twist (algebraMap K Γ(X, U)) p) :=
    coefficientCAlgebra (C := C) (K := K) (B := Γ(X, U)) p
  letI : IsScalarTower C K (RelativeFrobenius.twist (algebraMap K Γ(X, U)) p) :=
    coefficientTower (C := C) (K := K) (B := Γ(X, U)) p
  letI : Algebra R (RelativeFrobenius.twist (algebraMap K Γ(X, U)) p) := by
    change Algebra R (RelativeFrobenius.twist (chartStructuralRingMap π U) p)
    infer_instance
  letI : IsScalarTower C R (RelativeFrobenius.twist (algebraMap K Γ(X, U)) p) := by
    change IsScalarTower C R (RelativeFrobenius.twist (chartStructuralRingMap π U) p)
    infer_instance
  exact (RelativeTwistedAffineCotangentSheaves.cotangentSheafIso π p U hU).hom ≫
    affineSheafTerm p c a b F G hF hG ha hc v hv ≫
      (RelativeTwistedAffinePushforward.formIso π p U hU 0).inv
end Chart
end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistZeroFormTerm
