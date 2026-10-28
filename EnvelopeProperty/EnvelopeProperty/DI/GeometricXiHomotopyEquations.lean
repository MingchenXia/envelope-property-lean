import EnvelopeProperty.DI.GeometricLeadingCartier
import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistZeroFormCocycle
noncomputable section
namespace EnvelopeProperty.DI.GeometricXiHomotopyEquations
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Cartier Cartier.FrobeniusLiftDifference
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace NativePair
variable {K B C S : Type u} {R : Type v}
  [Field K] [CommRing B] [CommRing C] [CommRing R] [CommRing S]
  [Algebra K B] [Algebra C K] [Algebra C R] [Algebra C S]
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
  (b : FlatReduction p S B) (F : R →ₐ[C] S)
  (hF : b.map.comp F.toRingHom =
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)
  (ha : algebraMap R (RelativeFrobenius.twist (algebraMap K B) p) = a.map)
  (hc : algebraMap C K = c.map) [Algebra.FormallySmooth C S]
variable (G : R →ₐ[C] S)
  (hG : b.map.comp G.toRingHom =
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)
private theorem sub {n : ℕ} (w : Fin n → B)
    (hw : (MvPolynomial.aeval (R := K) w).toRingHom.Etale) :
    ModuleCat.ofHom
        (X := ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
          (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)))
        (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p 1)
        (DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc) -
    ModuleCat.ofHom
        (X := ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
          (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)))
        (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p 1)
        (DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b G hG ha hc) =
    ModuleCat.ofHom
        (X := ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
          (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)))
        (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p 0)
        (DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.nativeZeroFormTerm p c a b F G hF hG ha hc) ≫
      (SchemeRelativeFrobeniusAffineDeRham.complex w hw p).d 0 1 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  change DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc ω -
      DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b G hG ha hc ω =
    (SchemeRelativeFrobeniusAffineDeRham.differential w hw p 0).hom
      (DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.nativeZeroFormTerm p c a b F G hF hG ha hc ω)
  exact DFunLike.congr_fun
    (DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap_sub
      p c a b F hF ha hc G hG w hw) ω
end NativePair

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) [SmoothOfRelativeDimension n f]
  {U : X.Opens} (hU : IsAffineOpen U)
private abbrev structuralRingMap : k →+* X.presheaf.obj (op U) :=
  ((CanonicalGeometry.schemeConstantPresheafMap f).app (op U)).hom
local notation "T" => RelativeFrobenius.twist (structuralRingMap (U := U) f) p
private abbrev coefficientAlgebra : Algebra k (T) :=
  (RelativeFrobenius.coefficientMap (structuralRingMap (U := U) f) p).hom.toAlgebra
attribute [local instance] coefficientAlgebra
variable {C S : Type u} {R : Type v} [CommRing C] [CommRing R] [CommRing S]
  [Algebra C k] [Algebra C R] [Algebra C S]
private abbrev coefficientCAlgebra : Algebra C (T) :=
  ((RelativeFrobenius.coefficientMap (structuralRingMap (U := U) f) p).hom.comp (algebraMap C k)).toAlgebra
attribute [local instance] coefficientCAlgebra
private instance coefficientTower : IsScalarTower C k (T) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
variable [Algebra R (RelativeFrobenius.twist (structuralRingMap (U := U) f) p)] [IsScalarTower C R (RelativeFrobenius.twist (structuralRingMap (U := U) f) p)]
  (c : Reduction p C k) (a : Reduction p R (RelativeFrobenius.twist (structuralRingMap (U := U) f) p)) (b : FlatReduction p S Γ(X,U))
  (F : R →ₐ[C] S)
  (hF : b.map.comp F.toRingHom =
    (SchemeRelativeFrobeniusAffineMap.ringMap (structuralRingMap (U := U) f) p).hom.comp a.map)
  (ha : algebraMap R (RelativeFrobenius.twist (structuralRingMap (U := U) f) p) = a.map) (hc : algebraMap C k = c.map)
  [Algebra.FormallySmooth C S]
  (w : Fin n → Γ(X,U)) (hw : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (MvPolynomial.aeval (R := k) w).toRingHom.Etale)
local notation "Kn" => SchemeRelativeFrobeniusAffineDeRham.complex w hw p
local notation "Kg" => GeometricComplexExchange.sectionComplex f p n U
local notation "σ" => RelativeTwistedAffineCharts.sectionsIso f p U hU
private abbrev scalarRestriction : ModuleCat (T) ⥤
    ModuleCat ((SchemeRelativeFrobenius.twist p f).presheaf.obj (op (RelativeTwistedAffineBasis.twistedOpen f p U))) :=
  ModuleCat.restrictScalars (RelativeTwistedAffineCharts.sectionsIso f p U hU).hom.hom
local notation "RS" => scalarRestriction f p hU
local notation "Krs" => GeometricComplexExchange.nativeSectionComplex f p n hU w hw
local notation "ψ" => GeometricComplexExchange.complexIso f p n hU w hw
local notation "g" => pullback.snd f (SchemeRelativeFrobenius.baseMap (k := k) p)
local notation "WU" => RelativeTwistedAffineBasis.twistedOpen f p U
private abbrev sourceSections : ModuleCat ((SchemeRelativeFrobenius.twist p f).presheaf.obj (op WU)) :=
  (CanonicalGeometry.exteriorCotangentSheaf g 1).val.obj (op WU)
local notation "M" => sourceSections (U := U) f p
private abbrev nativeSource : ModuleCat (T) :=
  ModuleCat.of (T) (KaehlerDifferential k (T))

private def sourceMap :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U
    M ⟶ (RS).obj (nativeSource (U := U) f p) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact (GeometricLocalCartier.domainIso f p hU n w hw 1).hom ≫
    (RS).map (ModuleCat.ofHom (exteriorPower.oneEquiv (T) (KaehlerDifferential k (T))).toLinearMap)

variable (G J : R →ₐ[C] S)
  (hG : b.map.comp G.toRingHom =
    (SchemeRelativeFrobeniusAffineMap.ringMap (structuralRingMap (U := U) f) p).hom.comp a.map)
  (hJ : b.map.comp J.toRingHom =
    (SchemeRelativeFrobeniusAffineMap.ringMap (structuralRingMap (U := U) f) p).hom.comp a.map)

/-- Canonical homotopy on the original geometric source/target sections. -/
def homotopySections :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U
    M ⟶ (Kg).X 0 := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact sourceMap f p n hU w hw ≫ (RS).map
    (ModuleCat.ofHom (X := nativeSource (U := U) f p)
      (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := Γ(X,U)) p 0)
      (DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.nativeZeroFormTerm
        p c a b F G hF hG ha hc)) ≫ (ψ).hom.f 0

/-- The SAME entire geometric one-form maps differ by the differential of the canonical homotopy. -/
theorem xiSections_sub :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U
    GeometricLeadingCartier.xiSections f p n hU c a b F hF ha hc w hw -
      GeometricLeadingCartier.xiSections f p n hU c a b G hG ha hc w hw =
    homotopySections f p n hU c a b F hF ha hc w hw G hG ≫ (Kg).d 0 1 := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let Ξ (L) (hL) := ModuleCat.ofHom (X := nativeSource (U := U) f p)
    (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := Γ(X,U)) p 1)
    (DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b L hL ha hc)
  let HFG := ModuleCat.ofHom (X := nativeSource (U := U) f p)
    (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := Γ(X,U)) p 0)
    (DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.nativeZeroFormTerm p c a b F G hF hG ha hc)
  change (sourceMap f p n hU w hw ≫ (RS).map (Ξ F hF) ≫ (ψ).hom.f 1) -
      (sourceMap f p n hU w hw ≫ (RS).map (Ξ G hG) ≫ (ψ).hom.f 1) =
    (sourceMap f p n hU w hw ≫ (RS).map HFG ≫ (ψ).hom.f 0) ≫ (Kg).d 0 1
  calc
    _ = sourceMap f p n hU w hw ≫ (RS).map (Ξ F hF - Ξ G hG) ≫ (ψ).hom.f 1 := by
      simp only [Functor.map_sub, Preadditive.comp_sub, Preadditive.sub_comp]
    _ = sourceMap f p n hU w hw ≫ (RS).map (HFG ≫ (Kn).d 0 1) ≫ (ψ).hom.f 1 := by
      rw [NativePair.sub p c a b F hF ha hc G hG w hw]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      exact congrArg (fun z => sourceMap f p n hU w hw ≫ (RS).map HFG ≫ z) ((ψ).hom.comm 0 1).symm

omit [Algebra.FormallySmooth C S] in
/-- The SAME whole geometric homotopy maps satisfy the strict triple cocycle. -/
theorem homotopySections_cocycle :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U
    homotopySections f p n hU c a b F hF ha hc w hw J hJ =
      homotopySections f p n hU c a b F hF ha hc w hw G hG +
      homotopySections f p n hU c a b G hG ha hc w hw J hJ := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  simp only [homotopySections,
    DeligneIllusieLocalContinuationTrueTwistZeroFormCocycle.nativeZeroFormTerm_cocycle
      p c a b F G J hF hG hJ ha hc,
    ModuleCat.ofHom_add, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

end EnvelopeProperty.DI.GeometricXiHomotopyEquations
