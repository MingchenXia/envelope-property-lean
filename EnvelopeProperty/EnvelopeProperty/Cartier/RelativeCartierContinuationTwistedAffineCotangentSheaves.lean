import EnvelopeProperty.Cartier.RelativeCartierContinuationTwistedAffineSections
import EnvelopeProperty.Cartier.RelativeCartierContinuationGlobalCotangentExchange
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierDomain
import EnvelopeProperty.AlgGeom.Canonical.CanonicalLineSheaf

/-! # The original true-twist cotangent sheaves on the same native affine chart

All actual sheaf isomorphisms below are in Spec(T_U).Modules, retaining the
original coefficient inclusion. Empty opens and zero section rings are included.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeTwistedAffineCotangentSheaves
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
variable (U : X.Opens) (hU : IsAffineOpen U)
private def structuralRingMap : k →+* Γ(X, U) :=
  ((CanonicalGeometry.schemeConstantPresheafMap f).app (op U)).hom
local notation "α" => structuralRingMap f U
local notation "T" => RelativeFrobenius.twist (α) p
local notation "c" => RelativeFrobenius.coefficientMap (α) p
private local instance nativeCoefficientAlgebra : Algebra k T := (c).hom.toAlgebra
local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "π₂" => (pullback.snd f (SchemeRelativeFrobenius.baseMap (k := k) p) :
  Y ⟶ Spec (CommRingCat.of k))
local notation "j" => RelativeTwistedAffineFrobenius.chartMap f p U hU
local notation "σ" => RelativeTwistedAffineCharts.sectionsIso f p U hU

/-- The actual whole chart retains the ORIGINAL coefficient structure on the true twist. -/
theorem structuralMap_eq : (j) ≫ (π₂) = CanonicalGeometry.affineStructuralMap k T :=
  RelativeTwistedAffineFrobenius.chartMap_coefficient f p U hU

/-- The SAME actual section-ring isomorphism transports the original universal cotangent
module along its genuine coefficient square, with no cotangent comparison input. -/
def sectionCotangentIso :
    CommRingCat.KaehlerDifferential (RelativeTwistedAffineSections.coefficientSectionMap f p U) ≅
      (ModuleCat.restrictScalars (σ).hom.hom).obj
        (ModuleCat.of T (KaehlerDifferential k T)) :=
  RelativeGlobalCotangentExchange.cotangentIso
      (RelativeTwistedAffineSections.coefficientSectionMap f p U) (c) (σ)
      (RelativeTwistedAffineSections.sectionsIso_coefficient f p U hU) ≪≫
    (ModuleCat.restrictScalars (σ).hom.hom).mapIso
      (CanonicalGeometry.affineCotangentModuleIso k T)

/-- The ENTIRE original cotangent sheaf on Y, restricted along its SAME actual native
chart, has the true native T-module action, without an etale or nonzero premise. -/
def cotangentSheafIso :
    (Scheme.Modules.restrictFunctor (j)).obj (CanonicalGeometry.cotangentSheaf (π₂)) ≅
      AlgebraicGeometry.tilde (ModuleCat.of T (KaehlerDifferential k T)) := by
  exact @CanonicalGeometry.cotangentSheafOpenImmersionIso.{u} k _
    (SchemeRelativeFrobenius.twist p f) (Spec T) (π₂) (j)
    (RelativeTwistedAffineFrobenius.chartMap_isOpenImmersion f p U hU) ≪≫
    eqToIso (congrArg CanonicalGeometry.cotangentSheaf (structuralMap_eq f p U hU)) ≪≫
    CanonicalGeometry.affineCotangentSheafIso k T ≪≫
    (AlgebraicGeometry.tilde.functor T).mapIso (CanonicalGeometry.affineCotangentModuleIso k T)

variable {n : ℕ} (v : Fin n → Γ(X, U))
variable (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U
  (MvPolynomial.aeval (R := k) v).toRingHom.Etale)

/-- ALL original exterior cotangent sheaves on the SAME Y chart have their whole native
T-linear sheaf exchange, including q0 and zero Γ. The input algebra is the original one. -/
def exteriorCotangentSheafIso (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U
    (Scheme.Modules.restrictFunctor (j)).obj (CanonicalGeometry.exteriorCotangentSheaf (π₂) q) ≅
      AlgebraicGeometry.tilde (ModuleCat.of T (⋀[T]^q (KaehlerDifferential k T))) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  let b : Module.Basis (Fin n) T (KaehlerDifferential k T) :=
    RelativeEtaleCartierDomain.cotangentBasis v hv p
  exact @CanonicalGeometry.exteriorCotangentSheafOpenImmersionIso.{u} k _
    (SchemeRelativeFrobenius.twist p f) (Spec T) (π₂) (j)
    (RelativeTwistedAffineFrobenius.chartMap_isOpenImmersion f p U hU) q ≪≫
    eqToIso (congrArg (fun g => CanonicalGeometry.exteriorCotangentSheaf g q)
      (structuralMap_eq f p U hU)) ≪≫
    CanonicalGeometry.affineExteriorCotangentSheafIso k T b q

/-- The actual native cotangent basis gives a true finite-index frame on the SAME Y chart. -/
def cotangentSheafFrame :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U
    (Scheme.Modules.restrictFunctor (j)).obj (CanonicalGeometry.cotangentSheaf (π₂)) ≅
      AlgebraicGeometry.tilde (ModuleCat.of T (Fin n →₀ T)) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  let b : Module.Basis (Fin n) T (KaehlerDifferential k T) :=
    RelativeEtaleCartierDomain.cotangentBasis v hv p
  exact cotangentSheafIso f p U hU ≪≫
    (AlgebraicGeometry.tilde.functor T).mapIso b.repr.toModuleIso

/-- The SAME actual native exterior bases give true T-frames in EVERY degree, including zero. -/
def exteriorCotangentSheafFrame (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U
    (Scheme.Modules.restrictFunctor (j)).obj (CanonicalGeometry.exteriorCotangentSheaf (π₂) q) ≅
      AlgebraicGeometry.tilde (ModuleCat.of T (Set.powersetCard (Fin n) q →₀ T)) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  let b : Module.Basis (Fin n) T (KaehlerDifferential k T) :=
    RelativeEtaleCartierDomain.cotangentBasis v hv p
  exact exteriorCotangentSheafIso f p U hU v hv q ≪≫
    (AlgebraicGeometry.tilde.functor T).mapIso (b.exteriorPower q).repr.toModuleIso

end EnvelopeProperty.Cartier.RelativeTwistedAffineCotangentSheaves
