import EnvelopeProperty.Cartier.RelativeCartierContinuationOriginalFrobeniusNaturality
import EnvelopeProperty.Cartier.RelativeCartierContinuationGlobalExteriorExchange

/-! # The corrected original Cartier equivalence includes actual zero endpoints

The zero branch is derived from the original source inclusion and actual native
module actions. No characteristic-p instance on a zero ring is constructed.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeAllAlgebraCartier
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u v

/-- Every actual module over an actual zero ring is internally a singleton. -/
theorem zeroRingModuleSubsingleton {R : Type u} [CommRing R] [Subsingleton R]
    (M : ModuleCat.{v} R) : Subsingleton M := by
  have hz (x : M) : x = 0 := by
    calc
      x = (1 : R) • x := (one_smul R x).symm
      _ = (0 : R) • x := congrArg (fun r : R => r • x) (Subsingleton.elim _ _)
      _ = 0 := zero_smul R x
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra
section Algebra
variable {k B : Type u} [Field k] [CommRing B] [Algebra k B]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "T" => RelativeFrobenius.twist (algebraMap k B) p
local notation "S" => (CommRingCat.Hom.hom (RelativeFrobenius.sourceMap (algebraMap k B) p))
local notation "W" => KaehlerDifferential k T

/-- The ACTUAL original source inclusion from a zero endpoint proves the native twist
is itself genuinely zero, without any target-characteristic instance. -/
theorem twist_subsingleton [Subsingleton B] : Subsingleton T :=
  (RelativeFrobenius.sourceMap (algebraMap k B) p).hom.codomain_trivial

/-- Every actual T-linear cotangent exterior module is genuinely zero at a zero endpoint,
including its degree-zero exterior power with the ORIGINAL coefficient action. -/
theorem nativeExterior_isZero [Subsingleton B] (q : ℕ) :
    IsZero (ModuleCat.of T (⋀[T]^q W)) := by
  have : Subsingleton T := twist_subsingleton (k := k) (B := B) p
  have := zeroRingModuleSubsingleton (ModuleCat.of T (⋀[T]^q W))
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of T (⋀[T]^q W))

variable {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
local notation "E" => EtaleAlgebraFrobeniusComplex.complex v hv p

/-- The actual ORIGINAL whole-complex homology is a genuine zero B-module at every zero
endpoint, independently of all relative characteristic hypotheses. -/
theorem originalHomology_isZero [Subsingleton B] (q : ℕ) : IsZero ((E).homology q) := by
  have := zeroRingModuleSubsingleton ((E).homology q)
  exact ModuleCat.isZero_of_subsingleton ((E).homology q)

/-- The SAME corrected original Cartier iso on EVERY actual etale k-algebra, in ALL
q/q0, with the literal source-restricted native twist domain and no CharP B premise. -/
def correctedCartierIso (q : ℕ) :
    (ModuleCat.restrictScalars S).obj (ModuleCat.of T (⋀[T]^q W)) ≅ (E).homology q := by
  classical
  by_cases h : Nontrivial B
  · letI := h
    letI : CharP B p := charP_of_injective_algebraMap (algebraMap k B).injective p
    exact RelativeOriginalFrobeniusBridge.correctedCartierIso p v hv q
  · haveI : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    let M := (ModuleCat.restrictScalars S).obj (ModuleCat.of T (⋀[T]^q W))
    letI := zeroRingModuleSubsingleton M
    exact (ModuleCat.isZero_of_subsingleton M).iso (originalHomology_isZero p v hv q)

/-- Wherever the previous actual native Cartier iso is defined, the entire new iso is
that SAME original iso, derived without a supplied comparison. -/
theorem correctedCartierIso_eq [CharP B p] (q : ℕ) :
    correctedCartierIso p v hv q = RelativeOriginalFrobeniusBridge.correctedCartierIso p v hv q := by
  classical
  by_cases h : Nontrivial B
  · simp only [correctedCartierIso, dif_pos h]
  · have : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    apply Iso.ext
    exact (originalHomology_isZero p v hv q).eq_of_tgt _ _

/-- On every actual zero endpoint the entire corrected native Cartier map is the
internally derived unique zero map. -/
theorem correctedCartierIso_hom_eq_zero [Subsingleton B] (q : ℕ) :
    (correctedCartierIso p v hv q).hom = 0 :=
  (originalHomology_isZero p v hv q).eq_of_tgt _ _
end Algebra

section Naturality
variable {k A B : Type u} [Field k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {n m : ℕ} (a : Fin n → A) (ha : (MvPolynomial.aeval (R := k) a).toRingHom.Etale)
variable (b : Fin m → B) (hb : (MvPolynomial.aeval (R := k) b).toRingHom.Etale)

/-- ENTIRE actual corrected Cartier naturality includes either zero endpoint, in ALL
q/q0 and for any original intervening algebra map, without flatness/etaleness premises. -/
theorem correctedCartierIso_naturality (q : ℕ) :
    (correctedCartierIso p a ha q).hom ≫ EtaleAlgebraCartierNaturality.nativeHomologyMap p a ha b hb q =
      RelativeOriginalFrobeniusNaturality.exteriorMap (k := k) (A := A) (B := B) p q ≫
        (ModuleCat.restrictScalars (algebraMap A B)).map (correctedCartierIso p b hb q).hom := by
  classical
  by_cases h : Nontrivial B
  · have := h
    have : Nontrivial A := (algebraMap A B).domain_nontrivial
    have : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
    have : CharP B p := charP_of_injective_algebraMap (algebraMap k B).injective p
    rw [correctedCartierIso_eq, correctedCartierIso_eq]
    exact RelativeOriginalFrobeniusNaturality.correctedCartierIso_naturality p a ha b hb q
  · have : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    let H := (EtaleAlgebraFrobeniusComplex.complex b hb p).homology q
    have : Subsingleton ((ModuleCat.restrictScalars (algebraMap A B)).obj H) :=
      zeroRingModuleSubsingleton H
    exact (ModuleCat.isZero_of_subsingleton
      ((ModuleCat.restrictScalars (algebraMap A B)).obj H)).eq_of_tgt _ _
end Naturality

section Global
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The actual corrected global-domain PRESHEAF value has the actual corrected Cartier
iso on every genuine section-algebra etale chart, including zero, with no CharP Γ premise.
The algebra is the actual structural coefficient map, internally and explicitly. -/
def pointwiseCartierIso {n : ℕ} (U : X.Opensᵒᵖ) (a : Fin n → X.presheaf.obj U) (q : ℕ) :
    letI : Algebra k (X.presheaf.obj U) := ((CanonicalGeometry.schemeConstantPresheafMap f).app U).hom.toAlgebra
    ∀ (ha : (MvPolynomial.aeval (R := k) a).toRingHom.Etale),
      (RelativeGlobalCartierDomain.domainPresheaf f p q).obj U ≅
        (EtaleAlgebraFrobeniusComplex.complex a ha p).homology q := by
  letI : Algebra k (X.presheaf.obj U) := ((CanonicalGeometry.schemeConstantPresheafMap f).app U).hom.toAlgebra
  intro ha
  exact RelativeGlobalExteriorExchange.domainEvaluationIso f p U q ≪≫ correctedCartierIso p a ha q

/-- If an actual section ring is zero, the ENTIRE pointwise global-domain Cartier map
is internally the unique actual map to its native homology target. -/
theorem pointwiseCartierIso_hom_unique {n : ℕ} (U : X.Opensᵒᵖ) [Subsingleton (X.presheaf.obj U)]
    (a : Fin n → X.presheaf.obj U) (q : ℕ) :
    letI : Algebra k (X.presheaf.obj U) := ((CanonicalGeometry.schemeConstantPresheafMap f).app U).hom.toAlgebra
    ∀ (ha : (MvPolynomial.aeval (R := k) a).toRingHom.Etale)
      (g : (RelativeGlobalCartierDomain.domainPresheaf f p q).obj U ⟶
        (EtaleAlgebraFrobeniusComplex.complex a ha p).homology q),
      (pointwiseCartierIso f p U a q ha).hom = g := by
  let : Algebra k (X.presheaf.obj U) := ((CanonicalGeometry.schemeConstantPresheafMap f).app U).hom.toAlgebra
  intro ha g
  exact (originalHomology_isZero p a ha q).eq_of_tgt _ _
end Global
end EnvelopeProperty.Cartier.RelativeAllAlgebraCartier
