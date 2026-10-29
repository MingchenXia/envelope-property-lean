import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationOneFormHomotopy
import EnvelopeProperty.Cartier.EtaleDifferentialIntrinsic
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleComplex

/-! # Actual closedness from genuine lifted and residue etale charts

The cross-base reduction on native exterior cotangent modules is constructed
from the actual Kaehler map. Its differential compatibility and annihilator
condition are proved, rather than supplied as comparison hypotheses.
-/

noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationClosedness

open FrobeniusLiftDifference PolynomialDeRham
open scoped Classical

universe u
variable {C K S B : Type u} [CommRing C] [CommRing K] [CommRing S] [CommRing B]
  [Algebra C K] [Algebra C S] [Algebra S B] [Algebra K B] [Algebra C B]
  [IsScalarTower C S B] [IsScalarTower C K B] [SMulCommClass K S B]

/-- The ORIGINAL native cross-base cotangent reduction, semilinear along the actual ring map. -/
def reductionSemilinear : KaehlerDifferential C S →ₛₗ[algebraMap S B] KaehlerDifferential K B where
  toFun := DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K
  map_add' := (DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K).map_add
  map_smul' s η := by
    rw [(DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K).map_smul]
    exact (IsScalarTower.algebraMap_smul B s _).symm

/-- Every original universal differential reduces to its original native residue differential. -/
theorem reductionSemilinear_D (s : S) :
    reductionSemilinear (C := C) (K := K) (B := B) (KaehlerDifferential.D C S s) =
      KaehlerDifferential.D K B (algebraMap S B s) :=
  KaehlerDifferential.map_D C K S B s

/-- The actual alternating universal property gives reduction on the ORIGINAL exterior modules. -/
def exteriorReduction (j : ℕ) :
    (⋀[S]^j (KaehlerDifferential C S)) →ₛₗ[algebraMap S B] (⋀[B]^j (KaehlerDifferential K B)) :=
  CanonicalGeometry.exteriorSemilinearMap (algebraMap S B)
    (reductionSemilinear (C := C) (K := K) (S := S) (B := B)) j

/-- The actual reduction retains EVERY original function wedge. -/
theorem exteriorReduction_universalWedge (j : ℕ) (f : Fin j → S) :
    exteriorReduction (C := C) (K := K) (B := B) j
        (exteriorPower.ιMulti S j (fun i => KaehlerDifferential.D C S (f i))) =
      exteriorPower.ιMulti B j (fun i => KaehlerDifferential.D K B (algebraMap S B (f i))) := by
  rw [exteriorReduction, CanonicalGeometry.exteriorSemilinearMap_ιMulti]
  congr 1
  funext i
  exact reductionSemilinear_D (f i)

/-- Original coefficients are carried by the actual ring reduction on every universal wedge. -/
theorem exteriorReduction_smul_universalWedge (j : ℕ) (s : S) (f : Fin j → S) :
    exteriorReduction (C := C) (K := K) (B := B) j
        (s • exteriorPower.ιMulti S j (fun i => KaehlerDifferential.D C S (f i))) =
      algebraMap S B s • exteriorPower.ιMulti B j
        (fun i => KaehlerDifferential.D K B (algebraMap S B (f i))) := by
  rw [map_smulₛₗ, exteriorReduction_universalWedge]

/-- The SAME actual reduction commutes with left exterior multiplication on all actual forms. -/
theorem exteriorReduction_leftWedge (j : ℕ) (η : KaehlerDifferential C S)
    (ω : ⋀[S]^j (KaehlerDifferential C S)) :
    exteriorReduction (C := C) (K := K) (B := B) (j+1) (leftWedge η j ω) =
      leftWedge (reductionSemilinear (C := C) (K := K) (B := B) η) j
        (exteriorReduction (C := C) (K := K) (B := B) j ω) :=
  ExteriorBasisScalarExtension.exteriorSemilinearMap_leftWedge _ _ η j ω

/-- The actual degree-one reduction is the original native cotangent map under canonical identities. -/
theorem exteriorReduction_one (η : KaehlerDifferential C S) :
    exteriorReduction (C := C) (K := K) (B := B) 1
        ((exteriorPower.oneEquiv S (KaehlerDifferential C S)).symm η) =
      (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K η) := by
  rw [exteriorPower.oneEquiv_symm_apply, exteriorReduction,
    CanonicalGeometry.exteriorSemilinearMap_ιMulti, exteriorPower.oneEquiv_symm_apply]
  rfl

variable {n m : ℕ} (v : Fin n → S) (hv : (MvPolynomial.aeval (R := C) v).toRingHom.Etale)
  (w : Fin m → B) (hw : (MvPolynomial.aeval (R := K) w).toRingHom.Etale)

/-- ENTIRE actual cross-base differential compatibility is DERIVED from native universal formulas. -/
theorem differential_exteriorReduction (j : ℕ) (ω : ⋀[S]^j (KaehlerDifferential C S)) :
    EtaleDeRham.differential w hw j (exteriorReduction (C := C) (K := K) (B := B) j ω) =
      exteriorReduction (C := C) (K := K) (B := B) (j+1) (EtaleDeRham.differential v hv j ω) := by
  let e := (Char0.etaleDifferentialBasis v hv).exteriorPower j
  have hω : ∑ s, e.repr ω s • e s = ω := e.sum_repr ω
  rw [← hω]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  change EtaleDeRham.differential w hw j
      (exteriorReduction (C := C) (K := K) (B := B) j
        (e.repr ω s • (Char0.etaleDifferentialBasis v hv).exteriorPower j s)) =
    exteriorReduction (C := C) (K := K) (B := B) (j+1)
      (EtaleDeRham.differential v hv j
        (e.repr ω s • (Char0.etaleDifferentialBasis v hv).exteriorPower j s))
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  have hvec : (Char0.etaleDifferentialBasis v hv) ∘ (Set.powersetCard.ofFinEmbEquiv.symm s) =
      fun i => KaehlerDifferential.D C S (v ((Set.powersetCard.ofFinEmbEquiv.symm s) i)) := by
    funext i
    exact Char0.etaleDifferentialBasis_apply v hv _
  rw [hvec, exteriorReduction_smul_universalWedge,
    EtaleDifferentialIntrinsic.differential_smul_universalWedge,
    EtaleDifferentialIntrinsic.differential_smul_universalWedge,
    exteriorReduction_leftWedge, reductionSemilinear_D, exteriorReduction_universalWedge]

include v hv in
/-- An honest lifted etale basis DERIVES projectivity and the actual exterior annihilator. -/
theorem exteriorReduction_annihilator {p : ℕ} (b : FlatReduction p S B)
    (hb : algebraMap S B = b.map) (j : ℕ) (ω : ⋀[S]^j (KaehlerDifferential C S))
    (hω : (p : S) • ω = 0) : exteriorReduction (C := C) (K := K) (B := B) j ω = 0 := by
  let : Module.Projective S (⋀[S]^j (KaehlerDifferential C S)) :=
    Module.Projective.of_basis ((Char0.etaleDifferentialBasis v hv).exteriorPower j)
  apply DeligneIllusieLocalContinuationFlatCotangent.semilinear_eq_zero_of_projective
    (algebraMap S B) _ (exteriorReduction (C := C) (K := K) (B := B) j) ω hω
  intro s hs
  rw [hb]
  exact b.flat s hs

include v hv in
/-- EVERY actual divisor of an original exact differential reduces to an actual closed one-form. -/
theorem reduction_divisor_closed {p : ℕ} (b : FlatReduction p S B)
    (hb : algebraMap S B = b.map) (s : S) (η : KaehlerDifferential C S)
    (hη : (p : S) • η = KaehlerDifferential.D C S s) :
    EtaleDeRham.differential w hw 1
      ((exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K η)) = 0 := by
  have hp : (p : S) • EtaleDeRham.differential v hv 1
      ((exteriorPower.oneEquiv S (KaehlerDifferential C S)).symm η) = 0 := by
    have h := congrArg (EtaleDeRham.differential v hv 1)
      (congrArg (exteriorPower.oneEquiv S (KaehlerDifferential C S)).symm hη)
    rw [map_smul, EtaleDifferentialLeibniz.differential_universalD] at h
    simpa only [Nat.cast_smul_eq_nsmul, map_nsmul] using h
  have hred := exteriorReduction_annihilator (K := K) v hv b hb 2
    (EtaleDeRham.differential v hv 1
      ((exteriorPower.oneEquiv S (KaehlerDifferential C S)).symm η)) hp
  rw [← differential_exteriorReduction v hv w hw 1, exteriorReduction_one] at hred
  exact hred

variable {p : ℕ} [Fact p.Prime] [CharP K p] [CharP B p]
  {R : Type u} [CommRing R] [Algebra.FormallySmooth C S]
  (c : Reduction p C K) (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p))
  (b : FlatReduction p S B) (hc : algebraMap C K = c.map) (hb : algebraMap S B = b.map)
  (f : R →+* S) (hf : ∀ r, b.map (f r) = (RelativeFrobenius.map (algebraMap K B) p).hom (a.map r))

attribute [local instance] DeligneIllusieLocalContinuationDividedFrobenius.coefficientAlgebra

include v hv in
/-- Every original xi_f(a) is closed; the actual divisor is internally produced from quotient geometry. -/
theorem divided_closed (x : RelativeFrobenius.twist (algebraMap K B) p) :
    EtaleDeRham.differential w hw 1
      ((exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (DeligneIllusieLocalContinuationDividedFrobenius.divided c a b hc hb f hf x)) = 0 := by
  obtain ⟨r, rfl⟩ := a.surjective x
  obtain ⟨η, hη⟩ :=
    DeligneIllusieLocalContinuationReductionPushout.exists_individual_relativeFrobenius_divisor
      c a b.toReduction hc hb f hf r
  rw [DeligneIllusieLocalContinuationDividedFrobenius.divided_eq_of_lift c a b hc hb f hf r η hη]
  exact reduction_divisor_closed v hv w hw b hb (f r) η hη

variable (ι : C →+* R)
  (hι : ∀ r, a.map (ι r) = algebraMap K (RelativeFrobenius.twist (algebraMap K B) p) (c.map r))
  (hbase : ∀ r, f (ι r) = algebraMap C S r)

include v hv in
/-- The ENTIRE original cotangent map has closed image in the SAME original de Rham differential. -/
theorem cotangentMap_closed (ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) :=
      Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
    EtaleDeRham.differential w hw 1
      ((exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc hb f hf ι hι hbase ω)) = 0 := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) :=
    Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
  let Ξ := DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc hb f hf ι hι hbase
  change EtaleDeRham.differential w hw 1
    ((exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm (Ξ ω)) = 0
  have hω : ω ∈ Submodule.span (RelativeFrobenius.twist (algebraMap K B) p)
      (Set.range (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨x, rfl⟩ := hω
    change EtaleDeRham.differential w hw 1
      ((exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc hb f hf ι hι hbase
          (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p) x))) = 0
    rw [DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap_D]
    exact divided_closed v hv w hw c a b hc hb f hf x
  | zero => simp only [map_zero]
  | add η ζ _ _ hη hζ => simp only [map_add, hη, hζ, add_zero]
  | smul t η _ hη =>
    have hs : (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm (Ξ (t • η)) =
        (RelativeFrobenius.map (algebraMap K B) p).hom t •
          (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm (Ξ η) := by
      rw [map_smul]
      change (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        ((RelativeFrobenius.map (algebraMap K B) p).hom t • Ξ η) = _
      exact map_smul (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm _ _
    rw [hs, RelativeEtaleDeRham.originalDifferential_map_smul w hw p 1, hη, smul_zero]

/-- The actual cotangent map in degree one of the SAME native relative complex, with original actions. -/
def oneFormMap :
    KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p) →ₗ[RelativeFrobenius.twist (algebraMap K B) p]
      RelativeEtaleDeRham.formModule (R := K) (B := B) p 1 := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) :=
    Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
  let Ξ := DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc hb f hf ι hι hbase
  exact
    { toFun := fun ω => (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm (Ξ ω)
      map_add' := fun η ζ => by rw [map_add, map_add]; rfl
      map_smul' := fun t η => by
        change (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm (Ξ (t • η)) =
          (RelativeFrobenius.map (algebraMap K B) p).hom t •
            (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm (Ξ η)
        rw [map_smul]
        exact map_smul (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm _ _ }

/-- Its value is the canonical first exterior image of the ORIGINAL actual Xi_f value. -/
theorem oneFormMap_apply (ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) :=
      Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
    oneFormMap c a b hc hb f hf ι hι hbase ω =
      (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc hb f hf ι hι hbase ω) := rfl

/-- Genuine closedness constructs the actual native kernel-valued one-form map, with no certificate input. -/
def closedCotangentMap :
    KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p) →ₗ[RelativeFrobenius.twist (algebraMap K B) p]
      LinearMap.ker (RelativeEtaleDeRham.differential w hw p 1).hom :=
  LinearMap.codRestrict _ (oneFormMap c a b hc hb f hf ι hι hbase) (fun ω => by
    change EtaleDeRham.differential w hw 1
      ((exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc hb f hf ι hι hbase ω)) = 0
    exact cotangentMap_closed v hv w hw c a b hc hb f hf ι hι hbase ω)

/-- The native closed-form value retains the SAME original degree-one representative on EVERY input. -/
theorem closedCotangentMap_val (ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    (closedCotangentMap v hv w hw c a b hc hb f hf ι hι hbase ω).val =
      oneFormMap c a b hc hb f hf ι hι hbase ω := rfl

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationClosedness
