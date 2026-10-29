import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistZeroFormTerm
import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationOneFormHomotopy
import EnvelopeProperty.Cartier.RelativeCartierContinuationAllAlgebraCartier

/-! # Actual zero-safe divided one-forms for the original geometric relative action -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistDividedOneForm
open CategoryTheory FrobeniusLiftDifference
universe u v w z
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
private abbrev residueCAlgebra : Algebra C B :=
  ((algebraMap K B).comp (algebraMap C K)).toAlgebra
private theorem residueCoefficientTower :
    letI : Algebra C B := residueCAlgebra (C := C) (K := K) (B := B)
    IsScalarTower C K B := by
  let : Algebra C B := residueCAlgebra (C := C) (K := K) (B := B)
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

variable [Algebra R (RelativeFrobenius.twist (algebraMap K B) p)]
  [IsScalarTower C R (RelativeFrobenius.twist (algebraMap K B) p)]
  (c : Reduction p C K) (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p))
  (b : FlatReduction p S B) (F : R →ₐ[C] S)
  (hF : b.map.comp F.toRingHom = (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)
  (ha : algebraMap R (RelativeFrobenius.twist (algebraMap K B) p) = a.map)
  (hc : algebraMap C K = c.map)

include ha hc in
private theorem source_base (x : C) :
    a.map (algebraMap C R x) = algebraMap K (RelativeFrobenius.twist (algebraMap K B) p) (c.map x) := by
  rw [← ha, ← IsScalarTower.algebraMap_apply C R (RelativeFrobenius.twist (algebraMap K B) p),
    ← hc, ← IsScalarTower.algebraMap_apply C K (RelativeFrobenius.twist (algebraMap K B) p)]

include hF ha in
private theorem target_base (x : C) :
    b.map (algebraMap C S x) = algebraMap K B (algebraMap C K x) := by
  rw [← F.commutes x]
  have h := RingHom.congr_fun hF (algebraMap C R x)
  change b.map (F (algebraMap C R x)) =
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom (a.map (algebraMap C R x)) at h
  rw [h, ← ha, ← IsScalarTower.algebraMap_apply C R (RelativeFrobenius.twist (algebraMap K B) p)]
  change (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom
      ((RelativeFrobenius.coefficientMap (algebraMap K B) p).hom (algebraMap C K x)) =
    algebraMap K B (algebraMap C K x)
  exact congrArg (fun h : CommRingCat.of K ⟶ CommRingCat.of B => h.hom (algebraMap C K x))
    (SchemeRelativeFrobeniusAffineMap.coefficient_ringMap (algebraMap K B) p)

include hF ha in
private theorem targetTower :
    letI : Algebra C B := residueCAlgebra (C := C) (K := K) (B := B)
    letI : Algebra S B := b.map.toAlgebra
    IsScalarTower C S B := by
  let : Algebra C B := residueCAlgebra (C := C) (K := K) (B := B)
  let : Algebra S B := b.map.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun x => (target_base p (a := a) (b := b) (F := F) hF ha x).symm)

include hF in
omit [Algebra C K] [Algebra R (RelativeFrobenius.twist (algebraMap K B) p)]
  [IsScalarTower C R (RelativeFrobenius.twist (algebraMap K B) p)] in
private theorem native_square [CharP B p] (r : R) :
    b.map (F r) = (RelativeFrobenius.map (algebraMap K B) p).hom (a.map r) := by
  have h := RingHom.congr_fun hF r
  change b.map (F r) =
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom (a.map r) at h
  rw [SchemeRelativeFrobeniusAffineMap.ringMap_eq_native] at h
  exact h

variable [Algebra.FormallySmooth C S]

private def cotangentNative [CharP B p] :
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) :=
      Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
    KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p) →ₗ[RelativeFrobenius.twist (algebraMap K B) p]
      KaehlerDifferential K B := by
  letI : Algebra C B := residueCAlgebra (C := C) (K := K) (B := B)
  letI : IsScalarTower C K B := residueCoefficientTower (C := C) (K := K) (B := B)
  letI : Algebra S B := b.map.toAlgebra
  letI : IsScalarTower C S B := targetTower p (a := a) (b := b) (F := F) hF ha
  exact DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc rfl F.toRingHom
    (native_square p (a := a) (b := b) (F := F) hF) (algebraMap C R)
    (source_base p (c := c) (a := a) ha hc) F.commutes

private def oneFormNative [CharP B p] :
    KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p) →ₗ[RelativeFrobenius.twist (algebraMap K B) p]
      SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p 1 := by
  letI : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) :=
    Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
  let Ξ := cotangentNative p c a b F hF ha hc
  exact
    { toFun := fun ω => (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm (Ξ ω)
      map_add' := fun η ζ => by rw [map_add, map_add]; rfl
      map_smul' := fun t η => by
        change (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm (Ξ (t • η)) =
          (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom t •
            (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm (Ξ η)
        rw [Ξ.map_smul]
        change (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
            ((RelativeFrobenius.map (algebraMap K B) p).hom t • Ξ η) = _
        rw [SchemeRelativeFrobeniusAffineMap.ringMap_eq_native]
        exact map_smul (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm _ _ }

/-- ACTUAL individual divided Frobenius one-form map, including zero B, with original geometric beta action. -/
def oneFormMap :
    KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p) →ₗ[RelativeFrobenius.twist (algebraMap K B) p]
      SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p 1 := by
  classical
  exact if h : Nontrivial B then by
    letI := h
    letI : CharP B p := charP_of_injective_algebraMap (algebraMap K B).injective p
    exact oneFormNative p c a b F hF ha hc
  else 0

private theorem oneFormMap_eq_native [Nontrivial B] [CharP B p] :
    oneFormMap p c a b F hF ha hc = oneFormNative p c a b F hF ha hc := by
  classical
  simp only [oneFormMap, dif_pos (inferInstance : Nontrivial B)]

/-- EVERY actual divisor of dF(r) gives the same ORIGINAL native one-form value. -/
theorem oneFormMap_D_of_lift (r : R) (η : KaehlerDifferential C S)
    (hη : (p : S) • η = KaehlerDifferential.D C S (F r)) :
    letI : Algebra C B := residueCAlgebra (C := C) (K := K) (B := B)
    letI : IsScalarTower C K B := residueCoefficientTower (C := C) (K := K) (B := B)
    letI : Algebra S B := b.map.toAlgebra
    letI : IsScalarTower C S B := targetTower p (a := a) (b := b) (F := F) hF ha
    (exteriorPower.oneEquiv B (KaehlerDifferential K B))
        (oneFormMap p c a b F hF ha hc
          (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p) (a.map r))) =
      KaehlerDifferential.map C K S B η := by
  let : Algebra C B := residueCAlgebra (C := C) (K := K) (B := B)
  let : IsScalarTower C K B := residueCoefficientTower (C := C) (K := K) (B := B)
  let : Algebra S B := b.map.toAlgebra
  let : IsScalarTower C S B := targetTower p (a := a) (b := b) (F := F) hF ha
  classical
  by_cases h : Nontrivial B
  · let := h
    let : CharP B p := charP_of_injective_algebraMap (algebraMap K B).injective p
    rw [oneFormMap_eq_native]
    change (exteriorPower.oneEquiv B (KaehlerDifferential K B))
        ((exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
          (cotangentNative p c a b F hF ha hc
            (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p) (a.map r)))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap_D_of_lift
      c a b hc rfl F.toRingHom (native_square p (a := a) (b := b) (F := F) hF)
      (algebraMap C R) (source_base p (c := c) (a := a) ha hc) F.commutes r η hη
  · let : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    let : Subsingleton (KaehlerDifferential K B) :=
      RelativeAllAlgebraCartier.zeroRingModuleSubsingleton (ModuleCat.of B (KaehlerDifferential K B))
    exact Subsingleton.elim _ _

omit [Algebra.FormallySmooth C S] in
private theorem cotangent_value_congr (G : R →ₐ[C] S)
    (φ ψ : RelativeFrobenius.twist (algebraMap K B) p →+* B) (e : φ = ψ)
    (hFφ : ∀ r, b.map (F.toRingHom r) = φ (a.map r))
    (hGφ : ∀ r, b.map (G.toRingHom r) = φ (a.map r))
    (hFψ : ∀ r, b.map (F.toRingHom r) = ψ (a.map r))
    (hGψ : ∀ r, b.map (G.toRingHom r) = ψ (a.map r))
    (ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    FrobeniusLiftDifference.cotangentMap a b φ F.toRingHom G.toRingHom hFφ hGφ c.map c.surjective
        (algebraMap C R) (source_base p (c := c) (a := a) ha hc)
        (fun x => (F.commutes x).trans (G.commutes x).symm) ω =
      FrobeniusLiftDifference.cotangentMap a b ψ F.toRingHom G.toRingHom hFψ hGψ c.map c.surjective
        (algebraMap C R) (source_base p (c := c) (a := a) ha hc)
        (fun x => (F.commutes x).trans (G.commutes x).symm) ω := by
  cases e
  rfl

private theorem exteriorDifferential_zero {n : ℕ} (w : Fin n → B)
    (hw : (MvPolynomial.aeval (R := K) w).toRingHom.Etale) (z : B) :
    EtaleDeRham.differential w hw 0 ((exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm z) =
      (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm (KaehlerDifferential.D K B z) := by
  apply (exteriorPower.oneEquiv B (KaehlerDifferential K B)).injective
  exact (EtaleDeRham.differential_zero w hw z).trans
    ((exteriorPower.oneEquiv B (KaehlerDifferential K B)).apply_symm_apply _).symm

private theorem cotangentNative_sub_value [CharP B p] (G : R →ₐ[C] S)
    (hG : b.map.comp G.toRingHom = (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)
    (ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    cotangentNative p c a b F hF ha hc ω - cotangentNative p c a b G hG ha hc ω =
      KaehlerDifferential.D K B
        (DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm c a b F G
          (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom hF hG ha hc ω) := by
  let : Algebra C B := residueCAlgebra (C := C) (K := K) (B := B)
  let : IsScalarTower C K B := residueCoefficientTower (C := C) (K := K) (B := B)
  let : Algebra S B := b.map.toAlgebra
  let : IsScalarTower C S B := targetTower p (a := a) (b := b) (F := F) hF ha
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) B :=
    Module.compHom B (RelativeFrobenius.map (algebraMap K B) p).hom
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) :=
    Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
  have h := DeligneIllusieLocalContinuationOneFormHomotopy.cotangentMap_sub c a b hc rfl
    F.toRingHom G.toRingHom
    (native_square p (a := a) (b := b) (F := F) hF)
    (native_square p (a := a) (b := b) (F := G) hG)
    (algebraMap C R) (source_base p (c := c) (a := a) ha hc) F.commutes G.commutes
  have hω := congrArg (fun L : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p) →ₗ[RelativeFrobenius.twist (algebraMap K B) p]
    KaehlerDifferential K B => L ω) h
  change cotangentNative p c a b F hF ha hc ω - cotangentNative p c a b G hG ha hc ω =
    KaehlerDifferential.D K B
      (DeligneIllusieLocalContinuationOneFormHomotopy.homotopyTerm c a b F.toRingHom G.toRingHom
        (native_square p (a := a) (b := b) (F := F) hF)
        (native_square p (a := a) (b := b) (F := G) hG)
        (algebraMap C R) (source_base p (c := c) (a := a) ha hc) F.commutes G.commutes ω) at hω
  refine hω.trans ?_
  apply congrArg (KaehlerDifferential.D K B)
  unfold DeligneIllusieLocalContinuationOneFormHomotopy.homotopyTerm
    DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm
  exact cotangent_value_congr p c a b F ha hc G _ _
    (congrArg CommRingCat.Hom.hom (SchemeRelativeFrobeniusAffineMap.ringMap_eq_native (algebraMap K B) p).symm)
    (native_square p (a := a) (b := b) (F := F) hF)
    (native_square p (a := a) (b := b) (F := G) hG)
    (fun r => RingHom.congr_fun hF r) (fun r => RingHom.congr_fun hG r) ω

omit [Algebra.FormallySmooth C S] in
private theorem zeroFormTerm_differential (G : R →ₐ[C] S)
    (hG : b.map.comp G.toRingHom = (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)
    {n : ℕ} (w : Fin n → B) (hw : (MvPolynomial.aeval (R := K) w).toRingHom.Etale)
    (ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    (show ⋀[B]^1 (KaehlerDifferential K B) from
      (SchemeRelativeFrobeniusAffineDeRham.differential w hw p 0).hom
        (DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.nativeZeroFormTerm p c a b F G hF hG ha hc ω)) =
      (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (KaehlerDifferential.D K B
          (DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm c a b F G
            (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom hF hG ha hc ω)) := by
  have hH := DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.nativeZeroFormTerm_apply
    p c a b F G hF hG ha hc ω
  change EtaleDeRham.differential w hw 0
      (show ⋀[B]^0 (KaehlerDifferential K B) from
        DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.nativeZeroFormTerm p c a b F G hF hG ha hc ω) = _
  exact (congrArg (EtaleDeRham.differential w hw 0) hH).trans
    (exteriorDifferential_zero w hw
      (DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm c a b F G
        (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom hF hG ha hc ω))

private theorem oneFormNative_sub_value [CharP B p] (G : R →ₐ[C] S)
    (hG : b.map.comp G.toRingHom = (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)
    (ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    (show ⋀[B]^1 (KaehlerDifferential K B) from
      oneFormNative p c a b F hF ha hc ω - oneFormNative p c a b G hG ha hc ω) =
      (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (cotangentNative p c a b F hF ha hc ω - cotangentNative p c a b G hG ha hc ω) :=
  (map_sub (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
    (cotangentNative p c a b F hF ha hc ω) (cotangentNative p c a b G hG ha hc ω)).symm

/-- ENTIRE actual zero-safe one-form maps differ by the SAME frozen canonical zero-form term. -/
theorem oneFormMap_sub (G : R →ₐ[C] S)
    (hG : b.map.comp G.toRingHom = (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)
    {n : ℕ} (w : Fin n → B) (hw : (MvPolynomial.aeval (R := K) w).toRingHom.Etale) :
    oneFormMap p c a b F hF ha hc - oneFormMap p c a b G hG ha hc =
      (SchemeRelativeFrobeniusAffineDeRham.differential w hw p 0).hom.comp
        (DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.nativeZeroFormTerm
          p c a b F G hF hG ha hc) := by
  classical
  by_cases hB : Nontrivial B
  · let := hB
    let : CharP B p := charP_of_injective_algebraMap (algebraMap K B).injective p
    rw [oneFormMap_eq_native, oneFormMap_eq_native]
    apply LinearMap.ext
    intro ω
    rw [LinearMap.sub_apply, LinearMap.comp_apply]
    exact (oneFormNative_sub_value p c a b F hF ha hc G hG ω).trans
      ((congrArg (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (cotangentNative_sub_value p c a b F hF ha hc G hG ω)).trans
          (zeroFormTerm_differential p c a b F hF ha hc G hG w hw ω).symm)
  · let : Subsingleton B := not_nontrivial_iff_subsingleton.mp hB
    let : Subsingleton (SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p 1) :=
      RelativeAllAlgebraCartier.zeroRingModuleSubsingleton
        (ModuleCat.of B (⋀[B]^1 (KaehlerDifferential K B)))
    exact Subsingleton.elim _ _

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistDividedOneForm
