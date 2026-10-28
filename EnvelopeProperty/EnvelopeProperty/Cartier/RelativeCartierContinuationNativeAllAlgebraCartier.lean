import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineComplex
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierDomain
import EnvelopeProperty.Cartier.RelativeCartierContinuationAllAlgebraCartier

/-! # Native T-linear Cartier for the actual geometric-beta complex, including zero

The whole complex has an actual identity-component isomorphism from the original ring-map comparison.
The nonzero characteristic and zero native-module branches are derived internally.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeNativeAllAlgebraCartier
open CategoryTheory Limits
universe u
variable {k B : Type u} [Field k] [CommRing B] [Algebra k B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP k p]
attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra
local notation "T" => RelativeFrobenius.twist (algebraMap k B) p
local notation "K" => SchemeRelativeFrobeniusAffineDeRham.complex v hv p

/-- Original whole form modules have a genuine T-linear comparison with identity
underlying maps, derived from the ACTUAL geometric/native ring-map equality. -/
def formIso_native [CharP B p] (q : ℕ) :
    SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := B) p q ≅
      RelativeEtaleDeRham.formModule (R := k) (B := B) p q where
  hom := ModuleCat.ofHom
    (X := SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := B) p q)
    (Y := RelativeEtaleDeRham.formModule (R := k) (B := B) p q)
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a w
        change (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k B) p).hom a • (show ⋀[B]^q (KaehlerDifferential k B) from w) =
          (RelativeFrobenius.map (algebraMap k B) p).hom a •
            (show ⋀[B]^q (KaehlerDifferential k B) from w)
        rw [SchemeRelativeFrobeniusAffineMap.ringMap_eq_native] }
  inv := ModuleCat.ofHom
    (X := RelativeEtaleDeRham.formModule (R := k) (B := B) p q)
    (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := B) p q)
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a w
        change (RelativeFrobenius.map (algebraMap k B) p).hom a • (show ⋀[B]^q (KaehlerDifferential k B) from w) =
          (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k B) p).hom a •
            (show ⋀[B]^q (KaehlerDifferential k B) from w)
        rw [SchemeRelativeFrobeniusAffineMap.ringMap_eq_native] }
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    rfl
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    rfl

/-- EVERY original form is retained by the actual native comparison. -/
theorem formIso_native_hom_apply [CharP B p] (q : ℕ)
    (w : SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := B) p q) :
    (formIso_native (k := k) (B := B) p q).hom w = w := rfl

/-- EVERY original form is also retained by the inverse comparison. -/
theorem formIso_native_inv_apply [CharP B p] (q : ℕ)
    (w : RelativeEtaleDeRham.formModule (R := k) (B := B) p q) :
    (formIso_native (k := k) (B := B) p q).inv w = w := rfl

/-- The ACTUAL whole geometric-beta native complex has its genuine whole
identity-component comparison with the original native characteristic-p complex. -/
def complexIso_native [CharP B p] : (K) ≅ RelativeEtaleDeRham.complex v hv p := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun q => formIso_native (k := k) (B := B) p q) ?_
  intro q r h
  have hr : q+1 = r := h
  subst r
  simp only [SchemeRelativeFrobeniusAffineDeRham.complex, RelativeEtaleDeRham.complex,
    CochainComplex.of_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  rfl

/-- The genuine entire-complex comparison retains EVERY original degree component. -/
theorem complexIso_native_hom_f_apply [CharP B p] (q : ℕ) (w : (K).X q) :
    (complexIso_native v hv p).hom.f q w = w := rfl

/-- The actual native homology functor takes the genuine entire-complex comparison. -/
def homologyIso_native [CharP B p] (q : ℕ) :
    (K).homology q ≅ (RelativeEtaleDeRham.complex v hv p).homology q :=
  (HomologicalComplex.homologyFunctor (ModuleCat T) (ComplexShape.up ℕ) q).mapIso
    (complexIso_native v hv p)

/-- Every actual native T-linear homology object is genuinely zero at an actual zero B. -/
theorem actualHomology_isZero [Subsingleton B] (q : ℕ) : IsZero ((K).homology q) := by
  have : Subsingleton T := RelativeAllAlgebraCartier.twist_subsingleton (k := k) (B := B) p
  have := RelativeAllAlgebraCartier.zeroRingModuleSubsingleton ((K).homology q)
  exact ModuleCat.isZero_of_subsingleton ((K).homology q)

/-- ALL-degree actual Cartier IN ModuleCat T for EVERY actual etale k-algebra,
with the original geometric-beta target and no CharP B/PerfectRing premise. -/
def inverseCartierIso (q : ℕ) :
    ModuleCat.of T (⋀[T]^q (KaehlerDifferential k T)) ≅ (K).homology q := by
  classical
  by_cases h : Nontrivial B
  · letI := h
    letI : CharP B p := charP_of_injective_algebraMap (algebraMap k B).injective p
    exact RelativeEtaleCartierDomain.inverseCartierIso v hv p q ≪≫
      (homologyIso_native v hv p q).symm
  · haveI : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    exact (RelativeAllAlgebraCartier.nativeExterior_isZero (k := k) (B := B) p q).iso
      (actualHomology_isZero v hv p q)

/-- Wherever the previous native Cartier is defined, the SAME entire actual iso
is that native T-linear Cartier followed by the derived whole-complex comparison. -/
theorem inverseCartierIso_eq_native [CharP B p] (q : ℕ) :
    inverseCartierIso v hv p q = RelativeEtaleCartierDomain.inverseCartierIso v hv p q ≪≫
      (homologyIso_native v hv p q).symm := by
  classical
  by_cases h : Nontrivial B
  · simp only [inverseCartierIso, dif_pos h]
  · have : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    apply Iso.ext
    exact (actualHomology_isZero v hv p q).eq_of_tgt _ _

/-- At every actual zero endpoint, the ENTIRE actual native Cartier map is zero. -/
theorem inverseCartierIso_hom_eq_zero [Subsingleton B] (q : ℕ) :
    (inverseCartierIso v hv p q).hom = 0 :=
  (actualHomology_isZero v hv p q).eq_of_tgt _ _

/-- EVERY original T-scalar acts through the SAME whole actual Cartier map,
including q0 and zero endpoints; no B-linear map is promoted to T-linear. -/
theorem inverseCartierIso_smul (q : ℕ) (t : T) (w : ⋀[T]^q (KaehlerDifferential k T)) :
    (inverseCartierIso v hv p q).hom (t • w) =
      t • (inverseCartierIso v hv p q).hom w :=
  (inverseCartierIso v hv p q).hom.hom.map_smul t w

end EnvelopeProperty.Cartier.RelativeNativeAllAlgebraCartier
