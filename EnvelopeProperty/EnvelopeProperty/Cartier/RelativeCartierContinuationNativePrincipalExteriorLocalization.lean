import EnvelopeProperty.Cartier.RelativeCartierContinuationNativePrincipalLocalization
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierDomain

/-! # Actual native twist localization of all relative exterior degrees -/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeNativePrincipalExteriorLocalization
open scoped TensorProduct
universe u

/-- Ordinary span extension for an actual scalar-extension map; this abstract lemma
is consumed only with the PROVED native exterior spanning range and wedge formula. -/
private theorem tensor_one_ext {R A P N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup P] [Module R P] [AddCommGroup N] [Module A N]
    (e : A ⊗[R] P →ₗ[A] N)
    (g : letI : Module R N := Module.compHom N (algebraMap R A); P →ₗ[R] N)
    (S : Set P) (hS : Submodule.span R S = ⊤)
    (h : ∀ x ∈ S, e (1 ⊗ₜ[R] x) = g x) (z : P) : e (1 ⊗ₜ[R] z) = g z := by
  let : Module R N := Module.compHom N (algebraMap R A)
  have hz : z ∈ Submodule.span R S := by rw [hS]; trivial
  refine Submodule.span_induction h ?_ ?_ ?_ hz
  · rw [TensorProduct.tmul_zero, map_zero, map_zero]
  · intro x y _ _ hx hy
    rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
  · intro a x _ hx
    have ht : (1 : A) ⊗ₜ[R] (a • x) = algebraMap R A a • (1 ⊗ₜ[R] x) := by
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    calc
      e (1 ⊗ₜ[R] (a • x)) = e (algebraMap R A a • (1 ⊗ₜ[R] x)) := congrArg e ht
      _ = algebraMap R A a • e (1 ⊗ₜ[R] x) := e.map_smul _ _
      _ = algebraMap R A a • g x := congrArg (fun y => algebraMap R A a • y) hx
      _ = g (a • x) := (g.map_smul a x).symm

variable {k B : Type u} [Field k] [CommRing B] [Algebra k B]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra
attribute [local instance] RelativeNativePrincipalLocalization.nativeAlgebra
attribute [local instance] RelativeNativePrincipalLocalization.coefficientTower
attribute [local instance] RelativeNativePrincipalLocalization.native_isLocalization
local notation "T" => RelativeFrobenius.twist (algebraMap k B) p
local notation "bP" z => CommRingCat.Hom.hom
  (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k B) p) z
local notation "locB" z => Localization.Away (bP z)
local notation "αP" z => RingHom.comp (algebraMap B (locB z)) (algebraMap k B)
local notation "L" z => RelativeFrobenius.twist (αP z) p

/-- The SAME original coefficient inclusion on the ACTUAL native localized twist. -/
private instance nativeCoefficientAlgebra (t : T) : Algebra k (L t) :=
  (RelativeFrobenius.coefficientMap (αP t) p).hom.toAlgebra

/-- The literal original exterior numerator map, with native target action.
No chosen chart or basis occurs in this map; its target is the ACTUAL native localized twist. -/
def exteriorMap (t : T) (q : ℕ) :=
  CanonicalGeometry.algebraExteriorLinearMap (B := L t)
    (KaehlerDifferential.map k k (T) (L t)) q

/-- EVERY original ordered wedge has its SAME actual native cotangent image. -/
theorem exteriorMap_wedge (t : T) (q : ℕ) (m : Fin q → KaehlerDifferential k (T)) :
    exteriorMap (k := k) (B := B) p t q (exteriorPower.ιMulti (T) q m) =
      exteriorPower.ιMulti (L t) q (fun i => KaehlerDifferential.map k k (T) (L t) (m i)) :=
  CanonicalGeometry.algebraExteriorLinearMap_wedge _ q m

variable {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)

/-- Actual all-degree tensor localization, using the INTERNALLY proved original
native cotangent basis of the genuine etale chart. -/
def tensorExteriorEquiv (t : T) (q : ℕ) :
    (L t) ⊗[T] (⋀[T]^q (KaehlerDifferential k (T))) ≃ₗ[L t]
      (⋀[L t]^q (KaehlerDifferential k (L t))) :=
  CanonicalGeometry.exteriorKaehlerLocalizationEquiv (Submonoid.powers t)
    (RelativeEtaleCartierDomain.cotangentBasis v hv p) q

/-- All original pure wedges have the canonical actual localized value, including q0. -/
theorem tensorExteriorEquiv_wedge (t : T) (q : ℕ) (m : Fin q → KaehlerDifferential k (T)) :
    tensorExteriorEquiv p v hv t q (1 ⊗ₜ[T] exteriorPower.ιMulti (T) q m) =
      exteriorPower.ιMulti (L t) q (fun i => KaehlerDifferential.map k k (T) (L t) (m i)) :=
  CanonicalGeometry.exteriorKaehlerLocalizationEquiv_wedge (Submonoid.powers t)
    (RelativeEtaleCartierDomain.cotangentBasis v hv p) q m

/-- EVERY original scalar acts through the actual A-linear tensor comparison. -/
theorem tensorExteriorEquiv_tmul_wedge (t : T) (q : ℕ) (a : L t)
    (m : Fin q → KaehlerDifferential k (T)) :
    tensorExteriorEquiv p v hv t q (a ⊗ₜ[T] exteriorPower.ιMulti (T) q m) =
      a • exteriorPower.ιMulti (L t) q
        (fun i => KaehlerDifferential.map k k (T) (L t) (m i)) := by
  have ht : a ⊗ₜ[T] exteriorPower.ιMulti (T) q m =
      a • (1 ⊗ₜ[T] exteriorPower.ιMulti (T) q m) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact (congrArg (tensorExteriorEquiv p v hv t q) ht).trans
    (((tensorExteriorEquiv p v hv t q).map_smul a _).trans
      (congrArg (fun y : ⋀[L t]^q (KaehlerDifferential k (L t)) => a • y)
        (tensorExteriorEquiv_wedge p v hv t q m)))

/-- EVERY original differential tuple retains its original ordered numerator wedge. -/
theorem tensorExteriorEquiv_tmul_D (t : T) (q : ℕ) (a : L t) (x : Fin q → T) :
    tensorExteriorEquiv p v hv t q
        (a ⊗ₜ[T] exteriorPower.ιMulti (T) q (fun i => KaehlerDifferential.D k (T) (x i))) =
      a • exteriorPower.ιMulti (L t) q
        (fun i => KaehlerDifferential.D k (L t) (algebraMap (T) (L t) (x i))) := by
  have h : (fun i => KaehlerDifferential.map k k (T) (L t)
      (KaehlerDifferential.D k (T) (x i))) =
      (fun i => KaehlerDifferential.D k (L t) (algebraMap (T) (L t) (x i))) :=
    funext (fun i => KaehlerDifferential.map_D k k (T) (L t) (x i))
  exact (tensorExteriorEquiv_tmul_wedge p v hv t q a
    (fun i => KaehlerDifferential.D k (T) (x i))).trans
      (congrArg (fun m : Fin q → KaehlerDifferential k (L t) =>
        a • exteriorPower.ιMulti (L t) q m) h)

/-- The whole comparison is the literal canonical exterior numerator on EVERY form. -/
theorem tensorExteriorEquiv_one_tmul (t : T) (q : ℕ)
    (z : ⋀[T]^q (KaehlerDifferential k (T))) :
    tensorExteriorEquiv p v hv t q (1 ⊗ₜ[T] z) = exteriorMap (k := k) (B := B) p t q z := by
  let : Module (T) (⋀[L t]^q (KaehlerDifferential k (L t))) :=
    Module.compHom _ (algebraMap (T) (L t))
  apply tensor_one_ext (R := T) (A := L t)
    (P := ⋀[T]^q (KaehlerDifferential k (T)))
    (N := ⋀[L t]^q (KaehlerDifferential k (L t)))
    (tensorExteriorEquiv p v hv t q).toLinearMap
    (exteriorMap (k := k) (B := B) p t q)
    (Set.range (exteriorPower.ιMulti (T) q))
    (exteriorPower.ιMulti_span (T) q (KaehlerDifferential k (T))) _ z
  rintro _ ⟨m, rfl⟩
  exact (tensorExteriorEquiv_wedge p v hv t q m).trans (exteriorMap_wedge p t q m).symm

/-- EVERY tensor of EVERY original form has its literal canonical localization value. -/
theorem tensorExteriorEquiv_tmul (t : T) (q : ℕ) (a : L t)
    (z : ⋀[T]^q (KaehlerDifferential k (T))) :
    tensorExteriorEquiv p v hv t q (a ⊗ₜ[T] z) =
      a • exteriorMap (k := k) (B := B) p t q z := by
  have ht : a ⊗ₜ[T] z = a • (1 ⊗ₜ[T] z) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact (congrArg (tensorExteriorEquiv p v hv t q) ht).trans
    (((tensorExteriorEquiv p v hv t q).map_smul a _).trans
      (congrArg (fun y : ⋀[L t]^q (KaehlerDifferential k (L t)) => a • y)
        (tensorExteriorEquiv_one_tmul p v hv t q z)))

/-- The ENTIRE actual tensor comparison is independent of the genuine etale chart. -/
theorem tensorExteriorEquiv_eq {m : ℕ} (w : Fin m → B)
    (hw : (MvPolynomial.aeval (R := k) w).toRingHom.Etale) (t : T) (q : ℕ) :
    tensorExteriorEquiv p v hv t q = tensorExteriorEquiv p w hw t q := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro a z
  exact (tensorExteriorEquiv_tmul p v hv t q a z).trans
    (tensorExteriorEquiv_tmul p w hw t q a z).symm

include v hv in
/-- The SAME literal native exterior numerator is genuinely a localized-module map;
its property is DERIVED from the actual localization and actual etale chart. -/
theorem exteriorMap_isLocalizedModule (t : T) (q : ℕ) :
    letI : Module (T) (⋀[L t]^q (KaehlerDifferential k (L t))) :=
      Module.compHom _ (algebraMap (T) (L t))
    IsLocalizedModule (Submonoid.powers t) (exteriorMap (k := k) (B := B) p t q) := by
  let : Module (T) (⋀[L t]^q (KaehlerDifferential k (L t))) :=
    Module.compHom _ (algebraMap (T) (L t))
  exact CanonicalGeometry.algebraExteriorLinearMap_isLocalizedModule (Submonoid.powers t)
    (RelativeEtaleCartierDomain.cotangentBasis v hv p)
    (KaehlerDifferential.map k k (T) (L t)) q

end EnvelopeProperty.Cartier.RelativeNativePrincipalExteriorLocalization
