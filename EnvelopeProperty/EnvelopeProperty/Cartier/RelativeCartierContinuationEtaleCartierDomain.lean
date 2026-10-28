import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleComplexBaseChange
import EnvelopeProperty.Cartier.RelativeCartierContinuationPolynomialCohomologyZero
import EnvelopeProperty.Cartier.ExteriorBasisScalarExtension
import Mathlib.RingTheory.Etale.Kaehler

/-! # Genuine cotangent/exterior domain and native etale Cartier module equivalences

The original coefficient inclusion and actual etale twist map give the scalar
tower. Native formally-etale Kahler exchange supplies the actual domain. No
Cartier comparison or target module action is supplied as an assumption.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeEtaleCartierDomain
open CategoryTheory Limits
open scoped TensorProduct
universe u
variable {k B : Type u} [Field k] [CommRing B] [Algebra k B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "P" => MvPolynomial (Fin n) k
local notation "TP" => RelativeFrobenius.twist (algebraMap k P) p
local notation "TB" => RelativeFrobenius.twist (algebraMap k B) p

/-- The actual ORIGINAL coefficient inclusion supplies the native k-algebra on T_B. -/
abbrev coefficientAlgebra : Algebra k TB :=
  (RelativeFrobenius.coefficientMap (algebraMap k B) p).hom.toAlgebra

attribute [local instance] coefficientAlgebra

/-- The actual whole coefficient triangle derives the native scalar tower. -/
theorem coefficient_scalarTower :
    let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
    IsScalarTower k TP TB := by
  let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  exact (congrArg CommRingCat.Hom.hom
    (RelativeEtaleComplexBaseChange.chartTwistMap_coefficient (k := k) v p)).symm

/-- Genuine formally-etale base change of the ORIGINAL native cotangent modules. -/
def cotangentIso :
    (ModuleCat.extendScalars (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom).obj
      (ModuleCat.of TP (KaehlerDifferential k TP)) ≅ ModuleCat.of TB (KaehlerDifferential k TB) := by
  let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
  let :=  coefficient_scalarTower (k := k) v p
  let : Algebra.Etale TP TB := RelativeEtaleComplexBaseChange.chartTwistMap_etale v hv p
  exact (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k TP TB).toModuleIso

/-- Every original cotangent tensor has its SAME actual canonical cotangent image. -/
theorem cotangentIso_tmul (t : TB) (w : KaehlerDifferential k TP) :
    let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
    let :=  coefficient_scalarTower (k := k) v p
    (cotangentIso v hv p).hom (t ⊗ₜ[TP] w) = t • KaehlerDifferential.map k k TP TB w := by
  let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
  let :=  coefficient_scalarTower (k := k) v p
  let : Algebra.Etale TP TB := RelativeEtaleComplexBaseChange.chartTwistMap_etale v hv p
  change KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k TP TB (t ⊗ₜ[TP] w) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul]

/-- The actual extended polynomial twist basis becomes an ORIGINAL native cotangent basis. -/
def cotangentBasis : Module.Basis (Fin n) TB (KaehlerDifferential k TB) := by
  let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
  exact ((RelativePolynomialCartier.twistBasis k p n).baseChange TB).map
    (cotangentIso v hv p).toLinearEquiv

/-- The true target basis consists of the SAME actual cotangent images. -/
theorem cotangentBasis_apply (i : Fin n) :
    let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
    let :=  coefficient_scalarTower (k := k) v p
    cotangentBasis v hv p i = KaehlerDifferential.map k k TP TB
      (RelativePolynomialCartier.twistBasis k p n i) := by
  let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
  change (cotangentIso v hv p).hom
    (((RelativePolynomialCartier.twistBasis k p n).baseChange TB) i) = _
  rw [Module.Basis.baseChange_apply]
  exact (cotangentIso_tmul v hv p (1 : TB)
    (RelativePolynomialCartier.twistBasis k p n i)).trans (one_smul TB _)

/-- The actual twist chart takes EVERY original Y_i to the SAME original source inclusion of v_i. -/
theorem coordinate_image (i : Fin n) :
    (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom
      (RelativePolynomialCartier.twistCoordinate k p n i) =
      (RelativeFrobenius.sourceMap (algebraMap k B) p).hom (v i) := by
  rw [RelativePolynomialCartier.twistCoordinate,
    RelativePolynomialPresentation.polynomialPresentation_X]
  have h := congrArg (fun h : CommRingCat.of P ⟶ TB => h.hom (MvPolynomial.X i))
    (RelativeEtaleComplexBaseChange.chartTwistMap_source (k := k) v p)
  change (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom
    ((RelativeFrobenius.sourceMap (algebraMap k P) p).hom (MvPolynomial.X i)) =
    (RelativeFrobenius.sourceMap (algebraMap k B) p).hom
      ((MvPolynomial.aeval v) (MvPolynomial.X i)) at h
  exact h.trans (congrArg (RelativeFrobenius.sourceMap (algebraMap k B) p).hom
    (MvPolynomial.aeval_X v i))

/-- The actual target cotangent basis is PRECISELY d(source_B(v_i)), with original coefficients. -/
theorem cotangentBasis_D (i : Fin n) : cotangentBasis v hv p i =
    KaehlerDifferential.D k TB ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom (v i)) := by
  let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
  let :=  coefficient_scalarTower (k := k) v p
  rw [cotangentBasis_apply, RelativePolynomialCartier.twistBasis_apply,
    KaehlerDifferential.map_D]
  exact congrArg (KaehlerDifferential.D k TB) (coordinate_image (k := k) v p i)

/-- The actual degree-one basis comparison is the SAME canonical cotangent exchange. -/
theorem basisEquiv_eq_cotangentIso :
    let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
    ((RelativePolynomialCartier.twistBasis k p n).baseChange TB).equiv
      (cotangentBasis v hv p) (Equiv.refl _) = (cotangentIso v hv p).toLinearEquiv := by
  let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
  apply LinearEquiv.toLinearMap_injective
  apply ((RelativePolynomialCartier.twistBasis k p n).baseChange TB).ext
  intro i
  rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
  rfl

/-- Genuine native extension of EVERY original twist exterior power to the actual T_B exterior power. -/
def exteriorIso (q : ℕ) :
    (ModuleCat.extendScalars (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom).obj
      (ModuleCat.of TP (⋀[TP]^q (KaehlerDifferential k TP))) ≅
      ModuleCat.of TB (⋀[TB]^q (KaehlerDifferential k TB)) := by
  let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
  exact ((((RelativePolynomialCartier.twistBasis k p n).exteriorPower q).baseChange TB).equiv
    ((cotangentBasis v hv p).exteriorPower q) (Equiv.refl _)).toModuleIso

/-- EVERY original scalar/exterior-basis tensor keeps its actual scalar and actual image wedge. -/
theorem exteriorIso_tmul_basis (q : ℕ) (t : TB) (s : Set.powersetCard (Fin n) q) :
    let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
    (exteriorIso v hv p q).hom
      (t ⊗ₜ[TP] (RelativePolynomialCartier.twistBasis k p n).exteriorPower q s) =
      t • (cotangentBasis v hv p).exteriorPower q s := by
  let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
  change ((((RelativePolynomialCartier.twistBasis k p n).exteriorPower q).baseChange TB).equiv
    ((cotangentBasis v hv p).exteriorPower q) (Equiv.refl _))
      (t ⊗ₜ[TP] (RelativePolynomialCartier.twistBasis k p n).exteriorPower q s) = _
  have h : t ⊗ₜ[TP] (RelativePolynomialCartier.twistBasis k p n).exteriorPower q s =
      t • ((1 : TB) ⊗ₜ[TP] (RelativePolynomialCartier.twistBasis k p n).exteriorPower q s) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, ← Module.Basis.baseChange_apply, Module.Basis.equiv_apply]
  rfl

/-- EVERY decomposable original wedge maps to the wedge of the SAME canonical cotangent images. -/
theorem exteriorIso_wedge (q : ℕ) (w : Fin q → KaehlerDifferential k TP) :
    let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
    (exteriorIso v hv p q).hom ((1 : TB) ⊗ₜ[TP] exteriorPower.ιMulti TP q w) =
      exteriorPower.ιMulti TB q (fun j => (cotangentIso v hv p).hom ((1 : TB) ⊗ₜ[TP] w j)) := by
  let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
  change ((((RelativePolynomialCartier.twistBasis k p n).exteriorPower q).baseChange TB).equiv
    ((cotangentBasis v hv p).exteriorPower q) (Equiv.refl _))
      ((1 : TB) ⊗ₜ[TP] exteriorPower.ιMulti TP q w) = _
  rw [ExteriorBasisScalarExtension.exteriorEquiv_wedge, basisEquiv_eq_cotangentIso]
  rfl

private def moduleAssembly {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {M N : ModuleCat A} {V W : ModuleCat B}
    (e : (ModuleCat.extendScalars f).obj M ≅ V) (c : M ≅ N)
    (h : W ≅ (ModuleCat.extendScalars f).obj N) : V ≅ W :=
  e.symm ≪≫ (ModuleCat.extendScalars f).mapIso c ≪≫ h.symm

private theorem moduleAssembly_tmul {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {M N : ModuleCat A} {V W : ModuleCat B}
    (e : (ModuleCat.extendScalars f).obj M ≅ V) (c : M ≅ N)
    (h : W ≅ (ModuleCat.extendScalars f).obj N) (b : B) (m : M) :
    let _ := f.toAlgebra
    (moduleAssembly f e c h).hom (e.hom (b ⊗ₜ[A] m)) = h.inv (b ⊗ₜ[A] c.hom m) := by
  let := f.toAlgebra
  change h.inv (((ModuleCat.extendScalars f).map c.hom) (e.inv (e.hom (b ⊗ₜ[A] m)))) = _
  have hi := Iso.hom_inv_id_apply e (b ⊗ₜ[A] m)
  have hh := congrArg (fun z : (ModuleCat.extendScalars f).obj M =>
    h.inv (((ModuleCat.extendScalars f).map c.hom) z)) hi
  exact hh.trans (congrArg h.inv (ModuleCat.ExtendScalars.map_tmul f c.hom b m))

variable [CharP B p]

/-- Actual native etale Cartier in EVERY degree, derived only from genuine domain and homology exchange. -/
def inverseCartierIso (q : ℕ) : ModuleCat.of TB (⋀[TB]^q (KaehlerDifferential k TB)) ≅
    (RelativeEtaleDeRham.complex v hv p).homology q :=
  moduleAssembly (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom
    (exteriorIso v hv p q) (RelativePolynomialCartier.inverseCartierIso k p n q)
    (RelativeEtaleComplexBaseChange.homologyIso v hv p q)

/-- EVERY original pure exterior tensor has its specified actual polynomial Cartier/native homology value. -/
theorem inverseCartierIso_tmul (q : ℕ) (t : TB) (w : ⋀[TP]^q (KaehlerDifferential k TP)) :
    let :=  (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
    (inverseCartierIso v hv p q).hom ((exteriorIso v hv p q).hom (t ⊗ₜ[TP] w)) =
      (RelativeEtaleComplexBaseChange.homologyIso v hv p q).inv
        (t ⊗ₜ[TP] (RelativePolynomialCartier.inverseCartierIso k p n q).hom w) :=
  moduleAssembly_tmul (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom
    (exteriorIso v hv p q) (RelativePolynomialCartier.inverseCartierIso k p n q)
    (RelativeEtaleComplexBaseChange.homologyIso v hv p q) t w

end EnvelopeProperty.Cartier.RelativeEtaleCartierDomain
