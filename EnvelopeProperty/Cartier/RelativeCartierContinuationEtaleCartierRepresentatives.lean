import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierDomain
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierNativeClasses

/-! # Specified polynomial Cartier representatives are actual native étale classes

The adjacent-row quotient defining polynomial Cartier is identified with the
original whole-complex native class, and genuine étale transport retains that
specified representative. All coefficients use the native relative twist.
-/
noncomputable section
namespace EnvelopeProperty.Cartier
open CategoryTheory Limits
open scoped TensorProduct ChangeOfRings
universe u

private theorem actualShortClass_map {A : Type u} [CommRing A]
    {S T : ShortComplex (ModuleCat A)} (φ : S ⟶ T)
    (z : LinearMap.ker S.g.hom) (w : LinearMap.ker T.g.hom)
    (hzw : φ.τ₂ z.val = w.val) :
    ShortComplex.homologyMap φ (S.homologyπ (S.moduleCatCyclesIso.inv z)) =
      T.homologyπ (T.moduleCatCyclesIso.inv w) := by
  have hc : ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv z) =
      T.moduleCatCyclesIso.inv w := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    have h := congrArg (fun F : S.cycles ⟶ T.X₂ => F (S.moduleCatCyclesIso.inv z))
      (ShortComplex.cyclesMap_i φ)
    change T.iCycles (ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv z)) =
      φ.τ₂ (S.iCycles (S.moduleCatCyclesIso.inv z)) at h
    exact h.trans ((congrArg φ.τ₂ (S.moduleCatCyclesIso_inv_iCycles_apply z)).trans
      (hzw.trans (T.moduleCatCyclesIso_inv_iCycles_apply w).symm))
  have h := congrArg (fun F : S.cycles ⟶ T.homology => F (S.moduleCatCyclesIso.inv z))
    (ShortComplex.homologyπ_naturality φ)
  change ShortComplex.homologyMap φ (S.homologyπ (S.moduleCatCyclesIso.inv z)) =
    T.homologyπ (ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv z)) at h
  exact h.trans (congrArg T.homologyπ hc)

private def adjacentRowIso {A : Type u} [CommRing A]
    (X : ℕ → ModuleCat A) (d : ∀ q, X q ⟶ X (q+1))
    (sq : ∀ q, d q ≫ d (q+1) = 0) (q : ℕ) :
    (CochainComplex.of X d sq).sc' q (q+1) (q+1+1) ≅
      ShortComplex.mk (d q) (d (q+1)) (sq q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, CochainComplex.of_d])
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, CochainComplex.of_d])

private theorem adjacentClass_eq_native {A : Type u} [CommRing A]
    (X : ℕ → ModuleCat A) (d : ∀ q, X q ⟶ X (q+1))
    (sq : ∀ q, d q ≫ d (q+1) = 0) (q : ℕ)
    (z : LinearMap.ker (d (q+1)).hom) :
    let K := CochainComplex.of X d sq
    let S := ShortComplex.mk (d q) (d (q+1)) (sq q)
    let H := K.homologyIsoSc' q (q+1) (q+1+1)
      (CochainComplex.prev_nat_succ q) (CochainComplex.next ℕ (q+1)) ≪≫
        ShortComplex.homologyMapIso (adjacentRowIso X d sq q)
    (S.moduleCatHomologyIso.symm ≪≫ H.symm).hom (Submodule.Quotient.mk z) =
      ModuleComplexNativeCycleClasses.cycleClass K (q+1)
        (ModuleComplexNativeCycleClasses.ofCycle X d sq (q+1) z) := by
  let K := CochainComplex.of X d sq
  let S := ShortComplex.mk (d q) (d (q+1)) (sq q)
  let e₀ := K.isoSc' q (q+1) (q+1+1)
    (CochainComplex.prev_nat_succ q) (CochainComplex.next ℕ (q+1))
  let e₁ := adjacentRowIso X d sq q
  let H := K.homologyIsoSc' q (q+1) (q+1+1)
    (CochainComplex.prev_nat_succ q) (CochainComplex.next ℕ (q+1)) ≪≫
      ShortComplex.homologyMapIso e₁
  let zn := ModuleComplexNativeCycleClasses.ofCycle X d sq (q+1) z
  have hm := actualShortClass_map (e₀.hom ≫ e₁.hom) zn z (by rfl)
  have hcomp := congrArg
    (fun f : (K.sc (q+1)).homology ⟶ S.homology =>
      f (ModuleComplexNativeCycleClasses.cycleClass K (q+1) zn))
    (ShortComplex.homologyMap_comp e₀.hom e₁.hom)
  change ShortComplex.homologyMap (e₀.hom ≫ e₁.hom)
      (ModuleComplexNativeCycleClasses.cycleClass K (q+1) zn) =
    H.hom (ModuleComplexNativeCycleClasses.cycleClass K (q+1) zn) at hcomp
  have hH := hcomp.symm.trans (hm.trans (S.moduleCatCyclesIso_inv_π_apply z))
  exact (congrArg H.inv hH.symm).trans (Iso.hom_inv_id_apply H _)

private def initialCycle {A : Type u} [CommRing A]
    (K : CochainComplex (ModuleCat A) ℕ) (z : LinearMap.ker (K.d 0 1).hom) :
    LinearMap.ker (K.sc 0).g.hom :=
  ⟨z.val, by
    change K.d 0 ((ComplexShape.up ℕ).next 0) z.val = 0
    rw [CochainComplex.next ℕ 0]
    exact z.property⟩

private theorem initialClass_eq_native {A : Type u} [CommRing A]
    (K : CochainComplex (ModuleCat A) ℕ) (z : LinearMap.ker (K.d 0 1).hom) :
    (((K.sc' 0 0 1).moduleCatCyclesIso.symm ≪≫
      (K.cyclesIsoSc' 0 0 1 CochainComplex.prev_nat_zero (by simp)).symm ≪≫
        K.isoHomologyπ₀).hom z) =
      ModuleComplexNativeCycleClasses.cycleClass K 0 (initialCycle K z) := by
  let e := K.cyclesIsoSc' 0 0 1 CochainComplex.prev_nat_zero (by simp)
  let zn := initialCycle K z
  have hc : e.inv ((K.sc' 0 0 1).moduleCatCyclesIso.inv z) =
      (K.sc 0).moduleCatCyclesIso.inv zn := by
    apply (ModuleCat.mono_iff_injective (K.iCycles 0)).mp inferInstance
    have h := congrArg
      (fun f : (K.sc' 0 0 1).cycles ⟶ K.X 0 =>
        f ((K.sc' 0 0 1).moduleCatCyclesIso.inv z))
      (K.cyclesIsoSc'_inv_iCycles 0 0 1 CochainComplex.prev_nat_zero (by simp))
    change K.iCycles 0 (e.inv ((K.sc' 0 0 1).moduleCatCyclesIso.inv z)) =
      (K.sc' 0 0 1).iCycles ((K.sc' 0 0 1).moduleCatCyclesIso.inv z) at h
    exact h.trans (((K.sc' 0 0 1).moduleCatCyclesIso_inv_iCycles_apply z).trans
      ((K.sc 0).moduleCatCyclesIso_inv_iCycles_apply zn).symm)
  change K.homologyπ 0 (e.inv ((K.sc' 0 0 1).moduleCatCyclesIso.inv z)) =
    K.homologyπ 0 ((K.sc 0).moduleCatCyclesIso.inv zn)
  exact congrArg (K.homologyπ 0) hc

namespace RelativePolynomialCartier
variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)
local notation "P" => MvPolynomial (Fin n) k
local notation "T" => RelativeFrobenius.twist (algebraMap k P) p
local notation "KP" => RelativeEtaleDeRham.complex (MvPolynomial.X : Fin n → P)
  (polynomialEtale k n) p

private theorem polynomialNativeSquare (q : ℕ) :
    RelativeEtaleDeRham.differential (MvPolynomial.X : Fin n → P) (polynomialEtale k n) p q ≫
      RelativeEtaleDeRham.differential (MvPolynomial.X : Fin n → P) (polynomialEtale k n) p (q+1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  exact EtaleDeRham.differential_square (MvPolynomial.X : Fin n → P) (polynomialEtale k n) q w

/-- Every specified positive polynomial Cartier representative is an actual native cycle. -/
def positiveNativeCycle (q : ℕ) (w : ⋀[T]^(q+1) (KaehlerDifferential k T)) :
    LinearMap.ker ((KP).sc (q+1)).g.hom :=
  ModuleComplexNativeCycleClasses.ofCycle _ _ (polynomialNativeSquare k p n)
    (q+1) (positiveRepresentative k p n q w)

/-- The native cycle retains its entire original residual polynomial form. -/
theorem positiveNativeCycle_val (q : ℕ) (w : ⋀[T]^(q+1) (KaehlerDifferential k T)) :
    (positiveNativeCycle k p n q w).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := P) p (q+1) from
        originalExteriorRepresentative k p n (q+1) w) := rfl

/-- The original adjacent-row quotient class equals the actual whole-complex native class. -/
theorem positiveCycleClass_eq_native (q : ℕ)
    (z : LinearMap.ker (positiveShortComplex k p n q).g.hom) :
    positiveCycleClass k p n q z = ModuleComplexNativeCycleClasses.cycleClass KP (q+1)
      (ModuleComplexNativeCycleClasses.ofCycle _ _ (polynomialNativeSquare k p n) (q+1) z) := by
  unfold positiveCycleClass positiveQuotientIso positiveHomologyIso
  exact adjacentClass_eq_native _ _ _ q z

/-- The SAME positive Cartier isomorphism has its specified actual native cycle class. -/
theorem inverseCartierIso_succ_nativeClass (q : ℕ)
    (w : ⋀[T]^(q+1) (KaehlerDifferential k T)) :
    (inverseCartierIso k p n (q+1)).hom w =
      ModuleComplexNativeCycleClasses.cycleClass KP (q+1) (positiveNativeCycle k p n q w) :=
  positiveCycleClass_eq_native k p n q (positiveRepresentative k p n q w)

/-- The specified original degree-zero representative is an actual native initial cycle. -/
def zeroNativeCycle (t : T) : LinearMap.ker ((KP).sc 0).g.hom :=
  initialCycle KP (zeroCycleRepresentative k p n t)

/-- The actual initial native cycle has precisely its original relative Frobenius value. -/
theorem zeroNativeCycle_val (t : T) : (zeroNativeCycle k p n t).val =
    (show RelativeEtaleDeRham.formModule (R := k) (B := P) p 0 from
      (exteriorPower.zeroEquiv P (KaehlerDifferential k P)).symm
        ((RelativeFrobenius.map (algebraMap k P) p).hom t)) :=
  zeroRepresentative_val k p n t

/-- The SAME degree-zero Cartier equivalence takes its specified actual native initial class. -/
theorem inverseCartierZero_nativeClass (t : T) : inverseCartierZeroEquiv k p n t =
    ModuleComplexNativeCycleClasses.cycleClass KP 0 (zeroNativeCycle k p n t) :=
  initialClass_eq_native KP (zeroCycleRepresentative k p n t)

/-- Every original exterior degree has its specified actual native polynomial cycle. -/
def nativeCycle : (q : ℕ) → (⋀[T]^q (KaehlerDifferential k T)) →
    LinearMap.ker ((KP).sc q).g.hom
  | 0, w => zeroNativeCycle k p n (exteriorPower.zeroEquiv T (KaehlerDifferential k T) w)
  | q+1, w => positiveNativeCycle k p n q w

/-- The zero branch keeps the SAME original Ω⁰ identity and actual relative Frobenius. -/
theorem nativeCycle_zero_val (w : ⋀[T]^0 (KaehlerDifferential k T)) :
    (nativeCycle k p n 0 w).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := P) p 0 from
        (exteriorPower.zeroEquiv P (KaehlerDifferential k P)).symm
          ((RelativeFrobenius.map (algebraMap k P) p).hom
            (exteriorPower.zeroEquiv T (KaehlerDifferential k T) w))) :=
  zeroNativeCycle_val k p n _

/-- The actual all-degree polynomial Cartier isomorphism takes its specified native class. -/
theorem inverseCartierIso_nativeClass (q : ℕ) (w : ⋀[T]^q (KaehlerDifferential k T)) :
    (inverseCartierIso k p n q).hom w =
      ModuleComplexNativeCycleClasses.cycleClass KP q (nativeCycle k p n q w) := by
  cases q with
  | zero => exact inverseCartierZero_nativeClass k p n _
  | succ q => exact inverseCartierIso_succ_nativeClass k p n q w
end RelativePolynomialCartier

namespace RelativeEtaleCartierRepresentatives
variable {k B : Type u} [Field k] [CommRing B] [Algebra k B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP B p]
local notation "P" => MvPolynomial (Fin n) k
local notation "TP" => RelativeFrobenius.twist (algebraMap k P) p
local notation "TB" => RelativeFrobenius.twist (algebraMap k B) p
local notation "KB" => RelativeEtaleDeRham.complex v hv p

/-- Actual native étale cycles of the specified original polynomial Cartier representatives. -/
def positiveCycle (q : ℕ) (t : TB) (w : ⋀[TP]^(q+1) (KaehlerDifferential k TP)) :
    LinearMap.ker ((KB).sc (q+1)).g.hom :=
  RelativeEtaleNativeClasses.etaleCycle v hv p (q+1) t
    (RelativePolynomialCartier.positiveNativeCycle k p n q w)

/-- The actual étale representative is the SAME original pulled residual form. -/
theorem positiveCycle_val (q : ℕ) (t : TB) (w : ⋀[TP]^(q+1) (KaehlerDifferential k TP)) :
    (positiveCycle v hv p q t w).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := B) p (q+1) from
        (RelativeFrobenius.map (algebraMap k B) p).hom t •
          EtaleDeRham.polynomialFormMap v hv (q+1)
            (RelativePolynomialCartier.originalExteriorRepresentative k p n (q+1) w)) :=
  RelativeEtaleNativeClasses.etaleCycle_val v hv p (q+1) t _

/-- EVERY positive Cartier exterior tensor has its specified actual native étale class. -/
theorem inverseCartierIso_succ_tmul_class (q : ℕ) (t : TB)
    (w : ⋀[TP]^(q+1) (KaehlerDifferential k TP)) :
    let := (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
    (RelativeEtaleCartierDomain.inverseCartierIso v hv p (q+1)).hom
      ((RelativeEtaleCartierDomain.exteriorIso v hv p (q+1)).hom (t ⊗ₜ[TP] w)) =
      ModuleComplexNativeCycleClasses.cycleClass KB (q+1) (positiveCycle v hv p q t w) := by
  have h := RelativeEtaleCartierDomain.inverseCartierIso_tmul v hv p (q+1) t w
  rw [RelativePolynomialCartier.inverseCartierIso_succ_nativeClass k p n q w] at h
  exact h.trans (RelativeEtaleNativeClasses.homologyIso_inv_tmul_cycleClass v hv p (q+1) t _)

/-- Actual native étale cycles of the specified polynomial representatives in EVERY degree. -/
def nativeCycle (q : ℕ) (t : TB) (w : ⋀[TP]^q (KaehlerDifferential k TP)) :
    LinearMap.ker ((KB).sc q).g.hom :=
  RelativeEtaleNativeClasses.etaleCycle v hv p q t (RelativePolynomialCartier.nativeCycle k p n q w)

/-- Every original representative retains its entire actual pulled value in every degree. -/
theorem nativeCycle_val (q : ℕ) (t : TB) (w : ⋀[TP]^q (KaehlerDifferential k TP)) :
    (nativeCycle v hv p q t w).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := B) p q from
        (RelativeFrobenius.map (algebraMap k B) p).hom t •
          EtaleDeRham.polynomialFormMap v hv q (RelativePolynomialCartier.nativeCycle k p n q w).val) :=
  RelativeEtaleNativeClasses.etaleCycle_val v hv p q t _

/-- The original coefficient inclusion acts by its SAME original coefficient on every native cycle. -/
theorem nativeCycle_coefficient_val (q : ℕ) (a : k) (w : ⋀[TP]^q (KaehlerDifferential k TP)) :
    (nativeCycle v hv p q ((RelativeFrobenius.coefficientMap (algebraMap k B) p).hom a) w).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := B) p q from
        (algebraMap k B a) • EtaleDeRham.polynomialFormMap v hv q
          (RelativePolynomialCartier.nativeCycle k p n q w).val) :=
  RelativeEtaleNativeClasses.etaleCycle_coefficient_val v hv p q a _

/-- EVERY native étale Cartier exterior tensor takes its specified actual native class. -/
theorem inverseCartierIso_tmul_class (q : ℕ) (t : TB) (w : ⋀[TP]^q (KaehlerDifferential k TP)) :
    let := (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
    (RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom
      ((RelativeEtaleCartierDomain.exteriorIso v hv p q).hom (t ⊗ₜ[TP] w)) =
      ModuleComplexNativeCycleClasses.cycleClass KB q (nativeCycle v hv p q t w) := by
  have h := RelativeEtaleCartierDomain.inverseCartierIso_tmul v hv p q t w
  rw [RelativePolynomialCartier.inverseCartierIso_nativeClass k p n q w] at h
  exact h.trans (RelativeEtaleNativeClasses.homologyIso_inv_tmul_cycleClass v hv p q t _)
end RelativeEtaleCartierRepresentatives
end EnvelopeProperty.Cartier
