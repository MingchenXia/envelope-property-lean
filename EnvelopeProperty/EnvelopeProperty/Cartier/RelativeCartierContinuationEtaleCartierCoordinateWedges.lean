import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierRepresentatives

/-! # The SAME relative Cartier equivalence on every original coordinate wedge -/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeEtaleCartierCoordinateWedges
open CategoryTheory MvPolynomial
open scoped Classical TensorProduct
universe u
variable {k B : Type u} [Field k] [CommRing B] [Algebra k B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP B p]
attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra
local notation "P" => MvPolynomial (Fin n) k
local notation "TP" => RelativeFrobenius.twist (algebraMap k P) p
local notation "TB" => RelativeFrobenius.twist (algebraMap k B) p
local notation "KB" => RelativeEtaleDeRham.complex v hv p

omit [CharP k p] [CharP B p] in
/-- The SAME actual residual monomial evaluates to precisely the original coordinate powers,
without coefficient roots, in EVERY degree including zero. -/
theorem residueMonomial_eval (q : ℕ) (s : Set.powersetCard (Fin n) q) :
    (MvPolynomial.aeval v)
      (monomial (RelativePolynomialCoefficients.residueDigit p q s).toFinsupp (1 : k)) =
      ∏ j : Fin q, (v (Set.powersetCard.ofFinEmbEquiv.symm s j))^(p-1) := by
  have he : (RelativePolynomialCoefficients.residueDigit p q s).toFinsupp =
      Finsupp.indicator s.val (fun _ _ => p-1) := by
    ext i
    simp only [Box.toFinsupp_apply, RelativePolynomialCoefficients.residueDigit_apply,
      Finsupp.indicator_apply]
    by_cases hi : i ∈ s <;> simp [hi, Set.powersetCard.mem_coe_iff]
  have hp : ∏ i ∈ s.val, (v i)^(p-1) =
      ∏ j : Fin q, (v (Set.powersetCard.ofFinEmbEquiv.symm s j))^(p-1) := by
    have h := Finset.prod_map Finset.univ (s.val.orderEmbOfFin s.prop).toEmbedding
      (fun i => (v i)^(p-1))
    have hs := congrArg (fun z : Finset (Fin n) => ∏ i ∈ z, (v i)^(p-1))
      (Finset.map_orderEmbOfFin_univ s.val s.prop)
    exact hs.symm.trans h
  rw [he, ← MvPolynomial.prod_X_pow, map_prod]
  simp only [map_pow, MvPolynomial.aeval_X]
  exact hp

/-- Every specified ACTUAL polynomial native cycle on an original exterior basis vector
has the SAME original residual monomial/basis value, including degree zero. -/
theorem polynomialNativeCycle_basis_val (q : ℕ) (s : Set.powersetCard (Fin n) q) :
    (RelativePolynomialCartier.nativeCycle k p n q
      ((RelativePolynomialCartier.twistBasis k p n).exteriorPower q s)).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := P) p q from
        monomial (RelativePolynomialCoefficients.residueDigit p q s).toFinsupp (1 : k) •
          (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s) := by
  cases q with
  | zero =>
    have hz : s.val = ∅ := Finset.card_eq_zero.mp s.prop
    have he : (RelativePolynomialCoefficients.residueDigit p 0 s).toFinsupp = 0 := by
      ext i
      have hi : i ∉ s := by
        change i ∉ s.val
        rw [hz]
        exact Finset.notMem_empty i
      simp only [Box.toFinsupp_apply, RelativePolynomialCoefficients.residueDigit_apply,
        hi, if_false, Finsupp.coe_zero, Pi.zero_apply]
    rw [RelativePolynomialCartier.nativeCycle_zero_val, exteriorPower.basis_apply,
      exteriorPower.ιMulti_family, exteriorPower.zeroEquiv_ιMulti, map_one,
      he]
    change (exteriorPower.zeroEquiv P (KaehlerDifferential k P)).symm (1 : P) =
      (monomial 0 (1 : k) : P) •
        (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower 0 s
    rw [MvPolynomial.monomial_zero', MvPolynomial.C_1, one_smul]
    apply (exteriorPower.zeroEquiv P (KaehlerDifferential k P)).injective
    rw [LinearEquiv.apply_symm_apply, exteriorPower.basis_apply,
      exteriorPower.ιMulti_family, exteriorPower.zeroEquiv_ιMulti]
  | succ q =>
    change (RelativePolynomialCartier.positiveNativeCycle k p n q
      ((RelativePolynomialCartier.twistBasis k p n).exteriorPower (q+1) s)).val = _
    rw [RelativePolynomialCartier.positiveNativeCycle_val]
    change RelativePolynomialCartier.exteriorRepresentative k p n (q+1)
      ((RelativePolynomialCartier.twistBasis k p n).exteriorPower (q+1) s) =
        (show RelativeEtaleDeRham.formModule (R := k) (B := P) p (q+1) from
          monomial (RelativePolynomialCoefficients.residueDigit p (q+1) s).toFinsupp (1 : k) •
            (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower (q+1) s)
    exact Module.Basis.constr_basis _ _ _ _

/-- Actual whole-complex native coordinate cycles of the SAME relative Cartier map,
constructed from its genuine original polynomial representatives in EVERY degree. -/
def coordinateNativeCycle (q : ℕ) (s : Set.powersetCard (Fin n) q) :
    LinearMap.ker ((KB).sc q).g.hom :=
  RelativeEtaleCartierRepresentatives.nativeCycle v hv p q 1
    ((RelativePolynomialCartier.twistBasis k p n).exteriorPower q s)

/-- Their ENTIRE original form value is the actual coordinate power-differential wedge,
with original coefficients and no closedness or representative premise. -/
theorem coordinateNativeCycle_val (q : ℕ) (s : Set.powersetCard (Fin n) q) :
    (coordinateNativeCycle v hv p q s).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := B) p q from
        exteriorPower.ιMulti B q (fun j =>
          (v (Set.powersetCard.ofFinEmbEquiv.symm s j))^(p-1) •
            KaehlerDifferential.D k B (v (Set.powersetCard.ofFinEmbEquiv.symm s j)))) := by
  rw [coordinateNativeCycle, RelativeEtaleCartierRepresentatives.nativeCycle_val,
    map_one, one_smul, polynomialNativeCycle_basis_val]
  rw [EtaleDeRham.polynomialFormMap_smul_basis, residueMonomial_eval,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  rw [AlternatingMap.map_smul_univ]
  change (∏ j : Fin q, (v (Set.powersetCard.ofFinEmbEquiv.symm s j))^(p-1)) •
      exteriorPower.ιMulti B q (fun j => Char0.etaleDifferentialBasis v hv
        (Set.powersetCard.ofFinEmbEquiv.symm s j)) =
    (∏ j : Fin q, (v (Set.powersetCard.ofFinEmbEquiv.symm s j))^(p-1)) •
      exteriorPower.ιMulti B q (fun j => KaehlerDifferential.D k B
        (v (Set.powersetCard.ofFinEmbEquiv.symm s j)))
  congr 1
  congr 1
  funext j
  exact Char0.etaleDifferentialBasis_apply v hv _

/-- The SAME actual relative Cartier equivalence takes EVERY original native exterior basis
vector to its specified actual native coordinate cycle class, including degree zero. -/
theorem inverseCartierIso_basis_class (q : ℕ) (s : Set.powersetCard (Fin n) q) :
    (RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom
      ((RelativeEtaleCartierDomain.cotangentBasis v hv p).exteriorPower q s) =
      ModuleComplexNativeCycleClasses.cycleClass KB q (coordinateNativeCycle v hv p q s) := by
  let := (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
  have h := RelativeEtaleCartierRepresentatives.inverseCartierIso_tmul_class v hv p q
    (1 : TB) ((RelativePolynomialCartier.twistBasis k p n).exteriorPower q s)
  rw [RelativeEtaleCartierDomain.exteriorIso_tmul_basis, one_smul] at h
  exact h

end EnvelopeProperty.Cartier.RelativeEtaleCartierCoordinateWedges
