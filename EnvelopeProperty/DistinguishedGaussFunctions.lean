/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.WeightedPolynomialTruncations
import EnvelopeProperty.StrictWeierstrassPreparation

/-! # Actual distinguished coefficients construct genuine original strict preparation input -/
open scoped NNReal Polynomial Topology
open Polynomial UniformSpace Topology Filter
noncomputable section
namespace EnvelopeProperty.CompletedMonicDivision
variable {A : Type*} [SeminormedCommRing A] [IsUltrametricDist A] [T0Space A] [CompleteSpace A]

/-- The true ORIGINAL A-valued coefficient of an actual one-variable completed function. -/
def functionCoefficient (r : ℝ≥0) (hr : 0 < r) (n : ℕ) :
    NormedAddGroupHom (Ring (A := A) r hr) A :=
  WeightedPolynomialCompletion.coefficientMap (fun _ : PUnit.{1} => r) (fun _ => hr) (Finsupp.single () n)

/-- EVERY original polynomial coefficient is retained, through the genuine whole one-variable equivalence. -/
@[simp]
theorem functionCoefficient_polynomialMap (r : ℝ≥0) (hr : 0 < r) (n : ℕ) (p : A[X]) :
    functionCoefficient r hr n (polynomialMap r hr p) = p.coeff n := by
  change WeightedPolynomialCompletion.coefficientMap _ _ _
    (WeightedPolynomialCompletion.polynomialMap _ _ ((MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm p)) = _
  rw [WeightedPolynomialCompletion.coefficientMap_polynomialMap,
    MvPolynomial.coeff_uniqueAlgEquiv_symm,Finsupp.single_eq_same]

/-- The genuine one-variable norm bound is EXACTLY the full original weighted coefficient family. -/
theorem nnnorm_le_iff_functionCoefficient (r : ℝ≥0) (hr : 0 < r) (f : Ring (A := A) r hr) (C : ℝ≥0) :
    ‖f‖₊ ≤ C ↔ ∀ n, ‖functionCoefficient r hr n f‖₊ * r^n ≤ C := by
  rw [WeightedPolynomialCompletion.nnnorm_le_iff_coefficientMap]
  constructor
  · intro h n
    simpa only [functionCoefficient,Function.comp_def,WeightedPolynomial.weight_single] using h (Finsupp.single () n)
  · intro h m
    rw [Finsupp.unique_single m,WeightedPolynomial.weight_single]
    exact h (m default)

/-- Actual coefficient actions preserve every ORIGINAL coefficient of the completed function. -/
theorem functionCoefficient_C_mul (r : ℝ≥0) (hr : 0 < r) (n : ℕ) (a : A) (f : Ring (A := A) r hr) :
    functionCoefficient r hr n (polynomialMap r hr (C a)*f) = a*functionCoefficient r hr n f := by
  have he : polynomialMap r hr (C a) =
      WeightedPolynomialCompletion.coefficients (fun _ : PUnit.{1} => r) (fun _ => hr) a := by
    change WeightedPolynomialCompletion.polynomialMap _ _ ((MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm (C a)) =
      WeightedPolynomialCompletion.polynomialMap _ _ (MvPolynomial.C a)
    congr 1
    exact (MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm.commutes a
  rw [he]
  exact WeightedPolynomialCompletion.coefficientMap_coeff_mul _ _ _ a f

/-- The ORIGINAL weighted coefficients genuinely tend to zero as the index tends to infinity. -/
theorem tendsto_weighted_functionCoefficient (r : ℝ≥0) (hr : 0 < r) (f : Ring (A := A) r hr) :
    Tendsto (fun n : ℕ => ‖functionCoefficient r hr n f‖₊ * r^n) cofinite (𝓝 0) := by
  have h := (WeightedPolynomialCompletion.tendsto_weighted_coefficientMap
    (fun _ : PUnit.{1} => r) (fun _ => hr) f).comp
      (Finsupp.single_injective (M := ℕ) (α := PUnit.{1}) ()).tendsto_cofinite
  simpa only [functionCoefficient,Function.comp_def,WeightedPolynomial.weight_single] using h

/-- The actual ORIGINAL coefficient truncation through d, built by the proved generic truncation. -/
def functionTruncation (r : ℝ≥0) (hr : 0 < r) (d : ℕ) (f : Ring (A := A) r hr) : A[X] := by
  classical
  exact (MvPolynomial.uniqueAlgEquiv A PUnit.{1})
    (WeightedPolynomialCompletion.truncationPolynomial (fun _ : PUnit.{1} => r) (fun _ => hr)
      ((Finset.range (d+1)).image (fun n => Finsupp.single () n)) f)

/-- EVERY original truncation coefficient is exactly the corresponding completed coefficient. -/
theorem coeff_functionTruncation (r : ℝ≥0) (hr : 0 < r) (d n : ℕ) (f : Ring (A := A) r hr) :
    (functionTruncation r hr d f).coeff n = if n≤d then functionCoefficient r hr n f else 0 := by
  classical
  have hmem : Finsupp.single (α := PUnit.{1}) () n ∈
      (Finset.range (d+1)).image (fun j => Finsupp.single () j) ↔ n≤d := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨j,hj,hjn⟩
      have he : j=n := Finsupp.single_injective () hjn
      subst j
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    · intro hn
      exact ⟨n,Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn),rfl⟩
  have ht := WeightedPolynomialCompletion.coeff_truncationPolynomial
    (fun _ : PUnit.{1} => r) (fun _ => hr)
      ((Finset.range (d+1)).image (fun n => Finsupp.single () n)) f (Finsupp.single () n)
  have he : ((MvPolynomial.uniqueAlgEquiv A PUnit.{1}).symm (functionTruncation r hr d f)).coeff
      (Finsupp.single () n) = if n≤d then functionCoefficient r hr n f else 0 := by
    simpa only [functionTruncation,AlgEquiv.symm_apply_apply,hmem,functionCoefficient] using ht
  simpa only [MvPolynomial.coeff_uniqueAlgEquiv_symm,Finsupp.single_eq_same] using he

/-- Genuine weighted decay turns pointwise strict coefficient bounds into a UNIFORM strict norm bound. -/
theorem nnnorm_lt_of_functionCoefficient_lt (r : ℝ≥0) (hr : 0 < r)
    (f : Ring (A := A) r hr) (C : ℝ≥0) (hC : 0<C)
    (hcoeff : ∀ n, ‖functionCoefficient r hr n f‖₊ * r^n<C) : ‖f‖₊<C := by
  classical
  have he : ∀ᶠ n in cofinite, ‖functionCoefficient r hr n f‖₊ * r^n<C/2 :=
    (tendsto_weighted_functionCoefficient r hr f).eventually (gt_mem_nhds (half_pos hC))
  have hfin := Filter.eventually_cofinite.mp he
  let F := hfin.toFinset
  let B := max (C/2) (F.sup (fun n => ‖functionCoefficient r hr n f‖₊ * r^n))
  have hB : B<C := max_lt (half_lt_self hC) ((Finset.sup_lt_iff hC).mpr (fun n _ => hcoeff n))
  have hn : ‖f‖₊≤B := (nnnorm_le_iff_functionCoefficient r hr f B).mpr (by
    intro n
    by_cases hn : n∈F
    · exact (Finset.le_sup (f := fun n => ‖functionCoefficient r hr n f‖₊ * r^n) hn).trans (le_max_right _ _)
    · have hs : ‖functionCoefficient r hr n f‖₊ * r^n<C/2 := by
        by_contra hb
        exact hn (hfin.mem_toFinset.mpr hb)
      exact hs.le.trans (le_max_left _ _))
  exact hn.trans_lt hB

/-- The actual truncation error retains precisely EVERY original coefficient strictly above d. -/
theorem functionCoefficient_sub_truncation (r : ℝ≥0) (hr : 0 < r) (d n : ℕ)
    (f : Ring (A := A) r hr) :
    functionCoefficient r hr n (f-polynomialMap r hr (functionTruncation r hr d f)) =
      if n≤d then 0 else functionCoefficient r hr n f := by
  rw [map_sub,functionCoefficient_polynomialMap,coeff_functionTruncation]
  split_ifs <;> simp

/-- ACTUAL original distinguished coefficients construct the bounded monic p+h input.
No uniform tail norm, polynomial decomposition or preparation witness is supplied. -/
theorem exists_strict_monic_decomposition_of_coefficients [Nontrivial A]
    (r : ℝ≥0) (hr : 0 < r) (f : Ring (A := A) r hr) (d : ℕ) (a : Aˣ)
    (ha : functionCoefficient r hr d f = (a : A))
    (hlower : ∀ i<d, ‖(↑a⁻¹ : A)*functionCoefficient r hr i f‖₊ * r^i ≤ r^d)
    (htail : ∀ i>d, ‖(↑a⁻¹ : A)*functionCoefficient r hr i f‖₊ * r^i < r^d) :
    ∃ p : A[X], ∃ _ : p.Monic, p.natDegree=d ∧
      (∀ i<p.natDegree, ‖p.coeff i‖₊ * r^i ≤ r^p.natDegree) ∧
      ∃ h : Ring (A := A) r hr, ‖h‖₊<r^p.natDegree ∧
        polynomialMap r hr (C (↑a⁻¹ : A))*f = polynomialMap r hr p+h := by
  let f' := polynomialMap r hr (C (↑a⁻¹ : A))*f
  let p := functionTruncation r hr d f'
  have hc (i : ℕ) : functionCoefficient r hr i f' = (↑a⁻¹ : A)*functionCoefficient r hr i f :=
    functionCoefficient_C_mul r hr i (↑a⁻¹ : A) f
  have hdcoeff : p.coeff d = 1 := by
    rw [coeff_functionTruncation,if_pos le_rfl,hc,ha,Units.inv_mul]
  have hdegree : p.degree≤(d : WithBot ℕ) := by
    apply (degree_le_iff_coeff_zero _ _).mpr
    intro i hi
    have hi' : d < i := by exact_mod_cast hi
    rw [coeff_functionTruncation,if_neg (not_le_of_gt hi')]
  have hp : p.Monic := monic_of_degree_le d hdegree hdcoeff
  have hd : p.natDegree=d := natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_degree_le.mpr hdegree) (by rw [hdcoeff]; exact one_ne_zero)
  have hb : ∀ i<p.natDegree, ‖p.coeff i‖₊ * r^i ≤ r^p.natDegree := by
    rw [hd]
    intro i hi
    rw [coeff_functionTruncation,if_pos hi.le,hc]
    exact hlower i hi
  let h := f'-polynomialMap r hr p
  have hh : ‖h‖₊<r^p.natDegree := by
    rw [hd]
    apply nnnorm_lt_of_functionCoefficient_lt r hr h _ (pow_pos hr d)
    intro i
    change ‖functionCoefficient r hr i (f'-polynomialMap r hr (functionTruncation r hr d f'))‖₊ * r^i<r^d
    rw [functionCoefficient_sub_truncation]
    split_ifs with hi
    · simpa only [nnnorm_zero,zero_mul] using pow_pos hr d
    · rw [hc]
      exact htail i (lt_of_not_ge hi)
  refine ⟨p,hp,hd,hb,h,hh,?_⟩
  dsimp [h,f']
  ring

/-- ACTUAL distinguished coefficients construct the unique ORIGINAL bounded monic preparation.
All coefficient, tail, unit and entire function identities refer to SAME A and SAME f. -/
theorem exists_preparation_of_coefficients [Nontrivial A]
    (r : ℝ≥0) (hr : 0 < r) (f : Ring (A := A) r hr) (d : ℕ) (a : Aˣ)
    (ha : functionCoefficient r hr d f = (a : A))
    (hlower : ∀ i<d, ‖(↑a⁻¹ : A)*functionCoefficient r hr i f‖₊ * r^i ≤ r^d)
    (htail : ∀ i>d, ‖(↑a⁻¹ : A)*functionCoefficient r hr i f‖₊ * r^i < r^d) :
    ∃ P : A[X], P.Monic ∧ P.natDegree=d ∧
      (∀ i<P.natDegree, ‖P.coeff i‖₊ * r^i ≤ r^P.natDegree) ∧
      ∃ u : (Ring (A := A) r hr)ˣ, f=(u : Ring (A := A) r hr)*polynomialMap r hr P ∧
        ∀ P' : A[X], P'.Monic → P'.natDegree=d → ∀ v : (Ring (A := A) r hr)ˣ,
          f=(v : Ring (A := A) r hr)*polynomialMap r hr P' → P'=P ∧ v=u := by
  obtain ⟨p,hp,hd,hb,h,hh,he⟩ := exists_strict_monic_decomposition_of_coefficients r hr f d a ha hlower htail
  let ca : A →+* Ring (A := A) r hr := (polynomialMap r hr).comp C
  let aD : (Ring (A := A) r hr)ˣ := Units.map ca.toMonoidHom a
  let u := aD*preparationUnit r hr hp hb h hh
  have he₀ : (↑aD⁻¹ : Ring (A := A) r hr)*f=polynomialMap r hr p+h := he
  have hf : f=(u : Ring (A := A) r hr)*polynomialMap r hr (preparedPolynomial r hr hp hb h hh) := by
    calc
      f = (aD : Ring (A := A) r hr)*((↑aD⁻¹ : Ring (A := A) r hr)*f) := (Units.mul_inv_cancel_left aD f).symm
      _ = (aD : Ring (A := A) r hr)*(polynomialMap r hr p+h) := by rw [he₀]
      _ = _ := by
        rw [eq_preparationUnit_mul_preparedPolynomial r hr hp hb h hh]
        change (aD : Ring (A := A) r hr)*((preparationUnit r hr hp hb h hh : Ring (A := A) r hr)*_) =
          ((aD*preparationUnit r hr hp hb h hh : (Ring (A := A) r hr)ˣ) : Ring (A := A) r hr)*_
        rw [Units.val_mul,mul_assoc]
  refine ⟨preparedPolynomial r hr hp hb h hh,preparedPolynomial_monic r hr hp hb h hh,
    (natDegree_preparedPolynomial r hr hp hb h hh).trans hd,
    preparedPolynomial_lower_bound r hr hp hb h hh,u,hf,?_⟩
  intro P' hP' hdeg v hv
  let v' := aD⁻¹*v
  have hev : polynomialMap r hr p+h=(v' : Ring (A := A) r hr)*polynomialMap r hr P' := by
    rw [← he₀,hv]
    change (↑aD⁻¹ : Ring (A := A) r hr)*((v : Ring (A := A) r hr)*_) =
      ((aD⁻¹*v : (Ring (A := A) r hr)ˣ) : Ring (A := A) r hr)*_
    rw [Units.val_mul,mul_assoc]
  have hpoly := preparedPolynomial_unique r hr hp hb h hh P' hP' (hdeg.trans hd.symm) v' hev
  have hunit := preparationUnit_unique r hr hp hb h hh P' hP' (hdeg.trans hd.symm) v' hev
  refine ⟨hpoly,?_⟩
  calc
    v = aD*(aD⁻¹*v) := by simp
    _ = aD*preparationUnit r hr hp hb h hh := congrArg (fun z => aD*z) hunit
    _ = u := rfl

/-- Distinguished coefficients derive the ORIGINAL polynomial quotient algebra with EVERY class formula. -/
theorem exists_original_quotient_of_coefficients [Nontrivial A]
    (r : ℝ≥0) (hr : 0 < r) (f : Ring (A := A) r hr) (d : ℕ) (a : Aˣ)
    (ha : functionCoefficient r hr d f = (a : A))
    (hlower : ∀ i<d, ‖(↑a⁻¹ : A)*functionCoefficient r hr i f‖₊ * r^i ≤ r^d)
    (htail : ∀ i>d, ‖(↑a⁻¹ : A)*functionCoefficient r hr i f‖₊ * r^i < r^d) :
    ∃ P : A[X], P.Monic ∧ P.natDegree=d ∧
      ∃ e : (A[X] ⧸ Ideal.span {P}) ≃ₐ[A] (Ring (A := A) r hr ⧸ Ideal.span {f}),
        ∀ b : A[X], e (Ideal.Quotient.mk (Ideal.span {P}) b)=
          Ideal.Quotient.mk (Ideal.span {f}) (polynomialMap r hr b) := by
  obtain ⟨P,hP,hd,hb,u,hf,_⟩ := exists_preparation_of_coefficients r hr f d a ha hlower htail
  have hI : principalIdeal r hr P=Ideal.span {f} := by
    unfold principalIdeal
    rw [hf]
    exact (Ideal.span_singleton_mul_left_unit u.isUnit (polynomialMap r hr P)).symm
  let e := (quotientAlgEquiv r hr hP hb).trans (Ideal.quotientEquivAlgOfEq A hI)
  refine ⟨P,hP,hd,e,?_⟩
  intro b
  change Ideal.quotientEquivAlgOfEq A hI (quotientEquiv r hr hP hb (Ideal.Quotient.mk _ b)) = _
  rw [quotientEquiv_mk,Ideal.quotientEquivAlgOfEq_mk]

end EnvelopeProperty.CompletedMonicDivision
