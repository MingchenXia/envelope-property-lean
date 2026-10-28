/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.Spectrum

/-!
# Ideal calculus on spectra of arbitrary commutative rings

The intrinsic ideal norm is the supremum of the values of all ideal elements at a real
multiplicative ultrametric seminorm. Ideal sums and products satisfy the maximum and product
identities at every point, without any hypothesis on a base field or its valuation.

When the seminorm is bounded by one on the coefficient ring, intrinsic norms equal finite
generator maxima and commute with extension of ideals along a ring homomorphism. Their
logarithms are continuous on the bounded locus for finitely generated ideals. These give the
coefficient-ring foundations for the centered local ideal functions of Fang–Han–Xia, §2.1,
and apply over nontrivially valued bases as well. Boundedness is a condition on the chosen
coefficient ring; it is not imposed automatically on every relative spectrum.
-/

open scoped NNReal ENNReal Topology Pointwise

open Set Topology

noncomputable section

namespace EnvelopeProperty.Berkovich.Spectrum

variable {A : Type*} [CommRing A]

/-- A point is bounded on the affine coordinate ring: all its elements have absolute value
at most one. This is the coefficient bound needed for evaluating an ideal by generators. -/
def IsBounded (x : Spectrum A) : Prop := ∀ a : A, x.val a ≤ 1

theorem IsBounded.comap {B : Type*} [CommRing B] {y : Spectrum B}
    (hy : IsBounded y) (φ : A →+* B) : IsBounded (comap φ y) :=
  fun a => hy (φ a)

/-- The intrinsic norm of an ideal, defined as the supremum of the norms of its elements.
The supremum may be infinite at an arbitrary affine analytic point. -/
def idealNorm (I : Ideal A) (x : Spectrum A) : ℝ≥0∞ := ⨆ a ∈ I, (x.val a : ℝ≥0∞)

/-- The logarithmic ideal function. On bounded points it belongs to `[-∞, 0]`. -/
def idealLog (I : Ideal A) (x : Spectrum A) : EReal := ENNReal.log (idealNorm I x)

theorem val_le_idealNorm (I : Ideal A) (x : Spectrum A) {a : A} (ha : a ∈ I) :
    (x.val a : ℝ≥0∞) ≤ idealNorm I x :=
  le_iSup_of_le a (le_iSup_of_le ha le_rfl)

theorem idealNorm_le_iff (I : Ideal A) (x : Spectrum A) (M : ℝ≥0∞) :
    idealNorm I x ≤ M ↔ ∀ a ∈ I, (x.val a : ℝ≥0∞) ≤ M := by
  simp only [idealNorm, iSup_le_iff]

theorem idealNorm_mono {I J : Ideal A} (hIJ : I ≤ J) (x : Spectrum A) :
    idealNorm I x ≤ idealNorm J x := by
  exact (idealNorm_le_iff I x _).2 fun a ha => val_le_idealNorm J x (hIJ ha)

theorem idealNorm_le_one (I : Ideal A) {x : Spectrum A} (hx : IsBounded x) :
    idealNorm I x ≤ 1 :=
  (idealNorm_le_iff I x 1).2 fun a _ => by exact_mod_cast hx a

theorem idealLog_le_zero (I : Ideal A) {x : Spectrum A} (hx : IsBounded x) :
    idealLog I x ≤ 0 := by
  simpa [idealLog] using ENNReal.log_monotone (idealNorm_le_one I hx)

/-- An ideal norm vanishes exactly when the ideal is contained in the support.
This holds at every affine analytic point, without a boundedness assumption. -/
theorem idealNorm_eq_zero_iff (I : Ideal A) (x : Spectrum A) :
    idealNorm I x = 0 ↔ I ≤ x.val.supp := by
  simp only [idealNorm, ENNReal.iSup_eq_zero, ENNReal.coe_eq_zero]
  rfl

/-- The logarithmic ideal function equals `-∞` exactly on the ideal's vanishing locus. -/
theorem idealLog_eq_bot_iff (I : Ideal A) (x : Spectrum A) :
    idealLog I x = ⊥ ↔ I ≤ x.val.supp := by
  rw [idealLog, ENNReal.log_eq_bot_iff, idealNorm_eq_zero_iff]

/-! ### Independence of generators -/

/-- A seminorm bound on a generating set extends to the ideal it generates, provided the
point is bounded on the coefficient ring. -/
theorem val_le_of_mem_span {x : Spectrum A} (hx : IsBounded x) {S : Set A} {M : ℝ≥0∞}
    (hS : ∀ s ∈ S, (x.val s : ℝ≥0∞) ≤ M) {a : A} (ha : a ∈ Ideal.span S) :
    (x.val a : ℝ≥0∞) ≤ M := by
  let J : Ideal A :=
    { carrier := {a | (x.val a : ℝ≥0∞) ≤ M}
      zero_mem' := by simp
      add_mem' := fun hb hc => by
        exact (ENNReal.coe_le_coe.2 (x.val.map_add _ _)).trans
          (by simpa only [ENNReal.coe_max] using max_le hb hc)
      smul_mem' := fun r b hb => by
        change (x.val (r * b) : ℝ≥0∞) ≤ M
        rw [map_mul, ENNReal.coe_mul]
        calc (x.val r : ℝ≥0∞) * (x.val b : ℝ≥0∞)
            ≤ 1 * (x.val b : ℝ≥0∞) :=
              mul_le_mul' (by exact_mod_cast hx r) le_rfl
          _ ≤ M := by simpa using hb }
  exact (Ideal.span_le.2 hS : Ideal.span S ≤ J) ha

/-- The intrinsic ideal norm is the supremum of the norms of any generating set. -/
theorem idealNorm_span {x : Spectrum A} (hx : IsBounded x) (S : Set A) :
    idealNorm (Ideal.span S) x = ⨆ a ∈ S, (x.val a : ℝ≥0∞) := by
  apply le_antisymm
  · exact (idealNorm_le_iff _ x _).2 fun a ha => val_le_of_mem_span hx
      (fun s hs => le_iSup_of_le s (le_iSup_of_le hs le_rfl)) ha
  · exact iSup_le fun a => iSup_le fun ha => val_le_idealNorm _ x (Ideal.subset_span ha)

/-- For a finite generating family the ideal norm is its maximum, including the empty family. -/
theorem idealNorm_span_finset {x : Spectrum A} (hx : IsBounded x) (S : Finset A) :
    idealNorm (Ideal.span (S : Set A)) x = ((S.sup fun a => x.val a : ℝ≥0) : ℝ≥0∞) := by
  rw [idealNorm_span hx, ENNReal.coe_finset_sup]
  exact (Finset.sup_eq_iSup S _).symm

/-- Finite generating families of the same ideal give the same maximum on bounded points. -/
theorem idealNorm_span_finset_eq_of_span_eq {x : Spectrum A} (hx : IsBounded x)
    (S T : Finset A) (hST : Ideal.span (S : Set A) = Ideal.span (T : Set A)) :
    S.sup (fun a => x.val a) = T.sup (fun a => x.val a) := by
  apply ENNReal.coe_injective
  rw [← idealNorm_span_finset hx S, ← idealNorm_span_finset hx T, hST]

/-! ### Pullback along affine morphisms -/

/-- Pulling back an ideal to a bounded affine point commutes with ideal evaluation. -/
theorem idealNorm_map {B : Type*} [CommRing B]
    (φ : A →+* B) (I : Ideal A) {y : Spectrum B} (hy : IsBounded y) :
    idealNorm (Ideal.map φ I) y = idealNorm I (comap φ y) := by
  have hmap : Ideal.map φ I = Ideal.span (φ '' (I : Set A)) := by
    calc Ideal.map φ I
        = Ideal.map φ (Ideal.span (I : Set A)) := by rw [Ideal.span_eq]
      _ = Ideal.span (φ '' (I : Set A)) := Ideal.map_span φ _
  rw [hmap, idealNorm_span hy]
  apply le_antisymm
  · refine iSup_le fun b => iSup_le fun hb => ?_
    obtain ⟨a, ha, rfl⟩ := hb
    exact val_le_idealNorm I (comap φ y) ha
  · refine (idealNorm_le_iff I (comap φ y) _).2 fun a ha => ?_
    exact le_iSup_of_le (φ a) (le_iSup_of_le ⟨a, ha, rfl⟩ le_rfl)

/-- Extension of an ideal can only increase its intrinsic norm at a point above the base. -/
theorem idealNorm_le_map {B : Type*} [CommRing B] (φ : A →+* B)
    (I : Ideal A) (y : Spectrum B) :
    idealNorm I (comap φ y) ≤ idealNorm (Ideal.map φ I) y :=
  (idealNorm_le_iff I (comap φ y) _).2 fun _ ha =>
    val_le_idealNorm _ y (Ideal.mem_map_of_mem φ ha)

/-- The logarithmic pullback formula for an affine ideal function. -/
theorem idealLog_map {B : Type*} [CommRing B]
    (φ : A →+* B) (I : Ideal A) {y : Spectrum B} (hy : IsBounded y) :
    idealLog (Ideal.map φ I) y = idealLog I (comap φ y) :=
  congrArg ENNReal.log (idealNorm_map φ I hy)

/-! ### Ideal arithmetic -/

@[simp]
theorem idealNorm_bot (x : Spectrum A) : idealNorm (⊥ : Ideal A) x = 0 := by
  simp [idealNorm]

theorem idealNorm_top {x : Spectrum A} (hx : IsBounded x) :
    idealNorm (⊤ : Ideal A) x = 1 := by
  apply le_antisymm (idealNorm_le_one _ hx)
  simpa using val_le_idealNorm (⊤ : Ideal A) x (show (1 : A) ∈ (⊤ : Ideal A) from trivial)

/-- The norm of an ideal sum is the maximum of the two norms. -/
theorem idealNorm_sup (I J : Ideal A) (x : Spectrum A) :
    idealNorm (I ⊔ J) x = max (idealNorm I x) (idealNorm J x) := by
  apply le_antisymm
  · refine (idealNorm_le_iff _ x _).2 fun c hc => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hc
    exact (ENNReal.coe_le_coe.2 (x.val.map_add a b)).trans
      (by simpa only [ENNReal.coe_max] using
        max_le_max (val_le_idealNorm I x ha) (val_le_idealNorm J x hb))
  · exact max_le (idealNorm_mono le_sup_left x) (idealNorm_mono le_sup_right x)

/-- The norm of an ideal product is the product of the norms. -/
theorem idealNorm_mul (I J : Ideal A) (x : Spectrum A) :
    idealNorm (I * J) x = idealNorm I x * idealNorm J x := by
  apply le_antisymm
  · let M := idealNorm I x * idealNorm J x
    let K : Ideal A :=
      { carrier := {c | ∀ r : A, (x.val (r * c) : ℝ≥0∞) ≤ M}
        zero_mem' := fun r => by simp
        add_mem' := fun ha hb r => by
          rw [mul_add]
          exact (ENNReal.coe_le_coe.2 (x.val.map_add _ _)).trans
            (by simpa only [ENNReal.coe_max] using max_le (ha r) (hb r))
        smul_mem' := fun s c hc r => by
          simpa only [smul_eq_mul, mul_assoc] using hc (r * s) }
    have hmul : I * J ≤ K := Ideal.mul_le.2 fun a ha b hb r => by
      rw [← mul_assoc, map_mul, ENNReal.coe_mul]
      exact mul_le_mul' (val_le_idealNorm I x (I.mul_mem_left r ha))
        (val_le_idealNorm J x hb)
    refine (idealNorm_le_iff _ x _).2 fun c hc => ?_
    simpa only [one_mul] using hmul hc 1
  · simp only [idealNorm, ENNReal.iSup_mul, ENNReal.mul_iSup]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun b => iSup_le fun hb => ?_
    rw [← ENNReal.coe_mul, ← map_mul]
    exact val_le_idealNorm (I * J) x (Ideal.mul_mem_mul hb ha)

/-- Ideal powers are evaluated by powers of the ideal norm. -/
theorem idealNorm_pow {x : Spectrum A} (hx : IsBounded x) (I : Ideal A) (n : ℕ) :
    idealNorm (I ^ n) x = idealNorm I x ^ n := by
  induction n with
  | zero => simpa using idealNorm_top hx
  | succ n hn => rw [pow_succ, idealNorm_mul, hn, pow_succ]

/-- Positive powers require no boundedness on the coefficient ring. -/
theorem idealNorm_pow_succ (I : Ideal A) (x : Spectrum A) (n : ℕ) :
    idealNorm (I ^ (n + 1)) x = idealNorm I x ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n hn =>
    calc idealNorm (I ^ (n + 1 + 1)) x
        = idealNorm (I ^ (n + 1)) x * idealNorm I x := by
          rw [pow_succ, idealNorm_mul]
      _ = idealNorm I x ^ (n + 1) * idealNorm I x := by rw [hn]
      _ = idealNorm I x ^ (n + 1 + 1) := (pow_succ _ _).symm

/-! ### Logarithmic model formulas -/

@[simp]
theorem idealLog_bot (x : Spectrum A) : idealLog (⊥ : Ideal A) x = ⊥ := by
  simp [idealLog]

theorem idealLog_top {x : Spectrum A} (hx : IsBounded x) :
    idealLog (⊤ : Ideal A) x = 0 := by
  simp [idealLog, idealNorm_top hx]

theorem idealLog_sup (I J : Ideal A) (x : Spectrum A) :
    idealLog (I ⊔ J) x = max (idealLog I x) (idealLog J x) := by
  exact congrArg ENNReal.log (idealNorm_sup I J x) |>.trans
    ENNReal.log_monotone.map_max

theorem idealLog_mul (I J : Ideal A) (x : Spectrum A) :
    idealLog (I * J) x = idealLog I x + idealLog J x := by
  simp only [idealLog, idealNorm_mul, ENNReal.log_mul_add]

theorem idealLog_pow {x : Spectrum A} (hx : IsBounded x) (I : Ideal A) (n : ℕ) :
    idealLog (I ^ n) x = (n : EReal) * idealLog I x := by
  simp only [idealLog, idealNorm_pow hx, ENNReal.log_pow]

theorem idealLog_pow_succ (I : Ideal A) (x : Spectrum A) (n : ℕ) :
    idealLog (I ^ (n + 1)) x = (n + 1 : EReal) * idealLog I x := by
  simp only [idealLog, idealNorm_pow_succ, ENNReal.log_pow, Nat.cast_add, Nat.cast_one]

/-- A logarithmic ideal function is the finite maximum of the logarithms of generators. -/
theorem idealLog_span_finset {x : Spectrum A} (hx : IsBounded x) (S : Finset A) :
    idealLog (Ideal.span (S : Set A)) x = S.sup (fun a => logAbs a x) := by
  rw [idealLog, idealNorm_span_finset hx, ENNReal.coe_finset_sup]
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    simp only [Finset.sup_insert, ENNReal.log_monotone.map_max, ih, logAbs]

/-- A finitely generated ideal defines a continuous logarithmic function on the bounded locus. -/
theorem continuousOn_idealLog_of_span_eq (I : Ideal A) (S : Finset A)
    (hI : Ideal.span (S : Set A) = I) :
    ContinuousOn (idealLog I) {x : Spectrum A | IsBounded x} := by
  have hcont : Continuous fun x : Spectrum A => S.sup fun a => logAbs a x := by
    classical
    clear hI
    induction S using Finset.induction_on with
    | empty => simpa using (continuous_const : Continuous fun _ : Spectrum A => (⊥ : EReal))
    | @insert a S ha ih =>
      simpa only [Finset.sup_insert] using (continuous_logAbs a).max ih
  refine hcont.continuousOn.congr fun x hx => ?_
  rw [← hI, idealLog_span_finset hx]

end EnvelopeProperty.Berkovich.Spectrum
