import EnvelopeProperty.Berkovich.AffineLine
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Functions polynomial on affine lines

This file supplies the algebraic interpolation step in `lem:fc-lines-poly` of the fibre
constancy blueprint. All line tests concern actual rational affine parameter points; no
analytic or curve-chain hypothesis is used.
-/

open scoped Polynomial
noncomputable section

namespace EnvelopeProperty

namespace FcPolynomialOnLines

variable {F σ : Type*} [Field F]

/-- A function on a set of rational points is polynomial of uniformly bounded degree on
every nonconstant affine line. The values of the function outside the set are irrelevant. -/
def IsPolynomialOnLines (Ω : Set (σ → F)) (c : (σ → F) → F) (N : ℕ) : Prop :=
  ∀ a b : σ → F, b ≠ 0 → ∃ P : F[X], P.natDegree ≤ N ∧
    ∀ t : F, AffineLine.point a b t ∈ Ω → c (AffineLine.point a b t) = P.eval t

theorem IsPolynomialOnLines.mono {Ω Ω' : Set (σ → F)} {c : (σ → F) → F} {N : ℕ}
    (hc : IsPolynomialOnLines Ω c N) (h : Ω' ⊆ Ω) : IsPolynomialOnLines Ω' c N := by
  intro a b hb
  obtain ⟨P, hP, he⟩ := hc a b hb
  exact ⟨P, hP, fun t ht => he t (h ht)⟩

/-- Polynomial agreement on a principal open determines the entire multivariate polynomial. -/
theorem eq_of_eval_eq_on_principalOpen [Infinite F]
    {g P Q : MvPolynomial σ F} (hg : g ≠ 0)
    (h : ∀ x : σ → F, MvPolynomial.eval x g ≠ 0 →
      MvPolynomial.eval x P = MvPolynomial.eval x Q) : P = Q := by
  have hz : g * (P - Q) = 0 := by
    apply MvPolynomial.funext
    intro x
    by_cases hx : MvPolynomial.eval x g = 0
    · simp [hx]
    · simp [h x hx]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hg)

/-- Agreement with a polynomial on a nonempty principal open propagates to every point of
the original domain along a line meeting that open. This is the last step of the proof of
`lem:fc-lines-poly`; the degree bound is needed for interpolation, but not for this step. -/
theorem eqOn_of_eqOn_principalOpen [Infinite F] [Nonempty σ]
    {Ω : Set (σ → F)} {c : (σ → F) → F} {N : ℕ}
    (hc : IsPolynomialOnLines Ω c N) {g : MvPolynomial σ F} (hg : g ≠ 0)
    (hΩ : ∀ x : σ → F, MvPolynomial.eval x g ≠ 0 → x ∈ Ω)
    {Q : MvPolynomial σ F}
    (hQ : ∀ x : σ → F, MvPolynomial.eval x g ≠ 0 → c x = MvPolynomial.eval x Q) :
    ∀ x ∈ Ω, c x = MvPolynomial.eval x Q := by
  intro x hx
  obtain ⟨b, hb, hline⟩ := AffineLine.exists_direction_subst_ne_zero x hg
  obtain ⟨P, _hP, hP⟩ := hc x b hb
  have hinf : Set.Infinite {t : F | MvPolynomial.eval (AffineLine.point x b t) g ≠ 0} := by
    exact (AffineLine.finite_bad_parameters x b hline).infinite_compl
  have hpoly : P = AffineLine.subst x b Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinf.mono
    intro t ht
    change P.eval t = Polynomial.eval t (AffineLine.subst x b Q)
    rw [AffineLine.eval_subst, ← hP t (hΩ _ ht)]
    exact hQ _ ht
  have hzero : AffineLine.point x b 0 = x := by
    funext i
    simp [AffineLine.point]
  have he := hP 0 (by rw [hzero]; exact hx)
  simpa only [hpoly, AffineLine.eval_subst_zero, hzero] using he

/-- Restriction of a polynomial to the coordinate hyperplane with first coordinate `a`. -/
def slice {n : ℕ} (a : F) :
    MvPolynomial (Fin (n + 1)) F →ₐ[F] MvPolynomial (Fin n) F :=
  MvPolynomial.aeval (Fin.cons (MvPolynomial.C a) MvPolynomial.X)

theorem eval_slice {n : ℕ} (a : F) (y : Fin n → F)
    (P : MvPolynomial (Fin (n + 1)) F) :
    MvPolynomial.eval y (slice a P) = MvPolynomial.eval (Fin.cons a y) P := by
  change (MvPolynomial.aeval y).comp (slice a) P = MvPolynomial.aeval (Fin.cons a y) P
  rw [slice, MvPolynomial.comp_aeval]
  have hvec : (fun i : Fin (n + 1) => (MvPolynomial.aeval y)
      ((Fin.cons (MvPolynomial.C a) MvPolynomial.X :
        Fin (n + 1) → MvPolynomial (Fin n) F) i)) = Fin.cons a y := by
    funext i
    cases i using Fin.cases <;> simp
  rw [hvec]

theorem point_cons {n : ℕ} (a : F) (x b : Fin n → F) (t : F) :
    AffineLine.point (Fin.cons a x) (Fin.cons 0 b) t =
      Fin.cons a (AffineLine.point x b t) := by
  funext i
  cases i using Fin.cases <;> simp [AffineLine.point]

theorem point_head {n : ℕ} (y : Fin n → F) (t : F) :
    AffineLine.point (Fin.cons 0 y) (Fin.cons 1 (0 : Fin n → F)) t = Fin.cons t y := by
  funext i
  cases i using Fin.cases <;> simp [AffineLine.point]

theorem IsPolynomialOnLines.onSlice {n : ℕ} {g : MvPolynomial (Fin (n + 1)) F}
    {c : (Fin (n + 1) → F) → F} {N : ℕ}
    (hc : IsPolynomialOnLines {x | MvPolynomial.eval x g ≠ 0} c N) (a : F) :
    IsPolynomialOnLines {y | MvPolynomial.eval y (slice a g) ≠ 0}
      (fun y => c (Fin.cons a y)) N := by
  intro x b hb
  have hb' : Fin.cons 0 b ≠ (0 : Fin (n + 1) → F) := by
    intro he
    apply hb
    funext i
    exact congrFun he i.succ
  obtain ⟨P, hP, he⟩ := hc (Fin.cons a x) (Fin.cons 0 b) hb'
  refine ⟨P, hP, fun t ht => ?_⟩
  change MvPolynomial.eval (AffineLine.point x b t) (slice a g) ≠ 0 at ht
  rw [eval_slice] at ht
  have ht' : AffineLine.point (Fin.cons a x) (Fin.cons 0 b) t ∈
      {x | MvPolynomial.eval x g ≠ 0} := by
    change MvPolynomial.eval (AffineLine.point (Fin.cons a x) (Fin.cons 0 b) t) g ≠ 0
    rwa [point_cons]
  simpa only [point_cons] using he t ht'

/-- A uniform bound on polynomial restrictions to lines makes a function polynomial on a
nonempty principal open. This is the interpolation assertion of `lem:fc-lines-poly`. -/
theorem exists_polynomial_on_principalOpen [Infinite F] (n N : ℕ)
    (g : MvPolynomial (Fin n) F) (hg : g ≠ 0) (c : (Fin n → F) → F)
    (hc : IsPolynomialOnLines {x | MvPolynomial.eval x g ≠ 0} c N) :
    ∃ Q : MvPolynomial (Fin n) F,
      ∀ x : Fin n → F, MvPolynomial.eval x g ≠ 0 → c x = MvPolynomial.eval x Q := by
  classical
  induction n with
  | zero =>
    refine ⟨MvPolynomial.C (c (fun i => Fin.elim0 i)), fun x _hx => ?_⟩
    simp only [MvPolynomial.eval_C]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    obtain ⟨z, hz⟩ := AffineLine.exists_eval_ne_zero hg
    let y₀ := Fin.tail z
    let p := AffineLine.subst (Fin.cons 0 y₀) (Fin.cons 1 (0 : Fin n → F)) g
    have hp : p ≠ 0 := by
      intro hp
      have he := AffineLine.eval_subst (Fin.cons 0 y₀)
        (Fin.cons 1 (0 : Fin n → F)) (z 0) g
      rw [show AffineLine.subst _ _ g = p from rfl, hp, Polynomial.eval_zero,
        point_head, show Fin.cons (z 0) y₀ = z from Fin.cons_self_tail z] at he
      exact hz he.symm
    have hinf : Set.Infinite {a : F | p.eval a ≠ 0} :=
      (Polynomial.finite_setOfPred_isRoot hp).infinite_compl
    obtain ⟨s, hs, hcard⟩ := hinf.exists_subset_card_eq (N + 1)
    have hslice : ∀ a : s, slice (a : F) g ≠ 0 := by
      intro a ha
      have he := eval_slice (a : F) y₀ g
      rw [ha, map_zero] at he
      have hpa := hs a.property
      apply hpa
      rw [show p.eval (a : F) = MvPolynomial.eval (Fin.cons (a : F) y₀) g by
        simp only [p, AffineLine.eval_subst, point_head]]
      exact he.symm
    choose q hq using fun a : s => ih (slice (a : F) g) (hslice a)
      (fun y => c (Fin.cons (a : F) y)) (hc.onSlice (a : F))
    let h : MvPolynomial (Fin n) F := ∏ a : s, slice (a : F) g
    have hh : h ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun a _ha => hslice a)
    let Q : MvPolynomial (Fin (n + 1)) F := ∑ a : s,
      MvPolynomial.rename Fin.succ (q a) *
        Polynomial.aeval (MvPolynomial.X 0) (Lagrange.basis Finset.univ Subtype.val a)
    let G : MvPolynomial (Fin (n + 1)) F := g * MvPolynomial.rename Fin.succ h
    have hG : G ≠ 0 := mul_ne_zero hg
      ((MvPolynomial.rename_eq_zero_iff_of_injective h (Fin.succ_injective n)).not.mpr hh)
    refine ⟨Q, eqOn_of_eqOn_principalOpen hc hG ?_ ?_⟩
    · intro x hx
      exact (mul_ne_zero_iff.mp (by simpa only [G, map_mul] using hx)).1
    · intro x hx
      have hxg : MvPolynomial.eval x g ≠ 0 :=
        (mul_ne_zero_iff.mp (by simpa only [G, map_mul] using hx)).1
      have hxh : MvPolynomial.eval (Fin.tail x) h ≠ 0 := by
        have := (mul_ne_zero_iff.mp (by simpa only [G, map_mul] using hx)).2
        change MvPolynomial.eval (fun i => x i.succ) h ≠ 0
        simpa only [MvPolynomial.eval_rename, Function.comp_def] using this
      have hgood : ∀ a : s, MvPolynomial.eval (Fin.tail x) (slice (a : F) g) ≠ 0 := by
        have he : (∏ a : s, MvPolynomial.eval (Fin.tail x) (slice (a : F) g)) ≠ 0 := by
          simpa only [h, map_prod] using hxh
        exact fun a => Finset.prod_ne_zero_iff.mp he a (Finset.mem_univ a)
      have hb : Fin.cons 1 (0 : Fin n → F) ≠ (0 : Fin (n + 1) → F) := by
        intro he
        have := congrFun he 0
        simp at this
      obtain ⟨P, hPN, he⟩ := hc (Fin.cons 0 (Fin.tail x)) (Fin.cons 1 0) hb
      have hP : P = Lagrange.interpolate Finset.univ Subtype.val
          (fun a : s => MvPolynomial.eval (Fin.tail x) (q a)) := by
        apply Lagrange.eq_interpolate_of_eval_eq
        · exact fun _a _ha _b _hb hab => Subtype.ext hab
        · have hdeg : P.degree < (N + 1 : ℕ) :=
            P.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hPN)
          simpa only [Finset.card_univ, Fintype.card_coe, hcard] using hdeg
        · intro a _ha
          have ha := he (a : F) (by
            rw [point_head]
            change MvPolynomial.eval (Fin.cons (a : F) (Fin.tail x)) g ≠ 0
            rw [← eval_slice]
            exact hgood a)
          rw [point_head] at ha
          exact ha.symm.trans (hq a (Fin.tail x) (hgood a))
      have hcx := he (x 0) (by
        change MvPolynomial.eval
          (AffineLine.point (Fin.cons 0 (Fin.tail x)) (Fin.cons 1 0) (x 0)) g ≠ 0
        simpa only [point_head, Fin.cons_self_tail] using hxg)
      rw [point_head, Fin.cons_self_tail, hP] at hcx
      rw [hcx]
      simp only [Q, Lagrange.interpolate_apply, map_sum, map_mul, Polynomial.eval_finsetSum,
        Polynomial.eval_mul, Polynomial.eval_C, MvPolynomial.eval_rename]
      apply Finset.sum_congr rfl
      intro a _ha
      congr 1
      simpa only [MvPolynomial.aeval_X, Polynomial.coe_aeval_eq_eval,
        MvPolynomial.aeval_eq_eval] using
        Polynomial.aeval_algHom_apply (MvPolynomial.aeval x)
          (MvPolynomial.X 0) (Lagrange.basis Finset.univ Subtype.val a)

/-- The actual rational affine scheme point defined by evaluation of all polynomials. -/
def rationalPoint (x : σ → F) : PrimeSpectrum (MvPolynomial σ F) :=
  ⟨RingHom.ker (MvPolynomial.eval x), RingHom.ker_isPrime _⟩

theorem rationalPoint_mem_basicOpen (x : σ → F) (g : MvPolynomial σ F) :
    rationalPoint x ∈ PrimeSpectrum.basicOpen g ↔ MvPolynomial.eval x g ≠ 0 := Iff.rfl

/-- The source form of `lem:fc-lines-poly`: on a nonempty Zariski open of affine space over
an infinite field, uniform polynomiality on lines implies a single polynomial formula. -/
theorem exists_polynomial_on_open [Infinite F] (n N : ℕ)
    (U : TopologicalSpace.Opens (PrimeSpectrum (MvPolynomial (Fin n) F)))
    (hU : (U : Set (PrimeSpectrum (MvPolynomial (Fin n) F))).Nonempty)
    (c : (Fin n → F) → F)
    (hc : IsPolynomialOnLines {x | rationalPoint x ∈ U} c N) :
    ∃ Q : MvPolynomial (Fin n) F,
      ∀ x : Fin n → F, rationalPoint x ∈ U → c x = MvPolynomial.eval x Q := by
  classical
  obtain ⟨z, hz⟩ := hU
  obtain ⟨_, ⟨g, rfl⟩, hzg, hgU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.isOpen z hz
  have hg : g ≠ 0 := by
    intro he
    simp [he] at hzg
  have hΩ : ∀ x : Fin n → F, MvPolynomial.eval x g ≠ 0 → rationalPoint x ∈ U :=
    fun x hx => hgU ((rationalPoint_mem_basicOpen x g).mpr hx)
  obtain ⟨Q, hQ⟩ := exists_polynomial_on_principalOpen n N g hg c (hc.mono hΩ)
  refine ⟨Q, ?_⟩
  by_cases hn : n = 0
  · subst n
    obtain ⟨a, ha⟩ := AffineLine.exists_eval_ne_zero hg
    intro x _hx
    have hxa : x = a := Subsingleton.elim _ _
    exact hxa ▸ hQ a ha
  · have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    exact eqOn_of_eqOn_principalOpen hc hg hΩ hQ

/-- Substituting affine linear polynomials does not increase total degree. -/
theorem totalDegree_aeval_affine_le {τ : Type*} (v : σ → MvPolynomial τ F)
    (hv : ∀ i, (v i).totalDegree ≤ 1) (P : MvPolynomial σ F) :
    (MvPolynomial.aeval v P).totalDegree ≤ P.totalDegree := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  exact (Finset.sum_le_sum fun i _hi =>
    (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hv i))).trans
      (MvPolynomial.le_totalDegree hd)

/-- Bivariate polynomials in coordinates `(Z,t)` as polynomials in `Z` with polynomial
coefficients in `t`. Both variables and every coefficient are preserved. -/
def bivariateEquiv : MvPolynomial (Fin 2) F ≃ₐ[F] (F[X])[X] :=
  (MvPolynomial.finSuccEquiv F 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv F (Fin 1)))

/-- The actual bivariate restriction keeps the distinguished variable `Z` and restricts
all remaining coordinates to the affine line `a+t b`. -/
def bivariateLine {n : ℕ} (a b : Fin n → F) :
    MvPolynomial (Fin (n + 1)) F →ₐ[F] MvPolynomial (Fin 2) F :=
  MvPolynomial.aeval (Fin.cons (MvPolynomial.X 0) (fun i =>
    MvPolynomial.C (a i) + MvPolynomial.C (b i) * MvPolynomial.X 1))

theorem totalDegree_bivariateLine_le {n : ℕ} (a b : Fin n → F)
    (P : MvPolynomial (Fin (n + 1)) F) :
    (bivariateLine a b P).totalDegree ≤ P.totalDegree := by
  apply totalDegree_aeval_affine_le
  intro i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · simp
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

/-- The bivariate coordinate model agrees on the entire polynomial with the usual
coefficientwise restriction to the line. -/
theorem bivariateEquiv_bivariateLine {n : ℕ} (a b : Fin n → F)
    (P : MvPolynomial (Fin (n + 1)) F) :
    bivariateEquiv (bivariateLine a b P) =
      Polynomial.map (AffineLine.subst a b).toRingHom (MvPolynomial.finSuccEquiv F n P) := by
  let φ := bivariateEquiv.toAlgHom.comp (bivariateLine a b)
  let ψ := (Polynomial.mapAlgHom (AffineLine.subst a b)).comp
    (MvPolynomial.finSuccEquiv F n).toAlgHom
  have he : φ = ψ := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero => simp [φ, ψ, bivariateEquiv, bivariateLine, MvPolynomial.finSuccEquiv_apply]
    | succ i =>
      simp [φ, ψ, bivariateEquiv, bivariateLine, AffineLine.subst,
        MvPolynomial.uniqueAlgEquiv, MvPolynomial.finSuccEquiv_apply]
      left
      change Polynomial.map (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom
        (Polynomial.C (MvPolynomial.X 0)) = Polynomial.C Polynomial.X
      simp [MvPolynomial.uniqueAlgEquiv]
  exact congrArg (fun f : MvPolynomial (Fin (n + 1)) F →ₐ[F] (F[X])[X] => f P) he

theorem natDegree_uniqueAlgEquiv_le_totalDegree {τ : Type*} [Unique τ]
    (P : MvPolynomial τ F) :
    (MvPolynomial.uniqueAlgEquiv F τ P).natDegree ≤ P.totalDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [MvPolynomial.coeff_uniqueAlgEquiv]
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  change P.totalDegree < (Finsupp.single (default : τ) k).sum (fun _ e => e)
  simpa using hk

/-- Every coefficient of a bivariate polynomial has parameter degree at most its total
degree. -/
theorem natDegree_coeff_bivariateEquiv_le (P : MvPolynomial (Fin 2) F) (k : ℕ) :
    ((bivariateEquiv P).coeff k).natDegree ≤ P.totalDegree := by
  have he : (bivariateEquiv P).coeff k = (MvPolynomial.uniqueAlgEquiv F (Fin 1))
      ((MvPolynomial.finSuccEquiv F 1 P).coeff k) := by
    simp [bivariateEquiv]
  rw [he]
  refine (natDegree_uniqueAlgEquiv_le_totalDegree _).trans ?_
  by_cases hk : (MvPolynomial.finSuccEquiv F 1 P).coeff k = 0
  · simp [hk]
  · exact (Nat.le_add_right _ _).trans
      (MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P k hk)

/-- A factor of the actual restriction of a fixed polynomial to any affine line has
coefficient degrees uniformly bounded independently of the line and the factor. This
coarse estimate supplies the bound needed in step (iv) of `lem:fc-curve-chains`. -/
theorem natDegree_coeff_factor_bivariateLine_le {n : ℕ} (a b : Fin n → F)
    (P : MvPolynomial (Fin (n + 1)) F) (hP : bivariateLine a b P ≠ 0)
    (Q : (F[X])[X]) (hQ : Q ∣ bivariateEquiv (bivariateLine a b P)) (k : ℕ) :
    (Q.coeff k).natDegree ≤ P.totalDegree := by
  have hd : bivariateEquiv.symm Q ∣ bivariateLine a b P := by
    obtain ⟨R, hR⟩ := hQ
    refine ⟨bivariateEquiv.symm R, ?_⟩
    apply bivariateEquiv.injective
    simpa only [map_mul, AlgEquiv.apply_symm_apply] using hR
  have he := natDegree_coeff_bivariateEquiv_le (bivariateEquiv.symm Q) k
  rw [AlgEquiv.apply_symm_apply] at he
  exact he.trans ((MvPolynomial.totalDegree_le_of_dvd_of_isDomain hd hP).trans
    (totalDegree_bivariateLine_le a b P))

/-- The bound for actual factors of a monic polynomial restricted to a line. Monicity
supplies the required nonvanishing for every line, including special lines. -/
theorem natDegree_coeff_factor_line_le {n : ℕ} (a b : Fin n → F)
    (P : (MvPolynomial (Fin n) F)[X]) (hP : P.Monic)
    (Q : (F[X])[X]) (hQ : Q ∣ P.map (AffineLine.subst a b).toRingHom) (k : ℕ) :
    (Q.coeff k).natDegree ≤ ((MvPolynomial.finSuccEquiv F n).symm P).totalDegree := by
  let P' := (MvPolynomial.finSuccEquiv F n).symm P
  have he : bivariateEquiv (bivariateLine a b P') = P.map (AffineLine.subst a b).toRingHom := by
    rw [bivariateEquiv_bivariateLine, show MvPolynomial.finSuccEquiv F n P' = P from
      (MvPolynomial.finSuccEquiv F n).apply_symm_apply P]
  have hn : bivariateLine a b P' ≠ 0 := by
    intro hz
    have hm := (hP.map (AffineLine.subst a b).toRingHom).ne_zero
    apply hm
    rw [← he, hz, map_zero]
  exact natDegree_coeff_factor_bivariateLine_le a b P' hn Q (he ▸ hQ) k

/-- Coefficients of linewise polynomial factors of one fixed monic polynomial extend
to global polynomial functions on a nonempty Zariski open. The uniform degree bound is
proved from divisibility, rather than supplied as a hypothesis. This is the coefficient
interpolation step in the curve-chain argument. -/
theorem exists_polynomial_of_lineFactor_coeff [Infinite F] (n : ℕ)
    (U : TopologicalSpace.Opens (PrimeSpectrum (MvPolynomial (Fin n) F)))
    (hU : (U : Set (PrimeSpectrum (MvPolynomial (Fin n) F))).Nonempty)
    (P : (MvPolynomial (Fin n) F)[X]) (hP : P.Monic)
    (c : (Fin n → F) → F) (k : ℕ)
    (h : ∀ a b : Fin n → F, b ≠ 0 → ∃ Q : (F[X])[X],
      Q ∣ P.map (AffineLine.subst a b).toRingHom ∧
        ∀ t : F, rationalPoint (AffineLine.point a b t) ∈ U →
          c (AffineLine.point a b t) = (Q.coeff k).eval t) :
    ∃ R : MvPolynomial (Fin n) F,
      ∀ x : Fin n → F, rationalPoint x ∈ U → c x = MvPolynomial.eval x R := by
  apply exists_polynomial_on_open n ((MvPolynomial.finSuccEquiv F n).symm P).totalDegree U hU c
  intro a b hb
  obtain ⟨Q, hQ, he⟩ := h a b hb
  exact ⟨Q.coeff k, natDegree_coeff_factor_line_le a b P hP Q hQ k, he⟩

end FcPolynomialOnLines

end EnvelopeProperty
