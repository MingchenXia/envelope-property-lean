import EnvelopeProperty.AlgGeom.LineFactorCurves

/-!
# Polynomial line factors of actual monogenic curve classes

Monic polynomials admit finite monic irreducible factorizations. The actual
irreducible quotient curves identify which entire factors belong to a given
curve class, producing polynomial divisors along a genuine affine line.
-/

open scoped Polynomial Classical
noncomputable section

namespace EnvelopeProperty.FcMonogenicLineFactors

open FcCurveFibres FcLineFactorCurves FcMonogenicFibres

/-- Monic polynomials over any domain factor as a finite product of monic
irreducibles. This degree induction constructs the factors without a chosen list. -/
theorem exists_monic_irreducible_factorization {A : Type*} [CommRing A] [IsDomain A]
    (P : A[X]) (hP : P.Monic) :
    ∃ l : List A[X], (∀ Q ∈ l, Q.Monic ∧ Irreducible Q) ∧ l.prod = P := by
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases h1 : P = 1
    · exact ⟨[], by simp, by simpa only [List.prod_nil] using h1.symm⟩
    by_cases hi : Irreducible P
    · exact ⟨[P], by simpa using And.intro hP hi, by simp⟩
    rw [Polynomial.irreducible_of_monic hP h1] at hi
    push Not at hi
    obtain ⟨f, g, hf, hg, hfg, hf1, hg1⟩ := hi
    have hfd : f.natDegree < n := by
      rw [← hn, ← hfg, hf.natDegree_mul hg]
      exact Nat.lt_add_of_pos_right (hg.natDegree_pos.mpr hg1)
    have hgd : g.natDegree < n := by
      rw [← hn, ← hfg, hf.natDegree_mul hg]
      exact Nat.lt_add_of_pos_left (hf.natDegree_pos.mpr hf1)
    obtain ⟨lf, hlf, hlfprod⟩ := ih f.natDegree hfd f hf rfl
    obtain ⟨lg, hlg, hlgprod⟩ := ih g.natDegree hgd g hg rfl
    refine ⟨lf ++ lg, ?_, ?_⟩
    · intro Q hQ
      rcases List.mem_append.mp hQ with hQ | hQ
      · exact hlf Q hQ
      · exact hlg Q hQ
    · rw [List.prod_append, hlfprod, hlgprod, hfg]

/-- A finite indexed monic factorization, suitable for selecting entire actual
irreducible line components by their constructed reference points. -/
theorem exists_finite_monic_irreducible_factorization {A : Type*} [CommRing A] [IsDomain A]
    (P : A[X]) (hP : P.Monic) :
    ∃ (n : ℕ) (Q : Fin n → A[X]), (∀ i, (Q i).Monic ∧ Irreducible (Q i)) ∧
      ∏ i, Q i = P := by
  obtain ⟨l, hl, hprod⟩ := exists_monic_irreducible_factorization P hP
  refine ⟨l.length, l.get, fun i => hl _ (List.get_mem _ _), ?_⟩
  rw [← List.prod_ofFn, List.ofFn_get]
  exact hprod

/-- A root of an actual class factor is exactly the generator value of one of
its selected actual rational points. -/
theorem isRoot_classFactor_iff {F B : Type*} [Field F] [CommRing B] [Algebra F B]
    (s : Finset (B →ₐ[F] F)) (S : Set (PrimeSpectrum B)) (b : B) (z : F) :
    (classFactor s S b).IsRoot z ↔
      ∃ χ ∈ s, rationalPoint χ ∈ S ∧ z = χ b := by
  simp only [classFactor, Polynomial.IsRoot, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff, Finset.mem_filter, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
  aesop

/-- Specializing a finite polynomial product detects exactly the specialized
roots of one of its actual factors. -/
theorem isRoot_map_prod_iff {F ι : Type*} [Field F]
    (Q : ι → F[X][X]) (s : Finset ι) (t z : F) :
    ((∏ i ∈ s, Q i).map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).IsRoot z ↔
      ∃ i ∈ s, ((Q i).map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).IsRoot z := by
  simp only [Polynomial.IsRoot, Polynomial.map_prod, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff]

/-- The actual root-product family of a curve class in a monogenic affine scheme
is the specialization of one genuine polynomial divisor along every genuine line,
at every parameter where the specialized defining polynomial is separable. -/
theorem exists_curveClass_lineFactor {F σ : Type*} [Field F] [IsAlgClosed F]
    (a b : σ → F) (hb : b ≠ 0) (P : (MvPolynomial σ F)[X]) (hP : P.Monic)
    (x : PrimeSpectrum (AdjoinRoot P)) :
    ∃ D : F[X][X], D.Monic ∧ D ∣ P.map (AffineLine.subst a b).toRingHom ∧
      ∀ t : F, (P.map (MvPolynomial.aeval (AffineLine.point a b t)).toRingHom).Separable →
        D.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom =
          fibreClassFactor (AdjoinRoot.ofAlgHom F P) (ofAlgHom_finite P hP)
            (curveClass x) (AdjoinRoot.root P) (MvPolynomial.aeval (AffineLine.point a b t)) := by
  obtain ⟨n, Q, hQ, hprod⟩ := exists_finite_monic_irreducible_factorization
    (P.map (AffineLine.subst a b).toRingHom) (hP.map _)
  have hdiv (i : Fin n) : Q i ∣ P.map (AffineLine.subst a b).toRingHom := by
    rw [← hprod]
    exact Finset.dvd_prod_of_mem Q (Finset.mem_univ i)
  let selected : Fin n → Prop := fun i =>
    rationalPoint (lineFactorPoint a b P (Q i) (hQ i).1 (hQ i).2 (hdiv i)) ∈ curveClass x
  let s := Finset.univ.filter selected
  let D := ∏ i ∈ s, Q i
  have hDm : D.Monic := Polynomial.monic_prod_of_monic s Q (fun i _ => (hQ i).1)
  have hDdiv : D ∣ P.map (AffineLine.subst a b).toRingHom := by
    rw [← hprod]
    exact Finset.prod_dvd_prod_of_subset s Finset.univ Q (Finset.subset_univ s)
  have hmap (t : F) :
      (P.map (AffineLine.subst a b).toRingHom).map
          (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom =
        P.map (MvPolynomial.aeval (AffineLine.point a b t)).toRingHom := by
    rw [Polynomial.map_map]
    congr 1
    exact congrArg AlgHom.toRingHom (AffineLine.aeval_comp_subst a b t)
  have hDroot (t : F) (χ : AdjoinRoot P →ₐ[F] F)
      (hbase : χ.comp (AdjoinRoot.ofAlgHom F P) = MvPolynomial.aeval (AffineLine.point a b t)) :
      (D.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).IsRoot
          (χ (AdjoinRoot.root P)) ↔ rationalPoint χ ∈ curveClass x := by
    have hrootP := (rationalFibreEquivRoots P
      (MvPolynomial.aeval (AffineLine.point a b t)) ⟨χ, hbase⟩).2
    have hrootFull : ∃ i : Fin n,
        ((Q i).map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).IsRoot
          (χ (AdjoinRoot.root P)) := by
      have hh : ((∏ i, Q i).map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).IsRoot
          (χ (AdjoinRoot.root P)) := by
        rwa [hprod, hmap]
      simpa only [Finset.mem_univ, true_and] using (isRoot_map_prod_iff Q _ _ _).mp hh
    have hrootSelected :
        (D.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).IsRoot
            (χ (AdjoinRoot.root P)) ↔
          ∃ i, selected i ∧ ((Q i).map
            (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).IsRoot (χ (AdjoinRoot.root P)) := by
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using
        isRoot_map_prod_iff Q s t (χ (AdjoinRoot.root P))
    have hclass (i : Fin n)
        (hr : ((Q i).map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).IsRoot
          (χ (AdjoinRoot.root P))) : rationalPoint χ ∈ curveClass x ↔ selected i := by
      apply curveClass_iff_lineFactorPoint a b hb P (Q i) (hQ i).1 (hQ i).2
        (hdiv i) x χ t hbase
      simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hr
    constructor
    · intro hr
      obtain ⟨i, hi, hri⟩ := hrootSelected.mp hr
      exact (hclass i hri).mpr hi
    · intro hc
      obtain ⟨i, hri⟩ := hrootFull
      exact hrootSelected.mpr ⟨i, (hclass i hri).mp hc, hri⟩
  refine ⟨D, hDm, hDdiv, ?_⟩
  intro t hsep
  let w : MvPolynomial σ F →ₐ[F] F := MvPolynomial.aeval (AffineLine.point a b t)
  let q := fibreClassFactor (AdjoinRoot.ofAlgHom F P) (ofAlgHom_finite P hP)
    (curveClass x) (AdjoinRoot.root P) w
  have hqm : q.Monic := classFactor_monic _ _ _
  have hqtdiv : q ∣ P.map w.toRingHom := fibreClassFactor_dvd_map P hP (curveClass x) w hsep
  have hDtdiv : D.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom ∣ P.map w.toRingHom := by
    rw [← hmap]
    exact Polynomial.map_dvd _ hDdiv
  have hroots : (D.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).roots = q.roots := by
    apply ((Polynomial.nodup_roots (hsep.of_dvd hDtdiv)).ext
      (Polynomial.nodup_roots (hsep.of_dvd hqtdiv))).mpr
    intro z
    rw [Polynomial.mem_roots ((hDm.map _).ne_zero), Polynomial.mem_roots hqm.ne_zero]
    constructor
    · intro hzD
      have hzP : (P.map w.toRingHom).IsRoot z := by
        obtain ⟨E, hE⟩ := hDtdiv
        change (P.map w.toRingHom).eval z = 0
        rw [hE, Polynomial.eval_mul, hzD, zero_mul]
      obtain ⟨χ, hχ⟩ := (rationalFibreEquivRoots P w).surjective ⟨z, hzP⟩
      have hzχ : χ.1 (AdjoinRoot.root P) = z := congrArg Subtype.val hχ
      have hc : rationalPoint χ.1 ∈ curveClass x :=
        (hDroot t χ.1 χ.2).mp (by simpa only [hzχ] using hzD)
      exact (isRoot_classFactor_iff _ _ _ _).mpr
        ⟨χ.1, (mem_rationalFibreFinset _ _ _ _).mpr χ.2, hc, hzχ.symm⟩
    · intro hzq
      obtain ⟨χ, hχ, hc, hzχ⟩ := (isRoot_classFactor_iff _ _ _ _).mp hzq
      rw [hzχ]
      exact (hDroot t χ ((mem_rationalFibreFinset _ _ _ _).mp hχ)).mpr hc
  change D.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom = q
  rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (hDm.map _),
    (IsAlgClosed.splits _).eq_prod_roots_of_monic hqm, hroots]

/-- Both actual complementary curve-class factors come from complementary monic
polynomial divisors along the line. The complementary identification follows by
cancellation from the actual whole-fibre factorization, including multiplicities. -/
theorem exists_curveClass_complementary_lineFactors {F σ : Type*} [Field F] [IsAlgClosed F]
    (a b : σ → F) (hb : b ≠ 0) (P : (MvPolynomial σ F)[X]) (hP : P.Monic)
    (x : PrimeSpectrum (AdjoinRoot P)) :
    ∃ D E : F[X][X], D.Monic ∧ E.Monic ∧
      D * E = P.map (AffineLine.subst a b).toRingHom ∧
      ∀ t : F, (P.map (MvPolynomial.aeval (AffineLine.point a b t)).toRingHom).Separable →
        D.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom =
            fibreClassFactor (AdjoinRoot.ofAlgHom F P) (ofAlgHom_finite P hP)
              (curveClass x) (AdjoinRoot.root P) (MvPolynomial.aeval (AffineLine.point a b t)) ∧
          E.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom =
            fibreClassFactor (AdjoinRoot.ofAlgHom F P) (ofAlgHom_finite P hP)
              (curveClass x)ᶜ (AdjoinRoot.root P) (MvPolynomial.aeval (AffineLine.point a b t)) := by
  obtain ⟨D, hDm, ⟨E, hE⟩, hD⟩ := exists_curveClass_lineFactor a b hb P hP x
  have hPm := hP.map (AffineLine.subst a b).toRingHom
  rw [hE] at hPm
  have hEm : E.Monic := Polynomial.Monic.of_mul_monic_left hDm hPm
  refine ⟨D, E, hDm, hEm, hE.symm, ?_⟩
  intro t hsep
  refine ⟨hD t hsep, ?_⟩
  let w : MvPolynomial σ F →ₐ[F] F := MvPolynomial.aeval (AffineLine.point a b t)
  have hmap :
      (P.map (AffineLine.subst a b).toRingHom).map
          (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom = P.map w.toRingHom := by
    rw [Polynomial.map_map]
    congr 1
    exact congrArg AlgHom.toRingHom (AffineLine.aeval_comp_subst a b t)
  have hfull := fibreClassFactor_mul_compl_eq_map P hP (curveClass x) w hsep
  have hprod :
      fibreClassFactor (AdjoinRoot.ofAlgHom F P) (ofAlgHom_finite P hP)
          (curveClass x) (AdjoinRoot.root P) w *
        E.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom =
      fibreClassFactor (AdjoinRoot.ofAlgHom F P) (ofAlgHom_finite P hP)
          (curveClass x) (AdjoinRoot.root P) w *
        fibreClassFactor (AdjoinRoot.ofAlgHom F P) (ofAlgHom_finite P hP)
          (curveClass x)ᶜ (AdjoinRoot.root P) w := by
    rw [← hD t hsep, ← Polynomial.map_mul, ← hE, hmap]
    rw [hD t hsep]
    exact hfull.symm
  exact mul_left_cancel₀ (classFactor_monic _ _ _).ne_zero hprod

end EnvelopeProperty.FcMonogenicLineFactors
