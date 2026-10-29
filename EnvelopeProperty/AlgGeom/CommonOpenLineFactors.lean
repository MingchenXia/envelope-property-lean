import EnvelopeProperty.AlgGeom.CommonOpenRationalFibres
import EnvelopeProperty.AlgGeom.MonogenicLineFactors

/-!
# Actual polynomial line factors for original-algebra curve classes

The good-locus common-open presentation constructs reference points in the
ORIGINAL algebra for each irreducible line factor. The actual kernel closure
curve in that original spectrum determines which entire polynomial factors
belong to each original curve class.
-/

open scoped Polynomial Classical
noncomputable section

namespace EnvelopeProperty.FcCommonOpenLineFactors

open FcCurveFibres FcLineFactorCurves FcMonogenicLineFactors FcCommonOpenFibres FcCurveClosures

variable {F σ A : Type*} [Field F] [IsAlgClosed F] [CommRing A] [Algebra F A]

/-- Every irreducible line factor has a constructed rational reference point in
the ORIGINAL algebra over each good base parameter, with the entire quotient
base restriction and the actual generator value retained. -/
theorem exists_commonOpen_point_on_line_factor
    (a b : σ → F) (P : (MvPolynomial σ F)[X]) (Q : F[X][X])
    (hQm : Q.Monic) (hQi : Irreducible Q)
    (hQ : Q ∣ P.map (AffineLine.subst a b).toRingHom)
    (δ : AdjoinRoot P →ₐ[F] A) (h : AdjoinRoot P) (g : MvPolynomial σ F)
    (hdiv : h ∣ algebraMap _ (AdjoinRoot P) g)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h))
    (he : ∀ c : AdjoinRoot P, e (algebraMap _ (Localization.Away h) c) =
      algebraMap A (Localization.Away (δ h)) (δ c))
    (t : F) (ht : MvPolynomial.eval (AffineLine.point a b t) g ≠ 0) :
    ∃ χ : A →ₐ[F] F,
      (χ.comp δ).comp (AdjoinRoot.ofAlgHom F P) = MvPolynomial.aeval (AffineLine.point a b t) ∧
      Q.eval₂ (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom
        (χ (δ (AdjoinRoot.root P))) = 0 ∧ χ (δ h) ≠ 0 := by
  obtain ⟨χC, hbaseC, hrootC⟩ := exists_rationalPoint_on_line_factor a b P Q hQm hQi hQ t
  have hχC : χC h ≠ 0 := apply_ne_zero_of_dvd_base (AdjoinRoot.ofAlgHom F P)
    (MvPolynomial.aeval (AffineLine.point a b t)) χC hbaseC h g hdiv ht
  let χ := commonOpenRationalExtension δ h e χC hχC
  have hres : χ.comp δ = χC := commonOpenRationalExtension_comp δ h e he χC hχC
  refine ⟨χ, ?_, ?_, ?_⟩
  · rw [hres]
    exact hbaseC
  · have hr := congrArg (fun f : AdjoinRoot P →ₐ[F] F => f (AdjoinRoot.root P)) hres
    change χ (δ (AdjoinRoot.root P)) = χC (AdjoinRoot.root P) at hr
    rw [hr]
    exact hrootC
  · have hr := congrArg (fun f : AdjoinRoot P →ₐ[F] F => f h) hres
    change χ (δ h) = χC h at hr
    rwa [hr]

/-- A genuine polynomial line divisor for the actual ORIGINAL-spectrum curve
class root-product family. Reference points, whole-factor class grouping, and
all identifications of original rational points are constructed. -/
theorem exists_curveClass_lineFactor_of_commonOpen
    (a b : σ → F) (hb : b ≠ 0) (P : (MvPolynomial σ F)[X]) (hP : P.Monic)
    (δ : AdjoinRoot P →ₐ[F] A) (φ : MvPolynomial σ F →ₐ[F] A) (hφ : φ.toRingHom.Finite)
    (hδ : δ.comp (AdjoinRoot.ofAlgHom F P) = φ) (h : AdjoinRoot P) (g : MvPolynomial σ F)
    (hdiv : h ∣ algebraMap _ (AdjoinRoot P) g)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h))
    (he : ∀ c : AdjoinRoot P, e (algebraMap _ (Localization.Away h) c) =
      algebraMap A (Localization.Away (δ h)) (δ c)) (x : PrimeSpectrum A) :
    ∃ D : F[X][X], D.Monic ∧ D ∣ P.map (AffineLine.subst a b).toRingHom ∧
      ∀ t : F, MvPolynomial.eval (AffineLine.point a b t) g ≠ 0 →
        (P.map (MvPolynomial.aeval (AffineLine.point a b t)).toRingHom).Separable →
        D.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom =
          fibreClassFactor φ hφ (curveClass x) (δ (AdjoinRoot.root P))
            (MvPolynomial.aeval (AffineLine.point a b t)) := by
  by_cases hline : AffineLine.subst a b g = 0
  · refine ⟨1, Polynomial.monic_one, one_dvd _, ?_⟩
    intro t ht _hsep
    apply (ht ?_).elim
    rw [← AffineLine.eval_subst a b t g, hline, Polynomial.eval_zero]
  obtain ⟨t₀, ht₀⟩ : ∃ t : F, Polynomial.eval t (AffineLine.subst a b g) ≠ 0 := by
    by_contra! hz
    apply hline
    apply Polynomial.funext
    intro t
    simpa only [Polynomial.eval_zero] using hz t
  have ht₀' : MvPolynomial.eval (AffineLine.point a b t₀) g ≠ 0 := by
    simpa only [AffineLine.eval_subst] using ht₀
  obtain ⟨n, Q, hQ, hprod⟩ := exists_finite_monic_irreducible_factorization
    (P.map (AffineLine.subst a b).toRingHom) (hP.map _)
  have hQdiv (i : Fin n) : Q i ∣ P.map (AffineLine.subst a b).toRingHom := by
    rw [← hprod]
    exact Finset.dvd_prod_of_mem Q (Finset.mem_univ i)
  have href (i : Fin n) := exists_commonOpen_point_on_line_factor a b P (Q i)
    (hQ i).1 (hQ i).2 (hQdiv i) δ h g hdiv e he t₀ ht₀'
  choose χref hbaseRef hrootRef hhRef using href
  let selected : Fin n → Prop := fun i => rationalPoint (χref i) ∈ curveClass x
  let s := Finset.univ.filter selected
  let D := ∏ i ∈ s, Q i
  have hDm : D.Monic := Polynomial.monic_prod_of_monic s Q (fun i _ => (hQ i).1)
  have hDdiv : D ∣ P.map (AffineLine.subst a b).toRingHom := by
    rw [← hprod]
    exact Finset.prod_dvd_prod_of_subset s Finset.univ Q (Finset.subset_univ s)
  have hfinδ : (δ.comp (AdjoinRoot.ofAlgHom F P)).toRingHom.Finite := by
    rw [hδ]
    exact hφ
  have hmap (t : F) :
      (P.map (AffineLine.subst a b).toRingHom).map
          (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom =
        P.map (MvPolynomial.aeval (AffineLine.point a b t)).toRingHom := by
    rw [Polynomial.map_map]
    congr 1
    exact congrArg AlgHom.toRingHom (AffineLine.aeval_comp_subst a b t)
  have hDroot (t : F) (ht : MvPolynomial.eval (AffineLine.point a b t) g ≠ 0)
      (χ : A →ₐ[F] F) (hbase : χ.comp φ = MvPolynomial.aeval (AffineLine.point a b t)) :
      (D.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).IsRoot
          (χ (δ (AdjoinRoot.root P))) ↔ rationalPoint χ ∈ curveClass x := by
    have hbaseC : (χ.comp δ).comp (AdjoinRoot.ofAlgHom F P) =
        MvPolynomial.aeval (AffineLine.point a b t) := by
      rw [AlgHom.comp_assoc, hδ]
      exact hbase
    have hχh : χ (δ h) ≠ 0 := apply_ne_zero_of_dvd_base (AdjoinRoot.ofAlgHom F P)
      (MvPolynomial.aeval (AffineLine.point a b t)) (χ.comp δ) hbaseC h g hdiv ht
    have hrootP := (rationalFibreEquivRoots_of_commonOpen P δ φ hδ h g hdiv e he
      (MvPolynomial.aeval (AffineLine.point a b t)) ht ⟨χ, hbase⟩).2
    have hrootFull : ∃ i : Fin n,
        ((Q i).map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).IsRoot
          (χ (δ (AdjoinRoot.root P))) := by
      have hp : ((∏ i, Q i).map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).IsRoot
          (χ (δ (AdjoinRoot.root P))) := by rwa [hprod, hmap]
      simpa only [Finset.mem_univ, true_and] using (isRoot_map_prod_iff Q _ _ _).mp hp
    have hrootSelected :
        (D.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).IsRoot
            (χ (δ (AdjoinRoot.root P))) ↔
          ∃ i, selected i ∧ ((Q i).map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).IsRoot
            (χ (δ (AdjoinRoot.root P))) := by
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using
        isRoot_map_prod_iff Q s t (χ (δ (AdjoinRoot.root P)))
    have hclass (i : Fin n)
        (hr : ((Q i).map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).IsRoot
          (χ (δ (AdjoinRoot.root P)))) : rationalPoint χ ∈ curveClass x ↔ selected i := by
      apply mem_curveClass_iff_of_curveStep x
      exact curveStep_of_commonOpen_irreducible_line_factor a b hb P (Q i) (hQ i).1 (hQ i).2
        (hQdiv i) δ hfinδ h e he χ (χref i) t t₀ hbaseC (hbaseRef i)
        (by simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hr)
        (hrootRef i) hχh (hhRef i)
    constructor
    · intro hr
      obtain ⟨i, hi, hri⟩ := hrootSelected.mp hr
      exact (hclass i hri).mpr hi
    · intro hc
      obtain ⟨i, hri⟩ := hrootFull
      exact hrootSelected.mpr ⟨i, (hclass i hri).mp hc, hri⟩
  refine ⟨D, hDm, hDdiv, ?_⟩
  intro t ht hsep
  let w : MvPolynomial σ F →ₐ[F] F := MvPolynomial.aeval (AffineLine.point a b t)
  let q := fibreClassFactor φ hφ (curveClass x) (δ (AdjoinRoot.root P)) w
  have hqm : q.Monic := classFactor_monic _ _ _
  have hqtdiv : q ∣ P.map w.toRingHom := fibreClassFactor_dvd_map_of_commonOpen
    P hP δ φ hφ hδ h g hdiv e he (curveClass x) w ht hsep
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
      obtain ⟨χ, hχ⟩ := (rationalFibreEquivRoots_of_commonOpen P δ φ hδ h g hdiv e he w ht).surjective
        ⟨z, hzP⟩
      have hzχ : χ.1 (δ (AdjoinRoot.root P)) = z := congrArg Subtype.val hχ
      have hc : rationalPoint χ.1 ∈ curveClass x :=
        (hDroot t ht χ.1 χ.2).mp (by simpa only [hzχ] using hzD)
      exact (isRoot_classFactor_iff _ _ _ _).mpr
        ⟨χ.1, (mem_rationalFibreFinset _ _ _ _).mpr χ.2, hc, hzχ.symm⟩
    · intro hzq
      obtain ⟨χ, hχ, hc, hzχ⟩ := (isRoot_classFactor_iff _ _ _ _).mp hzq
      rw [hzχ]
      exact (hDroot t ht χ ((mem_rationalFibreFinset _ _ _ _).mp hχ)).mpr hc
  change D.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom = q
  rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (hDm.map _),
    (IsAlgClosed.splits _).eq_prod_roots_of_monic hqm, hroots]

/-- Both complementary actual ORIGINAL-algebra class factors come from
complementary monic polynomial line divisors, constructed by actual curve grouping. -/
theorem exists_curveClass_complementary_lineFactors_of_commonOpen
    (a b : σ → F) (hb : b ≠ 0) (P : (MvPolynomial σ F)[X]) (hP : P.Monic)
    (δ : AdjoinRoot P →ₐ[F] A) (φ : MvPolynomial σ F →ₐ[F] A) (hφ : φ.toRingHom.Finite)
    (hδ : δ.comp (AdjoinRoot.ofAlgHom F P) = φ) (h : AdjoinRoot P) (g : MvPolynomial σ F)
    (hdiv : h ∣ algebraMap _ (AdjoinRoot P) g)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h))
    (he : ∀ c : AdjoinRoot P, e (algebraMap _ (Localization.Away h) c) =
      algebraMap A (Localization.Away (δ h)) (δ c)) (x : PrimeSpectrum A) :
    ∃ D E : F[X][X], D.Monic ∧ E.Monic ∧ D * E = P.map (AffineLine.subst a b).toRingHom ∧
      ∀ t : F, MvPolynomial.eval (AffineLine.point a b t) g ≠ 0 →
        (P.map (MvPolynomial.aeval (AffineLine.point a b t)).toRingHom).Separable →
        D.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom =
            fibreClassFactor φ hφ (curveClass x) (δ (AdjoinRoot.root P))
              (MvPolynomial.aeval (AffineLine.point a b t)) ∧
          E.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom =
            fibreClassFactor φ hφ (curveClass x)ᶜ (δ (AdjoinRoot.root P))
              (MvPolynomial.aeval (AffineLine.point a b t)) := by
  obtain ⟨D, hDm, ⟨E, hE⟩, hD⟩ := exists_curveClass_lineFactor_of_commonOpen
    a b hb P hP δ φ hφ hδ h g hdiv e he x
  have hPm := hP.map (AffineLine.subst a b).toRingHom
  rw [hE] at hPm
  have hEm : E.Monic := Polynomial.Monic.of_mul_monic_left hDm hPm
  refine ⟨D, E, hDm, hEm, hE.symm, ?_⟩
  intro t ht hsep
  refine ⟨hD t ht hsep, ?_⟩
  let w : MvPolynomial σ F →ₐ[F] F := MvPolynomial.aeval (AffineLine.point a b t)
  have hmap :
      (P.map (AffineLine.subst a b).toRingHom).map
          (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom = P.map w.toRingHom := by
    rw [Polynomial.map_map]
    congr 1
    exact congrArg AlgHom.toRingHom (AffineLine.aeval_comp_subst a b t)
  have hfull := fibreClassFactor_mul_compl_eq_map_of_commonOpen
    P hP δ φ hφ hδ h g hdiv e he (curveClass x) w ht hsep
  have hprod :
      fibreClassFactor φ hφ (curveClass x) (δ (AdjoinRoot.root P)) w *
          E.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom =
        fibreClassFactor φ hφ (curveClass x) (δ (AdjoinRoot.root P)) w *
          fibreClassFactor φ hφ (curveClass x)ᶜ (δ (AdjoinRoot.root P)) w := by
    rw [← hD t ht hsep, ← Polynomial.map_mul, ← hE, hmap]
    rw [hD t ht hsep]
    exact hfull.symm
  exact mul_left_cancel₀ (classFactor_monic _ _ _).ne_zero hprod

end EnvelopeProperty.FcCommonOpenLineFactors
