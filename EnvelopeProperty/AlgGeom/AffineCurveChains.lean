import EnvelopeProperty.AlgGeom.CommonOpenLineFactors

/-!
# Actual curve chains in finite-type integral affine schemes

The constructed normalization, common monogenic good locus, actual original
fibre factors and actual original line curves feed polynomial interpolation and
irreducibility. No normalization, separability, line factor, or class-count
assumption remains in the finite-type-domain theorem.
-/

open scoped Polynomial Classical
noncomputable section

namespace EnvelopeProperty.FcAffineCurveChains

open FcCurveFibres FcCommonOpenFibres FcCommonOpenLineFactors

variable {F A : Type*} [Field F] [IsAlgClosed F] [CommRing A] [IsDomain A] [Algebra F A]

/-- Every actual rational curve class meets every rational fibre of a global
finite injective polynomial normalization. The principal-open producer is used
through the actual localization isomorphism at one. -/
theorem exists_curveChain_in_global_fibre {n : ℕ}
    (φ : MvPolynomial (Fin n) F →ₐ[F] A) (hφ : φ.toRingHom.Finite)
    (hiφ : Function.Injective φ) (χ : A →ₐ[F] F)
    (w : MvPolynomial (Fin n) F →ₐ[F] F) :
    ∃ ψ : A →ₐ[F] F, FcCurveChains.CurveChain (rationalPoint χ) (rationalPoint ψ) ∧
      ψ.comp φ = w := by
  let R := MvPolynomial (Fin n) F
  let e : R ≃ₐ[F] Localization.Away (1 : R) :=
    (IsLocalization.atUnit R (Localization.Away (1 : R)) 1 isUnit_one).restrictScalars F
  let φ₁ := φ.comp e.symm.toAlgHom
  have hφ₁ : φ₁.toRingHom.Finite :=
    hφ.comp (RingHom.Finite.of_surjective e.symm.toRingHom e.symm.surjective)
  have hiφ₁ : Function.Injective φ₁ := hiφ.comp e.symm.injective
  obtain ⟨ψ, hchain, hbase⟩ := exists_rational_curveChain_in_fibre (1 : R) φ₁ hφ₁ hiφ₁ χ
    (w.comp e.symm.toAlgHom)
  refine ⟨ψ, hchain, ?_⟩
  apply AlgHom.ext
  intro r
  have hr := congrArg (fun f : Localization.Away (1 : R) →ₐ[F] F => f (e r)) hbase
  change ψ (φ (e.symm (e r))) = w (e.symm (e r)) at hr
  change ψ (φ r) = w r
  simpa only [e.symm_apply_apply] using hr

/-- Any two actual rational points of an original finite-type domain over an
algebraically closed field are joined by a finite chain of genuine irreducible
closed affine curves. All normalization, primitive, good-locus and line-factor
data are constructed; there are no additional geometric assumptions. -/
theorem curveChain_of_finiteType_domain [Algebra.FiniteType F A] (χ η : A →ₐ[F] F) :
    FcCurveChains.CurveChain (rationalPoint χ) (rationalPoint η) := by
  by_contra hnot
  obtain ⟨n, φ, P, δ, h, g, hiφ, hφ, hPm, hPi, _hiδ, hδ, _hh, hg, hdiv, e, he, hsep⟩ :=
    FcMonogenicBirationalPresentation.exists_global_monic_presentation_goodLocus F A
  let U := PrimeSpectrum.basicOpen g
  obtain ⟨u, hu⟩ := AffineLine.exists_eval_ne_zero hg
  have huU : FcPolynomialOnLines.rationalPoint u ∈ U :=
    (FcPolynomialOnLines.rationalPoint_mem_basicOpen u g).mpr hu
  have hU : (U : Set (PrimeSpectrum (MvPolynomial (Fin n) F))).Nonempty :=
    ⟨FcPolynomialOnLines.rationalPoint u, huU⟩
  have hgood (z : Fin n → F) (hz : FcPolynomialOnLines.rationalPoint z ∈ U) :
      MvPolynomial.eval z g ≠ 0 :=
    (FcPolynomialOnLines.rationalPoint_mem_basicOpen z g).mp hz
  let q : (Fin n → F) → F[X] := fun z => fibreClassFactor φ hφ
    (curveClass (rationalPoint χ)) (δ (AdjoinRoot.root P)) (MvPolynomial.aeval z)
  let q' : (Fin n → F) → F[X] := fun z => fibreClassFactor φ hφ
    (curveClass (rationalPoint χ))ᶜ (δ (AdjoinRoot.root P)) (MvPolynomial.aeval z)
  have hprod (z : Fin n → F) (hz : FcPolynomialOnLines.rationalPoint z ∈ U) :
      P.map (MvPolynomial.eval z) = q z * q' z := by
    exact (fibreClassFactor_mul_compl_eq_map_of_commonOpen P hPm δ φ hφ hδ h g hdiv e he
      (curveClass (rationalPoint χ)) (MvPolynomial.aeval z) (hgood z hz)
      (hsep (MvPolynomial.aeval z) (hgood z hz))).symm
  have hpair (a b : Fin n → F) (hb : b ≠ 0) :
      ∃ D E : F[X][X], D * E = P.map (AffineLine.subst a b).toRingHom ∧
        ∀ t : F, FcPolynomialOnLines.rationalPoint (AffineLine.point a b t) ∈ U →
          D.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom = q (AffineLine.point a b t) ∧
          E.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom = q' (AffineLine.point a b t) := by
    obtain ⟨D, E, _hDm, _hEm, hDE, hspec⟩ :=
      exists_curveClass_complementary_lineFactors_of_commonOpen a b hb P hPm δ φ hφ hδ h g hdiv
        e he (rationalPoint χ)
    refine ⟨D, E, hDE, ?_⟩
    intro t ht
    exact hspec t (hgood _ ht) (hsep (MvPolynomial.aeval _) (hgood _ ht))
  have hline (k : Fin (P.natDegree + 1)) (a b : Fin n → F) (hb : b ≠ 0) :
      ∃ D : F[X][X], D ∣ P.map (AffineLine.subst a b).toRingHom ∧
        ∀ t : F, FcPolynomialOnLines.rationalPoint (AffineLine.point a b t) ∈ U →
          (q (AffineLine.point a b t)).coeff k = (D.coeff k).eval t := by
    obtain ⟨D, E, hDE, hspec⟩ := hpair a b hb
    refine ⟨D, ⟨E, hDE.symm⟩, ?_⟩
    intro t ht
    have hc := congrArg (fun p : F[X] => p.coeff k) (hspec t ht).1
    rw [Polynomial.coeff_map] at hc
    change Polynomial.aeval t (D.coeff k) = (q (AffineLine.point a b t)).coeff k at hc
    simpa only [Polynomial.coe_aeval_eq_eval] using hc.symm
  have hline' (k : Fin (P.natDegree + 1)) (a b : Fin n → F) (hb : b ≠ 0) :
      ∃ E : F[X][X], E ∣ P.map (AffineLine.subst a b).toRingHom ∧
        ∀ t : F, FcPolynomialOnLines.rationalPoint (AffineLine.point a b t) ∈ U →
          (q' (AffineLine.point a b t)).coeff k = (E.coeff k).eval t := by
    obtain ⟨D, E, hDE, hspec⟩ := hpair a b hb
    refine ⟨E, ⟨D, hDE.symm.trans (mul_comm D E)⟩, ?_⟩
    intro t ht
    have hc := congrArg (fun p : F[X] => p.coeff k) (hspec t ht).2
    rw [Polynomial.coeff_map] at hc
    change Polynomial.aeval t (E.coeff k) = (q' (AffineLine.point a b t)).coeff k at hc
    simpa only [Polynomial.coe_aeval_eq_eval] using hc.symm
  obtain ⟨ζ, hχζ, hζbase⟩ := exists_curveChain_in_global_fibre φ hφ hiφ χ (MvPolynomial.aeval u)
  have hpos : 0 < (q u).natDegree := natDegree_fibreClassFactor_pos φ hφ _ _ _ ζ hζbase hχζ
  obtain ⟨ζ', hηζ', hζ'base⟩ := exists_curveChain_in_global_fibre φ hφ hiφ η (MvPolynomial.aeval u)
  have hpos' : 0 < (q' u).natDegree := by
    apply natDegree_fibreClassFactor_pos φ hφ _ _ _ ζ' hζ'base
    intro hz
    exact hnot (hz.trans hηζ'.symm)
  exact (FcCurveChains.not_irreducible_of_line_factor_families U hU P hPm q q' hprod hline hline'
    u huU hpos hpos') hPi

/-- The actual closed-point form, with Nullstellensatz constructing both
rational homomorphisms rather than requiring them as extra data. -/
theorem curveChain_of_isMaximal [Algebra.FiniteType F A]
    (x y : PrimeSpectrum A) (hx : x.asIdeal.IsMaximal) (hy : y.asIdeal.IsMaximal) :
    FcCurveChains.CurveChain x y := by
  obtain ⟨χ, hχ⟩ := exists_rationalPoint_eq (F := F) x hx
  obtain ⟨η, hη⟩ := exists_rationalPoint_eq (F := F) y hy
  simpa only [hχ, hη] using curveChain_of_finiteType_domain χ η

/-- Any two closed points of an integral finite-type affine scheme over an
algebraically closed field are joined by genuine closed integral curves. -/
theorem curveChain_of_isClosed [Algebra.FiniteType F A]
    (x y : PrimeSpectrum A) (hx : IsClosed ({x} : Set (PrimeSpectrum A)))
    (hy : IsClosed ({y} : Set (PrimeSpectrum A))) :
    FcCurveChains.CurveChain x y := by
  exact curveChain_of_isMaximal (F := F) x y
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx)
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hy)

end EnvelopeProperty.FcAffineCurveChains
