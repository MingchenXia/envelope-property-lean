import EnvelopeProperty.AlgGeom.MonogenicCurveFibres

/-!
# Actual curves from irreducible line factors

An irreducible monic factor of the defining polynomial restricted to an actual
affine line defines a genuine irreducible curve in the original monogenic affine
scheme. This file constructs its quotient and the curve steps between its actual
rational points.
-/

open scoped Polynomial Classical
noncomputable section

namespace EnvelopeProperty.FcLineFactorCurves

open FcCurveFibres

variable {F R S : Type*} [Field F] [CommRing R] [CommRing S]
variable [Algebra F R] [Algebra F S]

/-- A surjective map on the actual coefficient rings gives a surjective map of
the actual monogenic quotients, for every divisor of the mapped relation. -/
theorem adjoinRoot_map_surjective (f : R →ₐ[F] S) (hf : Function.Surjective f)
    (P : R[X]) (Q : S[X]) (hQ : Q ∣ P.map f.toRingHom) :
    Function.Surjective (AdjoinRoot.mapAlgHom f P Q hQ) := by
  have he : (AdjoinRoot.map f.toRingHom P Q hQ).comp (AdjoinRoot.mk P) =
      (AdjoinRoot.mk Q).comp (Polynomial.mapRingHom f.toRingHom) := by
    apply Polynomial.ringHom_ext
    · intro r
      change AdjoinRoot.map f.toRingHom P Q hQ (AdjoinRoot.mk P (Polynomial.C r)) =
        AdjoinRoot.mk Q ((Polynomial.C r).map f.toRingHom)
      simp only [AdjoinRoot.mk_C, Polynomial.map_C, AdjoinRoot.map_of]
    · change AdjoinRoot.map f.toRingHom P Q hQ (AdjoinRoot.mk P Polynomial.X) =
        AdjoinRoot.mk Q (Polynomial.X.map f.toRingHom)
      simp only [AdjoinRoot.mk_X, Polynomial.map_X, AdjoinRoot.map_root]
  intro y
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective (g := Q) y
  obtain ⟨p, hp⟩ := Polynomial.map_surjective f.toRingHom hf q
  refine ⟨AdjoinRoot.mk P p, ?_⟩
  change AdjoinRoot.map f.toRingHom P Q hQ (AdjoinRoot.mk P p) = _
  have h := congrArg (fun k : R[X] →+* AdjoinRoot Q => k p) he
  change AdjoinRoot.map f.toRingHom P Q hQ (AdjoinRoot.mk P p) =
    AdjoinRoot.mk Q (p.map f.toRingHom) at h
  rwa [hp] at h

/-- A surjective homomorphism onto an actual integral curve constructs the curve
ideal in the original affine scheme and joins the induced whole rational points. -/
theorem curveStep_of_surjective_curve {B C : Type*} [CommRing B] [CommRing C]
    [Algebra F B] [Algebra F C] [IsDomain C]
    (κ : B →ₐ[F] C) (hκ : Function.Surjective κ) (hd : ringKrullDim C = 1)
    (χ ψ : C →ₐ[F] F) :
    FcCurveChains.CurveStep (rationalPoint (χ.comp κ)) (rationalPoint (ψ.comp κ)) := by
  refine ⟨RingHom.ker κ.toRingHom, RingHom.ker_isPrime κ, ?_, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hκ), hd]
  · intro b hb
    change χ (κ b) = 0
    change κ b = 0 at hb
    rw [hb, map_zero]
  · intro b hb
    change ψ (κ b) = 0
    change κ b = 0 at hb
    rw [hb, map_zero]

/-- A monic irreducible polynomial factor over the affine-line ring defines an
actual integral affine curve: its finite map from `F[t]` is faithful and integral. -/
theorem ringKrullDim_adjoinRoot_line_factor (Q : F[X][X]) (hQm : Q.Monic)
    (hQi : Irreducible Q) : ringKrullDim (AdjoinRoot Q) = 1 := by
  have : IsDomain (AdjoinRoot Q) := AdjoinRoot.isDomain_of_prime hQi.prime
  have : Module.Finite F[X] (AdjoinRoot Q) := hQm.finite_adjoinRoot
  have : Algebra.FiniteType F (AdjoinRoot Q) := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F F[X])
    (inferInstance : Algebra.FiniteType F[X] (AdjoinRoot Q))
  have hd : Q.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hQm.ne_zero]
    exact_mod_cast (hQm.natDegree_pos_of_not_isUnit hQi.not_isUnit).ne'
  have : FaithfulSMul F[X] (AdjoinRoot Q) :=
    (faithfulSMul_iff_algebraMap_injective F[X] (AdjoinRoot Q)).mpr
      (AdjoinRoot.of.injective_of_degree_ne_zero hd)
  rw [ringKrullDim_eq_of_normal_integral_finiteType_domain F F[X] (AdjoinRoot Q),
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp only [zero_add]

/-- A root of an actual mapped factor constructs the entire original rational
point as soon as its base restriction and value of the original generator agree. -/
theorem liftAlgHom_comp_map_eq (f : R →ₐ[F] S) (P : R[X]) (Q : S[X])
    (hQ : Q ∣ P.map f.toRingHom) (w : S →ₐ[F] F) (z : F)
    (hz : Q.eval₂ w z = 0) (χ : AdjoinRoot P →ₐ[F] F)
    (hbase : χ.comp (AdjoinRoot.ofAlgHom F P) = w.comp f)
    (hroot : χ (AdjoinRoot.root P) = z) :
    (AdjoinRoot.liftAlgHom Q w z hz).comp (AdjoinRoot.mapAlgHom f P Q hQ) = χ := by
  apply AdjoinRoot.algHom_ext'
  · trans w.comp f
    · apply AlgHom.ext
      intro r
      change AdjoinRoot.liftAlgHom Q w z hz
        (AdjoinRoot.map f.toRingHom P Q hQ (AdjoinRoot.of P r)) = w (f r)
      rw [AdjoinRoot.map_of, AdjoinRoot.liftAlgHom_of]
      rfl
    · exact hbase.symm
  · change AdjoinRoot.liftAlgHom Q w z hz
      (AdjoinRoot.map f.toRingHom P Q hQ (AdjoinRoot.root P)) = χ (AdjoinRoot.root P)
    rw [AdjoinRoot.map_root, AdjoinRoot.liftAlgHom_root]
    exact hroot.symm

/-- Two actual points whose generator values lie on the same monic irreducible
factor over a genuine affine line are joined by a constructed irreducible closed
curve in the original monogenic scheme. -/
theorem curveStep_of_irreducible_line_factor {σ : Type*} (a b : σ → F) (hb : b ≠ 0)
    (P : (MvPolynomial σ F)[X]) (Q : F[X][X]) (hQm : Q.Monic) (hQi : Irreducible Q)
    (hQ : Q ∣ P.map (AffineLine.subst a b).toRingHom)
    (χ ψ : AdjoinRoot P →ₐ[F] F) (t u : F)
    (hχbase : χ.comp (AdjoinRoot.ofAlgHom F P) = MvPolynomial.aeval (AffineLine.point a b t))
    (hψbase : ψ.comp (AdjoinRoot.ofAlgHom F P) = MvPolynomial.aeval (AffineLine.point a b u))
    (hχroot : Q.eval₂ (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom
      (χ (AdjoinRoot.root P)) = 0)
    (hψroot : Q.eval₂ (Polynomial.aeval u : F[X] →ₐ[F] F).toRingHom
      (ψ (AdjoinRoot.root P)) = 0) :
    FcCurveChains.CurveStep (rationalPoint χ) (rationalPoint ψ) := by
  have : IsDomain (AdjoinRoot Q) := AdjoinRoot.isDomain_of_prime hQi.prime
  let κ := AdjoinRoot.mapAlgHom (AffineLine.subst a b) P Q hQ
  let χQ := AdjoinRoot.liftAlgHom Q (Polynomial.aeval t) (χ (AdjoinRoot.root P)) hχroot
  let ψQ := AdjoinRoot.liftAlgHom Q (Polynomial.aeval u) (ψ (AdjoinRoot.root P)) hψroot
  have hχ : χQ.comp κ = χ := liftAlgHom_comp_map_eq (AffineLine.subst a b) P Q hQ
    (Polynomial.aeval t) _ hχroot χ
    (hχbase.trans (AffineLine.aeval_comp_subst a b t).symm) rfl
  have hψ : ψQ.comp κ = ψ := liftAlgHom_comp_map_eq (AffineLine.subst a b) P Q hQ
    (Polynomial.aeval u) _ hψroot ψ
    (hψbase.trans (AffineLine.aeval_comp_subst a b u).symm) rfl
  have hκ : Function.Surjective κ := adjoinRoot_map_surjective (AffineLine.subst a b)
    (AffineLine.subst_surjective a b hb) P Q hQ
  have hstep := curveStep_of_surjective_curve κ hκ
    (ringKrullDim_adjoinRoot_line_factor Q hQm hQi) χQ ψQ
  rwa [hχ, hψ] at hstep

/-- Every monic irreducible line factor has an actual rational point over each
line parameter, constructed from a root of its specialized relation. -/
theorem exists_rationalPoint_on_line_factor [IsAlgClosed F] {σ : Type*}
    (a b : σ → F) (P : (MvPolynomial σ F)[X]) (Q : F[X][X])
    (hQm : Q.Monic) (hQi : Irreducible Q)
    (hQ : Q ∣ P.map (AffineLine.subst a b).toRingHom) (t : F) :
    ∃ χ : AdjoinRoot P →ₐ[F] F,
      χ.comp (AdjoinRoot.ofAlgHom F P) = MvPolynomial.aeval (AffineLine.point a b t) ∧
      Q.eval₂ (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom (χ (AdjoinRoot.root P)) = 0 := by
  have hQtm : (Q.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).Monic := hQm.map _
  have hdeg : (Q.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hQtm.ne_zero, hQm.natDegree_map]
    exact_mod_cast (hQm.natDegree_pos_of_not_isUnit hQi.not_isUnit).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root
    (Q.map (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom) hdeg
  have hz' : Q.eval₂ (Polynomial.aeval t : F[X] →ₐ[F] F) z = 0 := by
    change Q.eval₂ (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom z = 0
    simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hz
  let κ := AdjoinRoot.mapAlgHom (AffineLine.subst a b) P Q hQ
  let χQ := AdjoinRoot.liftAlgHom Q (Polynomial.aeval t) z hz'
  refine ⟨χQ.comp κ, ?_, ?_⟩
  · rw [← AffineLine.aeval_comp_subst]
    apply AlgHom.ext
    intro r
    change AdjoinRoot.liftAlgHom Q (Polynomial.aeval t) z hz'
      (AdjoinRoot.map (AffineLine.subst a b).toRingHom P Q hQ (AdjoinRoot.of P r)) =
        (Polynomial.aeval t) (AffineLine.subst a b r)
    rw [AdjoinRoot.map_of, AdjoinRoot.liftAlgHom_of]
    rfl
  · change Q.eval₂ (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom
      (AdjoinRoot.liftAlgHom Q (Polynomial.aeval t) z hz'
        (AdjoinRoot.map (AffineLine.subst a b).toRingHom P Q hQ (AdjoinRoot.root P))) = 0
    rw [AdjoinRoot.map_root, AdjoinRoot.liftAlgHom_root]
    exact hz'

/-- An actual reference point at parameter zero for each actual irreducible line
factor. It is chosen from the proved geometric construction, rather than input. -/
def lineFactorPoint [IsAlgClosed F] {σ : Type*}
    (a b : σ → F) (P : (MvPolynomial σ F)[X]) (Q : F[X][X])
    (hQm : Q.Monic) (hQi : Irreducible Q)
    (hQ : Q ∣ P.map (AffineLine.subst a b).toRingHom) : AdjoinRoot P →ₐ[F] F :=
  (exists_rationalPoint_on_line_factor a b P Q hQm hQi hQ 0).choose

theorem lineFactorPoint_properties [IsAlgClosed F] {σ : Type*}
    (a b : σ → F) (P : (MvPolynomial σ F)[X]) (Q : F[X][X])
    (hQm : Q.Monic) (hQi : Irreducible Q)
    (hQ : Q ∣ P.map (AffineLine.subst a b).toRingHom) :
    (lineFactorPoint a b P Q hQm hQi hQ).comp (AdjoinRoot.ofAlgHom F P) =
        MvPolynomial.aeval (AffineLine.point a b 0) ∧
      Q.eval₂ (Polynomial.aeval 0 : F[X] →ₐ[F] F).toRingHom
        (lineFactorPoint a b P Q hQm hQi hQ (AdjoinRoot.root P)) = 0 :=
  (exists_rationalPoint_on_line_factor a b P Q hQm hQi hQ 0).choose_spec

/-- Class membership of every actual root on an irreducible line factor is
exactly membership of its constructed reference point, independently of parameter. -/
theorem curveClass_iff_lineFactorPoint [IsAlgClosed F] {σ : Type*}
    (a b : σ → F) (hb : b ≠ 0) (P : (MvPolynomial σ F)[X])
    (Q : F[X][X]) (hQm : Q.Monic) (hQi : Irreducible Q)
    (hQ : Q ∣ P.map (AffineLine.subst a b).toRingHom)
    (x : PrimeSpectrum (AdjoinRoot P)) (χ : AdjoinRoot P →ₐ[F] F) (t : F)
    (hχbase : χ.comp (AdjoinRoot.ofAlgHom F P) = MvPolynomial.aeval (AffineLine.point a b t))
    (hχroot : Q.eval₂ (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom
      (χ (AdjoinRoot.root P)) = 0) :
    rationalPoint χ ∈ curveClass x ↔
      rationalPoint (lineFactorPoint a b P Q hQm hQi hQ) ∈ curveClass x := by
  obtain ⟨hbase, hroot⟩ := lineFactorPoint_properties a b P Q hQm hQi hQ
  exact mem_curveClass_iff_of_curveStep x
    (curveStep_of_irreducible_line_factor a b hb P Q hQm hQi hQ χ
      (lineFactorPoint a b P Q hQm hQi hQ) t 0 hχbase hbase hχroot hroot)

end EnvelopeProperty.FcLineFactorCurves
