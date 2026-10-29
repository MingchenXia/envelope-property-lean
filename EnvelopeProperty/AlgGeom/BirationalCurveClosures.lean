import EnvelopeProperty.AlgGeom.LineFactorCurves

/-!
# Actual curve closures in a finite algebra

The kernel of a map from the original finite algebra into a localization of a
faithful line domain defines an actual closed curve in the original spectrum.
This is the closure construction needed when the original algebra only becomes
monogenic on a common principal open.
-/

open scoped Polynomial Classical
noncomputable section

namespace EnvelopeProperty.FcCurveClosures

open FcCurveFibres

variable {F σ A D : Type*} [Field F] [CommRing A] [CommRing D]
variable [Algebra F A] [Algebra F D]

/-- The kernel of an actual map into a localized faithful line domain has a
one-dimensional quotient in the original finite algebra. Its finiteness descends
from the original polynomial base to the entire actual line ring. -/
theorem kernel_quotient_dim_one_of_line_localization [IsDomain D]
    (a b : σ → F) (hb : b ≠ 0)
    (φ : MvPolynomial σ F →ₐ[F] A) (hφ : φ.toRingHom.Finite)
    (γ : F[X] →ₐ[F] D) (hiγ : Function.Injective γ) (d : D) (hd : d ≠ 0)
    (α : A →ₐ[F] Localization.Away d)
    (hbase : α.comp φ =
      ((IsScalarTower.toAlgHom F D (Localization.Away d)).comp γ).comp (AffineLine.subst a b)) :
    ringKrullDim (A ⧸ RingHom.ker α.toRingHom) = 1 := by
  let T := Localization.Away d
  have hnd : Submonoid.powers d ≤ nonZeroDivisors D :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hd)
  have : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T hnd
  have hloc : Function.Injective (algebraMap D T) := IsLocalization.injective T hnd
  let J := RingHom.ker α.toRingHom
  have : J.IsPrime := RingHom.ker_isPrime α
  let π := Ideal.Quotient.mkₐ F J
  let ρ := Ideal.Quotient.liftₐ J α (fun _ ha => ha)
  let η := (IsScalarTower.toAlgHom F D T).comp γ
  have hk : RingHom.ker (AffineLine.subst a b).toRingHom ≤
      RingHom.ker (π.comp φ).toRingHom := by
    intro p hp
    have he := congrArg (fun f : MvPolynomial σ F →ₐ[F] T => f p) hbase
    change α (φ p) = algebraMap D T (γ (AffineLine.subst a b p)) at he
    change AffineLine.subst a b p = 0 at hp
    have hz : α (φ p) = 0 := by simpa only [hp, map_zero] using he
    change Ideal.Quotient.mk J (φ p) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
  let lineHom := AlgHom.liftOfSurjective (AffineLine.subst a b)
    (AffineLine.subst_surjective a b hb) (π.comp φ) hk
  have hlineHom : lineHom.comp (AffineLine.subst a b) = π.comp φ :=
    AlgHom.liftOfSurjective_comp _ _ _ _
  have hρlineHom : ρ.comp lineHom = η := by
    apply AlgHom.ext
    intro q
    obtain ⟨p, rfl⟩ := AffineLine.subst_surjective a b hb q
    have he := congrArg (fun f : MvPolynomial σ F →ₐ[F] (A ⧸ J) => f p) hlineHom
    change lineHom (AffineLine.subst a b p) = π (φ p) at he
    change ρ (lineHom (AffineLine.subst a b p)) = η (AffineLine.subst a b p)
    rw [he]
    change α (φ p) = algebraMap D T (γ (AffineLine.subst a b p))
    exact congrArg (fun f : MvPolynomial σ F →ₐ[F] T => f p) hbase
  have hiη : Function.Injective η := hloc.comp hiγ
  have hilineHom : Function.Injective lineHom := by
    intro q r he
    apply hiη
    rw [← hρlineHom]
    exact congrArg ρ he
  let : Algebra (MvPolynomial σ F) A := φ.toRingHom.toAlgebra
  let : Algebra (MvPolynomial σ F) F[X] := (AffineLine.subst a b).toRingHom.toAlgebra
  let : Algebra F[X] (A ⧸ J) := lineHom.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial σ F) A := hφ
  have : IsScalarTower (MvPolynomial σ F) F[X] (A ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun p =>
      (congrArg (fun f : MvPolynomial σ F →ₐ[F] (A ⧸ J) => f p) hlineHom).symm
  have : Module.Finite F[X] (A ⧸ J) :=
    Module.Finite.of_restrictScalars_finite (MvPolynomial σ F) F[X] (A ⧸ J)
  have : IsScalarTower F F[X] (A ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun c => (lineHom.commutes c).symm
  have : Algebra.FiniteType F (A ⧸ J) := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F F[X])
    (inferInstance : Algebra.FiniteType F[X] (A ⧸ J))
  have : FaithfulSMul F[X] (A ⧸ J) :=
    (faithfulSMul_iff_algebraMap_injective F[X] (A ⧸ J)).mpr hilineHom
  rw [ringKrullDim_eq_of_normal_integral_finiteType_domain F F[X] (A ⧸ J),
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

/-- Actual rational points of the localized line domain lie on the actual closed
kernel curve in the original spectrum. -/
theorem curveStep_of_line_localization [IsDomain D]
    (a b : σ → F) (hb : b ≠ 0)
    (φ : MvPolynomial σ F →ₐ[F] A) (hφ : φ.toRingHom.Finite)
    (γ : F[X] →ₐ[F] D) (hiγ : Function.Injective γ) (d : D) (hd : d ≠ 0)
    (α : A →ₐ[F] Localization.Away d)
    (hbase : α.comp φ =
      ((IsScalarTower.toAlgHom F D (Localization.Away d)).comp γ).comp (AffineLine.subst a b))
    (χ ψ : Localization.Away d →ₐ[F] F) :
    FcCurveChains.CurveStep (rationalPoint (χ.comp α)) (rationalPoint (ψ.comp α)) := by
  have : IsDomain (Localization.Away d) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers d)
      (Localization.Away d) (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hd))
  refine ⟨RingHom.ker α.toRingHom, RingHom.ker_isPrime α,
    kernel_quotient_dim_one_of_line_localization a b hb φ hφ γ hiγ d hd α hbase, ?_, ?_⟩
  · intro r hr
    change χ (α r) = 0
    change α r = 0 at hr
    rw [hr, map_zero]
  · intro r hr
    change ψ (α r) = 0
    change α r = 0 at hr
    rw [hr, map_zero]

/-- The actual map from the original algebra to the localized curve quotient,
constructed through the inverse of a genuine common-principal-open isomorphism. -/
def commonOpenCurveMap {C : Type*} [CommRing C] [Algebra F C]
    (δ : C →ₐ[F] A) (κ : C →ₐ[F] D) (h : C)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h)) :
    A →ₐ[F] Localization.Away (κ h) :=
  (IsLocalization.Away.mapₐ (Localization.Away h) (Localization.Away (κ h)) κ h).comp
    (e.symm.toAlgHom.comp (IsScalarTower.toAlgHom F A (Localization.Away (δ h))))

/-- Compatibility of the common-open isomorphism preserves the entire original
subalgebra homomorphism after mapping to the actual curve localization. -/
theorem commonOpenCurveMap_comp {C : Type*} [CommRing C] [Algebra F C]
    (δ : C →ₐ[F] A) (κ : C →ₐ[F] D) (h : C)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h))
    (he : ∀ c : C, e (algebraMap C (Localization.Away h) c) =
      algebraMap A (Localization.Away (δ h)) (δ c)) :
    (commonOpenCurveMap δ κ h e).comp δ =
      (IsScalarTower.toAlgHom F D (Localization.Away (κ h))).comp κ := by
  apply AlgHom.ext
  intro c
  change IsLocalization.Away.mapₐ (Localization.Away h) (Localization.Away (κ h)) κ h
    (e.symm (algebraMap A (Localization.Away (δ h)) (δ c))) =
      algebraMap D (Localization.Away (κ h)) (κ c)
  rw [← he c, e.symm_apply_apply]
  simp only [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq]
  rfl

/-- Under a genuine common-principal-open isomorphism, a faithful line factor
constructs a closed kernel curve in the original finite algebra. All rational
points transported through this open lie on that actual original-algebra curve. -/
theorem curveStep_of_commonOpen_line_factor [IsDomain D]
    {C : Type*} [CommRing C] [Algebra F C]
    (a b : σ → F) (hb : b ≠ 0) (φ : MvPolynomial σ F →ₐ[F] C)
    (δ : C →ₐ[F] A) (hφ : (δ.comp φ).toRingHom.Finite)
    (κ : C →ₐ[F] D) (γ : F[X] →ₐ[F] D) (hiγ : Function.Injective γ)
    (hκ : κ.comp φ = γ.comp (AffineLine.subst a b)) (h : C)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h))
    (he : ∀ c : C, e (algebraMap C (Localization.Away h) c) =
      algebraMap A (Localization.Away (δ h)) (δ c)) (hd : κ h ≠ 0)
    (χ ψ : Localization.Away (κ h) →ₐ[F] F) :
    FcCurveChains.CurveStep
      (rationalPoint (χ.comp (commonOpenCurveMap δ κ h e)))
      (rationalPoint (ψ.comp (commonOpenCurveMap δ κ h e))) := by
  have hbase : (commonOpenCurveMap δ κ h e).comp (δ.comp φ) =
      ((IsScalarTower.toAlgHom F D (Localization.Away (κ h))).comp γ).comp
        (AffineLine.subst a b) := by
    apply AlgHom.ext
    intro p
    have hc := congrArg (fun f : C →ₐ[F] Localization.Away (κ h) => f (φ p))
      (commonOpenCurveMap_comp δ κ h e he)
    have hp := congrArg (fun f : MvPolynomial σ F →ₐ[F] D => f p) hκ
    change commonOpenCurveMap δ κ h e (δ (φ p)) =
      algebraMap D (Localization.Away (κ h)) (γ (AffineLine.subst a b p))
    exact hc.trans (congrArg (algebraMap D (Localization.Away (κ h))) hp)
  exact curveStep_of_line_localization a b hb (δ.comp φ) hφ γ hiγ (κ h) hd
    (commonOpenCurveMap δ κ h e) hbase χ ψ

/-- On the genuine common principal open, the whole restriction to the
monogenic subalgebra determines an actual rational point of the original algebra. -/
theorem commonOpen_rationalHom_ext {C : Type*} [CommRing C] [Algebra F C]
    (δ : C →ₐ[F] A) (h : C)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h))
    (he : ∀ c : C, e (algebraMap C (Localization.Away h) c) =
      algebraMap A (Localization.Away (δ h)) (δ c))
    (χ ψ : A →ₐ[F] F) (hχ : χ (δ h) ≠ 0) (hbase : χ.comp δ = ψ.comp δ) : χ = ψ := by
  have hψ : ψ (δ h) ≠ 0 := by
    have hh := congrArg (fun f : C →ₐ[F] F => f h) hbase
    change χ (δ h) = ψ (δ h) at hh
    rwa [← hh]
  let χ' : Localization.Away (δ h) →ₐ[F] F :=
    IsLocalization.Away.liftAlgHom (δ h) (f := χ) (isUnit_iff_ne_zero.mpr hχ)
  let ψ' : Localization.Away (δ h) →ₐ[F] F :=
    IsLocalization.Away.liftAlgHom (δ h) (f := ψ) (isUnit_iff_ne_zero.mpr hψ)
  have hχeval (a : A) : χ' (algebraMap A (Localization.Away (δ h)) a) = χ a :=
    IsLocalization.Away.lift_eq (δ h) (g := χ.toRingHom) (isUnit_iff_ne_zero.mpr hχ) a
  have hψeval (a : A) : ψ' (algebraMap A (Localization.Away (δ h)) a) = ψ a :=
    IsLocalization.Away.lift_eq (δ h) (g := ψ.toRingHom) (isUnit_iff_ne_zero.mpr hψ) a
  have hcomp : χ'.comp e.toAlgHom = ψ'.comp e.toAlgHom := by
    apply IsLocalization.algHom_ext (Submonoid.powers h)
    apply AlgHom.ext
    intro c
    change χ' (e (algebraMap C (Localization.Away h) c)) =
      ψ' (e (algebraMap C (Localization.Away h) c))
    rw [he c, hχeval, hψeval]
    exact congrArg (fun f : C →ₐ[F] F => f c) hbase
  have hloc : χ' = ψ' := by
    apply AlgHom.ext
    intro a
    obtain ⟨c, rfl⟩ := e.surjective a
    exact congrArg (fun f : Localization.Away h →ₐ[F] F => f c) hcomp
  apply AlgHom.ext
  intro a
  rw [← hχeval a, ← hψeval a, hloc]

/-- A prescribed original rational point whose subalgebra restriction factors
through the curve quotient is the whole image of an actual localized curve point. -/
theorem exists_localized_curveEval_of_commonOpen_rationalPoint
    {C : Type*} [CommRing C] [Algebra F C]
    (δ : C →ₐ[F] A) (κ : C →ₐ[F] D) (h : C)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h))
    (he : ∀ c : C, e (algebraMap C (Localization.Away h) c) =
      algebraMap A (Localization.Away (δ h)) (δ c))
    (χ : A →ₐ[F] F) (χD : D →ₐ[F] F) (hχ : χ (δ h) ≠ 0)
    (hres : χD.comp κ = χ.comp δ) :
    ∃ χT : Localization.Away (κ h) →ₐ[F] F,
      χT.comp (commonOpenCurveMap δ κ h e) = χ := by
  have hχD : χD (κ h) ≠ 0 := by
    have hh := congrArg (fun f : C →ₐ[F] F => f h) hres
    change χD (κ h) = χ (δ h) at hh
    rwa [hh]
  let χT : Localization.Away (κ h) →ₐ[F] F :=
    IsLocalization.Away.liftAlgHom (κ h) (f := χD) (isUnit_iff_ne_zero.mpr hχD)
  have hχTeval (d : D) : χT (algebraMap D (Localization.Away (κ h)) d) = χD d :=
    IsLocalization.Away.lift_eq (κ h) (g := χD.toRingHom) (isUnit_iff_ne_zero.mpr hχD) d
  have hbase : (χT.comp (commonOpenCurveMap δ κ h e)).comp δ = χ.comp δ := by
    apply AlgHom.ext
    intro c
    have hc := congrArg (fun f : C →ₐ[F] Localization.Away (κ h) => f c)
      (commonOpenCurveMap_comp δ κ h e he)
    change commonOpenCurveMap δ κ h e (δ c) =
      algebraMap D (Localization.Away (κ h)) (κ c) at hc
    change χT (commonOpenCurveMap δ κ h e (δ c)) = χ (δ c)
    rw [hc, hχTeval]
    exact congrArg (fun f : C →ₐ[F] F => f c) hres
  exact ⟨χT, (commonOpen_rationalHom_ext δ h e he χ
    (χT.comp (commonOpenCurveMap δ κ h e)) hχ hbase.symm).symm⟩

/-- Two prescribed rational points of the original finite algebra, on its genuine
common open with a monogenic subalgebra and on the same irreducible line factor,
lie on one actual irreducible closed curve of the original spectrum. The prime,
its dimension, both localized lifts, and identification of the entire original
points are constructed. The original algebra need not be globally monogenic. -/
theorem curveStep_of_commonOpen_irreducible_line_factor
    (a b : σ → F) (hb : b ≠ 0) (P : (MvPolynomial σ F)[X])
    (Q : F[X][X]) (hQm : Q.Monic) (hQi : Irreducible Q)
    (hQ : Q ∣ P.map (AffineLine.subst a b).toRingHom)
    (δ : AdjoinRoot P →ₐ[F] A)
    (hφ : (δ.comp (AdjoinRoot.ofAlgHom F P)).toRingHom.Finite)
    (h : AdjoinRoot P)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h))
    (he : ∀ c : AdjoinRoot P, e (algebraMap _ (Localization.Away h) c) =
      algebraMap A (Localization.Away (δ h)) (δ c))
    (χ ψ : A →ₐ[F] F) (t u : F)
    (hχbase : (χ.comp δ).comp (AdjoinRoot.ofAlgHom F P) =
      MvPolynomial.aeval (AffineLine.point a b t))
    (hψbase : (ψ.comp δ).comp (AdjoinRoot.ofAlgHom F P) =
      MvPolynomial.aeval (AffineLine.point a b u))
    (hχroot : Q.eval₂ (Polynomial.aeval t : F[X] →ₐ[F] F).toRingHom
      (χ (δ (AdjoinRoot.root P))) = 0)
    (hψroot : Q.eval₂ (Polynomial.aeval u : F[X] →ₐ[F] F).toRingHom
      (ψ (δ (AdjoinRoot.root P))) = 0)
    (hχh : χ (δ h) ≠ 0) (hψh : ψ (δ h) ≠ 0) :
    FcCurveChains.CurveStep (rationalPoint χ) (rationalPoint ψ) := by
  have : IsDomain (AdjoinRoot Q) := AdjoinRoot.isDomain_of_prime hQi.prime
  let κ := AdjoinRoot.mapAlgHom (AffineLine.subst a b) P Q hQ
  let γ := AdjoinRoot.ofAlgHom F Q
  have hdQ : Q.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hQm.ne_zero]
    exact_mod_cast (hQm.natDegree_pos_of_not_isUnit hQi.not_isUnit).ne'
  have hiγ : Function.Injective γ := AdjoinRoot.of.injective_of_degree_ne_zero hdQ
  have hκ : κ.comp (AdjoinRoot.ofAlgHom F P) = γ.comp (AffineLine.subst a b) := by
    apply AlgHom.ext
    intro p
    change AdjoinRoot.map (AffineLine.subst a b).toRingHom P Q hQ (AdjoinRoot.of P p) =
      AdjoinRoot.of Q (AffineLine.subst a b p)
    rw [AdjoinRoot.map_of]
    rfl
  let χQ := AdjoinRoot.liftAlgHom Q (Polynomial.aeval t) (χ (δ (AdjoinRoot.root P))) hχroot
  let ψQ := AdjoinRoot.liftAlgHom Q (Polynomial.aeval u) (ψ (δ (AdjoinRoot.root P))) hψroot
  have hχres : χQ.comp κ = χ.comp δ := FcLineFactorCurves.liftAlgHom_comp_map_eq
    (AffineLine.subst a b) P Q hQ (Polynomial.aeval t) _ hχroot (χ.comp δ)
    (hχbase.trans (AffineLine.aeval_comp_subst a b t).symm) rfl
  have hψres : ψQ.comp κ = ψ.comp δ := FcLineFactorCurves.liftAlgHom_comp_map_eq
    (AffineLine.subst a b) P Q hQ (Polynomial.aeval u) _ hψroot (ψ.comp δ)
    (hψbase.trans (AffineLine.aeval_comp_subst a b u).symm) rfl
  obtain ⟨χT, hχT⟩ := exists_localized_curveEval_of_commonOpen_rationalPoint
    δ κ h e he χ χQ hχh hχres
  obtain ⟨ψT, hψT⟩ := exists_localized_curveEval_of_commonOpen_rationalPoint
    δ κ h e he ψ ψQ hψh hψres
  have hd : κ h ≠ 0 := by
    intro hz
    have hh := congrArg (fun f : AdjoinRoot P →ₐ[F] F => f h) hχres
    change χQ (κ h) = χ (δ h) at hh
    apply hχh
    rw [← hh, hz, map_zero]
  have hstep := curveStep_of_commonOpen_line_factor a b hb (AdjoinRoot.ofAlgHom F P)
    δ hφ κ γ hiγ hκ h e he hd χT ψT
  rwa [hχT, hψT] at hstep

end EnvelopeProperty.FcCurveClosures
