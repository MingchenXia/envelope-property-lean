import TranscendentalNakamaye.Pending.BlowupJacobianMultiplierGermEquivalence
import TranscendentalNakamaye.Pending.ComplexMonomialMultiplierUnit
import TranscendentalNakamaye.FirstPass.HolomorphicContDiff

set_option autoImplicit false

/-! # Literal multiplier germs under actual local holomorphic coordinates

The actual inverse internally supplies the nonzero holomorphic Jacobian units.
Actual Jacobian-weighted holomorphic pullback and unit cancellation then prove
exact covariance of the original weighted germ, preserving extended poles.
No nondegeneracy, compactness or integral-equivalence certificate is an input.
Reference: Demailly, *Analytic Methods in Algebraic Geometry*, multiplier
integrability; *Complex Analytic and Differential Geometry*, holomorphic charts.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace TranscendentalNakamaye.Pending.LocalHolomorphicMultiplierGermCovariance

open FirstPass DivisorialChangeOfVariables

noncomputable section

private theorem differentiableOn_complexJacobian {n : ℕ}
    {F : ComplexModel n → ComplexModel n} {D : Set (ComplexModel n)}
    (hD : IsOpen D) (hF : DifferentiableOn ℂ F D) :
    DifferentiableOn ℂ (complexJacobian F) D := by
  classical
  have hentry (i j : Fin n) : DifferentiableOn ℂ
      (fun z => (fderiv ℂ F z (FirstPass.MongeAmpere.coordinateVector j)) i) D :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp_differentiableOn
      (FirstPass.differentiableOn_fderiv_apply_of_isOpen hF hD
        (FirstPass.MongeAmpere.coordinateVector j))
  have hdet : complexJacobian F = fun z =>
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
        ∏ a : Fin n, (fderiv ℂ F z (FirstPass.MongeAmpere.coordinateVector a)) (σ a) := by
    funext z
    rw [complexJacobian, ContinuousLinearMap.det,
      ← FirstPass.MongeAmpere.det_standardMatrix, Matrix.det_apply]
    simp only [FirstPass.MongeAmpere.standardMatrix_apply]
    rfl
  rw [hdet]
  refine DifferentiableOn.fun_sum fun σ _ =>
    (?_ : DifferentiableOn ℂ _ D).const_smul _
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [differentiableOn_const]
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hentry (σ a) a).mul ih


/-- Actual differentiated inverse identities supply both genuine holomorphic
Jacobian units; no determinant certificate is an input. -/
theorem jacobian_units_of_local_holomorphic_equiv {n : ℕ} {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) :
    (∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (complexJacobian Φ.toFun) z) ∧
    (∀ᶠ z in 𝓝 (Φ.toFun p), DifferentiableAt ℂ (complexJacobian Φ.invFun) z) ∧
    complexJacobian Φ.toFun p ≠ 0 ∧ complexJacobian Φ.invFun (Φ.toFun p) ≠ 0 := by
  have hq : Φ.toFun p ∈ Φ.target := Φ.mapsTo_toFun Φ.center_mem_source
  have hto := Φ.toFun_holomorphic.differentiableAt
    (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
  have hinv := Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hq)
  have heq : (Φ.invFun ∘ Φ.toFun) =ᶠ[𝓝 p] id :=
    (show ∀ᶠ z in 𝓝 p, z ∈ Φ.source from
      Φ.isOpen_source.mem_nhds Φ.center_mem_source).mono fun z hz => Φ.left_inv z hz
  have hcomp : (fderiv ℂ Φ.invFun (Φ.toFun p)).comp (fderiv ℂ Φ.toFun p) =
      ContinuousLinearMap.id ℂ (ComplexModel n) := by
    calc
      _ = fderiv ℂ (Φ.invFun ∘ Φ.toFun) p :=
        (hinv.hasFDerivAt.comp p hto.hasFDerivAt).fderiv.symm
      _ = _ := by rw [heq.fderiv_eq, fderiv_id]
  have hlin : (fderiv ℂ Φ.invFun (Φ.toFun p)).toLinearMap.comp
      (fderiv ℂ Φ.toFun p).toLinearMap = LinearMap.id :=
    congrArg ContinuousLinearMap.toLinearMap hcomp
  have hdet := congrArg
    (fun L : ComplexModel n →ₗ[ℂ] ComplexModel n => LinearMap.det L) hlin
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  have hne : complexJacobian Φ.invFun (Φ.toFun p) * complexJacobian Φ.toFun p ≠ 0 := by
    change LinearMap.det (fderiv ℂ Φ.invFun (Φ.toFun p)).toLinearMap *
      LinearMap.det (fderiv ℂ Φ.toFun p).toLinearMap ≠ 0
    rw [hdet]
    exact one_ne_zero
  have hJto := differentiableOn_complexJacobian Φ.isOpen_source Φ.toFun_holomorphic
  have hJinv := differentiableOn_complexJacobian Φ.isOpen_target Φ.invFun_holomorphic
  refine ⟨?_, ?_, (mul_ne_zero_iff.mp hne).2, (mul_ne_zero_iff.mp hne).1⟩
  · filter_upwards [Φ.isOpen_source.mem_nhds Φ.center_mem_source] with z hz
    exact hJto.differentiableAt (Φ.isOpen_source.mem_nhds hz)
  · filter_upwards [Φ.isOpen_target.mem_nhds hq] with z hz
    exact hJinv.differentiableAt (Φ.isOpen_target.mem_nhds hz)

/-- Literal multiplier membership is covariant under an actual local
holomorphic inverse, with internal Jacobian units and actual volume integrals. -/
theorem multiplierIntegrableAt_comp_inv_iff {n : ℕ} {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p)
    {w : ComplexModel n → EReal} {f : ComplexModel n → ℂ} {c : ℝ}
    (hw : QuasiPlurisubharmonicAt w p) :
    MultiplierIntegrableAt (fun z => w (Φ.invFun z)) c
      (fun z => f (Φ.invFun z)) (Φ.toFun p) volume ↔
      MultiplierIntegrableAt w c f p volume := by
  have hq : Φ.toFun p ∈ Φ.target := Φ.mapsTo_toFun Φ.center_mem_source
  obtain ⟨hJto, hJinv, hJto0, hJinv0⟩ := jacobian_units_of_local_holomorphic_equiv Φ
  have hto : ContDiffOn ℂ ∞ Φ.toFun Φ.source :=
    contDiffOn_of_differentiableOn_complex Φ.toFun_holomorphic Φ.isOpen_source
  have hinv : ContDiffOn ℂ ∞ Φ.invFun Φ.target :=
    contDiffOn_of_differentiableOn_complex Φ.invFun_holomorphic Φ.isOpen_target
  have htoinj : InjOn Φ.toFun Φ.source := by
    intro a ha b hb hab
    have h := congrArg Φ.invFun hab
    simpa only [Φ.left_inv a ha, Φ.left_inv b hb] using h
  have hinvinj : InjOn Φ.invFun Φ.target := by
    intro a ha b hb hab
    have h := congrArg Φ.toFun hab
    simpa only [Φ.right_inv a ha, Φ.right_inv b hb] using h
  have hw' : QuasiPlurisubharmonicAt (fun z => w (Φ.invFun z)) (Φ.toFun p) :=
    HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic Φ.isOpen_target hinv hq
      (by simpa only [Φ.left_inv p Φ.center_mem_source] using hw)
  constructor
  · intro hint
    have hback := BlowupJacobianMultiplierGermEquivalence.multiplierIntegrableAt_comp_mul_complexJacobian
      Φ.isOpen_source hto Φ.center_mem_source (S := ∅) (by simp)
      (by simpa only [sdiff_empty] using htoinj) hw' hint
    have hunit := (ComplexMonomialMultiplierUnit.multiplierIntegrableAt_mul_unit_iff
      (φ := fun z => w (Φ.invFun (Φ.toFun z))) (c := c)
      (f := fun z => f (Φ.invFun (Φ.toFun z))) hJto hJto0).mp
        (by simpa only [mul_comm] using hback)
    apply hunit.congr
    · exact (show ∀ᶠ z in 𝓝 p, z ∈ Φ.source from
        Φ.isOpen_source.mem_nhds Φ.center_mem_source).mono fun z hz => congrArg w (Φ.left_inv z hz)
    · exact (show ∀ᶠ z in 𝓝 p, z ∈ Φ.source from
        Φ.isOpen_source.mem_nhds Φ.center_mem_source).mono fun z hz => congrArg f (Φ.left_inv z hz)
  · intro hint
    have hforward := BlowupJacobianMultiplierGermEquivalence.multiplierIntegrableAt_comp_mul_complexJacobian
      Φ.isOpen_target hinv hq (S := ∅) (by simp)
      (by simpa only [sdiff_empty] using hinvinj)
      (by simpa only [Φ.left_inv p Φ.center_mem_source] using hw)
      (by simpa only [Φ.left_inv p Φ.center_mem_source] using hint)
    exact (ComplexMonomialMultiplierUnit.multiplierIntegrableAt_mul_unit_iff
      (φ := fun z => w (Φ.invFun z)) (c := c) (f := fun z => f (Φ.invFun z))
      hJinv hJinv0).mp (by simpa only [mul_comm] using hforward)

end
end TranscendentalNakamaye.Pending.LocalHolomorphicMultiplierGermCovariance
