import EnvelopeProperty.AlgGeom.CurveChains
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import EnvelopeProperty.AlgGeom.ProjectionNoether

/-!
# Rational fibres and their actual curve-class root products

This file constructs the fibre factors used in steps (iii) and (iv) of
`lem:fc-curve-chains`. A rational fibre is the actual set of algebra homomorphisms
with a prescribed entire restriction to the base. Finiteness follows from the
actual finite algebra homomorphism. Filtering those actual points by their curve
class gives complementary monic root-product factors. The actual component
construction also lifts to rational points over an algebraically closed field.
-/

open scoped Polynomial Classical
noncomputable section

namespace EnvelopeProperty
namespace FcCurveFibres

variable {F R B : Type*} [Field F] [CommRing R] [CommRing B]
variable [Algebra F R] [Algebra F B]

/-- The actual rational fibre of an affine algebra homomorphism. -/
def rationalFibre (φ : R →ₐ[F] B) (w : R →ₐ[F] F) : Set (B →ₐ[F] F) :=
  {χ | χ.comp φ = w}

/-- The genuine scheme point underlying a rational algebra homomorphism. -/
def rationalPoint (χ : B →ₐ[F] F) : PrimeSpectrum B :=
  ⟨RingHom.ker χ.toRingHom, RingHom.ker_isPrime χ⟩

/-- The full rational algebra homomorphism is determined by its underlying scheme point. -/
theorem rationalPoint_injective : Function.Injective (rationalPoint (F := F) (B := B)) := by
  intro χ ψ he
  apply AlgHom.ext
  intro b
  have hker := congrArg PrimeSpectrum.asIdeal he
  have hb : b - algebraMap F B (ψ b) ∈ (rationalPoint ψ).asIdeal := by
    change ψ (b - algebraMap F B (ψ b)) = 0
    simp only [map_sub, ψ.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  rw [← hker] at hb
  change χ (b - algebraMap F B (ψ b)) = 0 at hb
  simpa only [map_sub, χ.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] using hb

/-- Underlying scheme points preserve the entire base restriction of a rational point. -/
theorem rationalPoint_comp (φ : R →ₐ[F] B) (χ : B →ₐ[F] F) :
    rationalPoint (χ.comp φ) = PrimeSpectrum.comap φ.toRingHom (rationalPoint χ) := by
  apply PrimeSpectrum.ext
  ext r
  rfl

/-- Every actual rational fibre of a finite algebra homomorphism is finite, over every
field and without any separability, reducedness, or chosen separating-element input. -/
theorem rationalFibre_finite (φ : R →ₐ[F] B) (hφ : φ.toRingHom.Finite)
    (w : R →ₐ[F] F) : (rationalFibre φ w).Finite := by
  let : Algebra R B := φ.toRingHom.toAlgebra
  let : Algebra R F := w.toRingHom.toAlgebra
  have : Module.Finite R B := hφ
  let lift : {χ : B →ₐ[F] F // χ ∈ rationalFibre φ w} → (B →ₐ[R] F) := fun χ =>
    { χ.1.toRingHom with
      commutes' := fun r => congrArg (fun ψ : R →ₐ[F] F => ψ r) χ.2 }
  have hi : Function.Injective lift := by
    intro χ ψ he
    apply Subtype.ext
    apply AlgHom.ext
    intro b
    exact congrArg (fun α : B →ₐ[R] F => α b) he
  have : Finite {χ : B →ₐ[F] F // χ ∈ rationalFibre φ w} := Finite.of_injective lift hi
  exact Set.toFinite _

/-- An actual `F`-rational scheme point is closed, without any finite type assumption. -/
theorem rationalPoint_isClosed (χ : B →ₐ[F] F) :
    IsClosed ({rationalPoint χ} : Set (PrimeSpectrum B)) := by
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal (rationalPoint χ)).mpr
  apply RingHom.ker_isMaximal_of_surjective χ
  intro a
  exact ⟨algebraMap F B a, by simpa only [Algebra.algebraMap_self, RingHom.id_apply] using χ.commutes a⟩

/-- Nullstellensatz constructs an actual rational algebra homomorphism representing any
closed point, using the author's finite-type residue-field theorem. -/
theorem exists_rationalPoint_eq [IsAlgClosed F] [Algebra.FiniteType F B]
    (x : PrimeSpectrum B) (hx : x.asIdeal.IsMaximal) :
    ∃ χ : B →ₐ[F] F, rationalPoint χ = x := by
  have : x.asIdeal.IsMaximal := hx
  let e : F ≃ₐ[F] B ⧸ x.asIdeal := AlgEquiv.ofBijective
    (Algebra.ofId F (B ⧸ x.asIdeal))
    (bijective_algebraMap_quotient_of_isMaximal F x.asIdeal)
  let χ := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ F x.asIdeal)
  refine ⟨χ, PrimeSpectrum.ext ?_⟩
  ext b
  change e.symm (Ideal.Quotient.mk x.asIdeal b) = 0 ↔ b ∈ x.asIdeal
  rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

/-- Actual curve components reach actual rational points of the line, preserving the
entire prescribed algebra homomorphism on the base. The given finite map supplies finite
type over `F`; the new point and the curve through it are constructed. -/
theorem exists_rational_curveStep_over_linePoint [IsAlgClosed F] [IsDomain B]
    {σ : Type*} [Fintype σ] (a b : σ → F) (j : σ) (g : MvPolynomial σ F)
    (hb : b j ≠ 0) (hg : g ≠ 0) (hline : AffineLine.subst a b g ≠ 0)
    (φ : Localization.Away g →ₐ[F] B) (hφ : φ.toRingHom.Finite)
    (hiφ : Function.Injective φ) (χ : B →ₐ[F] F)
    (hχ : (AffineLine.lineIdeal a b j).map
      (φ.toRingHom.comp (algebraMap _ (Localization.Away g))) ≤ RingHom.ker χ.toRingHom)
    (w : AffineLine.OpenLineRing (AffineLine.subst a b g) →ₐ[F] F) :
    ∃ ψ : B →ₐ[F] F, FcCurveChains.CurveStep (rationalPoint χ) (rationalPoint ψ) ∧
      ψ.comp φ = w.comp (AffineLine.principalLineHom a b g) := by
  let R₀ := Localization.Away g
  let : Algebra R₀ B := φ.toRingHom.toAlgebra
  have : IsScalarTower F R₀ B := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have : Module.Finite R₀ B := hφ
  have : Algebra.FinitePresentation (MvPolynomial σ F) R₀ :=
    IsLocalization.Away.finitePresentation g
  have : Algebra.FiniteType F R₀ := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F (MvPolynomial σ F))
    (inferInstance : Algebra.FiniteType (MvPolynomial σ F) R₀)
  have : Algebra.FiniteType F B := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F R₀) (inferInstance : Algebra.FiniteType R₀ B)
  have hw : (rationalPoint w).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal (rationalPoint w)).mp (rationalPoint_isClosed w)
  obtain ⟨y, hymax, hxy, hy⟩ := FcCurveChains.exists_closed_curveStep_over_linePoint
    a b j g hb φ hg hline hφ hiφ (rationalPoint χ) hχ (rationalPoint w) hw
  obtain ⟨ψ, hψ⟩ := exists_rationalPoint_eq (F := F) y hymax
  rw [← hψ] at hxy hy
  refine ⟨ψ, hxy, rationalPoint_injective ?_⟩
  rw [rationalPoint_comp, rationalPoint_comp]
  exact hy

section PrincipalCoordinates

variable {σ : Type*} {g : MvPolynomial σ F}

/-- The actual full affine coordinate tuple of a rational point of a principal open. -/
def principalCoordinates (v : Localization.Away g →ₐ[F] F) : σ → F :=
  fun i => v (algebraMap (MvPolynomial σ F) (Localization.Away g) (MvPolynomial.X i))

theorem principalCoordinates_eval (v : Localization.Away g →ₐ[F] F)
    (P : MvPolynomial σ F) :
    v (algebraMap _ (Localization.Away g) P) = MvPolynomial.eval (principalCoordinates v) P := by
  have he : v.comp (IsScalarTower.toAlgHom F (MvPolynomial σ F) (Localization.Away g)) =
      MvPolynomial.aeval (principalCoordinates v) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.aeval_X]
    rfl
  exact congrArg (fun f : MvPolynomial σ F →ₐ[F] F => f P) he

theorem principalCoordinates_injective :
    Function.Injective (principalCoordinates (F := F) (g := g)) := by
  intro v w he
  apply IsLocalization.algHom_ext (Submonoid.powers g)
  apply MvPolynomial.algHom_ext
  intro i
  change principalCoordinates v i = principalCoordinates w i
  exact congrFun he i

theorem principalCoordinates_eval_ne_zero (v : Localization.Away g →ₐ[F] F) :
    MvPolynomial.eval (principalCoordinates v) g ≠ 0 := by
  rw [← principalCoordinates_eval]
  exact ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).map
    v.toRingHom).ne_zero

end PrincipalCoordinates

/-- Every actual rational curve class meets every rational fibre of a finite injective
map to a principal open of affine space. The line, its component, and its rational point
are constructed from the two whole base homomorphisms; no geometric incidence is input. -/
theorem exists_rational_curveChain_in_fibre [IsAlgClosed F] [IsDomain B]
    {σ : Type*} [Fintype σ] (g : MvPolynomial σ F)
    (φ : Localization.Away g →ₐ[F] B) (hφ : φ.toRingHom.Finite)
    (hiφ : Function.Injective φ) (χ : B →ₐ[F] F)
    (w : Localization.Away g →ₐ[F] F) :
    ∃ ψ : B →ₐ[F] F, FcCurveChains.CurveChain (rationalPoint χ) (rationalPoint ψ) ∧
      ψ.comp φ = w := by
  by_cases he : χ.comp φ = w
  · exact ⟨χ, FcCurveChains.CurveChain.refl _, he⟩
  let a := principalCoordinates (χ.comp φ)
  let z := principalCoordinates w
  let b : σ → F := fun i => z i - a i
  have haz : a ≠ z := fun h => he (principalCoordinates_injective h)
  obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
    by_contra! h
    apply haz
    funext i
    exact (sub_eq_zero.mp (h i)).symm
  have ha : MvPolynomial.eval a g ≠ 0 := principalCoordinates_eval_ne_zero (χ.comp φ)
  have hz : MvPolynomial.eval z g ≠ 0 := principalCoordinates_eval_ne_zero w
  have hg : g ≠ 0 := by
    intro h
    apply ha
    simp only [h, map_zero]
  have hline : AffineLine.subst a b g ≠ 0 := by
    intro h
    apply ha
    rw [← AffineLine.eval_subst_zero a b g, h, Polynomial.eval_zero]
  have hpoint : AffineLine.point a b 1 = z := by
    funext i
    simp only [AffineLine.point, one_mul, b, add_sub_cancel]
  have ht : Polynomial.eval 1 (AffineLine.subst a b g) ≠ 0 := by
    rwa [AffineLine.eval_subst, hpoint]
  let wL := AffineLine.openLineEval (AffineLine.subst a b g) 1 ht
  have hwL : wL.comp (AffineLine.principalLineHom a b g) = w := by
    apply principalCoordinates_injective
    funext i
    change wL (AffineLine.principalLineHom a b g
      (algebraMap (MvPolynomial σ F) (Localization.Away g) (MvPolynomial.X i))) = z i
    rw [AffineLine.principalLineHom_algebraMap]
    change AffineLine.openLineEval _ _ _ _ = z i
    rw [AffineLine.openLineEval_algebraMap, AffineLine.eval_subst, hpoint,
      MvPolynomial.eval_X]
  have hχ : (AffineLine.lineIdeal a b j).map
      (φ.toRingHom.comp (algebraMap _ (Localization.Away g))) ≤ RingHom.ker χ.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro P hP
    change (χ.comp φ) (algebraMap _ (Localization.Away g) P) = 0
    rw [principalCoordinates_eval]
    change MvPolynomial.eval a P = 0
    rw [← AffineLine.eval_subst_zero a b P]
    have hzero := AffineLine.lineIdeal_le_ker_subst a b j hj hP
    change AffineLine.subst a b P = 0 at hzero
    rw [hzero, Polynomial.eval_zero]
  obtain ⟨ψ, hψ, hbase⟩ := exists_rational_curveStep_over_linePoint a b j g hj hg hline
    φ hφ hiφ χ hχ wL
  exact ⟨ψ, hψ.curveChain, hbase.trans hwL⟩

/-- A monic annihilator and an element separating the actual rational fibre make that
fibre finite: its image embeds in the finite root set of the specialized annihilator. -/
theorem rationalFibre_finite_of_separating_element
    (φ : R →ₐ[F] B) (w : R →ₐ[F] F) (b : B) (P : R[X]) (hP : P.Monic)
    (hann : P.eval₂ φ.toRingHom b = 0)
    (hsep : Set.InjOn (fun χ : B →ₐ[F] F => χ b) (rationalFibre φ w)) :
    (rationalFibre φ w).Finite := by
  apply Set.Finite.of_injOn (t := {a : F | Polynomial.IsRoot (P.map w.toRingHom) a})
    (f := fun χ : B →ₐ[F] F => χ b) ?_ hsep
      (Polynomial.finite_setOfPred_isRoot (hP.map w.toRingHom).ne_zero)
  intro χ hχ
  change (P.map w.toRingHom).eval (χ b) = 0
  have hc : χ.toRingHom.comp φ.toRingHom = w.toRingHom :=
    congrArg AlgHom.toRingHom hχ
  rw [Polynomial.eval_map, ← hc]
  change P.eval₂ (χ.toRingHom.comp φ.toRingHom) (χ.toRingHom b) = 0
  rw [← Polynomial.hom_eval₂ P φ.toRingHom χ.toRingHom b]
  simp only [hann, map_zero]

/-- The actual curve class of a scheme point, using finite chains of prime quotients
of Krull dimension one. -/
def curveClass (x : PrimeSpectrum B) : Set (PrimeSpectrum B) :=
  {y | FcCurveChains.CurveChain x y}

theorem mem_curveClass_iff_of_curveStep (x : PrimeSpectrum B) {y z : PrimeSpectrum B}
    (h : FcCurveChains.CurveStep y z) : y ∈ curveClass x ↔ z ∈ curveClass x :=
  ⟨fun hy => hy.trans h.curveChain, fun hz => hz.trans h.symm.curveChain⟩

/-- Curve-class membership is constant on the rational points of an actual irreducible
closed affine curve. -/
theorem rationalPoint_mem_curveClass_iff_on_curve
    (x : PrimeSpectrum B) (P : Ideal B) (hP : P.IsPrime)
    (hd : ringKrullDim (B ⧸ P) = 1) (χ ψ : B →ₐ[F] F)
    (hχ : P ≤ RingHom.ker χ.toRingHom) (hψ : P ≤ RingHom.ker ψ.toRingHom) :
    rationalPoint χ ∈ curveClass x ↔ rationalPoint ψ ∈ curveClass x :=
  mem_curveClass_iff_of_curveStep x ⟨P, hP, hd, hχ, hψ⟩

/-- The actual monic root product for points of one subset of the scheme spectrum. -/
def classFactor (s : Finset (B →ₐ[F] F)) (S : Set (PrimeSpectrum B)) (b : B) : F[X] :=
  ∏ χ ∈ s.filter (fun χ => rationalPoint χ ∈ S), (Polynomial.X - Polynomial.C (χ b))

theorem classFactor_monic (s : Finset (B →ₐ[F] F)) (S : Set (PrimeSpectrum B)) (b : B) :
    (classFactor s S b).Monic := by
  classical
  exact Polynomial.monic_prod_X_sub_C (fun χ : B →ₐ[F] F => χ b)
    (s.filter (fun χ => rationalPoint χ ∈ S))

/-- The two complementary actual root products multiply to the product over the whole
finite rational fibre. -/
theorem classFactor_mul_compl (s : Finset (B →ₐ[F] F)) (S : Set (PrimeSpectrum B)) (b : B) :
    classFactor s S b * classFactor s Sᶜ b =
      ∏ χ ∈ s, (Polynomial.X - Polynomial.C (χ b)) := by
  classical
  simpa only [classFactor, Set.mem_compl_iff] using
    Finset.prod_filter_mul_prod_filter_not s (fun χ => rationalPoint χ ∈ S)
      (fun χ => Polynomial.X - Polynomial.C (χ b))

/-- The degree is exactly the number of actual points in the selected part of the
fibre; repeated values of the chosen element cause no loss of multiplicity. -/
theorem natDegree_classFactor (s : Finset (B →ₐ[F] F)) (S : Set (PrimeSpectrum B)) (b : B) :
    (classFactor s S b).natDegree = (s.filter (fun χ => rationalPoint χ ∈ S)).card := by
  classical
  simpa only [classFactor, Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul,
    mul_one] using Polynomial.natDegree_prod_of_monic
      (s.filter (fun χ => rationalPoint χ ∈ S))
      (fun χ => Polynomial.X - Polynomial.C (χ b))
      (fun χ _hχ => Polynomial.monic_X_sub_C (χ b))

theorem natDegree_classFactor_pos_of_mem (s : Finset (B →ₐ[F] F))
    (S : Set (PrimeSpectrum B)) (b : B) {χ : B →ₐ[F] F}
    (hχ : χ ∈ s) (hS : rationalPoint χ ∈ S) : 0 < (classFactor s S b).natDegree := by
  classical
  rw [natDegree_classFactor]
  exact Finset.card_pos.mpr ⟨χ, Finset.mem_filter.mpr ⟨hχ, hS⟩⟩

/-- The actual finite rational fibre, with its membership condition preserved verbatim. -/
def rationalFibreFinset (φ : R →ₐ[F] B) (hφ : φ.toRingHom.Finite) (w : R →ₐ[F] F) :
    Finset (B →ₐ[F] F) := (rationalFibre_finite φ hφ w).toFinset

theorem mem_rationalFibreFinset (φ : R →ₐ[F] B) (hφ : φ.toRingHom.Finite)
    (w : R →ₐ[F] F) (χ : B →ₐ[F] F) :
    χ ∈ rationalFibreFinset φ hφ w ↔ χ.comp φ = w := by
  change χ ∈ (rationalFibre_finite φ hφ w).toFinset ↔ χ.comp φ = w
  rw [Set.Finite.mem_toFinset]
  rfl

/-- The concrete coefficient family associated to an actual subset of scheme points;
neither a finite fibre nor a polynomial factor family is an input. -/
def fibreClassFactor (φ : R →ₐ[F] B) (hφ : φ.toRingHom.Finite)
    (S : Set (PrimeSpectrum B)) (b : B) (w : R →ₐ[F] F) : F[X] :=
  classFactor (rationalFibreFinset φ hφ w) S b

theorem natDegree_fibreClassFactor_pos (φ : R →ₐ[F] B) (hφ : φ.toRingHom.Finite)
    (S : Set (PrimeSpectrum B)) (b : B) (w : R →ₐ[F] F) (χ : B →ₐ[F] F)
    (hχ : χ.comp φ = w) (hS : rationalPoint χ ∈ S) :
    0 < (fibreClassFactor φ hφ S b w).natDegree :=
  natDegree_classFactor_pos_of_mem _ S b ((mem_rationalFibreFinset φ hφ w χ).mpr hχ) hS

/-- The root-product factor of any actual rational curve class is nonconstant in every
rational fibre. Existence of a point in that fibre is a conclusion of the line argument. -/
theorem natDegree_fibreCurveClassFactor_pos [IsAlgClosed F] [IsDomain B]
    {σ : Type*} [Fintype σ] (g : MvPolynomial σ F)
    (φ : Localization.Away g →ₐ[F] B) (hφ : φ.toRingHom.Finite)
    (hiφ : Function.Injective φ) (χ : B →ₐ[F] F) (b : B)
    (w : Localization.Away g →ₐ[F] F) :
    0 < (fibreClassFactor φ hφ (curveClass (rationalPoint χ)) b w).natDegree := by
  obtain ⟨ψ, hψ, hbase⟩ := exists_rational_curveChain_in_fibre g φ hφ hiφ χ w
  exact natDegree_fibreClassFactor_pos φ hφ _ b w ψ hbase hψ

/-- If two actual rational points are in different curve classes, the complementary
factor is also nonconstant in every rational fibre. No constant class count is assumed. -/
theorem natDegree_fibreCurveClassFactor_compl_pos [IsAlgClosed F] [IsDomain B]
    {σ : Type*} [Fintype σ] (g : MvPolynomial σ F)
    (φ : Localization.Away g →ₐ[F] B) (hφ : φ.toRingHom.Finite)
    (hiφ : Function.Injective φ) (χ η : B →ₐ[F] F)
    (hη : rationalPoint η ∉ curveClass (rationalPoint χ)) (b : B)
    (w : Localization.Away g →ₐ[F] F) :
    0 < (fibreClassFactor φ hφ (curveClass (rationalPoint χ))ᶜ b w).natDegree := by
  obtain ⟨ψ, hψ, hbase⟩ := exists_rational_curveChain_in_fibre g φ hφ hiφ η w
  apply natDegree_fibreClassFactor_pos φ hφ _ b w ψ hbase
  intro h
  exact hη (h.trans hψ.symm)

end FcCurveFibres
end EnvelopeProperty
