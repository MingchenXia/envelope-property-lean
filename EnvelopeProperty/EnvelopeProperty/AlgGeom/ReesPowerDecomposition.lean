import EnvelopeProperty.AlgGeom.ReesFormalChartSheaf
import Mathlib.Algebra.DirectSum.Module

/-!
# Actual ideal-power decomposition of Rees chart sections

The actual Rees ring decomposes into the direct sum of its actual ideal
powers by its genuine polynomial coefficients. This is the coefficient
comparison used to construct the graded Čech comparison.
-/

open CategoryTheory AlgebraicGeometry
open scoped Polynomial DirectSum
noncomputable section
universe u

namespace EnvelopeProperty.FcReesPowerDecomposition

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The genuine coefficients of an actual Rees polynomial, with their actual
ideal-power membership and finite original polynomial support. -/
def coefficients (p : reesAlgebra I) : ⨁ n : ℕ, ↥(I ^ n) :=
  DFinsupp.mk (p : R[X]).support fun n => ⟨(p : R[X]).coeff n, p.2 n⟩

/-- Every actual coefficient is retained exactly in its original degree. -/
theorem coefficients_apply (p : reesAlgebra I) (n : ℕ) :
    coefficients I p n = ⟨(p : R[X]).coeff n, p.2 n⟩ := by
  classical
  apply Subtype.ext
  dsimp only [coefficients]
  rw [DFinsupp.mk_apply]
  split_ifs with hn
  · rfl
  · exact (Polynomial.notMem_support_iff.mp hn).symm

/-- The genuine coefficient map is linear on all actual Rees sections. -/
def coefficientLinear : reesAlgebra I →ₗ[R] ⨁ n : ℕ, ↥(I ^ n) where
  toFun := coefficients I
  map_add' p q := by
    ext n
    simp only [coefficients_apply, DirectSum.add_apply]
    exact Polynomial.coeff_add (p : R[X]) (q : R[X]) n
  map_smul' r p := by
    ext n
    simp only [coefficients_apply, DirectSum.smul_apply]
    exact Polynomial.coeff_smul r (p : R[X]) n

/-- The genuine Rees coefficient map is injective on all sections. -/
theorem coefficientLinear_injective : Function.Injective (coefficientLinear I) := by
  intro p q h
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  have hn := congrArg (fun x : ⨁ n : ℕ, ↥(I ^ n) => (x n : R)) h
  change (coefficients I p n : R) = (coefficients I q n : R) at hn
  simpa only [coefficients_apply] using hn

/-- A genuine homogeneous monomial is exactly the direct-sum inclusion of
its actual original ideal-power coefficient. -/
theorem coefficients_monomial (n : ℕ) (a : ↥(I ^ n)) :
    coefficients I (⟨Polynomial.monomial n (a : R),
      reesAlgebra.monomial_mem.mpr a.2⟩ : reesAlgebra I) =
        DirectSum.lof R ℕ (fun n => ↥(I ^ n)) n a := by
  ext j
  rw [coefficients_apply]
  change (Polynomial.monomial n (a : R)).coeff j =
    (DirectSum.lof R ℕ (fun n => ↥(I ^ n)) n a j : R)
  rw [DirectSum.lof_eq_of]
  by_cases hj : j = n
  · subst j
    rw [DirectSum.of_eq_same]
    simp only [Polynomial.coeff_monomial, ↓reduceIte]
  · rw [DirectSum.of_eq_of_ne (β := fun n => ↥(I ^ n)) n j a hj]
    simp only [Polynomial.coeff_monomial, if_neg (Ne.symm hj)]
    rfl

/-- Every finite family of actual ideal-power coefficients is realized by
an actual Rees polynomial, without any completion or finiteness hypothesis. -/
theorem coefficientLinear_surjective : Function.Surjective (coefficientLinear I) := by
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, (coefficientLinear I).map_zero⟩
  | of n a =>
    exact ⟨⟨Polynomial.monomial n (a : R), reesAlgebra.monomial_mem.mpr a.2⟩,
      coefficients_monomial I n a⟩
  | add x y hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p + q, (coefficientLinear I).map_add p q⟩

/-- The actual Rees ring is linearly the direct sum of its actual ideal
powers, through genuine original polynomial coefficients. -/
def powerEquiv : reesAlgebra I ≃ₗ[R] ⨁ n : ℕ, ↥(I ^ n) :=
  LinearEquiv.ofBijective (coefficientLinear I)
    ⟨coefficientLinear_injective I, coefficientLinear_surjective I⟩

section FiniteProduct

variable (A : Type u) [CommRing A] (J : Type u) [Fintype J]
variable (M : J → ℕ → Type u) [∀ j n, AddCommGroup (M j n)] [∀ j n, Module A (M j n)]

/-- A finite product of actual degree decompositions is the direct sum of
its finite products of actual degree pieces. -/
def finitePiDirectSumEquiv :
    (∀ j : J, ⨁ n : ℕ, M j n) ≃ₗ[A] ⨁ n : ℕ, (∀ j : J, M j n) := by
  classical
  let e : (Σ j : J, ℕ) ≃ (Σ n : ℕ, J) :=
    ⟨fun p => ⟨p.2, p.1⟩, fun p => ⟨p.2, p.1⟩, fun _ => rfl, fun _ => rfl⟩
  let s : (⨁ p : (Σ j : J, ℕ), M p.1 p.2) ≃ₗ[A]
      (⨁ p : (Σ n : ℕ, J), M p.2 p.1) := DFinsupp.domLCongr e
  exact (DirectSum.linearEquivFunOnFintype A J (fun j => ⨁ n : ℕ, M j n)).symm ≪≫ₗ
    (DirectSum.sigmaLcurryEquiv (δ := fun (j : J) (n : ℕ) => M j n) A).symm ≪≫ₗ
    s ≪≫ₗ
    (DirectSum.sigmaLcurryEquiv (δ := fun (n : ℕ) (j : J) => M j n) A) ≪≫ₗ
    (DFinsupp.mapRange.linearEquiv fun n =>
      DirectSum.linearEquivFunOnFintype A J (fun j => M j n))

/-- The finite product/direct-sum comparison retains every original
coefficient at its exact original index and degree. -/
theorem finitePiDirectSumEquiv_apply (x : ∀ j : J, ⨁ n : ℕ, M j n) (n : ℕ) (j : J) :
    finitePiDirectSumEquiv A J M x n j = x j n := by
  rfl

end FiniteProduct

section ReesProduct

variable (A : Type u) [CommRing A] (J : Type u) [Fintype J]
variable (S : J → Type u) [∀ j, CommRing (S j)] [∀ j, Algebra A (S j)]
variable (K : ∀ j, Ideal (S j))

/-- Every finite product of actual Rees chart rings decomposes linearly
over the original base into its finite products of actual ideal powers. -/
def finiteReesPowerEquiv :
    (∀ j : J, reesAlgebra (K j)) ≃ₗ[A]
      ⨁ n : ℕ, (∀ j : J, ↥(K j ^ n)) :=
  (LinearEquiv.piCongrRight fun j => (powerEquiv (K j)).restrictScalars A) ≪≫ₗ
    finitePiDirectSumEquiv A J (fun j n => ↥(K j ^ n))

/-- The finite Rees decomposition retains every actual original coefficient
in every actual chart and original degree. -/
theorem finiteReesPowerEquiv_apply (p : ∀ j : J, reesAlgebra (K j)) (n : ℕ) (j : J) :
    finiteReesPowerEquiv A J S K p n j = ⟨(p j : (S j)[X]).coeff n, (p j).2 n⟩ := by
  rw [finiteReesPowerEquiv, LinearEquiv.trans_apply, finitePiDirectSumEquiv_apply]
  exact coefficients_apply (K j) (p j) n

end ReesProduct

section ChartRestriction

open FcReesFormalRestriction FcReesFormalChartSheaf

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
variable {U V : X.Opens} (hUV : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V)

/-- Actual coefficientwise chart Rees restriction is an algebra homomorphism
over the SAME original coefficient ring, with its derived chart structures. -/
def chartReesRestriction :
    letI := chartAlgebra f hU
    letI := chartAlgebra f hV
    reesAlgebra (I.map (chartCoefficient f hV)) →ₐ[R]
      reesAlgebra (I.map (chartCoefficient f hU)) := by
  letI := chartAlgebra f hU
  letI := chartAlgebra f hV
  refine { toRingHom := reesRestriction I f hUV hU hV, commutes' := ?_ }
  intro r
  apply Subtype.ext
  change Polynomial.map (X.presheaf.map (homOfLE hUV).op).hom
      (Polynomial.C (chartCoefficient f hV r)) = Polynomial.C (chartCoefficient f hU r)
  rw [Polynomial.map_C]
  exact congrArg Polynomial.C
    (DFunLike.congr_fun (chartCoefficient_naturality f hUV hU hV) r)

/-- The actual original sheaf restriction on each ideal-power degree,
linear over the original coefficient ring. -/
def chartPowerRestriction (n : ℕ) :
    letI := chartAlgebra f hU
    letI := chartAlgebra f hV
    ↥((I.map (chartCoefficient f hV)) ^ n) →ₗ[R]
      ↥((I.map (chartCoefficient f hU)) ^ n) := by
  letI := chartAlgebra f hU
  letI := chartAlgebra f hV
  let ρ := (X.presheaf.map (homOfLE hUV).op).hom
  refine { toFun := fun a => ⟨ρ a, ?_⟩, map_add' := ?_, map_smul' := ?_ }
  · have ha := Ideal.mem_map_of_mem ρ a.2
    rw [Ideal.map_pow, Ideal.map_map, chartCoefficient_naturality f hUV hU hV] at ha
    exact ha
  · intro a b
    exact Subtype.ext (map_add ρ (a : Γ(X, V)) (b : Γ(X, V)))
  · intro r a
    apply Subtype.ext
    change ρ (chartCoefficient f hV r * (a : Γ(X, V))) =
      chartCoefficient f hU r * ρ (a : Γ(X, V))
    rw [map_mul]
    exact congrArg (fun b => b * ρ (a : Γ(X, V)))
      (DFunLike.congr_fun (chartCoefficient_naturality f hUV hU hV) r)

/-- Actual original chart Rees restriction becomes the direct sum of the
actual original ideal-power restrictions under the genuine decompositions. -/
theorem chartPowerEquiv_naturality :
    letI := chartAlgebra f hU
    letI := chartAlgebra f hV
    ((powerEquiv (I.map (chartCoefficient f hU))).restrictScalars R).toLinearMap.comp
        (chartReesRestriction I f hUV hU hV).toLinearMap =
      (DirectSum.lmap (fun n => chartPowerRestriction I f hUV hU hV n)).comp
        ((powerEquiv (I.map (chartCoefficient f hV))).restrictScalars R).toLinearMap := by
  let := chartAlgebra f hU
  let := chartAlgebra f hV
  apply LinearMap.ext
  intro p
  apply DirectSum.ext
  intro n
  change powerEquiv (I.map (chartCoefficient f hU))
      (chartReesRestriction I f hUV hU hV p) n =
    (DirectSum.lmap (fun n => chartPowerRestriction I f hUV hU hV n))
      (powerEquiv (I.map (chartCoefficient f hV)) p) n
  rw [DirectSum.lmap_apply]
  apply Subtype.ext
  change (coefficients (I.map (chartCoefficient f hU))
      (reesRestriction I f hUV hU hV p) n : Γ(X, U)) =
    (X.presheaf.map (homOfLE hUV).op).hom
      (coefficients (I.map (chartCoefficient f hV)) p n : Γ(X, V))
  rw [coefficients_apply, coefficients_apply]
  exact reesRestriction_coeff I f hUV hU hV p n

end ChartRestriction

end EnvelopeProperty.FcReesPowerDecomposition
