import EnvelopeProperty.AlgGeom.ReesCechDegreeTransitions
import EnvelopeProperty.AlgGeom.ReesCechHomogeneousAction
import EnvelopeProperty.AlgGeom.FormalFunctionsDegreeFinite
import EnvelopeProperty.AlgGeom.FormalFunctionsReesLinear

/-! # Actual stable image filtrations from genuine projective Rees cohomology -/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules
open scoped Polynomial DirectSum
noncomputable section
universe u
namespace EnvelopeProperty.FormalFunctionsImageFiltration

open FcReesCechDegreeComplex FcReesCechDegreeTransitions

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
variable [X.IsSeparated] {ι : Type u} [LinearOrder ι] [Fintype ι]
variable (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))

/-- The SAME original ideal-power cohomology, retaining its actual R-action. -/
abbrev cohomology (d q : ℕ) : ModuleCat R := (degreeComplex I f U hU d).homology q

/-- The actual original higher-to-zero cohomology image is a genuine
I-filtration of the SAME original degree-zero ideal-power cohomology. -/
def imageFiltration (q : ℕ) : I.Filtration (cohomology I f U hU 0 q) where
  N d := LinearMap.range (homologyLower I f U hU (Nat.zero_le d) q).hom
  mono d := by
    rintro x ⟨y, rfl⟩
    refine ⟨(homologyLower I f U hU (Nat.le_succ d) q).hom y, ?_⟩
    exact congrArg (fun b => b.hom y)
      (homologyLower_comp I f U hU (Nat.zero_le d) (Nat.le_succ d) q)
  smul_le d := Submodule.smul_le.mpr (by
    intro a ha x hx
    rcases hx with ⟨y, rfl⟩
    let b : ↥(I ^ 1) := ⟨a, by simpa only [pow_one] using ha⟩
    have h := congrArg (fun c => c.hom y)
      (homologyMultiply_lower I f U hU b (Nat.zero_le d) q)
    have h' : ∃ z : cohomology I f U hU (1 + d) q,
        (homologyLower I f U hU (Nat.zero_le (1 + d)) q).hom z =
          a • (homologyLower I f U hU (Nat.zero_le d) q).hom y :=
      ⟨(FcReesCechHomogeneousMultiplication.homologyMultiply I f U hU b d q).hom y, h⟩
    change ∃ z : cohomology I f U hU (d + 1) q,
      (homologyLower I f U hU (Nat.zero_le (d + 1)) q).hom z =
        a • (homologyLower I f U hU (Nat.zero_le d) q).hom y
    exact (congrArg (fun j : ℕ => ∃ z : cohomology I f U hU j q,
      (homologyLower I f U hU (Nat.zero_le j) q).hom z =
        a • (homologyLower I f U hU (Nat.zero_le d) q).hom y) (Nat.add_comm 1 d)).mp h')

/-- The genuine original image filtration begins at the WHOLE original module. -/
theorem imageFiltration_zero (q : ℕ) : (imageFiltration I f U hU q).N 0 = ⊤ := by
  change LinearMap.range (homologyLower I f U hU (Nat.zero_le 0) q).hom = ⊤
  rw [homologyLower_self]
  exact LinearMap.range_id

/-- The genuine entire original transition map into polynomial cohomology,
putting every original cohomology class in its unchanged actual degree. -/
def polynomialMap (q : ℕ) :
    FcReesCechHomologyModule.degreeHomology I f U hU q →ₗ[R]
      PolynomialModule R (cohomology I f U hU 0 q) :=
  DirectSum.toModule R ℕ (M := fun d => cohomology I f U hU d q) _ fun d =>
    (PolynomialModule.lsingle R d).comp (homologyLower I f U hU (Nat.zero_le d) q).hom

/-- Every original homogeneous cohomology summand is sent to its ENTIRE
original transition image, in exactly its original polynomial degree. -/
theorem polynomialMap_lof (q d : ℕ) (x : cohomology I f U hU d q) :
    polynomialMap I f U hU q
        (DirectSum.lof R ℕ (fun j => cohomology I f U hU j q) d x) =
      PolynomialModule.single R d
        ((homologyLower I f U hU (Nat.zero_le d) q).hom x) := by
  simp only [polynomialMap, DirectSum.toModule_lof]
  rfl

/-- The WHOLE actual original transition polynomial map is genuinely Rees-linear
for the SAME already constructed original projective Rees cohomology action. -/
def polynomialReesMap (q : ℕ) :
    letI := FcReesCechHomologyModule.reesModule I f U hU q
    FcReesCechHomologyModule.degreeHomology I f U hU q →ₗ[reesAlgebra I]
      PolynomialModule R (cohomology I f U hU 0 q) := by
  let := FcReesCechHomologyModule.reesModule I f U hU q
  apply FormalFunctionsReesLinear.linearMapOfMonomialSmul I (polynomialMap I f U hU q)
  intro e a d x
  rw [FcReesCechHomogeneousAction.reesModule_homogeneous,
    polynomialMap_lof, polynomialMap_lof]
  change PolynomialModule.single R (e + d)
      ((homologyLower I f U hU (Nat.zero_le (e + d)) q).hom
        ((FcReesCechHomogeneousMultiplication.homologyMultiply I f U hU a d q).hom x)) =
    Polynomial.monomial e (a : R) • PolynomialModule.single R d
      ((homologyLower I f U hU (Nat.zero_le d) q).hom x)
  rw [PolynomialModule.monomial_smul_single]
  exact congrArg (PolynomialModule.single R (e + d))
    (congrArg (fun b => b.hom x) (homologyMultiply_lower I f U hU a (Nat.zero_le d) q))

/-- EVERY actual original polynomial coefficient is exactly the whole
original cohomology transition image of that SAME actual original degree. -/
theorem polynomialMap_coeff (q : ℕ)
    (x : FcReesCechHomologyModule.degreeHomology I f U hU q) (d : ℕ) :
    (polynomialMap I f U hU q x).coeff d =
      (homologyLower I f U hU (Nat.zero_le d) q).hom (x d) := by
  induction x using DirectSum.induction_on with
  | zero =>
    simp only [map_zero, PolynomialModule.coeff_zero, Finsupp.zero_apply, DirectSum.zero_apply]
  | of e y =>
    change
      (polynomialMap I f U hU q
        (DirectSum.lof R ℕ (fun j => cohomology I f U hU j q) e y)).coeff d = _
    rw [polynomialMap_lof, PolynomialModule.coeff_single]
    by_cases he : e = d
    · subst d
      rw [Finsupp.single_eq_same, DirectSum.of_eq_same]
    · rw [Finsupp.single_apply, if_neg he,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm he), map_zero]
  | add x y hx hy =>
    rw [map_add, PolynomialModule.coeff_add, Finsupp.add_apply,
      DirectSum.add_apply, map_add, hx, hy]

/-- The ENTIRE genuine Rees-linear polynomial transition image is precisely
the actual associated submodule of the SAME original cohomology image filtration. -/
theorem polynomialReesMap_range (q : ℕ) :
    letI := FcReesCechHomologyModule.reesModule I f U hU q
    (polynomialReesMap I f U hU q).range = (imageFiltration I f U hU q).submodule := by
  let := FcReesCechHomologyModule.reesModule I f U hU q
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    intro d
    refine ⟨x d, ?_⟩
    exact (polynomialMap_coeff I f U hU q x d).symm
  · rw [← (imageFiltration I f U hU q).submodule_span_single]
    apply Submodule.span_le.mpr
    rw [Set.iUnion_subset_iff]
    intro d z hz
    rcases hz with ⟨x, hx, rfl⟩
    change x ∈ LinearMap.range (homologyLower I f U hU (Nat.zero_le d) q).hom at hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨DirectSum.lof R ℕ (fun j => cohomology I f U hU j q) d y,
      polynomialMap_lof I f U hU q d y⟩

/-- Original projective coherent cohomology and the genuine finite Rees action
prove stability of the ACTUAL original image filtration, with no stability assumption. -/
theorem imageFiltration_stable [IsNoetherianRing R]
    (hf : IsProjectiveFactorization f) (hcover : IsOpenCover U) (q : ℕ) :
    (imageFiltration I f U hU q).Stable := by
  let := FcReesCechHomologyModule.reesModule I f U hU q
  let : Module.Finite (reesAlgebra I) (FcReesCechHomologyModule.degreeHomology I f U hU q) :=
    FcReesCechHomologyModule.finiteReesHomology I f U hU hf hcover q
  let L := polynomialReesMap I f U hU q
  let : Module.Finite (reesAlgebra I) L.range := Module.Finite.range L
  have hfg : L.range.FG := Module.Finite.iff_fg.mp inferInstance
  let : Module.Finite R (cohomology I f U hU 0 q) :=
    FormalFunctionsDegreeFinite.degreeCech_finite I f hf U hcover hU 0 q
  apply ((imageFiltration I f U hU q).submodule_fg_iff_stable
    (fun d => IsNoetherian.noetherian ((imageFiltration I f U hU q).N d))).mp
  exact (congrArg (fun S : Submodule (reesAlgebra I)
    (PolynomialModule R (cohomology I f U hU 0 q)) => S.FG)
      (polynomialReesMap_range I f U hU q)).mp hfg

end EnvelopeProperty.FormalFunctionsImageFiltration
