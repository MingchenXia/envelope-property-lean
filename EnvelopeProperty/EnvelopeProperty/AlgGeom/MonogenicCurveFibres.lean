import EnvelopeProperty.AlgGeom.RationalCurveFibres
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Actual rational fibres of monogenic finite algebras

The actual rational fibre of `R[Z]/(P)` over a whole rational base point is in
bijection with the roots of the specialized polynomial. On the separable locus,
the two actual curve-class root products therefore multiply to that specialized
polynomial. The finite fibre and its identification are constructed here.
-/

open scoped Polynomial Classical
noncomputable section

namespace EnvelopeProperty.FcMonogenicFibres

open FcCurveFibres

variable {F R : Type*} [Field F] [CommRing R] [Algebra F R]

/-- The actual rational homomorphisms of a monogenic fibre are exactly the roots of
its specialized defining polynomial, with the entire base restriction retained. -/
def rationalFibreEquivRoots (P : R[X]) (w : R →ₐ[F] F) :
    {χ : AdjoinRoot P →ₐ[F] F // χ ∈ rationalFibre (AdjoinRoot.ofAlgHom F P) w} ≃
      {z : F // (P.map w.toRingHom).IsRoot z} := by
  let f : {χ : AdjoinRoot P →ₐ[F] F //
      χ ∈ rationalFibre (AdjoinRoot.ofAlgHom F P) w} →
      {z : F // (P.map w.toRingHom).IsRoot z} := fun χ =>
    ⟨χ.1 (AdjoinRoot.root P), by
      have hbase : χ.1.toRingHom.comp (AdjoinRoot.of P) = w.toRingHom :=
        congrArg AlgHom.toRingHom χ.2
      change (P.map w.toRingHom).eval (χ.1 (AdjoinRoot.root P)) = 0
      rw [Polynomial.eval_map, ← hbase]
      change P.eval₂ (χ.1.toRingHom.comp (AdjoinRoot.of P))
        (χ.1.toRingHom (AdjoinRoot.root P)) = 0
      rw [← Polynomial.hom_eval₂ P (AdjoinRoot.of P) χ.1.toRingHom (AdjoinRoot.root P)]
      rw [AdjoinRoot.eval₂_root, map_zero]⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro χ ψ h
    apply Subtype.ext
    exact AdjoinRoot.algHom_ext' (χ.2.trans ψ.2.symm) (congrArg Subtype.val h)
  · intro z
    have hz : P.eval₂ (w : R →+* F) z.1 = 0 := by
      change P.eval₂ w.toRingHom z.1 = 0
      simpa only [Polynomial.IsRoot, Polynomial.eval_map] using z.2
    have hbase : (AdjoinRoot.liftAlgHom P w z.1 hz).comp (AdjoinRoot.ofAlgHom F P) = w := by
      apply AlgHom.ext
      intro r
      exact AdjoinRoot.liftAlgHom_of P w z.1 hz r
    refine ⟨⟨AdjoinRoot.liftAlgHom P w z.1 hz, hbase⟩, ?_⟩
    exact Subtype.ext (AdjoinRoot.liftAlgHom_root P w z.1 hz)

/-- A monic defining polynomial makes the actual monogenic base homomorphism finite. -/
theorem ofAlgHom_finite (P : R[X]) (hP : P.Monic) :
    (AdjoinRoot.ofAlgHom F P).toRingHom.Finite := by
  have : Module.Finite R (AdjoinRoot P) := hP.finite_adjoinRoot
  exact (RingHom.finite_algebraMap (A := R) (B := AdjoinRoot P)).mpr inferInstance

/-- The adjoined root separates the actual rational fibre because both its value and
the whole base homomorphism determine a homomorphism of the polynomial quotient. -/
theorem root_injective_on_rationalFibre (P : R[X]) (w : R →ₐ[F] F) :
    Set.InjOn (fun χ : AdjoinRoot P →ₐ[F] F => χ (AdjoinRoot.root P))
      (rationalFibre (AdjoinRoot.ofAlgHom F P) w) := by
  intro χ hχ ψ hψ he
  exact AdjoinRoot.algHom_ext' (hχ.trans hψ.symm) he

/-- The values of the adjoined root on the actual fibre are precisely all roots of
the specialized polynomial, including the converse construction of a rational point. -/
theorem image_root_rationalFibreFinset (P : R[X]) (hP : P.Monic) (w : R →ₐ[F] F) :
    (rationalFibreFinset (AdjoinRoot.ofAlgHom F P) (ofAlgHom_finite P hP) w).image
      (fun χ => χ (AdjoinRoot.root P)) = (P.map w.toRingHom).roots.toFinset := by
  ext z
  rw [Finset.mem_image, Multiset.mem_toFinset,
    Polynomial.mem_roots ((hP.map w.toRingHom).ne_zero)]
  constructor
  · rintro ⟨χ, hχ, rfl⟩
    exact (rationalFibreEquivRoots P w
      ⟨χ, (mem_rationalFibreFinset _ _ _ _).mp hχ⟩).2
  · intro hz
    obtain ⟨χ, hχ⟩ := (rationalFibreEquivRoots P w).surjective ⟨z, hz⟩
    refine ⟨χ.1, (mem_rationalFibreFinset _ _ _ _).mpr χ.2, ?_⟩
    exact congrArg Subtype.val hχ

/-- On the separable locus the whole specialized polynomial is the root product over
the actual rational fibre, with each rational point occurring exactly once. -/
theorem prod_rationalFibre_eq_map [IsAlgClosed F] (P : R[X]) (hP : P.Monic)
    (w : R →ₐ[F] F) (hsep : (P.map w.toRingHom).Separable) :
    (∏ χ ∈ rationalFibreFinset (AdjoinRoot.ofAlgHom F P) (ofAlgHom_finite P hP) w,
      (Polynomial.X - Polynomial.C (χ (AdjoinRoot.root P)))) = P.map w.toRingHom := by
  have hinj : Set.InjOn (fun χ : AdjoinRoot P →ₐ[F] F => χ (AdjoinRoot.root P))
      (↑(rationalFibreFinset (AdjoinRoot.ofAlgHom F P) (ofAlgHom_finite P hP) w)) := by
    intro χ hχ ψ hψ he
    exact root_injective_on_rationalFibre P w
      ((mem_rationalFibreFinset _ _ _ _).mp hχ)
      ((mem_rationalFibreFinset _ _ _ _).mp hψ) he
  rw [← Finset.prod_image (f := fun z : F => Polynomial.X - Polynomial.C z) hinj,
    image_root_rationalFibreFinset P hP w]
  have hv : (P.map w.toRingHom).roots.toFinset.val = (P.map w.toRingHom).roots := by
    rw [Multiset.toFinset_val, (Polynomial.nodup_roots hsep).dedup]
  change ((P.map w.toRingHom).roots.toFinset.val.map
    (fun z => Polynomial.X - Polynomial.C z)).prod = _
  rw [hv]
  exact Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hP.map _)
    IsAlgClosed.card_roots_eq_natDegree

/-- The two actual complementary curve-class factors recover the specialized defining
polynomial. This identifies the constructed factors without a fibre factorization input. -/
theorem fibreClassFactor_mul_compl_eq_map [IsAlgClosed F]
    (P : R[X]) (hP : P.Monic) (S : Set (PrimeSpectrum (AdjoinRoot P)))
    (w : R →ₐ[F] F) (hsep : (P.map w.toRingHom).Separable) :
    fibreClassFactor (AdjoinRoot.ofAlgHom F P) (ofAlgHom_finite P hP) S
        (AdjoinRoot.root P) w *
      fibreClassFactor (AdjoinRoot.ofAlgHom F P) (ofAlgHom_finite P hP) Sᶜ
        (AdjoinRoot.root P) w = P.map w.toRingHom := by
  change classFactor _ S _ * classFactor _ Sᶜ _ = _
  rw [classFactor_mul_compl]
  exact prod_rationalFibre_eq_map P hP w hsep

/-- In a monogenic fibre on the separable locus, the actual selected root product is
a genuine divisor of the specialized defining polynomial. -/
theorem fibreClassFactor_dvd_map [IsAlgClosed F]
    (P : R[X]) (hP : P.Monic) (S : Set (PrimeSpectrum (AdjoinRoot P)))
    (w : R →ₐ[F] F) (hsep : (P.map w.toRingHom).Separable) :
    fibreClassFactor (AdjoinRoot.ofAlgHom F P) (ofAlgHom_finite P hP) S
      (AdjoinRoot.root P) w ∣ P.map w.toRingHom :=
  ⟨_, (fibreClassFactor_mul_compl_eq_map P hP S w hsep).symm⟩

end EnvelopeProperty.FcMonogenicFibres
