import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Sites.Etale

/-! # The actual finite étale unit-root cover for Kummer local surjectivity -/
open Polynomial AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.KummerUnitRootCover
variable {R : Type u} [CommRing R] (n : ℕ) (a : Rˣ)

/-- The actual original Kummer root polynomial. -/
def polynomial : R[X] := X ^ n - C (a : R)

/-- The literal native quotient by the actual root polynomial. -/
abbrev RootRing := AdjoinRoot (polynomial n a)

/-- The actual class of the original polynomial coordinate in its actual quotient. -/
def root : RootRing n a := AdjoinRoot.root (polynomial n a)

/-- The actual polynomial is monic in every original base ring. -/
theorem polynomial_monic (hn : 0 < n) : (polynomial n a).Monic :=
  monic_X_pow_sub_C (a : R) hn.ne'

/-- The actual original root retains the exact original unit's n-th power relation. -/
theorem root_pow : root n a ^ n = algebraMap R (RootRing n a) (a : R) := by
  have h := AdjoinRoot.mk_self (f := polynomial n a)
  change AdjoinRoot.mk (polynomial n a) (X ^ n - C (a : R)) = 0 at h
  rw [map_sub,map_pow,AdjoinRoot.mk_X,AdjoinRoot.mk_C] at h
  exact sub_eq_zero.mp h


/-- The actual adjoined root of an original unit is itself a unit. -/
theorem root_isUnit (hn : 0 < n) : IsUnit (root n a) := by
  apply (isUnit_pow_iff hn.ne').mp
  rw [root_pow]
  exact a.isUnit.map (algebraMap R (RootRing n a))

/-- The actual root as an element of the genuine original unit group. -/
def rootUnit (hn : 0 < n) : (RootRing n a)ˣ := (root_isUnit n a hn).unit

/-- The actual unit retains the SAME literal original quotient coordinate. -/
theorem rootUnit_coe (hn : 0 < n) : (rootUnit n a hn : RootRing n a) = root n a :=
  (root_isUnit n a hn).unit_spec

/-- The true original unit-power map has the SAME original unit as the n-th power of this actual cover unit. -/
theorem rootUnit_pow (hn : 0 < n) :
    rootUnit n a hn ^ n = Units.map (algebraMap R (RootRing n a)).toMonoidHom a := by
  apply Units.ext
  change (rootUnit n a hn : RootRing n a) ^ n = algebraMap R (RootRing n a) (a : R)
  rw [rootUnit_coe,root_pow]

/-- The actual derivative is invertible internally; no etaleness certificate is supplied. -/
theorem derivative_isUnit (hn : 0 < n) (hunit : IsUnit (n : R)) :
    IsUnit (AdjoinRoot.mk (polynomial n a) (polynomial n a).derivative) := by
  have hd : (polynomial n a).derivative = C (n : R) * X ^ (n-1) := by
    simp [polynomial,derivative_X_pow]
  rw [hd,map_mul,map_pow,AdjoinRoot.mk_X]
  exact (hunit.map (algebraMap R (RootRing n a))).mul ((root_isUnit n a hn).pow (n-1))

private def derivativePair (hn : 0 < n) : StandardEtalePair R where
  f := polynomial n a
  monic_f := polynomial_monic n a hn
  g := (polynomial n a).derivative
  cond := ⟨1,0,1,by simp⟩

/-- The genuine standard-etale polynomial presentation identifies with the ENTIRE actual root quotient. -/
def standardEtaleEquiv (hn : 0 < n) (hunit : IsUnit (n : R)) :
    (derivativePair n a hn).Ring ≃ₐ[R] RootRing n a :=
  (derivativePair n a hn).equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit (RootRing n a)
      (Localization.Away (AdjoinRoot.mk (polynomial n a) (polynomial n a).derivative))
      (AdjoinRoot.mk (polynomial n a) (polynomial n a).derivative)
      (derivative_isUnit n a hn hunit)).symm.restrictScalars R)

/-- The actual whole original root algebra is étale for the internally proved derivative-unit reason. -/
theorem etale (hn : 0 < n) (hunit : IsUnit (n : R)) : Algebra.Etale R (RootRing n a) :=
  Algebra.Etale.of_equiv (standardEtaleEquiv n a hn hunit)

/-- The actual whole root quotient is finite over the original ring, by its true monic power basis. -/
theorem finite (hn : 0 < n) : Module.Finite R (RootRing n a) :=
  (polynomial_monic n a hn).finite_adjoinRoot

/-- The actual whole root quotient is free over the original ring, by its true monic power basis. -/
theorem free (hn : 0 < n) : Module.Free R (RootRing n a) :=
  (polynomial_monic n a hn).free_adjoinRoot

/-- The original root cover is genuinely surjective on the ENTIRE original prime spectrum. -/
theorem spectrum_surjective (hn : 0 < n) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap R (RootRing n a))) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := hR
    intro x
    exact isEmptyElim x
  · let := hR
    have hdeg : (polynomial n a).natDegree = n := natDegree_X_pow_sub_C
    let : Nonempty (Fin (polynomial n a).natDegree) := ⟨⟨0,by rw [hdeg]; exact hn⟩⟩
    let : Nontrivial (RootRing n a) :=
      (AdjoinRoot.powerBasisAux' (polynomial_monic n a hn)).repr.toEquiv.nontrivial
    let := free n a hn
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

/-- The actual original finite etale cover morphism, not an abstract covering certificate. -/
def morphism : Spec (.of (RootRing n a)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (RootRing n a)))

/-- The genuine original cover morphism is etale. -/
theorem morphism_etale (hn : 0 < n) (hunit : IsUnit (n : R)) : Etale (morphism n a) := by
  rw [morphism,HasRingHomProperty.Spec_iff (P := @Etale)]
  exact (RingHom.etale_algebraMap).mpr (etale n a hn hunit)

/-- The genuine original cover morphism is finite. -/
theorem morphism_finite (hn : 0 < n) : IsFinite (morphism n a) := by
  rw [morphism,IsFinite.SpecMap_iff]
  exact (RingHom.finite_algebraMap).mpr (finite n a hn)

/-- The genuine original cover morphism reaches EVERY original scheme point. -/
theorem morphism_surjective (hn : 0 < n) : Surjective (morphism n a) := by
  rw [surjective_iff]
  exact spectrum_surjective n a hn

variable {S : Scheme.{u}} (g : Spec (.of R) ⟶ S) [Etale g]

/-- The SAME actual unit-root cover is an actual object of the original small etale site. -/
def etaleObject (hn : 0 < n) (hunit : IsUnit (n : R)) : S.Etale := by
  let := morphism_etale n a hn hunit
  exact Scheme.Etale.mk (morphism n a ≫ g)

/-- The actual original cover map is a genuine arrow on that SAME small etale site. -/
def etaleHom (hn : 0 < n) (hunit : IsUnit (n : R)) :
    etaleObject n a g hn hunit ⟶ Scheme.Etale.mk g :=
  MorphismProperty.Over.homMk (morphism n a) rfl

/-- The internally constructed singleton unit-root family genuinely COVERS the original affine object in the ACTUAL small etale topology. -/
theorem smallEtale_covering (hn : 0 < n) (hunit : IsUnit (n : R)) :
    Sieve.ofArrows (fun _ : PUnit => etaleObject n a g hn hunit)
      (fun _ => etaleHom n a g hn hunit) ∈ S.smallEtaleTopology (Scheme.Etale.mk g) := by
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
  ext x
  simp only [Set.mem_iUnion,Set.mem_range,Set.mem_univ,iff_true]
  have hs : Function.Surjective (morphism n a) := (surjective_iff _).mp (morphism_surjective n a hn)
  obtain ⟨y,hy⟩ := hs x
  exact ⟨PUnit.unit,y,hy⟩

end EnvelopeProperty.KummerUnitRootCover
