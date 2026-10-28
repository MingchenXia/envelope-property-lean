import EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyFlat
import EnvelopeProperty.Vanishing.SpecializationDerivedNatural
import EnvelopeProperty.Vanishing.GeometricCechBaseChange

/-! # Bounded flat cohomology commutes with scalar extension

The homology modules need only be flat over the arithmetic coefficient ring;
they may have arbitrary rank and may be finite only over a separate relative base.
-/

open CategoryTheory CategoryTheory.Limits TensorProduct

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyBaseChange

open RelativeArithmeticCohomologyFlat SpecializationDerivedReplacementStep
  SpecializationDerivedNatural

variable {A : Type u} [CommRing A]

/-- Every differential cokernel in a bounded flat complex with flat homology
is flat. The descending induction uses actual native homology. -/
theorem cokernel_flat (K : CochainComplex (ModuleCat.{u} A) ℕ)
    [∀ n, Module.Flat A (K.X n)] [∀ n, Module.Flat A (K.homology n)]
    (N : ℕ) (hnext : IsZero (K.X (N + 1))) (i : ℕ) (hi : i ≤ N) :
    Module.Flat A (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom) := by
  induction hi using Nat.decreasingInduction with
  | self =>
      let : Subsingleton (K.X (N + 1)) := ModuleCat.subsingleton_of_isZero hnext
      infer_instance
  | @of_succ j hj ih =>
      let S := K.sc' j (j + 1) (j + 2)
      let e := K.homologyIsoSc' j (j + 1) (j + 2)
        (CochainComplex.prev_nat_succ j) (CochainComplex.next ℕ (j + 1))
      let : Module.Flat A S.homology := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
      let : Module.Flat A S.X₃ := inferInstanceAs (Module.Flat A (K.X (j + 2)))
      let : Module.Flat A (S.X₃ ⧸ LinearMap.range S.g.hom) := ih
      let : Module.Flat A S.opcycles := opcycles_flat S
      exact Module.Flat.of_linearEquiv S.moduleCatOpcyclesIso.symm.toLinearEquiv

variable {C : Type u} [CommRing C] [Algebra A C]

/-- A bijective literal kernel comparison gives preservation of that actual
kernel by the original scalar tensor functor. -/
theorem preserves_kernel_of_bijective_comparison {P Q : ModuleCat.{u} A} (f : P ⟶ Q)
    (hb : Function.Bijective (ModularCurves.kerBaseChangeComparison C f.hom)) :
    PreservesLimit (parallelPair f 0)
      (FiniteCechFlatBaseChange.tensorFunctor (R := A) (S := C)) := by
  let F := FiniteCechFlatBaseChange.tensorFunctor (R := A) (S := C)
  let i := ModuleCat.ofHom (LinearMap.ker f.hom).subtype
  have hinj : Function.Injective (F.map i).hom := by
    intro x y hxy
    exact hb.1 (Subtype.ext hxy)
  have hexact : Function.Exact (F.map i).hom (F.map f).hom := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := hb.2 ⟨y, hy⟩
      exact ⟨x, congrArg Subtype.val hx⟩
    · rintro ⟨x, rfl⟩
      exact (ModularCurves.kerBaseChangeComparison C f.hom x).property
  apply preservesLimit_of_preserves_limit_cone (ModuleCat.kernelIsLimit f)
  exact ((ModuleCat.kernelCone f).isLimitMapConeEquiv F).symm
    (ModuleCat.isLimitKernelFork (F.map i) (F.map f) hexact hinj)

/-- Tensoring preserves the kernel of an actual map whose target and cokernel
are flat; the comparison is the literal pure-tensor kernel comparison. -/
theorem preserves_kernel_of_flat_cokernel {P Q : ModuleCat.{u} A} (f : P ⟶ Q)
    [Module.Flat A Q] [Module.Flat A (Q ⧸ LinearMap.range f.hom)] :
    PreservesLimit (parallelPair f 0)
      (FiniteCechFlatBaseChange.tensorFunctor (R := A) (S := C)) :=
  preserves_kernel_of_bijective_comparison f
    (ModularCurves.kerBaseChangeComparison_bijective C f.hom)

/-- The literal scalar tensor functor preserves every cokernel by actual
tensor right exactness, retaining the original coefficient action. -/
theorem preserves_cokernel {P Q : ModuleCat.{u} A} (f : P ⟶ Q) :
    PreservesColimit (parallelPair f 0)
      (FiniteCechFlatBaseChange.tensorFunctor (R := A) (S := C)) := by
  let F := FiniteCechFlatBaseChange.tensorFunctor (R := A) (S := C)
  let q := ModuleCat.ofHom (LinearMap.range f.hom).mkQ
  have hexact : Function.Exact f.hom (LinearMap.range f.hom).mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ]
  have hbase : Function.Exact (F.map f).hom (F.map q).hom :=
    lTensor_exact C hexact (LinearMap.range f.hom).mkQ_surjective
  have hsurj : Function.Surjective (F.map q).hom :=
    LinearMap.baseChange_surjective C (LinearMap.range f.hom).mkQ_surjective
  apply preservesColimit_of_preserves_colimit_cocone (ModuleCat.cokernelIsColimit f)
  exact ((ModuleCat.cokernelCocone f).isColimitMapCoconeEquiv F).symm
    (ModuleCat.isColimitCokernelCofork (F.map f) (F.map q) hbase hsurj)

/-- The actual tensor homology comparison when the outgoing target and
cokernel are flat. No flatness of the scalar algebra is required. -/
def shortHomologyIso (S : ShortComplex (ModuleCat.{u} A))
    [Module.Flat A S.X₃] [Module.Flat A (S.X₃ ⧸ LinearMap.range S.g.hom)] :
    (baseChangeComplex S C).homology ≅ ModuleCat.of C (C ⊗[A] S.homology) := by
  let F := FiniteCechFlatBaseChange.tensorFunctor (R := A) (S := C)
  let : S.homologyData.left.IsPreservedBy F :=
    { g := preserves_kernel_of_flat_cokernel (C := C) S.g
      f' := preserves_cokernel _ }
  let : F.PreservesLeftHomologyOf S := Functor.PreservesLeftHomologyOf.mk' F S.homologyData.left
  exact S.mapHomologyIso F

/-- Positive-degree scalar homology of the same bounded complex is the
scalar extension of its original native homology, with no finite-rank premise. -/
def naturalHomologyIso (K : CochainComplex (ModuleCat.{u} A) ℕ)
    [∀ n, Module.Flat A (K.X n)] [∀ n, Module.Flat A (K.homology n)]
    (N : ℕ) (hnext : IsZero (K.X (N + 1))) (t : ℕ) (ht : 0 < t) (htN : t ≤ N) :
    (baseChangeComplex (naturalSegment K t) C).homology ≅
      ModuleCat.of C (C ⊗[A] K.homology t) := by
  let S := naturalSegment K t
  let : Module.Flat A S.X₃ := inferInstanceAs (Module.Flat A (K.X (t + 1)))
  let : Module.Flat A (S.X₃ ⧸ LinearMap.range S.g.hom) :=
    cokernel_flat K N hnext t htN
  let e := K.homologyIsoSc' (t - 1) t (t + 1)
    (by simpa only [show t - 1 + 1 = t by omega] using
      CochainComplex.prev_nat_succ (t - 1))
    (CochainComplex.next ℕ t)
  exact shortHomologyIso (C := C) S ≪≫
    (FiniteCechFlatBaseChange.tensorFunctor (R := A) (S := C)).mapIso e.symm

end EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyBaseChange
