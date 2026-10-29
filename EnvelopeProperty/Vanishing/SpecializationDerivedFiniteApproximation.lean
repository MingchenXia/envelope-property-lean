import EnvelopeProperty.Vanishing.SpecializationDerivedAdjacent
import EnvelopeProperty.Vanishing.SpecializationDerivedUpper
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Finite free triples computing actual nonnegative chain homology

The recursive frontier is constructed from the actual original flat chain
complex and its independently finite native homology. It is never supplied
as a cohomology or finite-free model hypothesis.
-/

open CategoryTheory CategoryTheory.Limits TensorProduct

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.SpecializationDerivedFiniteApproximation

open SpecializationDerivedReplacementStep

variable {R : Type u} [CommRing R]

/-- The original consecutive three terms, with indices reduced explicitly. -/
def segment (C : ChainComplex (ModuleCat.{u} R) ℕ) : ℕ → ShortComplex (ModuleCat.{u} R)
  | 0 => C.sc' 1 0 0
  | n + 1 => C.sc' (n + 2) (n + 1) n

/-- The explicit original three terms have exactly the native chain homology. -/
def segmentIso (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    C.sc n ≅ segment C n := by
  cases n with
  | zero => exact C.isoSc' 1 0 0 (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero
  | succ n =>
    exact C.isoSc' (n + 2) (n + 1) n
      (ChainComplex.prev ℕ (n + 1)) (ChainComplex.next_nat_succ n)

/-- Self scalar extension is identified with the actual original short complex. -/
def selfBaseChangeIso (S : ShortComplex (ModuleCat.{u} R)) :
    baseChangeComplex S R ≅ S :=
  ShortComplex.isoMk (TensorProduct.lid R S.X₁).toModuleIso
    (TensorProduct.lid R S.X₂).toModuleIso
    (TensorProduct.lid R S.X₃).toModuleIso
    (by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro r
      apply LinearMap.ext
      intro x
      change S.f.hom ((TensorProduct.lid R S.X₁) (r ⊗ₜ[R] x)) =
        (TensorProduct.lid R S.X₂) (S.f.hom.baseChange R (r ⊗ₜ[R] x))
      simp only [TensorProduct.lid_tmul, LinearMap.baseChange_tmul, map_smul])
    (by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro r
      apply LinearMap.ext
      intro x
      change S.g.hom ((TensorProduct.lid R S.X₂) (r ⊗ₜ[R] x)) =
        (TensorProduct.lid R S.X₃) (S.g.hom.baseChange R (r ⊗ₜ[R] x))
      simp only [TensorProduct.lid_tmul, LinearMap.baseChange_tmul, map_smul])

/-- The actual first frontier has the original middle module and a zero finite
free outgoing term. -/
def initialSegment (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (C.d 1 0) (0 : C.X 0 ⟶ ModuleCat.of R (Fin 0 → R)) (by simp)

/-- The initial comparison fixes both original incoming terms. -/
def initialComparison (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    initialSegment C ⟶ segment C 0 where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 0
  comm₁₂ := by
    change 𝟙 (C.X 1) ≫ C.d 1 0 = C.d 1 0 ≫ 𝟙 (C.X 0)
    rw [Category.id_comp, Category.comp_id]
  comm₂₃ := by
    have hz : C.d 0 0 = 0 := C.shape 0 0 (by change ¬ 0 + 1 = 0; omega)
    change 𝟙 (C.X 0) ≫ C.d 0 0 = (0 : _ ⟶ _) ≫ 0
    rw [hz, comp_zero, zero_comp]

/-- The zero outgoing finite term retains actual first homology under every
algebra base change. -/
def initialBaseChangeHomologyIso (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (T : Type u) [CommRing T] [Algebra R T] :
    (baseChangeComplex (initialSegment C) T).homology ≅
      (baseChangeComplex (segment C 0) T).homology := by
  let φ := baseChangeComparison (initialComparison C) T
  have hc : IsIso (ShortComplex.cyclesMap φ) := by
    apply cyclesMap_isIso_of_relations
    · intro x y _ _ hxy
      change (LinearMap.id : C.X 0 →ₗ[R] C.X 0).baseChange T x =
        (LinearMap.id : C.X 0 →ₗ[R] C.X 0).baseChange T y at hxy
      rw [LinearMap.baseChange_id] at hxy
      exact hxy
    · intro y _
      refine ⟨y, ?_, ?_⟩
      · change (0 : C.X 0 →ₗ[R] (Fin 0 → R)).baseChange T y = 0
        rw [LinearMap.baseChange_zero]
        rfl
      · change (LinearMap.id : C.X 0 →ₗ[R] C.X 0).baseChange T y = y
        rw [LinearMap.baseChange_id]
        rfl
  let := hc
  have hfirst : φ.τ₁ = 𝟙 _ := by
    apply ModuleCat.hom_ext
    change (LinearMap.id : C.X 1 →ₗ[R] C.X 1).baseChange T = LinearMap.id
    exact LinearMap.baseChange_id
  let : Epi φ.τ₁ := by
    rw [hfirst]
    change Epi (𝟙 (ModuleCat.of T (T ⊗[R] C.X 1)))
    infer_instance
  let : IsIso (ShortComplex.homologyMap φ) :=
    ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi inferInstance inferInstance
  exact asIso (ShortComplex.homologyMap φ)

/-- Internal recursive frontier data. Public producers below construct this
from the original complex; no frontier is an external theorem hypothesis. -/
structure Frontier (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) where
  middle : ModuleCat.{u} R
  rank : ℕ
  incoming : C.X (n + 1) ⟶ middle
  outgoing : middle ⟶ ModuleCat.of R (Fin rank → R)
  zero : incoming ≫ outgoing = 0
  flat_middle : Module.Flat R middle
  rho : middle ⟶ C.X n
  incoming_rho : incoming ≫ rho = C.d (n + 1) n
  before_zero : C.d (n + 2) (n + 1) ≫ incoming = 0
  kernel_baseChange : ∀ (T : Type u) [CommRing T] [Algebra R T]
    (x : T ⊗[R] C.X (n + 1)),
    incoming.hom.baseChange T x = 0 ↔ (C.d (n + 1) n).hom.baseChange T x = 0
  homology_baseChange : ∀ (T : Type u) [CommRing T] [Algebra R T],
    (baseChangeComplex (ShortComplex.mk incoming outgoing zero) T).homology ≅
      (baseChangeComplex (segment C n) T).homology

namespace Frontier

variable {C : ChainComplex (ModuleCat.{u} R) ℕ} {n : ℕ}

/-- The actual three modules of an internal frontier. -/
def toShortComplex (F : Frontier C n) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk F.incoming F.outgoing F.zero

/-- The frontier's finite homology is derived from the actual original finite
native chain homology and the constructed comparison. -/
theorem homology_finite (F : Frontier C n) [Module.Finite R (C.homology n)] :
    Module.Finite R (F.toShortComplex.homology) := by
  let eC : C.homology n ≅ (segment C n).homology :=
    ShortComplex.homologyMapIso (segmentIso C n)
  let : Module.Finite R (segment C n).homology := Module.Finite.equiv eC.toLinearEquiv
  let e : F.toShortComplex.homology ≅ (segment C n).homology :=
    (ShortComplex.homologyMapIso (selfBaseChangeIso F.toShortComplex)).symm ≪≫
      F.homology_baseChange R ≪≫
        ShortComplex.homologyMapIso (selfBaseChangeIso (segment C n))
  exact Module.Finite.equiv e.symm.toLinearEquiv

end Frontier

namespace Frontier

variable {C : ChainComplex (ModuleCat.{u} R) ℕ} {n : ℕ}

/-- The original next two modules and incoming map, with the current lifted
outgoing differential. -/
def lowerInput (F : Frontier C n) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (C.d (n + 2) (n + 1)) F.incoming F.before_zero

/-- Its comparison with the original next-degree segment fixes both original
lower terms and uses the actually constructed predecessor projection. -/
def lowerInputComparison (F : Frontier C n) : F.lowerInput ⟶ segment C (n + 1) where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := F.rho
  comm₁₂ := by
    change 𝟙 _ ≫ C.d (n + 2) (n + 1) = C.d (n + 2) (n + 1) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  comm₂₃ := by
    change 𝟙 _ ≫ C.d (n + 1) n = F.incoming ≫ F.rho
    rw [Category.id_comp, F.incoming_rho]

/-- The frontier's actual incoming-kernel invariant constructs the next
original homology comparison after every algebra base change. -/
def lowerInputBaseChangeHomologyIso (F : Frontier C n)
    (T : Type u) [CommRing T] [Algebra R T] :
    (baseChangeComplex F.lowerInput T).homology ≅
      (baseChangeComplex (segment C (n + 1)) T).homology := by
  let φ := baseChangeComparison F.lowerInputComparison T
  have hc : IsIso (ShortComplex.cyclesMap φ) := by
    apply cyclesMap_isIso_of_relations
    · intro x y _ _ hxy
      change (LinearMap.id : C.X (n + 1) →ₗ[R] C.X (n + 1)).baseChange T x =
        (LinearMap.id : C.X (n + 1) →ₗ[R] C.X (n + 1)).baseChange T y at hxy
      rw [LinearMap.baseChange_id] at hxy
      exact hxy
    · intro y hy
      refine ⟨y, (F.kernel_baseChange T y).mpr hy, ?_⟩
      change (LinearMap.id : C.X (n + 1) →ₗ[R] C.X (n + 1)).baseChange T y = y
      rw [LinearMap.baseChange_id]
      rfl
  let := hc
  have hfirst : φ.τ₁ = 𝟙 _ := by
    apply ModuleCat.hom_ext
    change (LinearMap.id : C.X (n + 2) →ₗ[R] C.X (n + 2)).baseChange T = LinearMap.id
    exact LinearMap.baseChange_id
  let : Epi φ.τ₁ := by
    rw [hfirst]
    change Epi (𝟙 (ModuleCat.of T (T ⊗[R] C.X (n + 2))))
    infer_instance
  let : IsIso (ShortComplex.homologyMap φ) :=
    ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi inferInstance inferInstance
  exact asIso (ShortComplex.homologyMap φ)

end Frontier

/-- The first internal frontier is produced directly from the original complex. -/
def initialFrontier (C : ChainComplex (ModuleCat.{u} R) ℕ)
    [Module.Flat R (C.X 0)] : Frontier C 0 where
  middle := C.X 0
  rank := 0
  incoming := C.d 1 0
  outgoing := 0
  zero := by simp
  flat_middle := inferInstance
  rho := 𝟙 _
  incoming_rho := by simp
  before_zero := C.d_comp_d 2 1 0
  kernel_baseChange := fun _ _ _ _ => Iff.rfl
  homology_baseChange := initialBaseChangeHomologyIso C

variable [IsNoetherianRing R]

/-- One recursive frontier is actually constructed from the preceding one and
the original next module, using the proved finite-free replacement producer. -/
def nextFrontier {C : ChainComplex (ModuleCat.{u} R) ℕ} {n : ℕ}
    (F : Frontier C n) [Module.Finite R (C.homology n)]
    [Module.Flat R (C.X (n + 1))] : Frontier C (n + 1) := by
  let S := F.toShortComplex
  let : Module.Finite R S.homology := F.homology_finite
  let : Module.Finite R S.X₃ := by
    change Module.Finite R (Fin F.rank → R)
    infer_instance
  let : Module.Flat R S.X₁ := inferInstanceAs (Module.Flat R (C.X (n + 1)))
  let : Module.Flat R S.X₂ := F.flat_middle
  let h := (C.d (n + 2) (n + 1)).hom
  have hh : S.f.hom ∘ₗ h = 0 := ModuleCat.hom_ext_iff.mp F.before_zero
  refine {
    middle := ModuleCat.of R (PullbackTerm S)
    rank := (liftData S).1
    incoming := ModuleCat.ofHom (lowerDifferential S h hh)
    outgoing := ModuleCat.ofHom (differential S)
    zero := ?_
    flat_middle := pullback_flat S
    rho := ModuleCat.ofHom (predecessor S)
    incoming_rho := ?_
    before_zero := ?_
    kernel_baseChange := ?_
    homology_baseChange := ?_ }
  · apply ModuleCat.hom_ext
    ext x
    rfl
  · apply ModuleCat.hom_ext
    rfl
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · exact ConcreteCategory.congr_hom (C.d_comp_d (n + 3) (n + 2) (n + 1)) x
    · rfl
  · intro T _ _ x
    change (lowerDifferential S h hh).baseChange T x = 0 ↔ h.baseChange T x = 0
    have hp : (predecessor S).baseChange T ∘ₗ
        (lowerDifferential S h hh).baseChange T = h.baseChange T := by
      rw [← LinearMap.baseChange_comp]
      rfl
    have hd : (differential S).baseChange T ∘ₗ
        (lowerDifferential S h hh).baseChange T = 0 := by
      rw [← LinearMap.baseChange_comp]
      have hz : differential S ∘ₗ lowerDifferential S h hh = 0 := by ext z; rfl
      rw [hz, LinearMap.baseChange_zero]
    constructor
    · intro hx
      exact (LinearMap.congr_fun hp x).symm.trans
        ((congrArg ((predecessor S).baseChange T) hx).trans (map_zero _))
    · intro hx
      apply projections_baseChange_injective S T
      apply Prod.ext
      · change (predecessor S).baseChange T
          ((lowerDifferential S h hh).baseChange T x) = (predecessor S).baseChange T 0
        rw [← LinearMap.comp_apply, hp, map_zero]
        exact hx
      · change (differential S).baseChange T
          ((lowerDifferential S h hh).baseChange T x) = (differential S).baseChange T 0
        rw [← LinearMap.comp_apply, hd, map_zero, LinearMap.zero_apply]
  · intro T _ _
    exact baseChangeLowerHomologyIso S h hh T ≪≫ F.lowerInputBaseChangeHomologyIso T

/-- The frontier in every degree is produced by finite recursion on the actual
original flat chain complex and its actual finite native homology. -/
def frontier (C : ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ n, Module.Flat R (C.X n)] [∀ n, Module.Finite R (C.homology n)] :
    (n : ℕ) → Frontier C n
  | 0 => initialFrontier C
  | n + 1 => nextFrontier (frontier C n)

/-- Constructed finite free maps and their actual arbitrary-scalar homology
comparison. This is output data, never an input to the producer. -/
structure FiniteFreeTriple (C : ChainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) where
  incomingRank : ℕ
  middleRank : ℕ
  outgoingRank : ℕ
  incoming : (Fin incomingRank → R) →ₗ[R] (Fin middleRank → R)
  outgoing : (Fin middleRank → R) →ₗ[R] (Fin outgoingRank → R)
  zero : outgoing ∘ₗ incoming = 0
  homology_baseChange : ∀ (T : Type u) [CommRing T] [Algebra R T],
    (baseChangeComplex (ShortComplex.moduleCatMk incoming outgoing zero) T).homology ≅
      (baseChangeComplex (segment C q) T).homology

/-- An actual finite free triple is constructed for every degree of the original
flat chain complex with finite native homology. -/
def finiteFreeTriple (C : ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ n, Module.Flat R (C.X n)] [∀ n, Module.Finite R (C.homology n)]
    (q : ℕ) : FiniteFreeTriple C q := by
  let F := frontier C q
  let S := F.toShortComplex
  let : Module.Finite R S.homology := F.homology_finite
  let : Module.Finite R S.X₃ := by change Module.Finite R (Fin F.rank → R); infer_instance
  let : Module.Flat R S.X₁ := inferInstanceAs (Module.Flat R (C.X (q + 1)))
  let : Module.Flat R S.X₂ := F.flat_middle
  let h := (C.d (q + 2) (q + 1)).hom
  have hh : S.f.hom ∘ₗ h = 0 := ModuleCat.hom_ext_iff.mp F.before_zero
  let U := lowerReplacement S h hh
  let G := nextFrontier F
  let : Module.Finite R U.homology := by
    change Module.Finite R G.toShortComplex.homology
    exact G.homology_finite
  let : Module.Finite R U.X₃ := by change Module.Finite R (FreeTerm S); infer_instance
  have hupper : outgoing S ∘ₗ U.g.hom = 0 := outgoing_comp_differential S
  exact {
    incomingRank := (liftData U).1
    middleRank := (liftData S).1
    outgoingRank := F.rank
    incoming := outgoing U
    outgoing := outgoing S
    zero := (upperReplacement U (outgoing S) hupper).zero |> ModuleCat.hom_ext_iff.mp
    homology_baseChange := fun T _ _ =>
      baseChangeUpperHomologyIso U T (outgoing S) hupper ≪≫
        baseChangeHomologyIso S T ≪≫ F.homology_baseChange T }

/-- The public existence theorem has only original flatness and original finite
homology assumptions; all finite free maps and all scalar comparisons are produced. -/
theorem exists_finite_free_triple (C : ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ n, Module.Flat R (C.X n)] [∀ n, Module.Finite R (C.homology n)]
    (q : ℕ) :
    ∃ (a b c : ℕ) (f : (Fin a → R) →ₗ[R] (Fin b → R))
      (g : (Fin b → R) →ₗ[R] (Fin c → R)) (hgf : g ∘ₗ f = 0),
      ∀ (T : Type u) [CommRing T] [Algebra R T], Nonempty
        ((baseChangeComplex (ShortComplex.moduleCatMk f g hgf) T).homology ≅
          (baseChangeComplex (segment C q) T).homology) := by
  let E := finiteFreeTriple C q
  exact ⟨E.incomingRank, E.middleRank, E.outgoingRank, E.incoming, E.outgoing,
    E.zero, fun T _ _ => ⟨E.homology_baseChange T⟩⟩

end EnvelopeProperty.Vanishing.SpecializationDerivedFiniteApproximation
