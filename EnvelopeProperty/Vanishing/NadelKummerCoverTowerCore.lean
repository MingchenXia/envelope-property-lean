import EnvelopeProperty.Vanishing.NadelFiniteDualityTowerFinite

/-! # Actual universal maps and transitions of the original independent-root tower

The tower is the existing native successive AdjoinRoot construction. All
transition and evaluation homomorphisms are built internally from its actual
quotient universal properties; no desired comparison isomorphism is an input.
-/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelKummerCover.Tower

open NadelFiniteDualityTower

variable {R : Type u} [CommRing R] (d : ℕ → ℕ) (c : ℕ → R)

/-- The genuine composite of the original tower steps from stage i to stage j. -/
def transition {i j : ℕ} (hij : i ≤ j) :
    independentRootRing d c i →+* independentRootRing d c j :=
  Nat.leRecOn (C := fun j => independentRootRing d c i →+* independentRootRing d c j)
    hij (fun {k} f => (independentRootStep d c k).comp f) (RingHom.id _)

@[simp] theorem transition_self (i : ℕ) : transition d c (Nat.le_refl i) = RingHom.id _ :=
  Nat.leRecOn_self _

theorem transition_succ {i j : ℕ} (hij : i ≤ j) :
    transition d c (Nat.le_succ_of_le hij) =
      (independentRootStep d c j).comp (transition d c hij) :=
  Nat.leRecOn_succ hij _

/-- Every actual transition retains the SAME original coefficient map. -/
theorem transition_structure {i j : ℕ} (hij : i ≤ j) :
    (transition d c hij).comp (independentRootStructure d c i) =
      independentRootStructure d c j := by
  induction hij with
  | refl => rw [transition_self]; rfl
  | @step j hij ih =>
      rw [transition_succ d c hij, RingHom.comp_assoc, ih, independentRootStructure_succ]

/-- Actual transition composites agree on the whole original tower rings. -/
theorem transition_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (transition d c hjk).comp (transition d c hij) =
      transition d c (Nat.le_trans hij hjk) := by
  induction hjk with
  | refl => rw [transition_self]; rfl
  | @step k hjk ih =>
      rw [transition_succ d c hjk, RingHom.comp_assoc, ih,
        transition_succ d c (Nat.le_trans hij hjk)]

/-- Passing the actual newly adjoined coefficient inclusion into a later
stage is the same original transition from the previous stage. -/
theorem transition_comp_step {i j : ℕ} (hij : i + 1 ≤ j) :
    (transition d c hij).comp (independentRootStep d c i) =
      transition d c (Nat.le_trans (Nat.le_succ_of_le (Nat.le_refl i)) hij) := by
  have hs : transition d c (Nat.le_succ_of_le (Nat.le_refl i)) = independentRootStep d c i := by
    rw [transition_succ d c (Nat.le_refl i), transition_self]
    rfl
  rw [← hs]
  exact transition_comp d c (Nat.le_succ_of_le (Nat.le_refl i)) hij

variable {S : Type u} [CommRing S] (f : R →+* S) (r : ℕ → S)
    (hr : ∀ i, r i ^ (d i + 1) = f (c i))

private def evaluationData : ∀ k,
    {e : independentRootRing d c k →+* S // e.comp (independentRootStructure d c k) = f}
  | 0 => ⟨f, rfl⟩
  | k + 1 => by
      let e := evaluationData k
      let e' : independentRootRing d c (k + 1) →+* S :=
        AdjoinRoot.lift e.val (r k) (by
          simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
            Polynomial.eval₂_C]
          apply sub_eq_zero.mpr
          exact (hr k).trans
            (congrArg (fun h : R →+* S => h (c k)) e.property).symm)
      refine ⟨e', ?_⟩
      rw [independentRootStructure_succ, ← RingHom.comp_assoc]
      have he : e'.comp (independentRootStep d c k) = e.val := AdjoinRoot.lift_comp_of _
      rw [he]
      exact e.property

/-- The actual universal evaluation of every original finite root stage. -/
def evaluation (k : ℕ) : independentRootRing d c k →+* S :=
  (evaluationData d c f r hr k).val

/-- The entire original coefficient map is retained by the constructed evaluation. -/
theorem evaluation_structure (k : ℕ) :
    (evaluation d c f r hr k).comp (independentRootStructure d c k) = f :=
  (evaluationData d c f r hr k).property

/-- The actual original coefficient inclusion of a new stage evaluates
through the constructed stage evaluation. -/
theorem evaluation_step (k : ℕ) :
    (evaluation d c f r hr (k + 1)).comp (independentRootStep d c k) =
      evaluation d c f r hr k := by
  dsimp only [evaluation, evaluationData]
  exact AdjoinRoot.lift_comp_of _

/-- The original new root coordinate evaluates to its specified actual root. -/
theorem evaluation_root (k : ℕ) :
    evaluation d c f r hr (k + 1)
      (CyclicSectionAlgebra.root (d k + 1) (independentRootStructure d c k (c k))) = r k := by
  dsimp only [evaluation, evaluationData]
  exact AdjoinRoot.lift_root _

/-- Evaluations commute with every genuine original tower transition. -/
theorem evaluation_transition {i j : ℕ} (hij : i ≤ j) :
    (evaluation d c f r hr j).comp (transition d c hij) =
      evaluation d c f r hr i := by
  induction hij with
  | refl => rw [transition_self]; rfl
  | @step j hij ih =>
      rw [transition_succ d c hij, ← RingHom.comp_assoc, evaluation_step, ih]

/-- The original i-th adjoined root, genuinely carried into a later stage. -/
def rootInStage {i j : ℕ} (hij : i + 1 ≤ j) : independentRootRing d c j :=
  transition d c hij
    (CyclicSectionAlgebra.root (d i + 1) (independentRootStructure d c i (c i)))

/-- Its original power relation retains the SAME original coefficient. -/
theorem rootInStage_pow {i j : ℕ} (hij : i + 1 ≤ j) :
    rootInStage d c hij ^ (d i + 1) = independentRootStructure d c j (c i) := by
  let z : independentRootRing d c (i + 1) :=
    CyclicSectionAlgebra.root (d i + 1) (independentRootStructure d c i (c i))
  have hz : z ^ (d i + 1) =
      independentRootStep d c i (independentRootStructure d c i (c i)) :=
    CyclicSectionAlgebra.root_pow _ _
  have h := congrArg (fun t : R →+* independentRootRing d c j => t (c i))
    (transition_structure d c hij)
  change transition d c hij z ^ (d i + 1) = independentRootStructure d c j (c i)
  exact (map_pow (transition d c hij) z (d i + 1)).symm.trans
    ((congrArg (transition d c hij) hz).trans h)

/-- The actual universal evaluation sees every carried original root
as the SAME specified root, independent of the later stage. -/
theorem evaluation_rootInStage {i j : ℕ} (hij : i + 1 ≤ j) :
    evaluation d c f r hr j (rootInStage d c hij) = r i := by
  unfold rootInStage
  have h := congrArg
    (fun t : independentRootRing d c (i + 1) →+* S => t
      (CyclicSectionAlgebra.root (d i + 1) (independentRootStructure d c i (c i))))
    (evaluation_transition d c f r hr hij)
  exact h.trans (evaluation_root d c f r hr i)

end EnvelopeProperty.Vanishing.NadelKummerCover.Tower
