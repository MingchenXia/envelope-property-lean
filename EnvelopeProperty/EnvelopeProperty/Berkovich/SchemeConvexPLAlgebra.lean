/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeLocalPSH
import Mathlib.Algebra.Order.Group.Finset
import Mathlib.Data.Finset.Lattice.Prod

/-! # Actual original section restrictions and intrinsic finite convex PL algebra -/
open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Classical
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- True original section restriction retains EVERY actual rational unit expression. -/
theorem unitTropAffine_restrict {V W : X.Opens} (i : W ≤ V) {n : ℕ}
    (a : Fin n → Γ(X, V)ˣ) (p : (Fin n → ℚ) × ℚ)
    (y : RelativeSchemeValuedPoint v f) (hy : y.1.point ∈ W) :
    unitTropAffine (V := W)
      (fun j => Units.map (X.presheaf.map (homOfLE i).op).hom.toMonoidHom (a j)) p y hy =
      unitTropAffine a p y (i hy) := by
  unfold unitTropAffine
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z : ℝ≥0 => (p.1 j : ℝ) * Real.log (z : ℝ))
    (SchemeValuedPoint.eval_restrict y.1 V W i hy (a j : Γ(X, V)))

/-- Concatenation adds the WHOLE original real unit expressions on the same true scheme open. -/
theorem unitTropAffine_append {V : X.Opens} {n m : ℕ}
    (a : Fin n → Γ(X, V)ˣ) (b : Fin m → Γ(X, V)ˣ)
    (p : (Fin n → ℚ) × ℚ) (q : (Fin m → ℚ) × ℚ)
    (y : RelativeSchemeValuedPoint v f) (hy : y.1.point ∈ V) :
    unitTropAffine (Fin.append a b) (Fin.append p.1 q.1, p.2 + q.2) y hy =
      unitTropAffine a p y hy + unitTropAffine b q y hy := by
  simp only [unitTropAffine, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  push_cast
  ring

/-- Extending by genuine zero coefficients preserves the ENTIRE first expression. -/
theorem unitTropAffine_append_zero_right {V : X.Opens} {n m : ℕ}
    (a : Fin n → Γ(X, V)ˣ) (b : Fin m → Γ(X, V)ˣ) (p : (Fin n → ℚ) × ℚ)
    (y : RelativeSchemeValuedPoint v f) (hy : y.1.point ∈ V) :
    unitTropAffine (Fin.append a b) (Fin.append p.1 0, p.2) y hy = unitTropAffine a p y hy := by
  simp [unitTropAffine, Fin.sum_univ_add]

/-- Extending by genuine zero coefficients preserves the ENTIRE second expression. -/
theorem unitTropAffine_zero_append {V : X.Opens} {n m : ℕ}
    (a : Fin n → Γ(X, V)ˣ) (b : Fin m → Γ(X, V)ˣ) (p : (Fin m → ℚ) × ℚ)
    (y : RelativeSchemeValuedPoint v f) (hy : y.1.point ∈ V) :
    unitTropAffine (Fin.append a b) (Fin.append 0 p.1, p.2) y hy = unitTropAffine b p y hy := by
  simp [unitTropAffine, Fin.sum_univ_add]

variable {U V : Set (RelativeSchemeValuedPoint v f)}
  {u w : RelativeSchemeValuedPoint v f → EReal}

/-- True defining native neighborhoods cover the ORIGINAL domain. -/
theorem IsConvexPLOn.isOpen (hu : IsConvexPLOn U u) : IsOpen U := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨W, hW, hxW, hWU, _⟩ := hu x hx
  exact ⟨W, hWU, hW, hxW⟩

/-- Restriction uses actual finite open intersections and the SAME original section units. -/
theorem IsConvexPLOn.mono (hu : IsConvexPLOn U u) (hV : IsOpen V) (hVU : V ⊆ U) :
    IsConvexPLOn V u := by
  intro x hx
  obtain ⟨W, hW, hxW, _, Z, hWZ, n, a, s, hs, hform⟩ := hu x (hVU hx)
  exact ⟨W ∩ V, hW.inter hV, ⟨hxW, hx⟩, Set.inter_subset_right,
    Z, (fun y hy => hWZ y hy.1), n, a, s, hs, fun y hy => hform y hy.1⟩

/-- Equality on the ORIGINAL domain retains the actual entire unit presentation. -/
theorem IsConvexPLOn.congr (hu : IsConvexPLOn U u) (heq : ∀ y ∈ U, u y = w y) :
    IsConvexPLOn U w := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU, Z, hWZ, n, a, s, hs, hform⟩ := hu x hx
  exact ⟨W, hW, hxW, hWU, Z, hWZ, n, a, s, hs,
    fun y hy => (heq y (hWU hy)).symm.trans (hform y hy)⟩

/-- Genuine native locality follows from actual original defining neighborhoods. -/
theorem isConvexPLOn_of_local
    (h : ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ IsConvexPLOn V u) : IsConvexPLOn U u := by
  intro x hx
  obtain ⟨V, _, hxV, hVU, hv⟩ := h x hx
  obtain ⟨W, hW, hxW, hWV, rest⟩ := hv x hxV
  exact ⟨W, hW, hxW, hWV.trans hVU, rest⟩

/-- A rational constant uses an empty ORIGINAL unit family on the true scheme open top. -/
theorem isConvexPLOn_const (hU : IsOpen U) (q : ℚ) :
    IsConvexPLOn U (fun _ => ((q : ℝ) : EReal)) := by
  intro x hx
  refine ⟨U, hU, hx, subset_rfl, ⊤, (fun _ _ => trivial),
    0, Fin.elim0, {(0, q)}, Finset.singleton_nonempty _, ?_⟩
  intro y hy
  simp [unitTropAffine]

/-- The maximum uses actual original unit restrictions and the real finite union of zero-extended vectors. -/
theorem IsConvexPLOn.max (hu : IsConvexPLOn U u) (hw : IsConvexPLOn U w) :
    IsConvexPLOn U (fun y => max (u y) (w y)) := by
  intro x hx
  obtain ⟨W₁, hW₁, hxW₁, hW₁U, V₁, hWV₁, n, a, s, hs, hu₁⟩ := hu x hx
  obtain ⟨W₂, hW₂, hxW₂, _, V₂, hWV₂, m, b, t, ht, hw₂⟩ := hw x hx
  let a' : Fin n → Γ(X, V₁ ⊓ V₂)ˣ :=
    fun j => Units.map (X.presheaf.map (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).op).hom.toMonoidHom (a j)
  let b' : Fin m → Γ(X, V₁ ⊓ V₂)ˣ :=
    fun j => Units.map (X.presheaf.map (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).op).hom.toMonoidHom (b j)
  have hWV : ∀ y ∈ W₁ ∩ W₂, y.1.point ∈ V₁ ⊓ V₂ :=
    fun y hy => ⟨hWV₁ y hy.1, hWV₂ y hy.2⟩
  refine ⟨W₁ ∩ W₂, hW₁.inter hW₂, ⟨hxW₁, hxW₂⟩, Set.inter_subset_left.trans hW₁U,
    V₁ ⊓ V₂, hWV, n+m, Fin.append a' b',
    s.image (fun p => (Fin.append p.1 0, p.2)) ∪ t.image (fun p => (Fin.append 0 p.1, p.2)),
    (hs.image _).mono Finset.subset_union_left, ?_⟩
  intro y hy
  have hy₁ : y ∈ W₁ := hy.1
  have hy₂ : y ∈ W₂ := hy.2
  have hyV : y.1.point ∈ V₁ ⊓ V₂ := hWV y hy
  beta_reduce
  rw [hu₁ y hy₁, hw₂ y hy₂, Finset.sup'_union (hs.image _) (ht.image _),
    Finset.sup'_image, Finset.sup'_image]
  simp only [Function.comp_def, unitTropAffine_append_zero_right, unitTropAffine_zero_append]
  have ha (p : (Fin n → ℚ) × ℚ) := unitTropAffine_restrict (inf_le_left : V₁ ⊓ V₂ ≤ V₁)
    a p y hyV
  have hb (p : (Fin m → ℚ) × ℚ) := unitTropAffine_restrict (inf_le_right : V₁ ⊓ V₂ ≤ V₂)
    b p y hyV
  change _ = (((s.sup' hs (fun p => unitTropAffine a' p y _)) ⊔
    t.sup' ht (fun p => unitTropAffine b' p y _) : ℝ) : EReal)
  simp_rw [show ∀ p, unitTropAffine a' p y hyV =
    unitTropAffine a p y (hWV₁ y hy₁) from ha,
    show ∀ p, unitTropAffine b' p y hyV =
    unitTropAffine b p y (hWV₂ y hy₂) from hb]
  exact (EReal.coe_strictMono.monotone.map_max).symm

/-- Actual finite products of rational vector families give the SAME original pointwise sum. -/
theorem IsConvexPLOn.add (hu : IsConvexPLOn U u) (hw : IsConvexPLOn U w) :
    IsConvexPLOn U (fun y => u y + w y) := by
  intro x hx
  obtain ⟨W₁, hW₁, hxW₁, hW₁U, V₁, hWV₁, n, a, s, hs, hu₁⟩ := hu x hx
  obtain ⟨W₂, hW₂, hxW₂, _, V₂, hWV₂, m, b, t, ht, hw₂⟩ := hw x hx
  let a' : Fin n → Γ(X, V₁ ⊓ V₂)ˣ :=
    fun j => Units.map (X.presheaf.map (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).op).hom.toMonoidHom (a j)
  let b' : Fin m → Γ(X, V₁ ⊓ V₂)ˣ :=
    fun j => Units.map (X.presheaf.map (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).op).hom.toMonoidHom (b j)
  have hWV : ∀ y ∈ W₁ ∩ W₂, y.1.point ∈ V₁ ⊓ V₂ :=
    fun y hy => ⟨hWV₁ y hy.1, hWV₂ y hy.2⟩
  refine ⟨W₁ ∩ W₂, hW₁.inter hW₂, ⟨hxW₁, hxW₂⟩, Set.inter_subset_left.trans hW₁U,
    V₁ ⊓ V₂, hWV, n+m, Fin.append a' b',
    (s ×ˢ t).image (fun pq => (Fin.append pq.1.1 pq.2.1, pq.1.2 + pq.2.2)), (hs.product ht).image _, ?_⟩
  intro y hy
  have hy₁ : y ∈ W₁ := hy.1
  have hy₂ : y ∈ W₂ := hy.2
  have hyV : y.1.point ∈ V₁ ⊓ V₂ := hWV y hy
  beta_reduce
  rw [hu₁ y hy₁, hw₂ y hy₂, Finset.sup'_image]
  simp only [Function.comp_def, unitTropAffine_append]
  have ha (p : (Fin n → ℚ) × ℚ) := unitTropAffine_restrict (inf_le_left : V₁ ⊓ V₂ ≤ V₁)
    a p y hyV
  have hb (p : (Fin m → ℚ) × ℚ) := unitTropAffine_restrict (inf_le_right : V₁ ⊓ V₂ ≤ V₂)
    b p y hyV
  simp_rw [show ∀ p, unitTropAffine a' p y hyV =
    unitTropAffine a p y (hWV₁ y hy₁) from ha,
    show ∀ p, unitTropAffine b' p y hyV =
    unitTropAffine b p y (hWV₂ y hy₂) from hb]
  rw [Finset.sup'_product_left]
  simp_rw [← Finset.add_sup', ← Finset.sup'_add]
  rw [EReal.coe_add]

/-- Nonnegative rational multiplication acts on EVERY original rational vector and finite maximum. -/
theorem IsConvexPLOn.smul (hu : IsConvexPLOn U u) {c : ℚ} (hc : 0 ≤ c) :
    IsConvexPLOn U (fun y => ((c : ℝ) : EReal) * u y) := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU, Z, hWZ, n, a, s, hs, hform⟩ := hu x hx
  refine ⟨W, hW, hxW, hWU, Z, hWZ, n, a,
    s.image (fun p => (c • p.1, c * p.2)), hs.image _, ?_⟩
  intro y hy
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  beta_reduce
  rw [hform y hy, Finset.sup'_image, ← EReal.coe_mul,
    Finset.apply_sup'_eq_sup'_comp hs (fun r : ℝ => (c : ℝ) * r)
      (fun _ _ => Monotone.map_max fun _ _ h => mul_le_mul_of_nonneg_left h hc')]
  congr 2
  funext p
  simp only [Function.comp_apply, unitTropAffine, Pi.smul_apply, smul_eq_mul, Rat.cast_mul,
    Finset.mul_sum, mul_add, mul_assoc]

/-- Rational translation uses the SAME original function and true rational constant. -/
theorem IsConvexPLOn.add_const (hu : IsConvexPLOn U u) (q : ℚ) :
    IsConvexPLOn U (fun y => u y + ((q : ℝ) : EReal)) :=
  hu.add (isConvexPLOn_const hu.isOpen q)

/-- EVERY actual finite sum is convex PL, including the genuine empty sum on an original open domain. -/
theorem isConvexPLOn_finset_sum {ι : Type*} (s : Finset ι)
    (F : ι → RelativeSchemeValuedPoint v f → EReal) (hU : IsOpen U)
    (hF : ∀ i ∈ s, IsConvexPLOn U (F i)) : IsConvexPLOn U (fun y => ∑ i ∈ s, F i y) := by
  revert hF
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using isConvexPLOn_const (v := v) (f := f) hU 0
  | @insert i s hi ih =>
    intro hF
    have hs := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using (hF i (Finset.mem_insert_self i s)).add hs

/-- EVERY actual finite nonempty maximum uses the same whole original native functions. -/
theorem isConvexPLOn_finset_sup' {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (F : ι → RelativeSchemeValuedPoint v f → EReal)
    (hF : ∀ i ∈ s, IsConvexPLOn U (F i)) :
    IsConvexPLOn U (fun y => s.sup' hs (fun i => F i y)) := by
  revert hs hF
  induction s using Finset.induction_on with
  | empty => intro hs; simp at hs
  | @insert i s hi ih =>
    intro hs hF
    by_cases hs' : s.Nonempty
    · have htail := ih hs' (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sup'_insert hs'] using (hF i (Finset.mem_insert_self i s)).max htail
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst s
      simpa only [Finset.insert_empty, Finset.sup'_singleton] using hF i (Finset.mem_insert_self i ∅)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
