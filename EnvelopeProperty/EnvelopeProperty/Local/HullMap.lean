/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.Hull

/-!
# Hulls under morphisms and separating partitions

Two elementary facts used in the projection step (FHX Proposition 5.24, `prop:projection-step`):

* the image of the hull of `K` under the map induced by a `k`-algebra map `B → A` lies in the
  hull of the image of `K`;
* if `f₁ + f₂ = 1`, the open sets `{|f₂| < 1}` and `{|f₁| < 1}` are disjoint and `|f₁| = 1` on the
  first, `|f₂| = 1` on the second (ultrametric inequality).
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open Berk

variable {k : Type*} [Field k] {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- The map induced by a morphism sends hulls into hulls of images. -/
theorem comap_mem_hull_image (φ : B →ₐ[k] A) {K : Set (Berk k A)} {x : Berk k A}
    (hx : x ∈ hull K) : comap φ x ∈ hull (comap φ '' K) := by
  intro b
  rw [logAbs_comap]
  refine (hx (φ b)).trans (iSup₂_le fun y hy => ?_)
  rw [← logAbs_comap]
  exact le_iSup₂ (f := fun z (_ : z ∈ comap φ '' K) => logAbs b z) (comap φ y) ⟨y, hy, rfl⟩

theorem image_hull_subset_hull_image (φ : B →ₐ[k] A) (K : Set (Berk k A)) :
    comap φ '' hull K ⊆ hull (comap φ '' K) := by
  rintro _ ⟨x, hx, rfl⟩
  exact comap_mem_hull_image φ hx

/-- If `f₁ + f₂ = 1` and `|f₂|_x < 1` then `|f₁|_x = 1`. -/
theorem val_eq_one_of_add_eq_one {f₁ f₂ : A} (h : f₁ + f₂ = 1) {x : Berk k A}
    (hx : x.val f₂ < 1) : x.val f₁ = 1 := by
  have h1 : x.val (f₁ + f₂) = 1 := by rw [h, map_one]
  have hle : x.val f₁ ≤ 1 := by
    have : x.val f₁ = x.val (1 - f₂) := by rw [← h]; ring_nf
    rw [this]
    refine (x.val.map_sub 1 f₂).trans (max_le (by simp) hx.le)
  rcases hle.lt_or_eq with hlt | heq
  · exfalso
    have := x.val.map_add f₁ f₂
    rw [h1] at this
    exact absurd this (not_le.2 (max_lt hlt hx))
  · exact heq

/-- If `f₁ + f₂ = 1`, the sets `{|f₂| < 1}` and `{|f₁| < 1}` are disjoint. -/
theorem disjoint_of_add_eq_one {f₁ f₂ : A} (h : f₁ + f₂ = 1) :
    Disjoint {x : Berk k A | x.val f₂ < 1} {x : Berk k A | x.val f₁ < 1} := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have := val_eq_one_of_add_eq_one h hx
  simp only [Set.mem_ofPred_eq] at hx'
  rw [this] at hx'
  exact lt_irrefl _ hx'

end EnvelopeProperty
