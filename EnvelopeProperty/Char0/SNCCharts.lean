/-
Copyright (c) 2026. All rights reserved.
-/
import Hironaka.Scheme.Snc.SpreadSnc
import Hironaka.Scheme.Snc.Defs
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Algebra.Util.JacobsonCover

/-!
# Finite affine étale coordinates adapted to a simple normal crossing family

The principalization output supplies an actual `DivisorFamily.IsSnc`. Its local regular
parameters at a closed point spread to affine étale coordinates by Hironaka's checked producer.
These neighbourhoods cover the whole scheme by the Jacobson property; quasi-compactness gives
a finite cover. No chart-existence hypothesis is introduced.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal

universe u

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]

/-- The actual regular parameters of an SNC family give affine étale coordinates at a closed
point, with its components cut out by distinct coordinate functions. -/
theorem exists_snc_etale_chart_at_closed {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    {x : X} (hx : IsClosed ({x} : Set X)) :
    ∃ (U : X.affineOpens) (v : Fin n → Γ(X, U.1)), x ∈ U.1 ∧
      Etale (toAffineSpace f U.1 v) ∧
      ∃ c : {i : F.ι // x ∈ (F.component i).support} → Fin n,
        Function.Injective c ∧
        (∀ i, (F.component i.1).ideal U = span {v (c i)}) ∧
        ∀ i, x ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤ := by
  obtain ⟨m, z, hz, c, hcinj, hc⟩ := hF.2 x
  have hmn : m = n := by
    have hdim := Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed f n hx
    have hm := hz.2
    rw [hdim] at hm
    exact_mod_cast hm
  subst m
  obtain ⟨E, c', hc'inj, _, hc', habsent⟩ := exists_etaleCoordinatesAdapted_of_snc f n
    (Z := (⊥ : X.IdealSheafData)) F.component hx hz.1.symm ∅
    (by simpa using Scheme.IdealSheafData.stalkIdeal_bot x) c hcinj hc
  exact ⟨E.U, E.v, E.mem, E.etale, c', hc'inj, hc', habsent⟩

/-- Quasi-compactness gives finitely many actual affine étale charts adapted to the family.
Each chosen closed point records which components are coordinate hyperplanes; every other
component is absent on that whole chart. -/
theorem exists_finite_snc_etale_cover [CompactSpace X] {F : Scheme.DivisorFamily X}
    (hF : F.IsSnc) :
    ∃ t : Finset X.affineOpens, (∀ x : X, ∃ U ∈ t, x ∈ U.1) ∧
      ∀ U ∈ t, ∃ (x : X) (v : Fin n → Γ(X, U.1)), IsClosed ({x} : Set X) ∧
        x ∈ U.1 ∧ Etale (toAffineSpace f U.1 v) ∧
        ∃ c : {i : F.ι // x ∈ (F.component i).support} → Fin n,
          Function.Injective c ∧
          (∀ i, (F.component i.1).ideal U = span {v (c i)}) ∧
          ∀ i, x ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤ := by
  classical
  choose U v hmem het c hcinj hideal habsent using
    fun p : {x : X // IsClosed ({x} : Set X)} => exists_snc_etale_chart_at_closed f n hF p.2
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hcover : (Set.univ : Set X) ⊆ ⋃ p, ((U p).1 : Set X) := by
    intro x _
    obtain ⟨p, hp, _, hxp⟩ :=
      exists_isClosed_singleton_mem_specializes isClosed_univ (Set.mem_univ x)
    exact Set.mem_iUnion.mpr
      ⟨⟨p, hp⟩, hxp.mem_open (U ⟨p, hp⟩).1.isOpen (hmem ⟨p, hp⟩)⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun p => ((U p).1 : Set X)) (fun p => (U p).1.isOpen) hcover
  refine ⟨s.image U, ?_, ?_⟩
  · intro x
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
    obtain ⟨hps, hxp⟩ := Set.mem_iUnion.mp hp
    exact ⟨U p, Finset.mem_image.mpr ⟨p, hps, rfl⟩, hxp⟩
  · intro V hV
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hV
    exact ⟨p.1, v p, p.2, hmem p, het p, c p, hcinj p, hideal p, habsent p⟩

end EnvelopeProperty.Char0
