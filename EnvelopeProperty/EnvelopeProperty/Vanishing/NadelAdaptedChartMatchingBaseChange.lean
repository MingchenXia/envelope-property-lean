import EnvelopeProperty.Vanishing.NadelMixedKummerPresentation
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Actual whole varying-degree coefficient base change

The actual mixed quotient satisfies the whole native ring pushout property;
all original roots, components and nilpotents are retained.
-/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching
namespace BaseChange
open NadelMixedKummer
variable {R S : Type u} [CommRing R] [CommRing S] {q : ℕ}
  (N : Fin q → ℕ) (c : Fin q → R) (f : R →+* S)

/-- The actual WHOLE original family with its coefficients mapped to the new base. -/
abbrev Ring := NadelMixedKummer.Ring N (fun i => f (c i))

/-- The actual original coefficient-extension homomorphism on all original roots. -/
def map : NadelMixedKummer.Ring N c →+* Ring N c f :=
  evaluate N c ((algebraMap S (NadelMixedKummer.Ring N (fun i => f (c i)))).comp f)
    (root N (fun i => f (c i))) (fun i => root_pow N (fun i => f (c i)) i)

/-- The original coefficient square commutes on the WHOLE actual family algebra. -/
theorem map_structure : (map N c f).comp (algebraMap R (NadelMixedKummer.Ring N c)) =
    (algebraMap S (NadelMixedKummer.Ring N (fun i => f (c i)))).comp f := evaluate_structure _ _ _ _ _

/-- Every original root maps to its actual corresponding base-changed root. -/
theorem map_root (i : Fin q) : map N c f (root N c i) =
    root N (fun i => f (c i)) i := evaluate_root _ _ _ _ _ _

private theorem coconeRelation
    (s : Limits.PushoutCocone (CommRingCat.ofHom f)
      (CommRingCat.ofHom (algebraMap R (NadelMixedKummer.Ring N c)))) (i : Fin q) :
    s.inr (root N c i) ^ N i = s.inl (f (c i)) := by
  rw [← map_pow, root_pow]
  exact (congrArg (fun h : CommRingCat.of R ⟶ s.pt => h (c i)) s.condition).symm

private def coconeDesc
    (s : Limits.PushoutCocone (CommRingCat.ofHom f)
      (CommRingCat.ofHom (algebraMap R (NadelMixedKummer.Ring N c)))) : CommRingCat.of (Ring N c f) ⟶ s.pt :=
  CommRingCat.ofHom (evaluate N (fun i => f (c i)) s.inl.hom
    (fun i => s.inr (root N c i)) (coconeRelation N c f s))

/-- The actual WHOLE root-family coefficient square is a native ring pushout. -/
theorem isPushout : IsPushout (CommRingCat.ofHom f)
    (CommRingCat.ofHom (algebraMap R (NadelMixedKummer.Ring N c)))
    (CommRingCat.ofHom (algebraMap S (NadelMixedKummer.Ring N (fun i => f (c i)))))
    (CommRingCat.ofHom (map N c f)) := by
  have hw : CommRingCat.ofHom f ≫
      CommRingCat.ofHom (algebraMap S (NadelMixedKummer.Ring N (fun i => f (c i)))) =
      CommRingCat.ofHom (algebraMap R (NadelMixedKummer.Ring N c)) ≫ CommRingCat.ofHom (map N c f) := by
    apply CommRingCat.hom_ext
    exact (map_structure N c f).symm
  refine ⟨⟨hw⟩, ⟨Limits.PushoutCocone.IsColimit.mk hw (coconeDesc N c f) ?_ ?_ ?_⟩⟩
  · intro s
    apply CommRingCat.hom_ext
    exact evaluate_structure N (fun i => f (c i)) s.inl.hom
      (fun i => s.inr (root N c i)) (coconeRelation N c f s)
  · intro s
    apply CommRingCat.hom_ext
    apply hom_ext
    · change ((coconeDesc N c f s).hom.comp (map N c f)).comp (algebraMap R (NadelMixedKummer.Ring N c)) = _
      rw [RingHom.comp_assoc, map_structure, ← RingHom.comp_assoc]
      have hc : (coconeDesc N c f s).hom.comp
          (algebraMap S (NadelMixedKummer.Ring N (fun i => f (c i)))) = s.inl.hom :=
        evaluate_structure N (fun i => f (c i)) s.inl.hom
          (fun i => s.inr (root N c i)) (coconeRelation N c f s)
      rw [hc]
      exact congrArg CommRingCat.Hom.hom s.condition
    · intro i
      change coconeDesc N c f s (map N c f _) = s.inr _
      rw [map_root]
      exact evaluate_root N (fun i => f (c i)) s.inl.hom
        (fun i => s.inr (root N c i)) (coconeRelation N c f s) i
  · intro s m hl hr
    apply CommRingCat.hom_ext
    apply hom_ext
    · have hl' := congrArg CommRingCat.Hom.hom hl
      have hc : (coconeDesc N c f s).hom.comp
          (algebraMap S (NadelMixedKummer.Ring N (fun i => f (c i)))) = s.inl.hom :=
        evaluate_structure N (fun i => f (c i)) s.inl.hom
          (fun i => s.inr (root N c i)) (coconeRelation N c f s)
      exact hl'.trans hc.symm
    · intro i
      change m (root N (fun i => f (c i)) i) = _
      rw [← map_root N c f i]
      have hr' := congrArg (fun h : CommRingCat.of (NadelMixedKummer.Ring N c) ⟶ s.pt =>
        h (root N c i)) hr
      apply hr'.trans
      rw [map_root]
      exact (evaluate_root N (fun i => f (c i)) s.inl.hom
        (fun i => s.inr (root N c i)) (coconeRelation N c f s) i).symm

/-- The literal WHOLE family spectra form the actual native base-change square. -/
theorem isPullback : IsPullback (Spec.map (CommRingCat.ofHom (map N c f)))
    (Spec.map (CommRingCat.ofHom (algebraMap S (NadelMixedKummer.Ring N (fun i => f (c i))))))
    (Spec.map (CommRingCat.ofHom (algebraMap R (NadelMixedKummer.Ring N c))))
    (Spec.map (CommRingCat.ofHom f)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout N c f).flip

end BaseChange
end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching
