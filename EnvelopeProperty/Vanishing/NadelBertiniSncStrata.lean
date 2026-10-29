import Hironaka.Scheme.Snc.HasSncWith
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.FieldTheory.Perfect

/-! # Actual original closed SNC strata

Every stratum is the genuine ideal-sheaf sum of the selected original
components. Its SNC-with-family coordinates and smoothness are produced from
the original family's SNC data; no stratum smoothness certificate is supplied.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniSncStrata
variable {X : Scheme.{u}}

/-- The genuine original closed stratum ideal, retaining all scheme structure. -/
def stratum (E : X.DivisorFamily) (s : Finset E.ι) : X.IdealSheafData :=
  ⨆ i : s, E.component i.1

/-- Actual membership in the original closed stratum retains every selected
original component; the empty subset imposes no condition. -/
theorem mem_stratum_support_iff (E : X.DivisorFamily) (s : Finset E.ι) (x : X) :
    x ∈ (stratum E s).support ↔ ∀ i ∈ s, x ∈ (E.component i).support := by
  simp only [stratum, Scheme.IdealSheafData.support_iSup]
  rw [TopologicalSpace.Closeds.mem_iInf]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i.1 i.2⟩

/-- The SAME original SNC coordinates internally cut out every SAME original
closed stratum by their actual selected subset. -/
theorem stratum_hasSncWith (E : X.DivisorFamily) (hE : E.IsSnc) (s : Finset E.ι) :
    E.HasSncWith (stratum E s) := by
  classical
  intro x hx
  have hxmem := (mem_stratum_support_iff E s x).mp hx
  obtain ⟨n, z, hz, c, hcinj, hc⟩ := hE.2 x
  let a : s → Fin n := fun i => c ⟨i.1, hxmem i.1 i.2⟩
  refine ⟨n, z, ⟨hz, c, hcinj, hc⟩, Finset.univ.image a, ?_⟩
  rw [stratum, Scheme.IdealSheafData.stalkIdeal_iSup]
  have hspan : Ideal.span (z '' (↑(Finset.univ.image a) : Set (Fin n))) =
      ⨆ i : s, Ideal.span {z (a i)} := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, ← Set.range_comp,
      Ideal.span_range_eq_iSup]
    rfl
  rw [hspan]
  exact iSup_congr fun i => hc ⟨i.1, hxmem i.1 i.2⟩

/-- Every whole actual original closed SNC stratum is regular. -/
theorem stratum_isRegular {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) [Smooth p] (E : X.DivisorFamily) (hE : E.IsSnc)
    (s : Finset E.ι) : IsRegular (stratum E s).subscheme :=
  HasSncWith.isRegular p (stratum_hasSncWith E hE s)

/-- Over the original perfect field, every whole actual original closed SNC
stratum is smooth over that same field. -/
theorem stratum_smooth {k : Type u} [Field k] [PerfectField k]
    (p : X ⟶ Spec (.of k)) [Smooth p] (E : X.DivisorFamily) (hE : E.IsSnc)
    (s : Finset E.ι) : Smooth ((stratum E s).subschemeι ≫ p) :=
  HasSncWith.smooth p (stratum_hasSncWith E hE s)

/-- The original closed stratum retains its closed original projective embedding. -/
theorem stratum_embedding_closed {Y : Scheme.{u}} (j : X ⟶ Y) [IsClosedImmersion j]
    (E : X.DivisorFamily) (s : Finset E.ι) :
    IsClosedImmersion ((stratum E s).subschemeι ≫ j) := inferInstance

end EnvelopeProperty.Vanishing.NadelBertiniSncStrata
