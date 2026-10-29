import EnvelopeProperty.Vanishing.NadelBertiniSncStrata
import EnvelopeProperty.Vanishing.NadelBertiniSncLocal
import Hironaka.Scheme.Snc.Basic
import Hironaka.Scheme.Snc.SmoothDivisor

/-! # Genuine all-closed-strata transversality for the original new hypersurface

Smooth divisor means an actual codimension-one regular equation, rather than
mere smoothness of the zero subscheme. The actual deepest original stratum's
stalk map detects the original new equation's nonzero transverse cotangent class.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniSncTransverse
open NadelBertiniSncStrata NadelBertiniSncLocal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

/-- The SAME original equation is transverse to the original stratum whenever
its ACTUAL restriction is a genuine smooth divisor on that SAME stratum. -/
theorem equation_transverse_to_stratum (E : X.DivisorFamily) (s : Finset E.ι)
    (H : X.IdealSheafData)
    (hcut : IsSmoothDivisor (H.comap (stratum E s).subschemeι))
    {x : X} (hx : x ∈ (stratum E s).support) (hxH : x ∈ H.support)
    (h : X.presheaf.stalk x) (hh : H.stalkIdeal x = Ideal.span {h}) :
    h ∉ maximalIdeal (X.presheaf.stalk x) ^ 2 ⊔ (stratum E s).stalkIdeal x := by
  obtain ⟨w, rfl⟩ := (stratum E s).exists_subschemeι_eq hx
  have hw : w ∈ (H.comap (stratum E s).subschemeι).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hxH
  obtain ⟨g, _, hg2, hg⟩ := hcut.2 w hw
  have himage : (H.comap (stratum E s).subschemeι).stalkIdeal w =
      Ideal.span {(stratum E s).subschemeι.stalkMap w h} := by
    rw [Scheme.IdealSheafData.stalkIdeal_comap, hh, Ideal.map_span, Set.image_singleton]
  have hnot : (stratum E s).subschemeι.stalkMap w h ∉
      maximalIdeal ((stratum E s).subscheme.presheaf.stalk w) ^ 2 := by
    intro hbad
    have hle : Ideal.span {(stratum E s).subschemeι.stalkMap w h} ≤
        maximalIdeal ((stratum E s).subscheme.presheaf.stalk w) ^ 2 :=
      (Ideal.span_singleton_le_iff_mem _).mpr hbad
    apply hg2
    apply hle
    rw [← himage, hg]
    exact Ideal.mem_span_singleton_self g
  have htrans := notMem_sq_sup_ker_of_image_notMem_sq
    ((stratum E s).subschemeι.stalkMap w).hom h hnot
  rwa [(stratum E s).ker_stalkMap_subschemeι w] at htrans

/-- The canonical old-or-new label of a component through an original point. -/
def appendThrough (E : X.DivisorFamily) (H : X.IdealSheafData) (x : X)
    (i : {i : (E.append H).ι // x ∈ ((E.append H).component i).support}) :
    Option {i : E.ι // x ∈ (E.component i).support} :=
  match hi : ofLex i.1 with
  | Sum.inl j => some ⟨j, by
      have hcomp : (E.append H).component i.1 = E.component j :=
        congrArg (Sum.elim E.component (fun _ : PUnit.{u + 1} => H)) hi
      exact hcomp ▸ i.2⟩
  | Sum.inr _ => none

/-- The canonical old-or-new label retains the actual distinct original indices. -/
theorem appendThrough_injective (E : X.DivisorFamily) (H : X.IdealSheafData) (x : X) :
    Function.Injective (appendThrough E H x) := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ heq
  obtain ⟨i, rfl⟩ := toLex.surjective i
  obtain ⟨j, rfl⟩ := toLex.surjective j
  rcases i with i | i <;> rcases j with j | j
  · change some (⟨i, hi⟩ : {i : E.ι // x ∈ (E.component i).support}) = some ⟨j, hj⟩ at heq
    exact Subtype.ext (congrArg (fun i => toLex (Sum.inl i))
      (congrArg Subtype.val (Option.some.inj heq)))
  · change some (⟨i, hi⟩ : {i : E.ι // x ∈ (E.component i).support}) = none at heq
    cases heq
  · change none = some (⟨j, hj⟩ : {i : E.ι // x ∈ (E.component i).support}) at heq
    cases heq
  · cases i
    cases j
    rfl

end EnvelopeProperty.Vanishing.NadelBertiniSncTransverse
