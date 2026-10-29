/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.LocalPositivityUniformLimit
import EnvelopeProperty.Local.LocalPositivityNativeBridge
import EnvelopeProperty.Local.PositivityImport
import EnvelopeProperty.Local.PLIdealTwistedModelSheaves
import EnvelopeProperty.AlgGeom.NativeLineFSIsometries

/-!
# Assembly of FHX Lemma 5.5 from the native-scheme pipeline

This file assembles the last two links of the native-scheme proof of Fang–Han–Xia, *The envelope
property for unibranch projective varieties*, Lemma 5.5 (`lem:local-PL-positivity`, the class
`LocalPositivity`).

The upstream part of the pipeline (our native route for FHX Lemma 5.5: the PL model of `X × 𝔸¹`
of a locally convex `φ`, nefness of the twisted ratio line on the central fibre, nef plus ample is
ample, ampleness near `0`, exact finite Fubini–Study realization of model potentials, and the
identification of the potential of the twisted ratio line with `r φ + c`) produces, for a locally
`O(a)`-convex `φ` on a projectively normal `X`, the following datum, recorded as the `Prop`
`ProjSubvariety.NativePotentialFSFamily`. This route is not FHX's proof: FHX write `φ` as the
model function of a line bundle on a normal test configuration (Boucksom–Jonsson, BJ22,
Theorem 2.31) and check, via BJ22 Definition 3.2 and Lemma 4.3, that it has nonnegative degree on
the curves of the central fibre, which they deduce from the positivity criterion of
Chambert-Loir–Ducros (CLD12). Only the central-fibre nefness has a counterpart there; nef plus
ample is ample, the exact finite Fubini–Study realization and the family indexed by `b` below are
steps of the native route.

* `r ≥ 1`, `d = r a`, `q ∈ ℕ`, a real constant `c` and a bound `K`;
* functions `p_M, p_H` on the native valued points of `X.NativeScheme` (the model potentials of
  the twisted ratio line `M` and of an auxiliary line `H`), with `p_M = r φ + c` and `|p_H| ≤ K`
  on `X^an`;
* for every `b ≥ 1`, a native finite Fubini–Study function equal to `b p_M + p_H` of an invertible
  sheaf `Q ≅ O(N)` with class `e`, `N e = b d + q` (the exact FS realization of the model potential
  of the ample line `M^b ⊗ H`).

From this datum, links 8 (`ProjSubvariety.isFiniteFS_of_nativeIsFinFS`) and 9
(`ProjSubvariety.isPSH_of_potential_family`) give `φ ∈ PSH(X, a)`
(`ProjSubvariety.isPSH_of_nativePotentialFSFamily`), with no further hypothesis.
`LocalPositivity.of_nativePotentialFSFamily` then states that the class `LocalPositivity k`
holds as soon as every locally convex `φ` on every projectively normal `X` has such a datum. This
last statement is conditional: its hypothesis is the existence of the potential family, supplied by the theorem producing `NativePotentialFSFamily` from
`X.IsLocallyConvexAll a φ`.

## Main definitions

* `ProjSubvariety.NativePotentialFSFamily X a φ`: the native datum described above.

## Main results

* `ProjSubvariety.nativeTwistLineSheaf_eq_line`: the native twist `O(N)` of `X` is the pulled-back
  line of `NativePulledProjectiveLineFrames`.
* `ProjSubvariety.isPSH_of_nativePotentialFSFamily`: the native datum implies `φ ∈ PSH(X, a)`.
* `LocalPositivity.of_nativePotentialFSFamily`: the native datum for all `(X, a, φ)` gives the
  class `LocalPositivity k`.
-/

open AlgebraicGeometry CategoryTheory Filter
open Scheme.Modules
open scoped Classical NNReal ENNReal Topology

noncomputable section

universe u

namespace EnvelopeProperty

namespace ProjSubvariety

open Berkovich NativePulledProjectiveLineFrames

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The native twist `O(N)` of `X` (the pull-back of the coordinate-hyperplane pole sheaf power)
is the pulled-back line `NativePulledProjectiveLineFrames.line` along the native closed immersion
into `projectiveSpace k M`. -/
theorem nativeTwistLineSheaf_eq_line (t : Fin (M + 1)) (N : ℕ) :
    X.nativeTwistLineSheaf t N = line X.nativeProjectiveInclusion t N :=
  rfl

private local instance nativeStructureIsProper' : IsProper X.nativeStructure := by
  let : IsProper (ProjBerk.nativeStructureMap (R := k) (n := M)) :=
    ProjBerk.nativeStructureMap_isProper
  change IsProper (X.nativeInclusion ≫ ProjBerk.nativeStructureMap)
  infer_instance

/-- **The output of the native pipeline** (its upstream part, described in the module docstring).
For `a ∈ ℚ` and
`φ : X^an → ℝ`: there are `r ≥ 1`, `d = r a`, `q ∈ ℕ`, `c, K ∈ ℝ` and functions `p_M, p_H` on the
native valued points of `X` with `p_M = r φ + c` and `|p_H| ≤ K` on `X^an` such that, for every
`b ≥ 1`, `b p_M + p_H` is a native finite Fubini–Study function of class `e` of an invertible sheaf
`Q ≅ O(N)` with `N e = b d + q`. -/
def NativePotentialFSFamily (a : ℚ) (φ : X.an → ℝ) : Prop :=
  ∃ (r : ℕ) (_ : 0 < r) (d q : ℕ) (_ : (d : ℚ) = r * a) (c K : ℝ)
    (pM pH : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.nativeStructure → ℝ),
    (∀ w : X.an, pM (X.nativeAnalyticHomeomorph w) = r * φ w + c) ∧
    (∀ w : X.an, |pH (X.nativeAnalyticHomeomorph w)| ≤ K) ∧
    ∀ b : ℕ, 0 < b → ∃ (t : Fin (M + 1)) (N : ℕ) (e : ℚ) (Q : X.NativeScheme.Modules)
      (hQ : IsInvertible Q), Nonempty (Q ≅ X.nativeTwistLineSheaf t N) ∧
      (N : ℚ) * e = b * d + q ∧
      NativeLineFubiniStudy.IsFinFS X.nativeStructure Q hQ e
        fun y => ((b * pM y + pH y : ℝ) : EReal)

variable {X}

/-- **Links 8 and 9.** On a projectively normal `X`, the native datum
`NativePotentialFSFamily X a φ` implies `φ ∈ PSH(X, a)`: for each `b ≥ 1`, link 8 turns the native
finite FS function `b p_M + p_H` into a finite FS function of class `b d + q` on `X^an`, and the
ε-argument (`isPSH_of_potential_family`) concludes. -/
theorem isPSH_of_nativePotentialFSFamily (hX : X.IsProjNormal) {a : ℚ} {φ : X.an → ℝ}
    (h : X.NativePotentialFSFamily a φ) : X.IsPSH (a : ℝ) fun w => (φ w : EReal) := by
  obtain ⟨r, hr, d, q, hda, c, K, pM, pH, hpM, hpH, hFS⟩ := h
  refine isPSH_of_potential_family (X := X) hr (a := (a : ℝ)) (e := d) (e' := q) (c := c) (K := K)
    (by exact_mod_cast hda) (pM := fun w => pM (X.nativeAnalyticHomeomorph w))
    (pH := fun w => pH (X.nativeAnalyticHomeomorph w)) hpM hpH fun N₀ => ?_
  refine ⟨N₀ + 1, Nat.le_succ N₀, Nat.succ_pos N₀, ?_⟩
  obtain ⟨t, N, e, Q, hQ, ⟨ι⟩, hNe, hψ⟩ := hFS (N₀ + 1) (Nat.succ_pos N₀)
  have hψ' := hψ.mapLineIso ι X.nativeStructure hQ (X.nativeTwistLineSheaf_isInvertible t N)
  obtain ⟨-, hfin⟩ := X.isFiniteFS_of_nativeIsFinFS hX t N hψ'
  have hpsh := hfin.isPSH
  have hcl : (((N : ℚ) * e : ℚ) : ℝ) = ((N₀ + 1 : ℕ) : ℝ) * d + q := by
    rw [hNe]; push_cast; ring
  rw [hcl] at hpsh
  convert hpsh using 2 with w
  simp only [EReal.toReal_coe]

end ProjSubvariety

/-- **FHX Lemma 5.5 from the native pipeline.** If every locally `O(a)`-convex function on every
projectively normal `X = V(I) ⊆ ℙᴹ` over `k` has the native datum
`ProjSubvariety.NativePotentialFSFamily` described above, then the class
`LocalPositivity k` holds. -/
theorem LocalPositivity.of_nativePotentialFSFamily {k : Type u} [Field k] [IsAlgClosed k]
    (H : ∀ {M : ℕ} (X : ProjSubvariety k M), X.IsProjNormal → ∀ a : ℚ, 0 < a →
      ∀ φ : X.an → ℝ, X.IsLocallyConvexAll a φ → X.NativePotentialFSFamily a φ) :
    LocalPositivity k :=
  ⟨fun X hX a ha φ hφ => ProjSubvariety.isPSH_of_nativePotentialFSFamily hX (H X hX a ha φ hφ)⟩

end EnvelopeProperty
