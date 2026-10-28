/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.LocalPositivityNativeFamily

/-!
# FHX Lemma 5.5 holds: the instance `LocalPositivity k`

Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Lemma 5.5
(`lem:local-PL-positivity`, blueprint `lem:wu-local-positivity`): over an algebraically closed field
`k`, every locally `O(a)`-convex function on a projectively normal `X = V(I) ⊆ ℙᴹ` is `a`-psh.
The statement is the class `LocalPositivity k` (`Local/PositivityImport.lean`); this file proves
it for every algebraically closed `k`.

The proof is the native-scheme route of `.archon-horizon/scratch/ep/PLAN-LP-ASSEMBLY.md`:
`ProjSubvariety.IsLocallyConvexAll.nativePotentialFSFamily` (the PL model of `X × 𝔸¹`, central
nefness, the auxiliary polarization, nef plus ample, exact Fubini–Study realization of model
potentials) produces a native potential family, and `LocalPositivity.of_nativePotentialFSFamily`
(the bridge from native to graded Fubini–Study functions and the ε-argument) concludes. An
algebraically closed field is perfect and infinite, as the native route requires.
-/

namespace EnvelopeProperty

universe u

/-- **FHX Lemma 5.5** (`lem:local-PL-positivity`): over every algebraically closed field, locally
`O(a)`-convex functions on projectively normal subvarieties of `ℙᴹ` are `a`-psh. -/
instance LocalPositivity.instOfIsAlgClosed (k : Type u) [Field k] [IsAlgClosed k] :
    LocalPositivity k :=
  LocalPositivity.of_nativePotentialFSFamily fun _X hX _a ha _φ hφ =>
    ProjSubvariety.IsLocallyConvexAll.nativePotentialFSFamily hX ha hφ

end EnvelopeProperty
