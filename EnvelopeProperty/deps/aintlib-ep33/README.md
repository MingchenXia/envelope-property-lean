# aintlibEp33: AINTLIB `ModularCurves` and `Common` (vendored)

185 modules of [CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB) at commit
`6fc322756d32a30e9bc660aadb317221fb07c73a` (Apache-2.0, see [`LICENSE`](LICENSE)), adapted to
Lean v4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. They supply projective
factorizations, finite ordered Čech cohomology, sheaf tensor/dual/pullback infrastructure,
projective-space twist calculations and the Picard comparison. Some generic sources keep their
upstream `EllipticCurve` directory; the elliptic arithmetic and Weierstrass modules are not included.

Two selections go beyond complete upstream modules: one fibre-section declaration taken verbatim
from upstream `EllipticCurve/Basic`, and a generic exact-sequence lemma from a newer Mathlib,
renamed under `ModularCurves` so that it does not shadow Mathlib.

Compatibility changes adapt namespaces, argument order, coercion proofs, categorical Pi
projections, explicit universe and typeclass data, proof-local bindings and obsolete `simp`
arguments. The AINTLIB multiplicativity theorem is renamed `comap_mul_aintlib`, so that it
coexists with Hironaka's `comap_mul`; its statement and proof are unchanged. No axiom, `sorry` or
new hypothesis is introduced.

Provenance: [`UPSTREAM.json`](UPSTREAM.json) (upstream commit, selected modules and the sha256 of
each source) and [`COMPATIBILITY.patch`](COMPATIBILITY.patch) (every source change against upstream).

This package is a Lake path dependency of `EnvelopeProperty` (`deps/aintlib-ep33`); build it from
`EnvelopeProperty/` as described in the top-level README. Do not run `lake update`.
