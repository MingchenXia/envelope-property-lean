# tauCetiGenericEp33: generic freeness from Tau Ceti (vendored)

Four unmodified source modules from [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti)
at commit `15198c5caca3d2ccadc8d5b4e98cbef1a50b4a4c` (Apache-2.0, see [`LICENSE`](LICENSE)),
root `TauCeti.RingTheory.Spectrum.Prime.GenericFreeness`. Upstream targets Lean v4.35.0-rc3; the
sources compile without changes under Lean v4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. [`UPSTREAM.json`](UPSTREAM.json) records the sha256 of
each source.

The result: for a finite module over a finite-type algebra over a reduced Noetherian base, the
localized module is free on an open neighbourhood of each minimal prime of the base, and the
interior of the free locus is dense.

This package is a Lake path dependency of `EnvelopeProperty` (`deps/tauceti-generic-ep33`); build
it from `EnvelopeProperty/` as described in the top-level README. Do not run `lake update`.
