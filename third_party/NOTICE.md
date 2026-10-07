# Third-party source attribution

Lean and mathlib provide the language, kernel and mathematical library. The
project pins Lean 4.35.0-rc2 and mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55` in its build files. Dependency source
URLs and revisions are recorded in `lean/lake-manifest.json`.

## Scott McColm

Selected oscillatory integral, analytic, zero-counting and contour proofs derive
from [smccolm/Lean](https://github.com/smccolm/Lean/tree/2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be)
at `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`, under the MIT license.
Copyright 2026 Scott McColm. The retained license is `mccolm/LICENSE`.

The exponential-sum and selected approximate-functional-equation proofs under
`lean/GuthMaynard/` and `lean/WeylPort/` derive from revision
`6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1` of the same repository, under MIT-0.
The retained license is `weyl/LICENSES/McColm-MIT-0.txt`.

## PrimeNumberTheoremAnd

Selected nonstationary-phase, Euler–Maclaurin, zeta-continuation, contour and
digamma proofs derive from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/4ecb950126c4290293c5662dfe0e884123171df5)
at `4ecb950126c4290293c5662dfe0e884123171df5`, some through McColm's adaptations.
They retain Apache-2.0 licensing. The digamma source retains the notice
Copyright 2026 Robby Sneiderman; Authors: Robby Sneiderman. License texts and
upstream notices are in `mccolm/` and `weyl/LICENSES/`.

## Conor Grogan

Selected Fourier, Mellin and gamma-function proofs derive from
[prime-minor-arcs-2-15](https://github.com/jconorgrogan/prime-minor-arcs-2-15/tree/f369f267b4dcfebf010c8e7baa2c9602e2960eba)
at `f369f267b4dcfebf010c8e7baa2c9602e2960eba`, under Apache-2.0.
The retained license is `grogan/LICENSE`.

## IEANTN

The Riemann zeta vocabulary derives from [IEANTN](https://github.com/teorth/IEANTN/tree/2a10e721ff645865c45c344333b1934f34c45b41)
at `2a10e721ff645865c45c344333b1934f34c45b41`, under Apache-2.0.
Copyright 2026 IEANTN contributors; vocabulary author: Terence Tao.
The retained license is `ieantn/LICENSE`.

## Adaptations

Selected declarations were extracted into local namespaces, imports were
narrowed, module visibility was adapted, and proof syntax was updated for the
pinned Lean/mathlib versions. The density argument, cutoff specializations,
reflection assembly, counting interfaces and final theorem are local additions.
Copyright and author headers in retained source files remain intact. These
adaptations do not imply upstream endorsement or verification of entire upstream
repositories. The original works retain their respective licenses.
