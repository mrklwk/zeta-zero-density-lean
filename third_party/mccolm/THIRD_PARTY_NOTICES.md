# Third-Party Notices

## PrimeNumberTheoremAnd (PNT+)

The files under `RiemannZeta/External/PNT/` are adapted from
[AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd).
The upstream work is distributed under the Apache License 2.0. Copyright remains
with the upstream contributors.

The local port combines the Lean 4.30-compatible rectangle and contour core from
upstream commit `80c12dfd93` with later divisor-support and rectangle
argument-principle developments. The sharp-zeta files `ZetaBoundsUpstream.lean`
and `ZetaAppendix.lean` come from pinned upstream revision
`4ecb950126c4290293c5662dfe0e884123171df5`, with imports and declaration
visibility adapted to this project's exact Lean/Mathlib versions. Source
attribution is also retained in each adapted file.
