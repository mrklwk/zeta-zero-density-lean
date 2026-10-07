# The density hypothesis for σ > 3/4

This project formalizes a zero-density bound for the Riemann zeta function in Lean.
For every fixed 3/4 < σ < 1 and ε > 0,

\[
N_\zeta(\sigma,T)\ll_{\sigma,\varepsilon}T^{2(1-\sigma)+\varepsilon}
\qquad(T\ge2).
\]

Here Nζ(σ,T) counts zeros ρ with Re(ρ) ≥ σ and 0 < Im(ρ) ≤ T, with analytic
multiplicity. In the convention with exponent A(σ)(1−σ)+ε, this proves
**A(σ) ≤ 2** for 3/4 < σ < 1.

The underlying Lean theorem bounds the symmetric count

\[
S(\sigma,T) \le C T^{2(1-\sigma)+\varepsilon},
\qquad
S(\sigma,T)=\sum_{\substack{\zeta(\rho)=0\\\Re\rho\ge\sigma\\|\Im\rho|\le T}}
\operatorname{mult}(\rho).
\]

The symmetric sum S includes both signs of the ordinate and both boundary
cutoffs. The proved positive-height adapter restricts this finite sum to
0 < Im(ρ) ≤ T; nonnegative multiplicities give Nζ(σ,T) ≤ S(σ,T). The constant
C = C(σ, ε) > 0 is existential and chosen before all real T ≥ 2. No numerical
value of C is supplied.

The endpoint σ = 3/4 and the case ε = 0 are excluded. The result is for the
fixed range 3/4 < σ < 1 stated above.

The density hypothesis predicts A(σ) ≤ 2 for 1/2 < σ < 1. [Bourgain](https://doi.org/10.1155/S107379280000009X) established this bound for σ > 25/32. The theorem formalized here establishes it for every fixed σ > 3/4, with σ = 3/4 excluded. This concerns the range in which the density hypothesis holds, rather than the separate problem of improving the uniform zero-density coefficient.

## Origins

This formalization arose from the author’s work on large values of Dirichlet polynomials and zero-density estimates for the Riemann zeta function. The author intends to write a paper presenting the argument.

## Statement and proof

The public theorem is `DensityThreeQuarters.density_bound` in
[Solution.lean](lean/Solution.lean). It states the zero region and the sum of
analytic multiplicities directly. [Challenge.lean](lean/Challenge.lean) contains
the matching specification. Its single intentional `sorry` is not imported by
Solution and is not part of the proof.

The conventional positive-height statement is
`DensityInterfaces.positive_count_density_bound` in
[PositiveCount.lean](lean/DensityInterfaces/PositiveCount.lean). It retains the
closed real-part cutoff and closed upper height cutoff, and counts multiplicity.

The proof uses oscillatory integral estimates, reflection, a large-values
argument, zero detection and multiplicity counting. The source also contains
proved adapters for IEANTN's open rectangle and ANTEDB's exponent convention
with a positive left shift in σ. These interfaces do not assert acceptance by
either project.

## Verification

The Lean build, transitive-axiom checks and fresh kernel replay pass on Lean 4.35.0-rc2 with mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55. The proof uses only propext, Classical.choice and Quot.sound. Direct checks of the exported public theorem passed with Lean, NanoDa and con-ron. Full hosted Palomar verification has not run, and no Palomar acceptance or external peer review is claimed.

With the pinned toolchain and dependencies available, run:

```sh
bash scripts/verify.sh
```

This builds the proof, prints the selected statements and their axioms, audits
local declarations, replays the proof dependencies in an empty Lean kernel, and
compares the separately elaborated Challenge and Solution types. On Linux,
`python3 scripts/check-export.py` reproduces the direct bundled-checker tests.
The GitHub workflow runs the full pinned Palomar mechanical preflight. A
successful mechanical preflight is separate from registry acceptance.

## Author and acknowledgements

Mathematical argument: Mark Lewko. Formalization author and maintainer: Mark Lewko. The author supplied the mathematical argument and directed the formalization. Codex assisted with Lean proof development, interface code and verification scripts. Reused proofs and definitions are credited separately in third_party/NOTICE.md.

The development uses Lean and mathlib, selected proofs by Scott McColm,
PrimeNumberTheoremAnd contributors including Robby Sneiderman, selected
transform and gamma proofs from Conor Grogan's repository, and IEANTN vocabulary
by Terence Tao and the IEANTN contributors. Exact source revisions, adaptations
and licenses are listed in [third_party/NOTICE.md](third_party/NOTICE.md).

## License

Original contributions are licensed under the GNU Affero General Public License, version 3 only (AGPL-3.0-only). Imported material retains its original licenses and attribution. The planned paper and unpublished proof notes are not included in this code license.
See [LICENSE](LICENSE) and the [AGPL-3.0-only license text](https://spdx.org/licenses/AGPL-3.0-only.html).
