#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"
mkdir -p build
bash scripts/with-lean.sh lake --no-cache --wfail build MathCollab Solution DensityInterfaces.PositiveCount
bash scripts/with-lean.sh lake env lean -DwarningAsError=true ../scripts/InterfaceStatements.lean
bash scripts/with-lean.sh lake env lean -DwarningAsError=true ../scripts/InterfaceAudit.lean
bash scripts/with-lean.sh lake env lean -DwarningAsError=true ../scripts/InterfaceProofReplay.lean
bash scripts/with-lean.sh lake --no-cache build Challenge
bash scripts/with-lean.sh lake env lean --run ../scripts/InterfaceType.lean Challenge DensityThreeQuarters.density_bound > build/challenge-type.txt
bash scripts/with-lean.sh lake env lean --run ../scripts/InterfaceType.lean Solution DensityThreeQuarters.density_bound > build/solution-type.txt
cmp build/challenge-type.txt build/solution-type.txt
printf '%s\n' 'PASS: proof build, axiom checks, fresh replay and statement equality.'
