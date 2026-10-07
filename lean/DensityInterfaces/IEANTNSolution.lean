module
public import IEANTN.Nodes.DensityThreeQuarters.v1.Conclusions
public import DensityInterfaces.IEANTNAdapter

@[expose] public section

theorem DensityThreeQuarters.v1.challenge_density_bound :
    DensityThreeQuarters.v1.density_bound := by
  intro σ ε hσ hε
  exact DensityInterfaces.ieantn_density_bound hσ hε
