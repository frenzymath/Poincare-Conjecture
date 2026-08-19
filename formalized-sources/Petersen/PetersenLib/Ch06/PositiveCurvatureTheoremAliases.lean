import PetersenLib.Ch06.PositiveCurvatureTopology

/-!
# Petersen Ch. 6, section 6.5: public theorem names

The topology file contains the honest, data-driven cores for the section 6.5
statements.  This module publishes the names used by the chapter inventory as
aliases of those cores.  The aliases do not add axioms or hide the missing
geometric work: callers still supply the corresponding `*_Data` witness (for
example, the Morse deformation, covering, or holonomy construction).
-/

namespace PetersenLib

/-- Klingenberg's even-dimensional estimate, conditional on
`KlingenbergEvenDimData.noShortRadius` (the closed-parallel-field bridge is not
formalized yet). -/
alias klingenbergEvenDimInjectivity := klingenbergEvenDimInjectivity_of_data

/-- Morse-theoretic connectivity, conditional on an explicit
`MorseConnectivityData.deformation` witness. -/
alias morseTheoreticConnectivity := morseTheoreticConnectivity_of_data

/-- Submanifold index connectivity, conditional on the supplied path-space
index and Morse deformation data. -/
alias submanifoldIndexConnectivity := submanifoldIndexConnectivity_of_data

/-- Berger's sphere conclusion at the interface level; the curvature and
Morse deformation data remain explicit. -/
alias bergerSphereTheorem := bergerSphereTheorem_of_data

/-- Klingenberg's quarter-pinching injectivity estimate, conditional on the
positive-extension/no-short-radius witness in `KlingenbergPinchingData`. -/
alias klingenbergPinchingInjectivity := klingenbergPinchingInjectivity_of_data

/-- The Rauch--Berger--Klingenberg sphere core, conditional on both bundled
Berger and pinching data. -/
alias rauchBergerKlingenbergSphereTheorem :=
  rauchBergerKlingenbergSphereTheorem_of_data

/-- The Ricci/diameter simple-connectivity core, conditional on the explicit
loop-nullhomotopy witness in `RicciDiameterInjectivityData`. -/
alias ricciDiameterInjectivitySimplyConnected :=
  ricciDiameterInjectivitySimplyConnected_of_data

/-- Wilking's connectedness principle at the available interface boundary;
the totally-geodesic Morse deformations and intersection witness are required
as fields of `WilkingConnectednessData`. -/
alias wilkingConnectednessPrinciple := wilkingConnectednessPrinciple_of_data

end PetersenLib
