export const stages = [
  {
    id: "flow",
    number: "1",
    title: "Flow and curvature control",
    color: "#1f4b99",
  },
  {
    id: "analysis",
    number: "2",
    title: "Geometric analysis",
    color: "#5b3fa3",
  },
  {
    id: "models",
    number: "3",
    title: "Singularity models",
    color: "#147357",
  },
  {
    id: "surgery",
    number: "4",
    title: "Surgery and extinction",
    color: "#b45309",
  },
  {
    id: "topology",
    number: "5",
    title: "Smooth reconstruction",
    color: "#18356f",
  },
  {
    id: "smoothing",
    number: "6",
    title: "Topological conclusion",
    color: "#8b3c55",
  },
];

const proof = "PoincareConjecture";

export const nodes = [
  {
    id: "ricci-flow",
    stage: "flow",
    title: "Ricci flow",
    subtitle: "Hamilton's evolution equation",
    formula: String.raw`\partial_t g=-2\operatorname{Ric}(g)`,
    visual: "sphere",
    layout: { column: "3 / span 4", row: "1" },
    summary:
      "Replace the fixed metric by a parabolic evolution that smooths geometry while recording curvature concentration.",
    statement:
      "Every smooth metric on a closed manifold starts a unique Ricci flow for a short time. If the curvature stays bounded up to a finite time, the solution extends beyond that time.",
    mechanism: [
      "The Ricci tensor is invariant under diffeomorphisms, so the equation is only weakly parabolic. The DeTurck gauge adds a Lie derivative term, producing a strictly parabolic system that can be solved and then pulled back.",
      "Curvature satisfies reaction-diffusion equations. Maximum principles turn these equations into quantitative bounds and preserved curvature conditions.",
      "Parabolic rescaling magnifies regions of large curvature. Compactness theorems then make possible the study of limits near singularities.",
    ],
    role:
      "This supplies the dynamical setting. Every later estimate is designed either to understand a singularity of this equation or to restart the equation after surgery.",
    theorem: {
      project: proof,
      label: "thm:rf-local",
      title: "Local existence and uniqueness (Hamilton)",
    },
  },
  {
    id: "pinching",
    stage: "flow",
    title: "Hamilton-Ivey pinching",
    subtitle: "Negative curvature becomes negligible",
    formula: String.raw`R\to\infty\quad\Longrightarrow\quad \nu/R\to 0`,
    visual: "pinch",
    layout: { column: "8 / span 5", row: "1" },
    summary:
      "In dimension three, regions of very large curvature become almost nonnegatively curved after rescaling.",
    statement:
      "The least eigenvalue of the curvature operator obeys a logarithmic lower bound in terms of scalar curvature. Consequently, blow-up limits at singular points have nonnegative curvature operator.",
    mechanism: [
      "Write the curvature operator through its three eigenvalues and use their coupled reaction-diffusion inequalities.",
      "Construct a time-dependent convex pinching region in eigenvalue space. The tensor maximum principle prevents the curvature operator from leaving it.",
      "At scales where scalar curvature diverges, the permitted negative eigenvalue is lower order. Rescaled limits therefore inherit nonnegative sectional curvature.",
    ],
    role:
      "Nonnegative curvature is the rigidity input behind the classification of ancient blow-up limits and the neck-or-cap description of singular regions.",
    theorem: {
      project: proof,
      label: "thm:rf-pinching",
      title: "Pinching toward positive curvature",
    },
  },
  {
    id: "reduced-volume",
    stage: "analysis",
    title: "Reduced length and volume",
    subtitle: "A monotone quantity looking backward in time",
    formula: String.raw`\widetilde V(\tau)=\int (4\pi\tau)^{-3/2}e^{-\ell}\,d\mu`,
    visual: "hourglass",
    layout: { column: "2 / span 4", row: "2" },
    summary:
      "Perelman's space-time distance produces a scale-invariant volume that cannot increase backward from a base point.",
    statement:
      "The reduced volume is monotone in backward time and is bounded above by its Euclidean value. Equality forces the corresponding flow to be the flat Gaussian model.",
    mechanism: [
      "Minimize the L-length, a curvature-corrected energy for curves moving backward through the evolving metric, and normalize it to obtain the reduced distance.",
      "A second-variation inequality controls the Jacobian of the L-exponential map. Combined with the evolution of the volume form, this makes the reduced-volume density monotone along minimizing L-geodesics.",
      "Integration gives a global monotonicity formula that survives parabolic rescaling, making it suited to singularity analysis.",
    ],
    role:
      "The reduced volume detects a forbidden loss of volume at the curvature scale and is the key analytic input to no local collapsing.",
    theorem: {
      project: proof,
      label: "thm:m10-reduced-volume",
      title: "Monotonicity of reduced volume",
    },
  },
  {
    id: "noncollapsing",
    stage: "analysis",
    title: "No local collapsing",
    subtitle: "Curvature control forces volume control",
    formula: String.raw`|\operatorname{Rm}|\le r^{-2}\quad\Longrightarrow\quad \operatorname{Vol}B(x,r)\ge\kappa r^3`,
    visual: "balls",
    layout: { column: "6 / span 4", row: "2" },
    summary:
      "A region cannot become arbitrarily thin while its curvature remains controlled at the same scale.",
    statement:
      "On a fixed time interval, a compact three-dimensional Ricci flow is kappa-noncollapsed at every sufficiently small scale, with kappa depending only on the initial data and the interval.",
    mechanism: [
      "Assume that controlled-curvature balls collapse and choose an almost-minimal collapsing scale.",
      "Rescale that ball to unit size. Collapsing would force its reduced volume to be very small, while monotonicity transports a definite lower bound from a regular earlier scale.",
      "The contradiction supplies both a volume lower bound and, through comparison geometry, an injectivity-radius lower bound needed for smooth compactness.",
    ],
    role:
      "This prevents blow-up sequences from degenerating dimensionally. Singular rescalings therefore converge to genuine complete three-dimensional models.",
    theorem: {
      project: proof,
      label: "thm:m15-noncollapse",
      title: "Kappa-non-collapsing for generalized Ricci flows",
    },
  },
  {
    id: "kappa-solutions",
    stage: "analysis",
    title: "Kappa-solutions",
    subtitle: "Ancient models of singularities",
    formula: String.raw`t\in(-\infty,0],\qquad \operatorname{Rm}\ge 0`,
    visual: "models",
    layout: { column: "10 / span 4", row: "2" },
    summary:
      "Blowing up around points of unbounded curvature yields ancient, noncollapsed flows with nonnegative curvature.",
    statement:
      "A three-dimensional kappa-solution is a complete ancient Ricci flow with bounded nonnegative curvature, positive scalar curvature, and kappa-noncollapsing. Such solutions form a compact family after normalization and have tightly constrained geometry.",
    mechanism: [
      "Hamilton-Ivey pinching gives nonnegative curvature in the limit, while no local collapsing gives the injectivity radius required for Hamilton compactness.",
      "Reduced-volume limits produce asymptotic shrinking solitons. Splitting and soliton classification restrict the possible geometries at infinity.",
      "A point in a noncompact model is either in a quantitatively round neck or lies in a bounded cap core; compact models are controlled positively curved components.",
    ],
    role:
      "Kappa-solutions are not arbitrary examples. They are the universal local models that every sufficiently high-curvature region must resemble.",
    theorem: {
      project: proof,
      label: "thm:ancient-compactness",
      title: "Compactness of based three-dimensional kappa-solutions",
    },
  },
  {
    id: "canonical-neighborhoods",
    stage: "models",
    title: "Canonical neighborhoods",
    subtitle: "Every singular region is a neck, cap, or round component",
    formula: String.raw`R(x,t)\gg 1\quad\Longrightarrow\quad U_{x,t}\approx U_{\kappa\text{-solution}}`,
    visual: "canonical",
    layout: { column: "4 / span 7", row: "3" },
    summary:
      "At the curvature scale, every sufficiently singular point belongs to a short list of controlled geometric models.",
    statement:
      "For fixed small epsilon, sufficiently high-curvature points have a canonical neighborhood: a strong epsilon-neck, a controlled epsilon-cap, or a compact positively curved component.",
    mechanism: [
      "If the assertion failed, select points of increasing curvature where no canonical neighborhood exists and rescale each point to scalar curvature one.",
      "Pinching, noncollapsing, curvature control at bounded distance, and Hamilton compactness produce a kappa-solution limit.",
      "The qualitative structure theorem for kappa-solutions gives a neck, cap, or compact model at the limit point. Stability under smooth convergence transfers that model back to the original flow, a contradiction.",
    ],
    role:
      "This converts an uncontrolled analytic singularity into recognizable geometry. In particular, sufficiently thin horns contain standard necks on which surgery can be performed.",
    theorem: {
      project: proof,
      label: "thm:neck-cap-canonical",
      title: "Existence of canonical neighborhoods",
    },
  },
  {
    id: "surgery",
    stage: "surgery",
    title: "Ricci flow with surgery",
    subtitle: "Cut standard necks and insert controlled caps",
    formula: String.raw`S^2\times(-L,L)\ \rightsquigarrow\ B^3\sqcup B^3`,
    visual: "surgery",
    layout: { column: "2 / span 4", row: "4" },
    summary:
      "Remove the part of the manifold beyond selected thin necks, cap the new spherical boundaries, and restart the flow.",
    statement:
      "At a singular time, one can choose disjoint strong delta-necks, cut along their central two-spheres, and glue in standard caps while preserving the required curvature pinching and scale estimates.",
    mechanism: [
      "Canonical neighborhoods locate long horns, and a neck-selection argument chooses cross-sections at a controlled surgery scale.",
      "A rotationally symmetric cap metric interpolates between the cylindrical neck and a smooth tip. Its curvature is computed explicitly to preserve the pinching inequalities.",
      "Components whose geometry is already completely understood may be discarded. The remaining capped manifold provides new smooth initial data for Ricci flow.",
    ],
    role:
      "Surgery removes only geometrically standard high-curvature regions. Its topological effect is explicit, so the original manifold can later be reconstructed from the pieces that disappear.",
    theorem: {
      project: proof,
      label: "thm:metric-surgery",
      title: "The surgery operation at a singular time",
    },
  },
  {
    id: "surgery-control",
    stage: "surgery",
    title: "A priori estimates after surgery",
    subtitle: "The construction can be repeated",
    formula: String.raw`\text{pinching}+\kappa\text{-noncollapse}+\text{canonical neighborhoods}`,
    visual: "cap",
    layout: { column: "6 / span 4", row: "4" },
    summary:
      "Fresh caps remain close to the standard solution, while noncollapsing and canonical-neighborhood estimates persist uniformly.",
    statement:
      "For successively chosen control parameters, a controlled Ricci flow with surgery can always be extended to the next time interval; surgery times are discrete and the process continues for all time unless the manifold becomes empty.",
    mechanism: [
      "After rescaling, a newly inserted cap stays close for a definite time to the standard cap solution, so it cannot immediately create an unknown singularity.",
      "A reduced-length argument adapted to paths avoiding surgery regions restores kappa-noncollapsing for the surgery flow.",
      "Contradiction blow-ups re-establish canonical neighborhoods at each stage. Quantized volume loss and the parameter hierarchy prevent surgery times from accumulating.",
    ],
    role:
      "These estimates close the induction. Surgery is not a one-time repair: it defines a globally controlled evolution whose topology can be followed until extinction.",
    theorem: {
      project: proof,
      label: "thm:global-controlled-flow",
      title: "Controlled Ricci flow with surgery extends for all time",
    },
  },
  {
    id: "extinction",
    stage: "surgery",
    title: "Finite-time extinction",
    subtitle: "A topological width cannot survive forever",
    formula: String.raw`D^+W(t)\le -4\pi+\frac{3}{4(t+C)}W(t)`,
    visual: "extinction",
    layout: { column: "10 / span 4", row: "4" },
    summary:
      "Min-max areas attached to nontrivial homotopy decrease too quickly for a relevant component to persist indefinitely.",
    statement:
      "The constructed controlled surgery flow from a closed simply connected smooth three-manifold becomes empty at an actual finite surgery event. The argument retains the initial homotopy class and its component ancestry throughout the flow.",
    mechanism: [
      "When pi_2 is nontrivial, minimize the maximal area in a nontrivial family of two-spheres. Minimal-surface variation under Ricci flow supplies a negative topological term in its upper derivative.",
      "After essential two-spheres disappear, a nontrivial pi_3 class is encoded by a family of loops and spanning disks. Curve shortening and disk-area estimates give the analogous decay inequality for this second width.",
      "Surgery does not increase the relevant width. The differential inequalities force a positive width to cross zero in finite time, which is impossible; hence no component remains.",
    ],
    role:
      "Extinction turns the analytic evolution into a finite topological history: every initial component is eventually accounted for by surgeries and standard discarded pieces.",
    theorem: {
      project: proof,
      label: "prop:v4-global-extinction",
      title: "Finite-time extinction for Ricci flow with surgery",
    },
  },
  {
    id: "space-forms",
    stage: "topology",
    title: "Spherical space-form decomposition",
    subtitle: "Read the topology backward through surgery",
    formula: String.raw`M\cong\#(S^3/\Gamma)\ \#\ \#(S^2\text{-bundles over }S^1)`,
    visual: "spaceform",
    layout: { column: "3 / span 5", row: "5" },
    summary:
      "Tracking every cut and discarded component expresses the original manifold as a connected sum of standard pieces.",
    statement:
      "The initial manifold is reconstructed by a finite smooth connected-sum assembly of the exact non-survivor pieces in its surgery history. Each piece retains its event and its geometric classification.",
    mechanism: [
      "Cutting a neck corresponds to cutting along an embedded two-sphere. Depending on whether that sphere separates, the operation records a connected-sum splitting or an S^2-bundle factor.",
      "Discarded positively curved components are spherical space forms; the other allowed discarded components are explicit S^2-bundle or connected-sum types.",
      "Because extinction leaves the empty manifold, downward induction through the finite surgery history reconstructs the initial manifold entirely from these standard factors.",
    ],
    role:
      "This is where geometry returns to topology. The Ricci-flow analysis provides a controlled decomposition rather than directly identifying the original manifold.",
    theorem: {
      project: proof,
      label: "prop:connected-sum-reconstruction",
      title: "Finite reverse-history reconstruction",
    },
  },
  {
    id: "smooth-poincare",
    stage: "topology",
    title: "Smooth Poincaré theorem",
    subtitle: "The simply connected special case",
    formula: String.raw`\pi_1(M)=1\quad\Longrightarrow\quad M\cong S^3`,
    visual: "final-sphere",
    layout: { column: "9 / span 5", row: "5" },
    summary:
      "Simple connectivity eliminates every nontrivial factor in the space-form decomposition.",
    statement:
      "Every closed simply connected smooth three-manifold is diffeomorphic, and hence homeomorphic, to the three-sphere.",
    mechanism: [
      "Van Kampen identifies the fundamental group of a connected sum as the free product of the fundamental groups of its summands.",
      "An S^2-bundle over S^1 contributes an infinite cyclic factor. A nontrivial spherical space form S^3/Gamma contributes the nontrivial finite group Gamma.",
      "If the full fundamental group is trivial, all those factors are excluded. Only S^3 summands remain, and a connected sum of copies of S^3 is again S^3.",
    ],
    role:
      "This proves the smooth endpoint for the same initial manifold reconstructed from the surgery history. Compatible smoothing then removes the original smoothness assumption.",
    theorem: {
      project: proof,
      label: "thm:sphere-smooth-endpoint",
      title: "Smooth Poincaré theorem",
    },
  },
  {
    id: "compatible-smoothing",
    stage: "smoothing",
    title: "Compatible smoothing",
    subtitle: "From topological charts to a smooth model",
    formula: String.raw`M\cong M_{\mathrm{sm}}`,
    visual: "spaceform",
    summary:
      "A compact topological three-manifold admits a compatible smooth model, independently of simple connectivity.",
    statement:
      "Every nonempty connected compact Hausdorff second-countable topological three-manifold has a homeomorphic smooth three-manifold model.",
    mechanism: [
      "Protected compact cores and the relative topological results support straightening in each chart-handle index.",
      "Finite supported atlas straightening constructs a finite geometric triangulation with compatible affine stars.",
      "Cairns smoothing of that triangulation gives the smooth model and the homeomorphism back to the original carrier.",
    ],
    role:
      "This is a separate topological branch. It transports compactness and simple connectivity to the chosen smooth model without assuming a smooth atlas on the original manifold.",
    theorem: {
      project: proof,
      label: "thm:m76",
      title: "Compatible smoothing of topological three-manifolds",
    },
  },
  {
    id: "poincare",
    stage: "smoothing",
    title: "Poincaré conjecture",
    subtitle: "The topological three-dimensional theorem",
    formula: String.raw`\pi_1(M)=1\quad\Longrightarrow\quad M\cong S^3`,
    visual: "final-sphere",
    summary:
      "Combine the smooth theorem with compatible smoothing to identify the original topological manifold with the three-sphere.",
    statement:
      "Every compact Hausdorff second-countable simply connected topological three-manifold is homeomorphic to the standard three-sphere.",
    mechanism: [
      "Choose the compatible smooth model and transport compactness and simple connectivity through its homeomorphism.",
      "Apply the smooth Poincaré theorem to obtain a diffeomorphism from that model to the standard three-sphere.",
      "Forget smoothness and compose the two homeomorphisms. The conclusion is about the original topological manifold.",
    ],
    role:
      "This is the public topological endpoint proved by PoincareMT.topologicalPoincareSkeleton, alongside the separate smooth endpoint.",
    theorem: {
      project: proof,
      label: "thm:topological-endpoint",
      title: "Poincaré conjecture",
    },
  },
];

export const edges = [
  { from: "ricci-flow", to: "pinching", label: "curvature evolution" },
  { from: "ricci-flow", to: "reduced-volume", label: "space-time geometry" },
  { from: "reduced-volume", to: "noncollapsing", label: "monotonicity" },
  { from: "pinching", to: "kappa-solutions", label: "nonnegative limits" },
  { from: "noncollapsing", to: "kappa-solutions", label: "compact blow-ups" },
  { from: "kappa-solutions", to: "canonical-neighborhoods", label: "model structure" },
  { from: "canonical-neighborhoods", to: "surgery", label: "find necks" },
  { from: "canonical-neighborhoods", to: "surgery-control", label: "local control" },
  { from: "surgery", to: "surgery-control", label: "restart" },
  { from: "noncollapsing", to: "surgery-control", label: "volume control" },
  { from: "surgery-control", to: "extinction", label: "global evolution" },
  { from: "surgery", to: "space-forms", label: "topology of cuts" },
  { from: "extinction", to: "space-forms", label: "finite history" },
  { from: "space-forms", to: "smooth-poincare", label: "trivial fundamental group" },
  { from: "smooth-poincare", to: "poincare", label: "smooth endpoint" },
  { from: "compatible-smoothing", to: "poincare", label: "transport and compose" },
];

export function theoremHref(theorem) {
  return `../#/${theorem.project}#${encodeURIComponent(theorem.label)}`;
}
