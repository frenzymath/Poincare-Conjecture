# Shared notation and chapter contracts

This is authoring metadata, not text to reproduce in the book. Read
`outline-v4.md` for the chapter scope. Each draft may discover missing
dependencies; report them with a proposed owner before assuming them.

- `M` is the original closed three-manifold; `S^3` is the standard unit
  three-sphere. Specify topological and smooth hypotheses separately.
- `g_0` is a chosen normalized metric. On an ordinary interval write `g(t)`
  for Ricci flow, with `partial_t g = -2 Ric`. State sign and norm conventions.
- A single surgery flow has slices `M_t`, a time-zero identification with
  `M`, and events `t_j`; distinguish incoming and outgoing slices explicitly.
  Do not silently replace the flow, component, or metric in a later argument.
- Write `R`, `Rm`, and `R_min` for scalar, full curvature and scalar infimum.
  State the dimension and the relevant compactness/completeness hypothesis
  of every estimate. Constants must retain the formal quantifier order.
- Use `L`, `ell`, and `V_red` for backward action, reduced length and reduced
  volume. The actual reduced-volume normalization has Euclidean value
  `(4*pi)^(n/2)`; do not insert a normalized factor without changing every
  downstream formula and explicitly explaining the conversion.
- Let `Lambda^1 M` be the actual C1 free-loop space. A raw family
  `F:S^2 -> Lambda^1 M` is pointwise nullhomotopic. Define the fixed model
  sphere and based/free identification once in `filling-width`.
- `A_g(gamma)` is filling area, `W_g(F)` the supremum over one family, and
  `W_g[F]` the infimum over its free-class competitors. A based class label
  uses the fixed identification; it must not alter the competitor set.
- Use `rho` for the product-circle circumference in ramps, `u` for slope,
  `H` for curvature vector, and `Theta` for total curvature. Continuation
  for fixed `rho` and estimates uniform in `rho` are different assertions.
- The extinction profile and scalar clock must match the actual sources.
  On the normalized clock the comparison RHS is
  `-2*pi + 3*z/(1+4*t)`. Other clock origins require an explicit conversion.
- A connected-sum assembly includes collared balls and gluing maps. Keep
  the finite event/factor indexing in the narrative only to the extent
  needed to identify the actual factors and justify induction.
- In the smoothing chapters use `A` for a protected compact set, `R` for a
  PL domain only within those chapters, and `K` for a compact core. Define
  one simply connected end using the two compact sets in the source; do
  not replace it by simple connectedness of a single complement.
- A compatible smoothing consists of a smooth model `N` and a specified
  homeomorphism `h:M -> N`. Transport hypotheses through this same `h`.

Cross-chapter references use stable labels proposed by their owning authors.
Until the target exists, record the full mathematical input in the review
artifact rather than cite an invented theorem number. New authors draft in
`blueprint-publication/drafts/KEY.tex`; they do not edit shared macros,
bibliography, content order, inventories or another chapter. The existing
six chapter owners may retain their previous legacy-file corrections.

Each `inventory/reviews/KEY-v4.json` must record: source revision; sections;
Lean declarations and paths; definitions and hypotheses checked; substantive
proof mechanisms; exact external source locators; cross-chapter inputs and
outputs; background/helper classification with justification; unresolved
issues; and source/readability review status. A pending item makes the draft
pending. Main-agent acceptance is a separate decision.
