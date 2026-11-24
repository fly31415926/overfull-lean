# Independent semantic review of the native integration

Recorded at `2026-11-24T01:04:01.321002+00:00`. Contemporaneous source hashes and the files actually read are recorded in `integration-review-01.json`.

## Findings

No mathematical counterexample or circular assumption of the target edge-coloring was identified in the reviewed interfaces. This is a semantic review, not a substitute for the strict build or complete axiom audit.

### Weighted native seeds
 
Original h is retained. Odd primary seeds are injective with one seed per color, primary size at most two, actual star weight at most4b, hence at mosth/8 from128D<=h,b<=D; all-even seeds are empty. Reserved singleton/empty joining traces are exact.

### Available-color accounting
 
Remaining palettes exclude protected, joining-used and bundle-used colors. On those labels bundleClasses equals the actual JoiningPalette class, so inherited D-load and h/8-weight estimates apply without a global protected-class D-load assumption.

### Same-label growth
 
A bundle-used color is outside both remaining star palettes, so receives no star. Every other color contains no bundle and gains at most two star copies. Therefore max(3L,|Z|+1)+2 copies and2max(3L,|Z|+1)+4 support are justified.

### Uniform support instantiation
 
To reduce the native max support bound to6L+4, explicitly use|Z|<=2 and0<L. NativeCore.WeightedBudget proves the exact requested constants but does not itself establish this class inequality.

### Core load from actual host
 
For disjoint classes outside an embedded Core edge set, family support load is bounded by degree of their used union at the vertex. Complementary core degree equals h-d_core<=a, so coreFootprint_load_le_error gives global load<=a, including protected classes. This requires disjointness from the actual retained Core edge map, not merely a descriptive claim of being boundary copies.

### Native multiplicities
 
Weighted native constructors assume actual exception-to-core parallel-copy bounds. They cannot be inferred from joining-only D bounds alone. With z outside U, all z-v copies lie outside coreEdges C, hence their number is at most the core-complement incidence a; a natural floor choice and monotonicity to D provide the needed b. NativeCore.Incidence is to supply this step.

### Core parity
 
Covering all exceptional vertices makes uncovered assigned corePart exactly the uncovered original core. Matching cut parity then gives even uncovered core orders using separate source/current edge-copy types.

### Prefix versus factorization
 
Core completion constructs actual CorePacking objects and perfect matchings. Its q<=floor(h-gamma|U_i|) requirements leave a robust remainder and do not construct a full h-color factorization. The final prefix selection, preservation for the terminal phase, and terminal factorization remain to be instantiated.

### Uniform arithmetic
 
128*30=3840; gap>=h/4>=alpha*n/120. Twice-piece-count plus natural quotient gives support<=360delta*n/alpha+10, absorbed by delta<=epsilon*alpha/720 and n>=20/epsilon. Numerical load D+2b<=3delta*n is absorbed separately by delta<=epsilon/3.

## Pending at this snapshot

- NativeAssembly.NativeTwoStars had no completed focused receipt at review time.
- NativeAssembly.OtherCases latest attempt othercases-003 was running; only the visible single-exception/no-bundle statements reviewed.
- NativeCore.Incidence and NativeAssembly.SeparateStars appeared during review recording; their contents are not semantically certified by this first note.

The review makes no claim that these pending modules have completed verification. NativeTwoStars and OtherCases were under active development; the recorded hashes identify the worktree at report writing. Later source edits require reconciliation with this review.
