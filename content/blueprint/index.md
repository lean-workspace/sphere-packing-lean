---
title: "Sphere Packing blueprint"
description: "Companion blueprint for thefundamentaltheor3m/Sphere-Packing-Lean — reference chapters over the upstream Lean library, statuses computed from the kernel."
type: "blueprint-index"
tags:
  - "blueprint"
---

Companion blueprint for
[Sphere-Packing-Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean),
the Lean 4 formalization of Viazovska's solution to the sphere packing
problem in dimension 8.

The Lean code lives upstream and is pinned as a Lake dependency; chapters here
are reference chapters whose items point at upstream declarations with
`lean="..."`. Statuses, dependency edges, and source snippets are recomputed
from the compiled environment on every sync — nothing here is hand-maintained:

```bash
lake exe cache get        # prebuilt mathlib (upstream pins rev v4.30.0)
lake build +SpherePacking # compile the upstream library
npm run blueprint:sync    # extract kernel truth + regenerate the canvas
```

The original leanblueprint site remains at
[thefundamentaltheor3m.github.io/Sphere-Packing-Lean/blueprint](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/blueprint/).
This workspace starts with a scaffold chapter on sphere packings and their
density; the remaining chapters are being migrated.
