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

The mathematics is the work of the upstream project by Christopher Birkbeck,
Sidharth Hariharan, Seewoo Lee, Gareth Ma, Bhavik Mehta, and Maryna
Viazovska — kickstarted at EPFL by Maryna Viazovska and Sidharth Hariharan
in March 2024. The prose here is converted from the upstream LaTeX sources
(Apache-2.0).

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
All 8 chapters are migrated as native chapters (141 items), from sphere
packings and the $E_8$ lattice through the modular-form construction of the
magic function.
