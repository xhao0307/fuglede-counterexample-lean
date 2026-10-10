# Third-party source notices

`CanonicalDefinitions.lean` adapts definitions and supporting proofs from Google DeepMind's Formal Conjectures repository, commit `a924684979d41f543898ec43b940b74e124315d9`, including `FormalConjecturesForMathlib/Analysis/Fourier/SpectralSets.lean` and `FormalConjectures/Wikipedia/Fuglede.lean`. The adapted names are enclosed in the `FugledeTarget` namespace and changes are identified in the source header.

Original source notice: **Copyright 2026 The Formal Conjectures Authors. Licensed under the Apache License, Version 2.0.**

The three local `UnitAddCircle` measure instances in each of `FourierCube.lean` and `CubeOrthogonality.lean` are adapted from Mathlib's `Mathlib/Analysis/Fourier/AddCircleMulti.lean`, commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. Their placement in the local proof namespaces is identified in the file headers.

Original portion notice: **Copyright (c) 2023 David Loeffler. All rights reserved. Authors: David Loeffler. Released under Apache 2.0 license.**

The full Apache 2.0 license is supplied in `Apache-2.0.txt`. These notices concern the identified adapted portions and do not select a license for the user's remaining original proof code. Imported Mathlib dependencies remain in their original repositories under their respective notices and licenses; they are not vendored here.

The mathematical construction is credited to Tao Zhang, arXiv:2607.15632v1. No paper text is redistributed as part of this project. `ATTRIBUTION.md` records detailed provenance and the limits of human contribution evidence.
