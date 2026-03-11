## Project purpose
This repository formalizes parts of the following papers in Lean 4:

1. Path-like bialgebras and antipodes
   https://arxiv.org/abs/2104.08895

2. The structure of simply colored coalgebras
   https://arxiv.org/abs/2301.08462

## Current scope
Focus on colored coalgebras and related categorical/algebraic constructions.
Do not attempt a full formalization of Feynman categories yet.

## Core policy
Before implementing any construction, check whether mathlib already provides it.
Reuse mathlib whenever possible.
Introduce custom definitions only for paper-specific notions.

## Development style
Prefer small, compilable changes.
Prefer structures over typeclasses for project-specific objects.
Record major design decisions in DESIGN.md.
Do not silently add assumptions to force proofs through.
When blocked, explain whether the issue is mathematical, API-related, or due to Lean engineering.
