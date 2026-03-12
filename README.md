# lean-colored-coalgebras

Lean 4 formalization project for selected results and constructions from:

1. **R. M. Kaufmann and Y. Mo**, *Pathlike Co/Bialgebras and their Antipodes with Applications to Bi- and Hopf Algebras Appearing in Topology, Number Theory and Physics*, **SIGMA** 18 (2022), 053, 42 pages.  
   DOI: https://doi.org/10.3842/SIGMA.2022.053  
   arXiv preprint: https://arxiv.org/abs/2104.08895
2. **Y. Mo**, *The structure of simply colored coalgebras*, in *Higher Structures in Topology, Geometry, and Physics*, Contemporary Mathematics **802**, American Mathematical Society, 2024.  
   Volume DOI: https://doi.org/10.1090/conm/802  
   arXiv preprint: https://arxiv.org/abs/2301.08462

## What this repository is doing

- Formalizing as much of the algebraic/categorical content of these papers as feasible in Lean 4.
- Prioritizing colored coalgebras and related constructions first.
- Adding auxiliary structures (for example, Rota-Baxter operators) when useful for the development.

## Current scope

- Focus on colored coalgebras and related algebraic constructions.
- Not attempting a full formalization of higher-categorical/Feynman-category parts yet.
- Profunctor/endoprofunctor draft work lives in the separate `DraftProfunctor` library.

## Reference for auxiliary Rota-Baxter development

- Li Guo, *What is a Rota-Baxter algebra?*, Notices of the AMS 56 (2009), 1436-1437.
  https://www.ams.org/notices/200911/rtx091101436p.pdf
