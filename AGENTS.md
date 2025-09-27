# AGENTS.md

This project aims to formalize the KRIPKE GAME (by cannorin) and strategies against the game.

## The Rules of the KRIPKE GAME

### Overview

The game starts by fixing a finite Kripke frame of size n (= number of worlds), and discloses the number of edges in the accessibility relation to the player. The aim of the game is to identify the prepared frame (up to isomorphism) by asking a fixed number (N) of queries in the form of modal formulas.

In the current version of the game at https://www.cannorin.net/kripke, n=4, N=10 and `p`, `q`, `r`, `s` are the only propositional variables allowed in queries.

### Hidden target and visible state

There is an (unknown to the querying player) finite Kripke frame F with:

* A set of n worlds.
* An accessibility relation R ⊆ W × W.

Only two kinds of information about F become visible over the course of the game:
1. The cardinality |R| of the accessibility relation. This number is revealed at the very beginning and never changes.
2. A growing list of (query, answer) pairs, where a query is a modal formula, and the answer is a natural number k with 0 ≤ k ≤ n giving how many worlds of F satisfy that formula.

The visible game state therefore consists of:
```
	(relationEdgeCount, [(φ₁, k₁), (φ₂, k₂), ..., (φ_m, k_m)])
```
with m the number of queries already asked.

An initial visible state has an empty list of queries; only the edge count is known.

### Queries

On each move (provided we still have a query budget remaining) we may choose any modal formula φ built from the fixed set of variables (p, q, r, s in the official version of the game) using the usual connectives, verum/falsum and modal operators Box/Dia. We submit φ as a query.

The answer we immediately receive is the number of worlds in the hidden frame F that satisfy φ. The relation "satisfy" is the usual one for Kripke semantics of modal logic: Under a valuation `v: W × {P, Q, R, S} → bool` a world `w: W` satisfies
 - a propositional variable p if `v(w, P) == true`
 - ⊤ (verum) always
 - ⊥ (falsum) never
 - ¬φ if w does not satisfy φ
 - Box φ if all worlds v with (w,v) ∈ R satisfy φ
 - Dia φ if some world v with (w,v) ∈ R satisfies φ
 - φ ∧ ψ if w satisfies φ and w satisfies ψ
 - φ ∨ ψ if w satisfies φ or w satisfies ψ
 - φ → ψ if w does not satisfy φ or w satisfies ψ

and a world `w: W` satisfies `φ` if all `w` satisfies `φ` under all valuations `v`.

The visible game state is extended by cons-ing (φ, answer) onto the front of the list.

## Building the Project

Main proofs are in the `main-proofs` directory.

When `lake` is installed, run `lake build` in `main-proofs` to build the project. As an AI agent, however, you should always prefer to use the relevant MCP server for code analysis and generation, and only fallback to `lake build` when necessary.
