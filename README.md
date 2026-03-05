# ANT: Algebraic Number Theory in Lean

A Lean 4 formalization of algebraic number theory, focusing on ideal theory in the quadratic integer ring Z[sqrt(-5)].

## Main Results

- **Ideal factorizations**: Formal proofs of the factorizations of (2), (3), (1 + sqrt(-5)), and (1 - sqrt(-5)) into products of prime ideals in Z[sqrt(-5)].
- **Primality proofs**: The ideals (2, 1 + sqrt(-5)), (3, 1 + sqrt(-5)), and (3, 1 - sqrt(-5)) are prime.
- **Ramification and inertia calculations**: Computation of ramification indices e(P|p) and inertia degrees f(P|p) for the primes lying above 2 and 3.

## Integration

This project has been integrated into the [QuadraticNumberFields](https://github.com/FrankieeW/QuadraticNumberFields) project, which provides a broader framework for formalizing results about quadratic number fields.

## Building

From the project root:

```sh
lake build
```
