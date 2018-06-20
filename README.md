# SCTLProV

This repository includes three version of the SCTLProV prover, the difference of these three versions is the input language:

* The ordinary version, which accepts the full input language of SCTLProV, which is specified in `./docs/language_specification.md`.

  This version is compiled by `make all`.
* The optimized version which can perform some optimizations that cannot be used generally, but can be used when dealing specific kind of input files. This version of SCTLProV accepts a restricted version of the input language:
    - No definition of types, values, or functions;
    - Data types can only have fixed ranges: booleans and scalars.
  
  The main optimization of this version is the representation of states: since both the number of state variables and the value range of each state variable are both fixed, we can represent each state by a int array (or a boolean array). Moreover, a set of int or boolean arrays can also be represented by a Binary Decision Diagram.

  This kind of optimizations is more cache-friendly in practice, and the optimized version is usually more faster than the ordinary version.

  When using this version only, compile with `make opt`.

* The bcg version, which prove the existence of deadlocks or livelocks of BCG files.

  When using this version only, compile with `make bcg`.

The way of the invokation of these three versions is as follows.

![sctlprov](sctlprov.png)

## Input Language
See `./docs/language_specification.md`.

## Compiling and Running
See `./docs/compiling_running.md`.

## Testing
See [this repository](https://github.com/sctlprov/sctlprov_testing).