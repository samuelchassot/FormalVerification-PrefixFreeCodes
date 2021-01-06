# FormalVerification-PrefixFreeCodes

## Abstract
Prefix-free codes are widely used in communication systems, e.g. in compression algorithms combined with Huffman's algorithm. In this work, we propose an implementation in the Scala programming language of an encoder decoder pair as well as a naive prefix-free code generator. Such implementations can be critical due to the fundamental role they play. Therefore, our implementations are formally proven for correctness thanks to the verification framework Stainless \cite{stainless}. Those three functions can be chained to form a pipeline as a whole on a given input string `s`, i.e. generate a correspoding prefix-free code `c`, use `c` to encode `s` as `e` and finally decode `e` with `c` as `d`. Correctness is therefore defined as `s == d`.

## Depedencies
- Scala
- Stainless

## How to run
1. Run ```stainless --solvers=smt-z3 PrefixFreeCodes.scala``` in the `code` directory
2. Check that everything is valid
