$(
  Statement-only formalization of "The Partition Theorem (Euler)" from
  Hundred Theorems item 045: for every natural number, partitions into
  distinct positive parts and partitions into odd positive parts have equal
  cardinality. This file contains no proof.
$)

$[ library/set.mm $]

$(
  The included set.mm foundation supplies the natural-number classes NN and
  NN0, functions and application, finite sets, infinite and finite sums,
  divisibility, restricted set abstraction, and finite-set cardinality.

  A partition of N is represented by a function f : NN --> NN0. The set
  ( `' f " NN ) is its support: the positive part sizes assigned a positive
  multiplicity. Requiring this support to belong to Fin makes the
  multiplicity function finitely supported, and the sum condition says that
  the sum of each positive part times its multiplicity is N.

  The left restricted set consists of partitions whose multiplicities are at
  most one. The right restricted set consists of partitions whose supported
  part sizes are not divisible by two. The assertion is an unproved $a
  statement and adds no proof to the included foundation.
$)

hundred-theorems-045-euler-partition $a
  |- A. N e. NN0
       (
         ( # `
           { g e.
             { f e. ( NN0 ^m NN ) |
               ( ( `' f " NN ) e. Fin /\
                 ( sum_ k e. NN ( ( f ` k ) x. k ) ) = N
               )
             } |
             A. n e. NN ( g ` n ) <_ 1
           }
         )
         =
         ( # `
           { g e.
             { f e. ( NN0 ^m NN ) |
               ( ( `' f " NN ) e. Fin /\
                 ( sum_ k e. NN ( ( f ` k ) x. k ) ) = N
               )
             } |
             A. n e. ( `' g " NN ) -. 2 || n
           }
         )
       )
$.
