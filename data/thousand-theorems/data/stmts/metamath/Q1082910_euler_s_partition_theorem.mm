$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1082910
  (thousand-theorems__metamath__Q1082910), "Euler's partition theorem": for
  every natural number, the number of partitions into odd positive parts
  equals the number of partitions into distinct positive parts. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  A partition of m is represented by a finitely supported multiplicity
  function f : NN --> NN0 whose weighted sum is m. Its support is
  ( `' f " NN ), the positive part sizes having nonzero multiplicity.

  The left restricted set requires every supported part size to be odd,
  expressed as not divisible by two. The right restricted set requires every
  multiplicity to be at most one. Thus the two finite cardinalities encode
  Nat.Partition.odds N and Nat.Partition.distincts N, respectively.

  The declaration below is the single unproved $a corpus statement; it
  introduces no $p proof statement.
$)

${
  $d f g k m n $.

  thousand-theorems-q1082910-euler-partition $a
    |- A. m e. NN0
         (
           ( # `
             { g e.
               { f e. ( NN0 ^m NN ) |
                 ( ( `' f " NN ) e. Fin /\
                   ( sum_ k e. NN ( ( f ` k ) x. k ) ) = m
                 )
               } |
               A. n e. ( `' g " NN ) -. 2 || n
             }
           )
           =
           ( # `
             { g e.
               { f e. ( NN0 ^m NN ) |
                 ( ( `' f " NN ) e. Fin /\
                   ( sum_ k e. NN ( ( f ` k ) x. k ) ) = m
                 )
               } |
               A. n e. NN ( g ` n ) <_ 1
             }
           )
         )
  $.
$}
