$(
  Statement-only formalization of Thousand Theorems corpus artifact Q5566491
  (thousand-theorems__metamath__Q5566491), "Glaisher's theorem": for every
  nonnegative integer and every positive integer M, the number of partitions
  with no part divisible by M equals the number of partitions in which every
  part occurs fewer than M times. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A partition of q is represented by a finitely supported multiplicity
  function f : NN --> NN0 whose weighted sum is q. Its support
  ( `' f " NN ) is exactly the set of positive part sizes occurring in the
  partition.

  On the left, no supported part size is divisible by m. On the right, every
  positive part size has multiplicity strictly below m; outside the support
  the multiplicity is zero, and m is positive. These are respectively
  Nat.Partition.restricted q (not m divides .) and
  Nat.Partition.countRestricted q m.

  The declaration below is the single unproved $a corpus statement. This file
  introduces no $p proof statement.
$)

${
  $d f g k m n q $.

  thousand-theorems-q5566491-glaisher $a
    |- A. q e. NN0
         A. m e. NN
           (
             ( # `
               { g e.
                 { f e. ( NN0 ^m NN ) |
                   ( ( `' f " NN ) e. Fin /\
                     ( sum_ k e. NN ( ( f ` k ) x. k ) ) = q
                   )
                 } |
                 A. n e. ( `' g " NN ) -. m || n
               }
             )
             =
             ( # `
               { g e.
                 { f e. ( NN0 ^m NN ) |
                   ( ( `' f " NN ) e. Fin /\
                     ( sum_ k e. NN ( ( f ` k ) x. k ) ) = q
                   )
                 } |
                 A. n e. NN ( g ` n ) < m
               }
             )
           )
  $.
$}
