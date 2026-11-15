$(
  Statement-only formalization of PutnamBench artifact putnam_1964_b6:
  the closed unit disk in the real plane cannot be partitioned into two
  disjoint congruent subsets, where congruence is witnessed by a global
  distance-preserving self-map of the plane. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P64B6R2 is the real coordinate plane, P64B6Zero is its zero vector,
  P64B6Dist is Euclidean distance, and P64B6Disk is the closed unit disk.
  The source-defined disk and congruence predicate are inlined in the final
  assertion. A and B range over all subsets of the plane, while f ranges over
  all total plane self-maps and preserves distance for every pair of plane
  points. The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

$c P64B6I P64B6R2 P64B6Zero P64B6Dist P64B6Disk $.

p64b6-index-syntax $a class P64B6I $.
p64b6-plane-syntax $a class P64B6R2 $.
p64b6-zero-syntax $a class P64B6Zero $.
p64b6-distance-syntax $a class ( P64B6Dist A B ) $.
p64b6-disk-syntax $a class P64B6Disk $.

p64b6-index-definition $a |- P64B6I = ( 1 ... 2 ) $.

p64b6-plane-definition $a |- P64B6R2 = ( RR ^m P64B6I ) $.

p64b6-zero-definition $a |- P64B6Zero =
  ( j e. P64B6I |-> 0 )
$.

${
  $d A B j $.

  p64b6-distance-definition $a |- (
    P64B6Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P64B6I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.
$}

p64b6-disk-definition $a |- P64B6Disk = {
  x e. P64B6R2 |
    ( P64B6Dist P64B6Zero x ) <_ 1
} $.

${
  $d A B f v w $.

  putnambench-putnam-1964-b6 $a |- -.
    E. A e. ~P P64B6R2 E. B e. ~P P64B6R2
      E. f e. ( P64B6R2 ^m P64B6R2 )
        (
          (
            B = ( f " A )
            /\
            A. v e. P64B6R2 A. w e. P64B6R2
              ( P64B6Dist v w ) =
                ( P64B6Dist ( f ` v ) ( f ` w ) )
          )
          /\
          (
            ( A i^i B ) = (/)
            /\
            ( A u. B ) = P64B6Disk
          )
        )
  $.
$}
