$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1985_a1: the number of ordered triples of subsets of
  {1, ..., 10} whose union is {1, ..., 10} and whose triple intersection
  is empty equals 2^10 * 3^10 * 5^0 * 7^0. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A source ordered triple (A1, A2, A3) is represented by set.mm's nested
  ordered pair <. <. A1 , A2 >. , A3 >. The three components range over the
  full power set of ( 1 ... 10 ). This is equivalent to the source's
  unrestricted-set formulation because union equal to ( 1 ... 10 ) forces
  each component to be a subset of that interval.

  The nested projections recover A1, A2, and A3. SetMM's # operator gives the
  finite cardinality of exactly the ordered triples satisfying the union and
  intersection conditions. The exponents are the explicit source solution
  (10, 10, 0, 0). The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  putnambench-putnam-1985-a1 $a |-
    (
      #
      `
      {
        t e.
          (
            ( ~P ( 1 ... ; 1 0 ) X. ~P ( 1 ... ; 1 0 ) )
            X.
            ~P ( 1 ... ; 1 0 )
          )
        |
        (
          (
            (
              ( 1st ` ( 1st ` t ) )
              u.
              ( 2nd ` ( 1st ` t ) )
            )
            u.
            ( 2nd ` t )
          )
          =
          ( 1 ... ; 1 0 )
          /\
          (
            (
              ( 1st ` ( 1st ` t ) )
              i^i
              ( 2nd ` ( 1st ` t ) )
            )
            i^i
            ( 2nd ` t )
          )
          =
          (/)
        )
      }
    )
    =
    (
      (
        ( 2 ^ ; 1 0 )
        x.
        ( 3 ^ ; 1 0 )
      )
      x.
      (
        ( 5 ^ 0 )
        x.
        ( 7 ^ 0 )
      )
    )
  $.
$}
