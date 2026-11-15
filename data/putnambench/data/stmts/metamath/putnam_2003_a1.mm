$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2003_a1: the number of nondecreasing decompositions of a positive
  integer whose largest part is at most one above the smallest is the integer
  itself. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A decomposition with k parts is represented by a function a from the
  one-based finite interval 1 ... k to NN. This is in bijection with the
  zero-based Fin k families and the finite lists in the ground-truth sources.
  Since every such function is a subset of NN X. NN, the surrounding power
  set is only a set-sized ambient carrier and imposes no additional bound.

  The finite sum gives n, the half-open interval 1 ..^ k indexes exactly the
  adjacent pairs, and the final inequality bounds the largest part by the
  smallest plus one. Distinct lengths give functions with distinct domains,
  so the restricted class counts exactly the requested decompositions. The
  right side inlines the explicit solution function from the Rocq source.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a i k n $.

  putnambench-putnam-2003-a1 $a |- A. n e. NN
    (
      (
        #
        `
        {
          a e. ~P ( NN X. NN )
          |
          E. k e. NN
            (
              a e. ( NN ^m ( 1 ... k ) )
              /\
              (
                (
                  sum_ i e. ( 1 ... k )
                    ( a ` i )
                )
                =
                n
                /\
                (
                  A. i e. ( 1 ..^ k )
                    ( a ` i ) <_ ( a ` ( i + 1 ) )
                  /\
                  ( a ` k ) <_ ( ( a ` 1 ) + 1 )
                )
              )
            )
        }
      )
      =
      n
    )
  $.
$}
