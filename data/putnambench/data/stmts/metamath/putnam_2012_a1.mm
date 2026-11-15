$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2012_a1: among any twelve real numbers in the open interval
  from one to twelve, three distinct indexed values satisfy the
  largest-side squared inequality for an acute triangle. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The index set 0 ... 11 has exactly the twelve members corresponding to
  Fin 12 in the Lean source and the bounded natural indices in the Isabelle
  source. Thus RR ^m ( 0 ... 11 ) is the class of all twelve-term
  real-valued families.

  The three indices remain internally existentially quantified and pairwise
  distinct. The two weak inequalities select d(k) as a largest side, while
  d(k)^2 < d(i)^2 + d(j)^2 is exactly the source's strict acute-triangle
  condition. The final declaration is a single unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

${
  $d d i j k $.

  putnambench-putnam-2012-a1 $a |-
    A. d e. ( RR ^m ( 0 ... ; 1 1 ) )
      (
        A. i e. ( 0 ... ; 1 1 )
          (
            1 < ( d ` i )
            /\
            ( d ` i ) < ; 1 2
          )
        ->
        E. i e. ( 0 ... ; 1 1 )
          E. j e. ( 0 ... ; 1 1 )
            E. k e. ( 0 ... ; 1 1 )
              (
                (
                  i =/= j
                  /\
                  (
                    i =/= k
                    /\
                    j =/= k
                  )
                )
                /\
                (
                  (
                    ( d ` i ) <_ ( d ` k )
                    /\
                    ( d ` j ) <_ ( d ` k )
                  )
                  /\
                  (
                    ( d ` k ) ^ 2
                  )
                  <
                  (
                    ( ( d ` i ) ^ 2 )
                    +
                    ( ( d ` j ) ^ 2 )
                  )
                )
              )
      )
  $.
$}
