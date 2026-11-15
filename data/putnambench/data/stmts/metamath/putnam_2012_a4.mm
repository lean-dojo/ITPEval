$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2012_a4: under the interval-length product bound, the integers in
  one interval whose r-multiples are congruent modulo q to an integer in a
  second interval form a finite arithmetic progression. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  A and B are the endpoints of the first real interval, while C and D are
  the endpoints of the second. The left side of the biconditional inlines
  the source definitions of T and S: x is an integer in [A,B], and there
  are integers b and m with b in [C,D] and r*x = b + m*q.

  On the right, 0 ..^ n is the n-element zero-based index set corresponding
  to Fin n in the primary Lean source. Thus a, the positive integer d, and
  n describe exactly the source finite arithmetic progression. All defining
  witnesses remain under their source quantifiers. The final declaration is
  a single unproved $a statement encoding; this database contains no $p
  proof declaration.
$)

${
  $d A B C D a b d i m n q r x $.

  putnambench-putnam-2012-a4 $a |-
    A. q e. ZZ A. r e. ZZ
      A. A e. RR A. B e. RR A. C e. RR A. D e. RR
        (
          (
            0 < q
            /\
            (
              A < B
              /\
              C < D
            )
          )
          ->
          (
            (
              ( B - A )
              x.
              ( D - C )
            )
            < q
            ->
            E. n e. NN0 E. a e. ZZ E. d e. NN
              A. x e. ZZ
                (
                  (
                    (
                      A <_ x
                      /\
                      x <_ B
                    )
                    /\
                    E. b e. ZZ E. m e. ZZ
                      (
                        (
                          C <_ b
                          /\
                          b <_ D
                        )
                        /\
                        ( r x. x )
                        =
                        (
                          b
                          +
                          ( m x. q )
                        )
                      )
                  )
                  <->
                  E. i e. ( 0 ..^ n )
                    x
                    =
                    (
                      a
                      +
                      ( i x. d )
                    )
                )
          )
        )
  $.
$}
