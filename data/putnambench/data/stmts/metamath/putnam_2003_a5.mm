$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2003_a5: Dyck n-paths with no return of even length are in
  one-to-one correspondence with Dyck (n-1)-paths. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  For m e. NN0, the carrier 0 ..^ (2*m) is SetMM's canonical copy of
  Fin (2*m), and ZZ ^m (0 ..^ (2*m)) is the full set of integer-valued
  paths on that carrier. The range, total-sum, and prefix-sum conditions
  define Dyck paths exactly as in the primary formal source.

  On the left, i is the upstep immediately preceding a contiguous block of
  downsteps through j. Requiring the prefix sum through j to be zero makes
  that block a return, and 2 || (j-i) says that its length is even. Negating
  the existential condition therefore states that no return has even length.

  SetMM's equipollence relation ~~ means that a bijection exists between the
  two displayed path classes. The final declaration is the single unproved
  $a corpus statement; this database contains no $p proof statement.
$)

${
  $d i j k n p q $.

  putnambench-putnam-2003-a5 $a |- A. n e. NN
    (
      {
        p e. ( ZZ ^m ( 0 ..^ ( 2 x. n ) ) ) |
        (
          (
            (
              ran p C_ { -u 1 , 1 }
              /\
              (
                sum_ k e. ( 0 ..^ ( 2 x. n ) )
                  ( p ` k )
              )
              =
              0
            )
            /\
            A. j e. ( 0 ..^ ( 2 x. n ) )
              0
              <_
              (
                sum_ k e. ( 0 ... j )
                  ( p ` k )
              )
          )
          /\
          -.
          E. i e. ( 0 ..^ ( 2 x. n ) )
            E. j e. ( 0 ..^ ( 2 x. n ) )
              (
                i < j
                /\
                (
                  ( p ` i ) = 1
                  /\
                  (
                    A. k e. ( ( i + 1 ) ... j )
                      ( p ` k ) = ( -u 1 )
                    /\
                    (
                      2 || ( j - i )
                      /\
                      (
                        sum_ k e. ( 0 ... j )
                          ( p ` k )
                      )
                      =
                      0
                    )
                  )
                )
              )
        )
      }
      ~~
      {
        q e.
          (
            ZZ
            ^m
            ( 0 ..^ ( 2 x. ( n - 1 ) ) )
          )
        |
        (
          (
            ran q C_ { -u 1 , 1 }
            /\
            (
              sum_ k e. ( 0 ..^ ( 2 x. ( n - 1 ) ) )
                ( q ` k )
            )
            =
            0
          )
          /\
          A. j e. ( 0 ..^ ( 2 x. ( n - 1 ) ) )
            0
            <_
            (
              sum_ k e. ( 0 ... j )
                ( q ` k )
            )
        )
      }
    )
  $.
$}
