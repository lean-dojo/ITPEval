$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1970_b5: a real function is continuous exactly when every
  natural-level clamp composed with it is continuous. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  P70B5Ramp is the integer-indexed family of real clamp functions from the
  sources. Its nested conditional gives -n on x <= -n, gives x on
  -n < x <= n, and gives n otherwise. The final assertion quantifies over
  every total real function F and uses membership in ( RR -cn-> RR ) for
  global continuity.

  The ramp definition and final corpus statement are unproved $a
  declarations; this database contains no $p proof statement.
$)

$c P70B5Ramp $.

p70b5-ramp-syntax $a class P70B5Ramp $.

${
  $d n x $.

  p70b5-ramp-definition $a |- P70B5Ramp =
    (
      n e. ZZ |->
        (
          x e. RR |->
            if (
              x <_ ( -u n ) ,
              ( -u n ) ,
              if (
                ( ( -u n ) < x /\ x <_ n ) ,
                x ,
                n
              )
            )
        )
    )
  $.
$}

${
  $d F n $.

  putnambench-putnam-1970-b5 $a |-
    A. F e. ( RR ^m RR )
      (
        F e. ( RR -cn-> RR )
        <->
        A. n e. NN0
          ( ( ( P70B5Ramp ` n ) o. F ) e. ( RR -cn-> RR ) )
      )
  $.
$}
