$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/sf_HoareLogic_factorialqtvc: the factorial Hoare-logic verification
  condition states the initialization facts and the universally quantified
  loop-step obligations for a nonnegative integer input. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain. A is the source input x,
  and B is the arbitrary total source function fact. Its value at zero and
  its recurrence at every positive integer are retained as scoped essential
  hypotheses, exactly matching the source fact_0 and fact_n declarations.

  The proposition-valued source conditional on z being nonzero is expanded
  into two exhaustive guarded branches. This is bidirectionally equivalent
  to the source if-then-else. The source variables z and y remain internally
  universally quantified over all integers, and the conjunction nesting,
  arithmetic expressions, assumptions, and conclusion are preserved.

  The source inductive predicate even is unused by this verification
  condition and is therefore omitted. The final declaration is Metamath's
  native unproved $a statement encoding; this database contains no
  artifact-level $p proof declaration.
$)

${
  $d n z y A B $.

  $( Source parameters: A=x and B=fact. $)

  ntp4vc-factorial-x-integer
    $e |- A e. ZZ $.
  ntp4vc-factorial-fact-function
    $e |- B e. ( ZZ ^m ZZ ) $.
  ntp4vc-factorial-x-nonnegative
    $e |- 0 <_ A $.

  ntp4vc-factorial-fact-zero
    $e |- ( B ` 0 ) = 1 $.

  ntp4vc-factorial-fact-positive $e |- A. n e. ZZ
    (
      0 < n
      ->
      ( B ` n ) = ( n x. ( B ` ( n - 1 ) ) )
    ) $.

  ntp4vc-pearl-sf-hoarelogic-factorial-vc $a |- (
    0 <_ A
    /\
    (
      ( 1 x. ( B ` A ) ) = ( B ` A )
      /\
      A. z e. ZZ A. y e. ZZ
        (
          (
            0 <_ z
            /\
            ( y x. ( B ` z ) ) = ( B ` A )
          )
          ->
          (
            (
              z =/= 0
              /\
              (
                (
                  0 <_ z
                  /\
                  ( z - 1 ) < z
                )
                /\
                (
                  0 <_ ( z - 1 )
                  /\
                  (
                    ( ( y x. z ) x. ( B ` ( z - 1 ) ) )
                    =
                    ( B ` A )
                  )
                )
              )
            )
            \/
            (
              -. z =/= 0
              /\
              y = ( B ` A )
            )
          )
        )
    )
  ) $.
$}
