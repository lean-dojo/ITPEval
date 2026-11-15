$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/tortoise_and_hare_TortoiseAndHareAlgorithm_tortoise_and_hareqtvc:
  the Floyd tortoise-and-hare verification condition preserves the first
  cycle-search loop invariant and the second loop that computes the cycle
  entry and period for an iterated integer function. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and ZZ ^m ZZ is the type
  of arbitrary total integer functions. NTP4VCSeq characterizes the source
  sequence x on every nonnegative index by x(0) = x0 and
  x(k+1) = f(x(k)); this is exactly the part of Why3's int.Iter used by the
  verification condition. The sequence remains internally quantified in
  NTP4VCMainVC rather than becoming an additional theorem parameter. Every
  occurrence in the VC is at a nonnegative index under its source guard, so
  this recurrence is bidirectionally equivalent to the source definition
  x(i) = iter f i x0 for the complete statement.

  NTP4VCFirstInv, NTP4VCFirstAdvance, NTP4VCSecondInit,
  NTP4VCSecondInv, NTP4VCAdvanceBase, NTP4VCAdvanceByI,
  NTP4VCAdvanceByLam, NTP4VCSecondResult, NTP4VCSecondLoop,
  NTP4VCFirstStop, NTP4VCFirstLoop, and NTP4VCConclusion only factor the
  source conjunctions, quantifiers, loop invariants, variants, let-bound
  values, and proposition-valued conditionals. Each conditional is rendered
  by its two exhaustive guarded implications. The source Boolean o1 ranges
  over SetMM's exact two-element carrier 2, with false represented by 0 and
  true by 1.

  Thus all function and integer domains, cycle assumptions, quantifier
  scopes, repeated inequalities, recurrence facts, branch obligations, and
  the final cycle specification are retained. The final $a declaration is
  Metamath's native unproved statement encoding; every auxiliary $a is syntax
  or a faithful biconditional definition, and this database contains no $p
  proof declaration.
$)

$c
  NTP4VCSeq NTP4VCNoRepeat NTP4VCFirstInv
  NTP4VCFirstAdvance NTP4VCShiftDistinct
  NTP4VCSecondInit NTP4VCSecondInv NTP4VCAdvanceBase
  NTP4VCAdvanceByI NTP4VCAdvanceByLam NTP4VCBoolStep
  NTP4VCSecondResult NTP4VCSecondLoop NTP4VCFirstStop
  NTP4VCFirstLoop NTP4VCConclusion NTP4VCMainVC
$.

ntp4vc-seq-syntax
  $a wff ( NTP4VCSeq A B C ) $.
ntp4vc-no-repeat-syntax
  $a wff ( NTP4VCNoRepeat A B ) $.
ntp4vc-first-inv-syntax
  $a wff ( NTP4VCFirstInv A B ) $.
ntp4vc-first-advance-syntax
  $a wff ( NTP4VCFirstAdvance A B C D ) $.
ntp4vc-shift-distinct-syntax
  $a wff ( NTP4VCShiftDistinct A B C ) $.
ntp4vc-second-init-syntax
  $a wff ( NTP4VCSecondInit A B C D ) $.
ntp4vc-second-inv-syntax
  $a wff ( NTP4VCSecondInv A B C D E F ) $.
ntp4vc-advance-base-syntax
  $a wff ( NTP4VCAdvanceBase A B C D E ) $.
ntp4vc-advance-by-i-syntax
  $a wff ( NTP4VCAdvanceByI A B C D E F ) $.
ntp4vc-advance-by-lam-syntax
  $a wff ( NTP4VCAdvanceByLam A B C D E F G ) $.
ntp4vc-bool-step-syntax
  $a wff ( NTP4VCBoolStep A B C D E F G H ) $.
ntp4vc-second-result-syntax
  $a wff ( NTP4VCSecondResult A B C D E ) $.
ntp4vc-second-loop-syntax
  $a wff ( NTP4VCSecondLoop A B C D E F ) $.
ntp4vc-first-stop-syntax
  $a wff ( NTP4VCFirstStop A B C D E F G ) $.
ntp4vc-first-loop-syntax
  $a wff ( NTP4VCFirstLoop A B C D E F ) $.
ntp4vc-conclusion-syntax
  $a wff ( NTP4VCConclusion A B C D E F ) $.
ntp4vc-main-vc-syntax
  $a wff ( NTP4VCMainVC A B C D E ) $.

${
  $d k A B C $.

  ntp4vc-seq-definition $a |- (
    NTP4VCSeq A B C
  ) <-> (
    ( C ` 0 ) = B
    /\
    A. k e. ZZ
      (
        0 <_ k
        ->
        ( C ` ( k + 1 ) ) = ( A ` ( C ` k ) )
      )
  ) $.
$}

${
  $d i j A B $.

  ntp4vc-no-repeat-definition $a |- (
    NTP4VCNoRepeat A B
  ) <-> (
    A. i e. ZZ A. j e. ZZ
      (
        (
          0 <_ i
          /\
          (
            i < j
            /\
            j < B
          )
        )
        ->
        ( A ` i ) =/= ( A ` j )
      )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-first-inv-definition $a |- (
    NTP4VCFirstInv A B
  ) <-> (
    A. i e. ZZ
      (
        (
          1 <_ i
          /\
          i < B
        )
        ->
        ( A ` i ) =/= ( A ` ( 2 x. i ) )
      )
  ) $.
$}

ntp4vc-first-advance-definition $a |- (
  NTP4VCFirstAdvance A B C D
) <-> (
  -. C < ( D + 1 )
  /\
  (
    -. C < ( D + 1 )
    ->
    (
      (
        0 <_ ( C - D )
        /\
        ( C - ( D + 1 ) ) < ( C - D )
      )
      /\
      (
        (
          1 <_ ( D + 1 )
          /\
          ( D + 1 ) <_ C
        )
        /\
        (
          ( A ` ( B ` D ) ) = ( B ` ( D + 1 ) )
          /\
          (
            ( A ` ( A ` ( B ` ( 2 x. D ) ) ) )
            =
            ( B ` ( 2 x. ( D + 1 ) ) )
          )
        )
        /\
        ( NTP4VCFirstInv B ( D + 1 ) )
      )
    )
  )
) $.

${
  $d j A B C $.

  ntp4vc-shift-distinct-definition $a |- (
    NTP4VCShiftDistinct A B C
  ) <-> (
    A. j e. ZZ
      (
        (
          0 < j
          /\
          j < C
        )
        ->
        ( A ` ( B + j ) ) =/= ( A ` B )
      )
  ) $.
$}

${
  $d j A B C D $.

  ntp4vc-second-init-definition $a |- (
    NTP4VCSecondInit A B C D
  ) <-> (
    (
      0 <_ 0
      /\
      0 <_ C
    )
    /\
    (
      B = ( A ` 0 )
      /\
      ( A ` D ) = ( A ` ( D + 0 ) )
    )
    /\
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < 0
        )
        ->
        ( A ` j ) =/= ( A ` ( D + j ) )
      )
    /\
    A. j e. ZZ
      (
        (
          0 < j
          /\
          j < 0
        )
        ->
        ( A ` ( D + j ) ) =/= ( A ` D )
      )
  ) $.
$}

${
  $d j A B C D E F $.

  $(
    A=x, B=mu, C=lambda, D=n, E=lam, and F=i.
  $)
  ntp4vc-second-inv-definition $a |- (
    NTP4VCSecondInv A B C D E F
  ) <-> (
    (
      0 <_ F
      /\
      F <_ B
    )
    /\
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < F
        )
        ->
        ( A ` j ) =/= ( A ` ( D + j ) )
      )
    /\
    (
      (
        E = 0
        ->
        ( NTP4VCShiftDistinct A D F )
      )
      /\
      (
        E =/= 0
        ->
        E = C
      )
    )
  ) $.
$}

${
  $d j A B C D E $.

  $(
    A=f, B=x, C=mu, D=n, and E=i.
  $)
  ntp4vc-advance-base-definition $a |- (
    NTP4VCAdvanceBase A B C D E
  ) <-> (
    (
      0 <_ ( C - E )
      /\
      ( C - ( E + 1 ) ) < ( C - E )
    )
    /\
    (
      0 <_ ( E + 1 )
      /\
      ( E + 1 ) <_ C
    )
    /\
    (
      ( A ` ( B ` E ) ) = ( B ` ( E + 1 ) )
      /\
      (
        ( A ` ( B ` ( D + E ) ) )
        =
        ( B ` ( D + ( E + 1 ) ) )
      )
    )
    /\
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < ( E + 1 )
        )
        ->
        ( B ` j ) =/= ( B ` ( D + j ) )
      )
  ) $.
$}

ntp4vc-advance-by-i-definition $a |- (
  NTP4VCAdvanceByI A B C D E F
) <-> (
  ( NTP4VCAdvanceBase A B C E F )
  /\
  (
    (
      F = 0
      ->
      ( NTP4VCShiftDistinct B E ( F + 1 ) )
    )
    /\
    (
      F =/= 0
      ->
      F = D
    )
  )
) $.

ntp4vc-advance-by-lam-definition $a |- (
  NTP4VCAdvanceByLam A B C D E F G
) <-> (
  ( NTP4VCAdvanceBase A B C E G )
  /\
  (
    (
      F = 0
      ->
      ( NTP4VCShiftDistinct B E ( G + 1 ) )
    )
    /\
    (
      F =/= 0
      ->
      F = D
    )
  )
) $.

ntp4vc-bool-step-definition $a |- (
  NTP4VCBoolStep A B C D E F G H
) <-> (
  H = if (
    F = 0 ,
    if (
      0 < G ,
      if (
        ( B ` ( E + G ) ) = ( B ` E ) ,
        1 ,
        0
      ) ,
      0
    ) ,
    0
  )
  ->
  (
    (
      H = 1
      ->
      ( NTP4VCAdvanceByI A B C D E G )
    )
    /\
    (
      H =/= 1
      ->
      ( NTP4VCAdvanceByLam A B C D E F G )
    )
  )
) $.

${
  $d l A B C D E $.

  $(
    A=x, B=m, C=n, D=lam, and E=i.
  $)
  ntp4vc-second-result-definition $a |- (
    NTP4VCSecondResult A B C D E
  ) <-> (
    A. l e. ZZ
      (
        (
          (
            D = 0
            ->
            l = C
          )
          /\
          (
            D =/= 0
            ->
            l = D
          )
        )
        ->
        (
          (
            (
              0 <_ E
              /\
              E < B
            )
            /\
            (
              (
                1 <_ l
                /\
                l <_ B
              )
              /\
              (
                ( E + l ) <_ B
                /\
                ( A ` ( E + l ) ) = ( A ` E )
              )
            )
          )
          /\
          ( NTP4VCNoRepeat A ( E + l ) )
        )
      )
  ) $.
$}

${
  $d i k o A B C D E F $.

  $(
    A=f, B=x, C=m, D=mu, E=lambda, and F=n.
  $)
  ntp4vc-second-loop-definition $a |- (
    NTP4VCSecondLoop A B C D E F
  ) <-> (
    A. k e. ZZ A. i e. ZZ
      (
        ( NTP4VCSecondInv B D E F k i )
        ->
        (
          (
            ( B ` i ) =/= ( B ` ( F + i ) )
            ->
            A. o e. 2
              (
                NTP4VCBoolStep
                  A B D E F k i o
              )
          )
          /\
          (
            ( B ` i ) = ( B ` ( F + i ) )
            ->
            (
              NTP4VCSecondResult
                B C F k i
            )
          )
        )
      )
  ) $.
$}

ntp4vc-first-stop-definition $a |- (
  NTP4VCFirstStop A B C D E F G
) <-> (
  ( NTP4VCSecondInit B C E G )
  /\
  ( NTP4VCSecondLoop A B D E F G )
) $.

${
  $d n A B C D E F $.

  $(
    A=f, B=x, C=x0, D=m, E=mu, and F=lambda.
  $)
  ntp4vc-first-loop-definition $a |- (
    NTP4VCFirstLoop A B C D E F
  ) <-> (
    A. n e. ZZ
      (
        (
          (
            1 <_ n
            /\
            n <_ ( E + F )
          )
          /\
          ( NTP4VCFirstInv B n )
        )
        ->
        (
          (
            ( B ` n ) =/= ( B ` ( 2 x. n ) )
            ->
            (
              NTP4VCFirstAdvance
                A B ( E + F ) n
            )
          )
          /\
          (
            ( B ` n ) = ( B ` ( 2 x. n ) )
            ->
            (
              NTP4VCFirstStop
                A B C D E F n
            )
          )
        )
      )
  ) $.
$}

$(
  A=f, B=x, C=x0, D=m, E=mu, and F=lambda.
$)
ntp4vc-conclusion-definition $a |- (
  NTP4VCConclusion A B C D E F
) <-> (
  1 <_ 1
  /\
  (
    1 <_ ( E + F )
    /\
    (
      ( A ` C ) = ( B ` 1 )
      /\
      (
        ( A ` ( A ` C ) ) = ( B ` ( 2 x. 1 ) )
        /\
        (
          ( NTP4VCFirstInv B 1 )
          /\
          ( NTP4VCFirstLoop A B C D E F )
        )
      )
    )
  )
) $.

${
  $d s A B C D E $.

  $(
    A=f, B=m, C=x0, D=mu, and E=lambda. The internally quantified s is the
    source-defined iterate sequence x.
  $)
  ntp4vc-main-vc-definition $a |- (
    NTP4VCMainVC A B C D E
  ) <-> (
    A. s e. ( ZZ ^m ZZ )
      (
        ( NTP4VCSeq A C s )
        ->
        (
          (
            ( s ` ( D + E ) ) = ( s ` D )
            /\
            ( NTP4VCNoRepeat s ( D + E ) )
          )
          ->
          (
            NTP4VCConclusion
              A s C B D E
          )
        )
      )
  ) $.
$}

${
  $d q
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source parameters: A=f, B=m, C=x0, D=mu, and E=lambda. $)
  ntp4vc-f-function
    $e |- A e. ( ZZ ^m ZZ ) $.
  ntp4vc-m-integer
    $e |- B e. ZZ $.
  ntp4vc-m-positive
    $e |- 0 < B $.

  ntp4vc-f-range $e |- A. q e. ZZ
    (
      (
        0 <_ q
        /\
        q < B
      )
      ->
      (
        0 <_ ( A ` q )
        /\
        ( A ` q ) < B
      )
    ) $.

  ntp4vc-x0-integer
    $e |- C e. ZZ $.
  ntp4vc-x0-range
    $e |- ( 0 <_ C /\ C < B ) $.

  ntp4vc-mu-integer
    $e |- D e. ZZ $.
  ntp4vc-lambda-integer
    $e |- E e. ZZ $.
  ntp4vc-fact0
    $e |- 0 <_ D $.
  ntp4vc-fact1
    $e |- D < B $.
  ntp4vc-fact2
    $e |- 1 <_ E $.
  ntp4vc-fact3
    $e |- E <_ B $.
  ntp4vc-fact4
    $e |- ( D + E ) <_ B $.

  ntp4vc-pearl-tortoise-and-hare-vc
    $a |- ( NTP4VCMainVC A B C D E ) $.
$}
