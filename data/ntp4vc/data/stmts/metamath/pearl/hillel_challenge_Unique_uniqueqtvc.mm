$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/hillel_challenge_Unique_uniqueqtvc: the unique-elements verification
  condition initializes an output list, scans an integer list while recording
  previously seen values, and specifies that the returned prefix contains
  exactly the input values without duplicates. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Integer lists are represented exactly by SetMM words over ZZ, hence by
  arbitrary finite zero-based sequences of integers. NTP4VCToNat,
  NTP4VCAt, and NTP4VCSet are respectively the source integer-to-natural
  conversion, totalized lookup with integer default 0, and list update.

  A finite map from integers to unit is represented by its finite set of
  keys. This is a bijection: map equality, the empty map, key membership, and
  insertion of the sole unit value correspond exactly to set equality, the
  empty set, membership, and singleton union. NTP4VCMem expands the source
  bounded-list membership predicate.

  The remaining predicates are biconditional factorizations of the source
  uniqueness invariant, function-update premise, conditional loop step,
  result extraction obligation, loop contract, and outer verification
  condition. Expanding them recovers every integer, list, finite-map, and
  result quantifier, every repeated bound and implication, both branches of
  the proposition-valued conditional, and the two source let-bound values.
  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCFMap
  NTP4VCMem NTP4VCUnique NTP4VCInv NTP4VCUpdateLaw
  NTP4VCStep NTP4VCExtract NTP4VCLoop NTP4VCBody NTP4VCUniqueVC
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-fmap-syntax $a class NTP4VCFMap $.

ntp4vc-mem-syntax $a wff ( NTP4VCMem A B C ) $.
ntp4vc-unique-syntax $a wff ( NTP4VCUnique A B ) $.
ntp4vc-inv-syntax $a wff ( NTP4VCInv A B C D E ) $.
ntp4vc-update-law-syntax
  $a wff ( NTP4VCUpdateLaw A B C ) $.
ntp4vc-step-syntax $a wff ( NTP4VCStep A B C D E ) $.
ntp4vc-extract-syntax $a wff ( NTP4VCExtract A B C ) $.
ntp4vc-loop-syntax $a wff ( NTP4VCLoop A B C ) $.
ntp4vc-body-syntax $a wff ( NTP4VCBody A B C ) $.
ntp4vc-unique-vc-syntax $a wff ( NTP4VCUniqueVC A ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  0
) $.

${
  $d k A B C $.

  ntp4vc-set-definition $a |- (
    NTP4VCSet A B C
  ) = (
    k e. ( 0 ..^ ( # ` A ) ) |->
      if (
        k = ( NTP4VCToNat B ) ,
        C ,
        ( A ` k )
      )
  ) $.
$}

${
  ntp4vc-fmap-definition $a |- NTP4VCFMap = {
    s e. Fin | s C_ ZZ
  } $.
$}

${
  $d j A B C $.

  ntp4vc-mem-definition $a |- (
    NTP4VCMem A B C
  ) <-> (
    E. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < C
        )
        /\
        ( NTP4VCAt B j ) = A
      )
  ) $.
$}

${
  $d i j A B $.

  ntp4vc-unique-definition $a |- (
    NTP4VCUnique A B
  ) <-> (
    A. i e. ZZ
      A. j e. ZZ
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
          ( NTP4VCAt A i ) =/= ( NTP4VCAt A j )
        )
  ) $.
$}

${
  $d x A B C D E $.

  $( Source arguments: A=a, B=i, C=h, D=res, E=len. $)
  ntp4vc-inv-definition $a |- (
    NTP4VCInv A B C D E
  ) <-> (
    (
      0 <_ E
      /\
      E <_ B
    )
    /\
    (
      A. x e. ZZ
        (
          ( NTP4VCMem x A B )
          <->
          x e. C
        )
      /\
      (
        A. x e. ZZ
          (
            ( NTP4VCMem x A B )
            <->
            ( NTP4VCMem x D E )
          )
        /\
        ( NTP4VCUnique D E )
      )
    )
  ) $.
$}

${
  $d k A B C $.

  ntp4vc-update-law-definition $a |- (
    NTP4VCUpdateLaw A B C
  ) <-> (
    A. k e. ZZ
      (
        ( NTP4VCAt ( NTP4VCSet A B C ) k )
        =
        if (
          k = B ,
          C ,
          ( NTP4VCAt A k )
        )
      )
  ) $.
$}

${
  $d q A B C D E $.

  $( Source arguments: A=a, B=i, C=h1, D=res1, E=len. $)
  ntp4vc-step-definition $a |- (
    NTP4VCStep A B C D E
  ) <-> (
    (
      0 <_ B
      /\
      B < ( # ` A )
    )
    /\
    (
      (
        -. ( NTP4VCAt A B ) e. C
        ->
        (
          (
            0 <_ B
            /\
            B < ( # ` A )
          )
          /\
          A. q e. NTP4VCFMap
            (
              q = ( C u. { ( NTP4VCAt A B ) } )
              ->
              (
                (
                  0 <_ B
                  /\
                  B < ( # ` A )
                )
                /\
                (
                  (
                    0 <_ E
                    /\
                    E < ( # ` D )
                  )
                  /\
                  (
                    (
                      # ` ( NTP4VCSet D E ( NTP4VCAt A B ) )
                    )
                    =
                    ( # ` D )
                    ->
                    (
                      ( NTP4VCUpdateLaw D E ( NTP4VCAt A B ) )
                      ->
                      (
                        NTP4VCInv
                          A
                          ( B + 1 )
                          q
                          ( NTP4VCSet D E ( NTP4VCAt A B ) )
                          ( E + 1 )
                      )
                    )
                  )
                )
              )
            )
        )
      )
      /\
      (
        ( NTP4VCAt A B ) e. C
        ->
        ( NTP4VCInv A ( B + 1 ) C D E )
      )
    )
  ) $.
$}

${
  $d i x r A B C $.

  $( Source arguments: A=a, B=res1 (or res), C=len. $)
  ntp4vc-extract-definition $a |- (
    NTP4VCExtract A B C
  ) <-> (
    A. r e. Word ZZ
      (
        (
          ( # ` r ) = C
          /\
          A. i e. ZZ
            (
              (
                0 <_ i
                /\
                i < C
              )
              ->
              ( NTP4VCAt r i ) = ( NTP4VCAt B ( 0 + i ) )
            )
        )
        ->
        (
          A. x e. ZZ
            (
              ( NTP4VCMem x r ( # ` r ) )
              <->
              ( NTP4VCMem x A ( # ` A ) )
            )
          /\
          ( NTP4VCUnique r ( # ` r ) )
        )
      )
  ) $.
$}

${
  $d h i l r A B C $.

  $( Source arguments: A=a, B=h, C=res. $)
  ntp4vc-loop-definition $a |- (
    NTP4VCLoop A B C
  ) <-> (
    A. l e. ZZ
      A. r e. Word ZZ
        A. h e. NTP4VCFMap
          (
            ( # ` r ) = ( # ` C )
            ->
            (
              (
                A. i e. ZZ
                  (
                    (
                      (
                        0 <_ i
                        /\
                        i <_ ( ( # ` A ) - 1 )
                      )
                      /\
                      ( NTP4VCInv A i h r l )
                    )
                    ->
                    ( NTP4VCStep A i h r l )
                  )
              )
              /\
              (
                (
                  NTP4VCInv
                    A
                    ( ( ( # ` A ) - 1 ) + 1 )
                    h
                    r
                    l
                )
                ->
                (
                  (
                    0 <_ 0
                    /\
                    (
                      0 <_ l
                      /\
                      ( 0 + l ) <_ ( # ` r )
                    )
                  )
                  /\
                  ( NTP4VCExtract A r l )
                )
              )
            )
          )
  ) $.
$}

${
  $d A B C $.

  $( Source arguments: A=a, B=h, C=res. The source let-bound
     o1 is expanded as (# ` A) - 1. $)
  ntp4vc-body-definition $a |- (
    NTP4VCBody A B C
  ) <-> (
    (
      0 <_ ( ( ( # ` A ) - 1 ) + 1 )
      ->
      (
        ( NTP4VCInv A 0 B C 0 )
        /\
        ( NTP4VCLoop A B C )
      )
    )
    /\
    (
      ( ( ( # ` A ) - 1 ) + 1 ) < 0
      ->
      (
        (
          0 <_ 0
          /\
          (
            0 <_ 0
            /\
            ( 0 + 0 ) <_ ( # ` C )
          )
        )
        /\
        ( NTP4VCExtract A C 0 )
      )
    )
  ) $.
$}

${
  $d h i r A $.

  ntp4vc-unique-vc-definition $a |- (
    NTP4VCUniqueVC A
  ) <-> (
    A. h e. NTP4VCFMap
      (
        h = (/)
        ->
        (
          0 <_ ( # ` A )
          /\
          A. r e. Word ZZ
            (
              (
                (
                  A. i e. ZZ
                    (
                      (
                        0 <_ i
                        /\
                        i < ( # ` A )
                      )
                      ->
                      ( NTP4VCAt r i ) = 0
                    )
                )
                /\
                ( # ` r ) = ( # ` A )
              )
              ->
              ( NTP4VCBody A h r )
            )
        )
      )
  ) $.
$}

${
  ntp4vc-a-list $e |- A e. Word ZZ $.

  ntp4vc-pearl-hillel-unique-vc $a |- (
    NTP4VCUniqueVC A
  ) $.
$}
