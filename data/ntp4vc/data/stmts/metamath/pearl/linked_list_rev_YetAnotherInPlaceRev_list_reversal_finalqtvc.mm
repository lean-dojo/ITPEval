$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/linked_list_rev_YetAnotherInPlaceRev_list_reversal_finalqtvc: the
  linked-list reversal verification condition derives a forward list segment
  with distinct non-null cells and shows that any framed reverse segment is
  the reversed recursive list. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  G is the arbitrary inhabited source carrier loc, E is null, and A is the
  total next-location function mem1. The one-field source mem record is
  identified definitionally with its next function. B is the full
  integer-indexed location sequence s, C is the integer length n, and D is
  the initial location l. All integer variables retain the full unbounded
  carrier ZZ, and all memory and sequence values retain their full total
  function spaces.

  F represents the source proposition-valued is_list operation extensionally
  as a relation on memory functions, locations, sequences, and integers. Its
  displayed law is exactly is_list'def on every nonnegative integer.
  NTP4VCShift is result as fixed by result'def, and NTP4VCReverseSeq is fc as
  fixed by fc'def. NTP4VCValidCells, NTP4VCListLR, NTP4VCListRL, and
  NTP4VCFrame directly expand the corresponding source definitions.
  Proposition-valued conditionals are expanded into their two exhaustive
  guarded branches.

  The theorem's mem3 and r remain universally quantified inside the
  conclusion at their source scopes. Every auxiliary $a declaration below is
  syntax or an explicit faithful definition. The final $a declaration is
  Metamath's native unproved statement encoding; this database contains no
  $p declaration.
$)

$c
  NTP4VCShift NTP4VCReverseSeq NTP4VCIsList NTP4VCValidCells
  NTP4VCListLR NTP4VCListRL NTP4VCFrame NTP4VCListReversalVC
$.

ntp4vc-shift-syntax
  $a class ( NTP4VCShift A ) $.
ntp4vc-reverse-seq-syntax
  $a class ( NTP4VCReverseSeq A B ) $.
ntp4vc-is-list-syntax
  $a wff ( NTP4VCIsList A B C D E ) $.
ntp4vc-valid-cells-syntax
  $a wff ( NTP4VCValidCells A B C ) $.
ntp4vc-list-lr-syntax
  $a wff ( NTP4VCListLR A B C D E F ) $.
ntp4vc-list-rl-syntax
  $a wff ( NTP4VCListRL A B C D E F ) $.
ntp4vc-frame-syntax
  $a wff ( NTP4VCFrame A B C D E ) $.
ntp4vc-list-reversal-vc-syntax
  $a wff ( NTP4VCListReversalVC A B C D E F G ) $.

${
  $d i A $.

  ntp4vc-shift-definition $a |- (
    NTP4VCShift A
  ) = (
    i e. ZZ |->
      ( A ` ( i + 1 ) )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-reverse-seq-definition $a |- (
    NTP4VCReverseSeq A B
  ) = (
    i e. ZZ |->
      ( A ` ( ( B - 1 ) - i ) )
  ) $.
$}

ntp4vc-is-list-definition $a |- (
  NTP4VCIsList A B C D E
) <-> (
  <. <. <. B , C >. , D >. , E >. e. A
) $.

${
  $d i j A B C $.

  ntp4vc-valid-cells-definition $a |- (
    NTP4VCValidCells A B C
  ) <-> (
    (
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < B
          )
          ->
          ( A ` i ) =/= C
        )
    )
    /\
    A. i e. ZZ
      A. j e. ZZ
        (
          (
            (
              0 <_ i
              /\
              i < B
            )
            /\
            (
              (
                0 <_ j
                /\
                j < B
              )
              /\
              i =/= j
            )
          )
          ->
          ( A ` i ) =/= ( A ` j )
        )
  ) $.
$}

${
  $d k A B C D E F $.

  ntp4vc-list-lr-definition $a |- (
    NTP4VCListLR A B C D E F
  ) <-> (
    (
      0 <_ D
      /\
      D <_ E
    )
    /\
    (
      (
        D = E
        /\
        C = F
      )
      \/
      (
        D =/= E
        /\
        (
          C = ( B ` D )
          /\
          (
            ( A ` ( B ` ( E - 1 ) ) ) = F
            /\
            A. k e. ZZ
              (
                (
                  D <_ k
                  /\
                  k < ( E - 1 )
                )
                ->
                ( A ` ( B ` k ) ) = ( B ` ( k + 1 ) )
              )
          )
        )
      )
    )
  ) $.
$}

${
  $d k A B C D E F $.

  ntp4vc-list-rl-definition $a |- (
    NTP4VCListRL A B C D E F
  ) <-> (
    (
      0 <_ D
      /\
      D <_ E
    )
    /\
    (
      (
        D = E
        /\
        C = F
      )
      \/
      (
        D =/= E
        /\
        (
          ( A ` ( B ` D ) ) = F
          /\
          (
            C = ( B ` ( E - 1 ) )
            /\
            A. k e. ZZ
              (
                (
                  D < k
                  /\
                  k < E
                )
                ->
                ( A ` ( B ` k ) ) = ( B ` ( k - 1 ) )
              )
          )
        )
      )
    )
  ) $.
$}

${
  $d i p A B C D E $.

  ntp4vc-frame-definition $a |- (
    NTP4VCFrame A B C D E
  ) <-> (
    A. p e. E
      (
        (
          A. i e. ZZ
            (
              (
                0 <_ i
                /\
                i < D
              )
              ->
              p =/= ( C ` i )
            )
        )
        ->
        ( A ` p ) = ( B ` p )
      )
  ) $.
$}

${
  $d m r A B C D E F G $.

  ntp4vc-list-reversal-vc-definition $a |- (
    NTP4VCListReversalVC A B C D E F G
  ) <-> (
    (
      (
        0 <_ C
        /\
        ( NTP4VCIsList F A D B C )
      )
      ->
      (
        (
          ( NTP4VCValidCells B C E )
          /\
          ( NTP4VCListLR A B D 0 C E )
        )
        /\
        A. m e. ( G ^m G )
          A. r e. G
            (
              (
                ( NTP4VCListRL m B r 0 C E )
                /\
                ( NTP4VCFrame m A B C G )
              )
              ->
              (
                (
                  NTP4VCIsList
                    F m r ( NTP4VCReverseSeq B C ) C
                )
                /\
                ( NTP4VCFrame m A B C G )
              )
            )
      )
    )
  ) $.
$}

${
  $d i j k l m n p r s
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source carrier and theorem parameters:
     G=loc, E=null, A=mem1, B=s, C=n, D=l, and F=is_list. $)

  ntp4vc-location-carrier-nonempty $e |- G =/= (/) $.
  ntp4vc-null-location $e |- E e. G $.
  ntp4vc-mem1-function $e |- A e. ( G ^m G ) $.
  ntp4vc-s-sequence $e |- B e. ( G ^m ZZ ) $.
  ntp4vc-n-integer $e |- C e. ZZ $.
  ntp4vc-l-location $e |- D e. G $.

  ntp4vc-is-list-relation $e |- F C_
    (
      (
        (
          ( G ^m G )
          X.
          G
        )
        X.
        ( G ^m ZZ )
      )
      X.
      ZZ
    ) $.

  ntp4vc-is-list-recursion $e |- A. m e. ( G ^m G )
    A. l e. G A. s e. ( G ^m ZZ ) A. n e. ZZ
      (
        0 <_ n
        ->
        (
          (
            n = 0
            ->
            (
              ( NTP4VCIsList F m l s n )
              <->
              l = E
            )
          )
          /\
          (
            n =/= 0
            ->
            (
              ( NTP4VCIsList F m l s n )
              <->
              (
                (
                  l = ( s ` 0 )
                  /\
                  ( s ` 0 ) =/= E
                )
                /\
                (
                  NTP4VCIsList
                    F m ( m ` l ) ( NTP4VCShift s ) ( n - 1 )
                )
              )
            )
          )
        )
      ) $.

  ntp4vc-pearl-linked-list-rev-yet-another-in-place-rev-list-reversal-final-vc
    $a |- ( NTP4VCListReversalVC A B C D E F G ) $.
$}
