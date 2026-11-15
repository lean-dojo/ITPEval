$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/schorr_waite_SchorrWaite_schorr_waiteqtvc: the Schorr-Waite
  graph-marking verification condition initializes the empty traversal
  stack, preserves its graph, path, marking, pointer-reversal, and
  lexicographic termination invariants through pop, swing, and push steps,
  and establishes the final reachability and marking specification. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source location carrier, D is the inhabitant
  used by totalized sequence lookup, and Z is null. G is the finite graph.
  L0 and R0 are the original left and right maps; Boolean maps have the exact
  carrier { 0, 1 }, with false represented by 0 and true by 1. SetMM Word U
  is exactly the full type of arbitrary finite zero-based location lists.

  NTP4VCToNat, NTP4VCAt, NTP4VCTail, and NTP4VCUpdate directly encode the
  source integer-to-natural conversion, totalized lookup, list tail, and
  total function update. NTP4VCNotInStack, NTP4VCLast, NTP4VCDistinct, and
  NTP4VCEdge are literal expansions of the source definitions.
  NTP4VCPath is bidirectionally equivalent to the source inductive path: the
  empty word connects a location to itself, while a nonempty word records
  the initial location and every edge before the final destination.

  NTP4VCInv is the complete loop invariant. NTP4VCPop, NTP4VCSwing, and the
  two NTP4VCPush cases instantiate that same invariant with exactly the
  source map, mark, finite-set, stack, path, and pointer updates. Repeated
  non-null conjuncts and all three lexicographic-decrease disjuncts are
  retained. Proposition-valued conditionals are expanded into equivalent
  guarded implications. All locations, finite sets, lists, maps, Booleans,
  and integer indices retain their full source domains. Every auxiliary $a
  below is syntax or an explicit faithful definition; the final $a is
  Metamath's native unproved statement encoding, and there is no $p
  declaration.
$)

$c
  NTP4VCFSet NTP4VCToNat NTP4VCAt NTP4VCTail NTP4VCUpdate
  NTP4VCNotInStack NTP4VCLast NTP4VCDistinct NTP4VCEdge
  NTP4VCPath NTP4VCReachable NTP4VCInv
  NTP4VCPop NTP4VCSwing NTP4VCConsLaw
  NTP4VCPushNonRoot NTP4VCPushRoot NTP4VCPush
  NTP4VCPost NTP4VCLoop NTP4VCInitial NTP4VCSchorrWaiteVC
$.

ntp4vc-fset-syntax $a class ( NTP4VCFSet A ) $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.
ntp4vc-tail-syntax $a class ( NTP4VCTail A ) $.
ntp4vc-update-syntax $a class ( NTP4VCUpdate A B C D ) $.
ntp4vc-not-in-stack-syntax
  $a wff ( NTP4VCNotInStack A B C ) $.
ntp4vc-last-syntax $a class ( NTP4VCLast A B ) $.
ntp4vc-distinct-syntax $a wff ( NTP4VCDistinct A B ) $.
ntp4vc-edge-syntax $a wff ( NTP4VCEdge A B C D E ) $.
ntp4vc-path-syntax $a wff ( NTP4VCPath A B C D E F G ) $.
ntp4vc-reachable-syntax
  $a wff ( NTP4VCReachable A B C D E F ) $.
ntp4vc-inv-syntax
  $a wff (
    NTP4VCInv A B C D E F G H I J K L M N O P Q R
  ) $.
ntp4vc-pop-syntax
  $a wff (
    NTP4VCPop A B C D E F G H I J K L M N O P Q R
  ) $.
ntp4vc-swing-syntax
  $a wff (
    NTP4VCSwing A B C D E F G H I J K L M N O P Q R
  ) $.
ntp4vc-cons-law-syntax $a wff ( NTP4VCConsLaw A B C ) $.
ntp4vc-push-non-root-syntax
  $a wff (
    NTP4VCPushNonRoot A B C D E F G H I J K L M N O P Q R
  ) $.
ntp4vc-push-root-syntax
  $a wff (
    NTP4VCPushRoot A B C D E F G H I J K L M N O P Q R
  ) $.
ntp4vc-push-syntax
  $a wff (
    NTP4VCPush A B C D E F G H I J K L M N O P Q R
  ) $.
ntp4vc-post-syntax
  $a wff ( NTP4VCPost A B C D E F G H I J ) $.
ntp4vc-loop-syntax
  $a wff ( NTP4VCLoop A B C D E F G ) $.
ntp4vc-initial-syntax
  $a wff ( NTP4VCInitial A B C D E F G H I J ) $.
ntp4vc-schorr-waite-vc-syntax
  $a wff ( NTP4VCSchorrWaiteVC A B C D E F G H I J ) $.

${
  $d s A $.

  ntp4vc-fset-definition $a |- (
    NTP4VCFSet A
  ) = {
    s e. Fin | s C_ A
  } $.
$}

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if ( 0 <_ A , A , 0 ) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B C
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  C
) $.

${
  $d k A $.

  ntp4vc-tail-definition $a |- (
    NTP4VCTail A
  ) = (
    k e. ( 0 ..^ ( ( # ` A ) - 1 ) )
      |-> ( A ` ( k + 1 ) )
  ) $.
$}

${
  $d x A B C D $.

  ntp4vc-update-definition $a |- (
    NTP4VCUpdate A B C D
  ) = (
    x e. D |-> if ( x = B , C , ( A ` x ) )
  ) $.
$}

${
  $d i A B C $.

  ntp4vc-not-in-stack-definition $a |- (
    NTP4VCNotInStack A B C
  ) <-> (
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < ( # ` B )
        )
        ->
        A =/= ( NTP4VCAt B i C )
      )
  ) $.
$}

ntp4vc-last-definition $a |- (
  NTP4VCLast A B
) = (
  NTP4VCAt A ( ( # ` A ) - 1 ) B
) $.

${
  $d i j A B $.

  ntp4vc-distinct-definition $a |- (
    NTP4VCDistinct A B
  ) <-> (
    A. i e. ZZ A. j e. ZZ
      (
        (
          0 <_ i
          /\
          i < ( # ` A )
        )
        ->
        (
          (
            0 <_ j
            /\
            j < ( # ` A )
          )
          ->
          (
            i =/= j
            ->
            ( NTP4VCAt A i B ) =/= ( NTP4VCAt A j B )
          )
        )
      )
  ) $.
$}

ntp4vc-edge-definition $a |- (
  NTP4VCEdge A B C D E
) <-> (
  A =/= E
  /\
  (
    ( C ` A ) = B
    \/
    ( D ` A ) = B
  )
) $.

${
  $d k A B C D E F G $.

  ntp4vc-path-definition $a |- (
    NTP4VCPath A B C D E F G
  ) <-> (
    G e. Word A
    /\
    (
      (
        ( # ` G ) = 0
        /\
        E = F
      )
      \/
      (
        0 < ( # ` G )
        /\
        (
          ( G ` 0 ) = E
          /\
          (
            A. k e. ( 0 ..^ ( ( # ` G ) - 1 ) )
              (
                NTP4VCEdge
                  ( G ` k )
                  ( G ` ( k + 1 ) )
                  C D B
              )
            /\
            (
              NTP4VCEdge
                ( G ` ( ( # ` G ) - 1 ) )
                F C D B
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d p A B C D E F $.

  ntp4vc-reachable-definition $a |- (
    NTP4VCReachable A B C D E F
  ) <-> (
    E. p e. Word A
      ( NTP4VCPath A B C D E F p )
  ) $.
$}

${
  $d i k n A B C D E F G H I J K L M N O P Q R $.

  $(
    Arguments are:
    U, default, null, graph, root, original-left, original-right,
    stack, p, t, path, path-map, current-left, current-right,
    mark, direction-mark, unmarked-set, false-direction-set.
  $)
  ntp4vc-inv-definition $a |- (
    NTP4VCInv A B C D E F G H I J K L M N O P Q R
  ) <-> (
    (
      A. n e. A
        (
          n e. D
          ->
          (
            ( NTP4VCNotInStack n H B )
            \/
            E. i e. ZZ ( NTP4VCAt H i B ) = n
          )
        )
    )
    /\
    (
      ( NTP4VCNotInStack C H B )
      /\
      (
        (
          ( # ` H ) = 0
          <->
          I = C
        )
        /\
        (
          (
            I =/= C
            ->
            I e. D
          )
          /\
          (
            (
              ( # ` H ) =/= 0
              ->
              ( NTP4VCAt H 0 B ) = I
            )
            /\
            (
              A. n e. A
                (
                  n e. D
                  ->
                  (
                    ( O ` n ) =/= 1
                    ->
                    n e. Q
                  )
                )
              /\
              (
                A. n e. A
                  (
                    n e. D
                    ->
                    (
                      ( P ` n ) =/= 1
                      ->
                      n e. R
                    )
                  )
                /\
                (
                  A. i e. ZZ
                    (
                      (
                        0 <_ i
                        /\
                        i < ( # ` H )
                      )
                      ->
                      ( NTP4VCAt H i B ) e. D
                    )
                  /\
                  (
                    A. i e. ZZ
                      (
                        (
                          0 <_ i
                          /\
                          i < ( ( # ` H ) - 1 )
                        )
                        ->
                        (
                          (
                            ( P ` ( NTP4VCAt H ( i + 1 ) B ) ) = 1
                            ->
                            (
                              (
                                F ` ( NTP4VCAt H ( i + 1 ) B )
                              )
                              =
                              (
                                M ` ( NTP4VCAt H ( i + 1 ) B )
                              )
                              /\
                              (
                                G ` ( NTP4VCAt H ( i + 1 ) B )
                              )
                              =
                              ( NTP4VCAt H i B )
                            )
                          )
                          /\
                          (
                            ( P ` ( NTP4VCAt H ( i + 1 ) B ) ) =/= 1
                            ->
                            (
                              (
                                F ` ( NTP4VCAt H ( i + 1 ) B )
                              )
                              =
                              ( NTP4VCAt H i B )
                              /\
                              (
                                G ` ( NTP4VCAt H ( i + 1 ) B )
                              )
                              =
                              (
                                N ` ( NTP4VCAt H ( i + 1 ) B )
                              )
                            )
                          )
                        )
                      )
                    /\
                    (
                      ( L ` E ) = (/)
                      /\
                      (
                        A. n e. A
                          (
                            n e. D
                            ->
                            (
                              ( NTP4VCNotInStack n H B )
                              ->
                              (
                                ( M ` n ) = ( F ` n )
                                /\
                                ( N ` n ) = ( G ` n )
                              )
                            )
                          )
                        /\
                        (
                          (
                            ( # ` H ) =/= 0
                            ->
                            (
                              (
                                (
                                  P ` ( NTP4VCLast H B )
                                ) = 1
                                ->
                                (
                                  N ` ( NTP4VCLast H B )
                                ) = C
                              )
                              /\
                              (
                                (
                                  P ` ( NTP4VCLast H B )
                                ) =/= 1
                                ->
                                (
                                  M ` ( NTP4VCLast H B )
                                ) = C
                              )
                            )
                          )
                          /\
                          (
                            (
                              ( # ` H ) =/= 0
                              ->
                              ( NTP4VCLast H B ) = E
                            )
                            /\
                            (
                              A. k e. ZZ
                                (
                                  (
                                    0 <_ k
                                    /\
                                    k < ( ( # ` H ) - 1 )
                                  )
                                  ->
                                  (
                                    (
                                      (
                                        P ` ( NTP4VCAt H k B )
                                      ) = 1
                                      ->
                                      (
                                        N ` ( NTP4VCAt H k B )
                                      )
                                      =
                                      ( NTP4VCAt H ( k + 1 ) B )
                                    )
                                    /\
                                    (
                                      (
                                        P ` ( NTP4VCAt H k B )
                                      ) =/= 1
                                      ->
                                      (
                                        M ` ( NTP4VCAt H k B )
                                      )
                                      =
                                      ( NTP4VCAt H ( k + 1 ) B )
                                    )
                                  )
                                )
                              /\
                              (
                                A. i e. ZZ
                                  (
                                    (
                                      0 <_ i
                                      /\
                                      i < ( # ` H )
                                    )
                                    ->
                                    (
                                      O ` ( NTP4VCAt H i B )
                                    ) = 1
                                  )
                                /\
                                (
                                  ( NTP4VCDistinct H B )
                                  /\
                                  (
                                    A. i e. ZZ
                                      (
                                        (
                                          0 <_ i
                                          /\
                                          i < ( # ` H )
                                        )
                                        ->
                                        (
                                          (
                                            (
                                              P ` ( NTP4VCAt H i B )
                                            ) = 1
                                            ->
                                            (
                                              M ` ( NTP4VCAt H i B )
                                            )
                                            =
                                            (
                                              F ` ( NTP4VCAt H i B )
                                            )
                                          )
                                          /\
                                          (
                                            (
                                              P ` ( NTP4VCAt H i B )
                                            ) =/= 1
                                            ->
                                            (
                                              N ` ( NTP4VCAt H i B )
                                            )
                                            =
                                            (
                                              G ` ( NTP4VCAt H i B )
                                            )
                                          )
                                        )
                                      )
                                    /\
                                    (
                                      (
                                        ( # ` H ) =/= 0
                                        ->
                                        (
                                          (
                                            ( P ` I ) = 1
                                            ->
                                            ( G ` I ) = J
                                          )
                                          /\
                                          (
                                            ( P ` I ) =/= 1
                                            ->
                                            ( F ` I ) = J
                                          )
                                        )
                                      )
                                      /\
                                      (
                                        A. k e. ZZ
                                          (
                                            (
                                              0 < k
                                              /\
                                              k < ( # ` H )
                                            )
                                            ->
                                            (
                                              (
                                                (
                                                  P `
                                                  ( NTP4VCAt H k B )
                                                ) = 1
                                                ->
                                                (
                                                  NTP4VCAt
                                                    H ( k - 1 ) B
                                                )
                                                =
                                                (
                                                  G `
                                                  ( NTP4VCAt H k B )
                                                )
                                              )
                                              /\
                                              (
                                                (
                                                  P `
                                                  ( NTP4VCAt H k B )
                                                ) =/= 1
                                                ->
                                                (
                                                  NTP4VCAt
                                                    H ( k - 1 ) B
                                                )
                                                =
                                                (
                                                  F `
                                                  ( NTP4VCAt H k B )
                                                )
                                              )
                                            )
                                          )
                                        /\
                                        (
                                          (
                                            I =/= C
                                            ->
                                            (
                                              NTP4VCPath
                                                A C F G E I K
                                            )
                                          )
                                          /\
                                          (
                                            A. n e. A
                                              (
                                                n e. D
                                                ->
                                                (
                                                  ( O ` n ) = 1
                                                  ->
                                                  (
                                                    NTP4VCReachable
                                                      A C F G E n
                                                  )
                                                )
                                              )
                                            /\
                                            (
                                              (
                                                I = C
                                                ->
                                                J = E
                                              )
                                              /\
                                              (
                                                A. n e. A
                                                  (
                                                    n e. D
                                                    ->
                                                    (
                                                      ( O ` n ) = 1
                                                      ->
                                                      (
                                                        NTP4VCPath
                                                          A C F G E n
                                                          ( L ` n )
                                                      )
                                                    )
                                                  )
                                                /\
                                                (
                                                  A. n e. A
                                                    (
                                                      n e. D
                                                      ->
                                                      (
                                                        n =/= C
                                                        ->
                                                        (
                                                          ( O ` n ) = 1
                                                          ->
                                                          (
                                                            (
                                                              NTP4VCNotInStack
                                                                n H B
                                                            )
                                                            ->
                                                            (
                                                              (
                                                                ( M ` n )
                                                                =/= C
                                                                ->
                                                                (
                                                                  O `
                                                                  ( M ` n )
                                                                ) = 1
                                                              )
                                                              /\
                                                              (
                                                                ( N ` n )
                                                                =/= C
                                                                ->
                                                                (
                                                                  O `
                                                                  ( N ` n )
                                                                ) = 1
                                                              )
                                                            )
                                                          )
                                                        )
                                                      )
                                                    )
                                                  /\
                                                  A. i e. ZZ
                                                    (
                                                      (
                                                        0 <_ i
                                                        /\
                                                        i < ( # ` H )
                                                      )
                                                      ->
                                                      (
                                                        (
                                                          P `
                                                          (
                                                            NTP4VCAt H i B
                                                          )
                                                        ) = 1
                                                        ->
                                                        (
                                                          (
                                                            M `
                                                            (
                                                              NTP4VCAt H i B
                                                            )
                                                          ) =/= C
                                                          ->
                                                          (
                                                            O `
                                                            (
                                                              M `
                                                              (
                                                                NTP4VCAt H i B
                                                              )
                                                            )
                                                          ) = 1
                                                        )
                                                        /\
                                                        (
                                                          (
                                                            N `
                                                            (
                                                              NTP4VCAt H i B
                                                            )
                                                          ) =/= C
                                                          ->
                                                          (
                                                            O `
                                                            (
                                                              N `
                                                              (
                                                                NTP4VCAt H i B
                                                              )
                                                            )
                                                          ) = 1
                                                        )
                                                      )
                                                    )
                                                )
                                              )
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d n A B C D E F G H I J K L M N O P Q R $.

  ntp4vc-pop-definition $a |- (
    NTP4VCPop A B C D E F G H I J K L M N O P Q R
  ) <-> (
    0 < ( # ` H )
    /\
    (
      (
        A. n e. A
          (
            ( NTP4VCNotInStack n H B )
            ->
            ( NTP4VCNotInStack n ( NTP4VCTail H ) B )
          )
      )
      ->
      (
        I =/= C
        /\
        (
          I =/= C
          /\
          (
            (
              (
                0 <_ ( # ` Q )
                /\
                ( # ` Q ) < ( # ` Q )
              )
              \/
              (
                0 <_ ( # ` R )
                /\
                ( # ` R ) < ( # ` R )
              )
              \/
              (
                0 <_ ( # ` H )
                /\
                ( # ` ( NTP4VCTail H ) ) < ( # ` H )
              )
            )
            /\
            (
              NTP4VCInv
                A B C D E F G
                ( NTP4VCTail H )
                ( N ` I )
                I
                ( L ` ( N ` I ) )
                L
                M
                ( NTP4VCUpdate N I J A )
                O P Q R
            )
          )
        )
      )
    )
  ) $.
$}

ntp4vc-swing-definition $a |- (
  NTP4VCSwing A B C D E F G H I J K L M N O P Q R
) <-> (
  I =/= C
  /\
  (
    I =/= C
    /\
    (
      I =/= C
      /\
      (
        I =/= C
        /\
        (
          I =/= C
          /\
          (
            (
              (
                0 <_ ( # ` Q )
                /\
                ( # ` Q ) < ( # ` Q )
              )
              \/
              (
                (
                  0 <_ ( # ` R )
                  /\
                  ( # ` ( R \ { I } ) ) < ( # ` R )
                )
                \/
                (
                  ( # ` R ) = ( # ` ( R \ { I } ) )
                  /\
                  (
                    0 <_ ( # ` H )
                    /\
                    ( # ` H ) < ( # ` H )
                  )
                )
              )
            )
            /\
            (
              NTP4VCInv
                A B C D E F G H I
                ( N ` I )
                K L
                ( NTP4VCUpdate M I J A )
                ( NTP4VCUpdate N I ( M ` I ) A )
                O
                ( NTP4VCUpdate P I 1 A )
                Q
                ( R \ { I } )
            )
          )
        )
      )
    )
  )
) $.

${
  $d i A B C $.

  ntp4vc-cons-law-definition $a |- (
    NTP4VCConsLaw A B C
  ) <-> (
    (
      ( # ` ( <" B "> ++ A ) )
      =
      ( 1 + ( # ` A ) )
    )
    /\
    (
      ( NTP4VCAt ( <" B "> ++ A ) 0 C ) = B
      /\
      A. i e. ZZ
        (
          (
            0 < i
            /\
            i <_ ( # ` A )
          )
          ->
          (
            NTP4VCAt ( <" B "> ++ A ) i C
          )
          =
          ( NTP4VCAt A ( i - 1 ) C )
        )
    )
  ) $.
$}

ntp4vc-push-non-root-definition $a |- (
  NTP4VCPushNonRoot A B C D E F G H I J K L M N O P Q R
) <-> (
  J =/= C
  /\
  (
    J =/= C
    /\
    (
      (
        (
          0 <_ ( # ` Q )
          /\
          ( # ` ( Q \ { J } ) ) < ( # ` Q )
        )
        \/
        (
          ( # ` Q ) = ( # ` ( Q \ { J } ) )
          /\
          (
            (
              0 <_ ( # ` R )
              /\
              ( # ` ( R u. { J } ) ) < ( # ` R )
            )
            \/
            (
              ( # ` R ) = ( # ` ( R u. { J } ) )
              /\
              (
                0 <_ ( # ` H )
                /\
                ( # ` ( <" J "> ++ H ) ) < ( # ` H )
              )
            )
          )
        )
      )
      /\
      (
        NTP4VCInv
          A B C D E F G
          ( <" J "> ++ H )
          J
          ( M ` J )
          ( K ++ <" I "> )
          ( NTP4VCUpdate L J ( K ++ <" I "> ) A )
          ( NTP4VCUpdate M J I A )
          N
          ( NTP4VCUpdate O J 1 A )
          ( NTP4VCUpdate P J 0 A )
          ( Q \ { J } )
          ( R u. { J } )
      )
    )
  )
) $.

ntp4vc-push-root-definition $a |- (
  NTP4VCPushRoot A B C D E F G H I J K L M N O P Q R
) <-> (
  J =/= C
  /\
  (
    J =/= C
    /\
    (
      (
        (
          0 <_ ( # ` Q )
          /\
          ( # ` ( Q \ { J } ) ) < ( # ` Q )
        )
        \/
        (
          ( # ` Q ) = ( # ` ( Q \ { J } ) )
          /\
          (
            (
              0 <_ ( # ` R )
              /\
              ( # ` ( R u. { J } ) ) < ( # ` R )
            )
            \/
            (
              ( # ` R ) = ( # ` ( R u. { J } ) )
              /\
              (
                0 <_ ( # ` H )
                /\
                ( # ` ( <" J "> ++ H ) ) < ( # ` H )
              )
            )
          )
        )
      )
      /\
      (
        NTP4VCInv
          A B C D E F G
          ( <" J "> ++ H )
          J
          ( M ` J )
          (/)
          ( NTP4VCUpdate L J (/) A )
          ( NTP4VCUpdate M J I A )
          N
          ( NTP4VCUpdate O J 1 A )
          ( NTP4VCUpdate P J 0 A )
          ( Q \ { J } )
          ( R u. { J } )
      )
    )
  )
) $.

ntp4vc-push-definition $a |- (
  NTP4VCPush A B C D E F G H I J K L M N O P Q R
) <-> (
  ( NTP4VCConsLaw H J B )
  ->
  (
    J =/= C
    /\
    (
      J =/= C
      /\
      (
        J =/= C
        /\
        (
          (
            J =/= E
            ->
            (
              NTP4VCPushNonRoot
                A B C D E F G H I J K L M N O P Q R
            )
          )
          /\
          (
            J = E
            ->
            (
              NTP4VCPushRoot
                A B C D E F G H I J K L M N O P Q R
            )
          )
        )
      )
    )
  )
) $.

${
  $d n x A B C D E F G H I J $.

  $(
    Arguments are U, null, graph, root, original-left, original-right,
    current-left, current-right, current-mark, and default inhabitant.
  $)
  ntp4vc-post-definition $a |- (
    NTP4VCPost A B C D E F G H I J
  ) <-> (
    (
      A. n e. A
        (
          n e. C
          ->
          (
            ( E ` n ) = ( G ` n )
            /\
            ( F ` n ) = ( H ` n )
          )
        )
    )
    /\
    (
      (
        A. n e. A
          (
            n e. C
            ->
            (
              ( I ` n ) = 1
              ->
              ( NTP4VCReachable A B E F D n )
            )
          )
      )
      /\
      (
        ( I ` D ) = 1
        /\
        A. n e. A
          (
            n e. C
            ->
            (
              ( I ` n ) = 1
              ->
              A. x e. A
                (
                  ( NTP4VCEdge n x G H B )
                  ->
                  (
                    x =/= B
                    ->
                    ( I ` x ) = 1
                  )
                )
            )
          )
      )
    )
  ) $.
$}

${
  $d c f i l m n o p q r s t u x
     A B C D E F G H I J K L M N O P Q R $.

  $(
    Arguments are U, default, null, graph, root, original-left,
    original-right.
  $)
  ntp4vc-loop-definition $a |- (
    NTP4VCLoop A B C D E F G
  ) <-> (
    A. r e. ( NTP4VCFSet A )
      A. q e. ( NTP4VCFSet A )
        A. l e. Word A
          A. s e. Word A
            A. p e. A
              A. t e. A
                A. u e. ( ( Word A ) ^m A )
                  A. x e. ( A ^m A )
                    A. n e. ( A ^m A )
                      A. c e. ( { 0 , 1 } ^m A )
                        A. m e. ( { 0 , 1 } ^m A )
                          (
                            (
                              NTP4VCInv
                                A B C D E F G s p t l u n x m c q r
                            )
                            ->
                            A. o e. { 0 , 1 }
                              (
                                o = if (
                                  p =/= C ,
                                  1 ,
                                  if (
                                    t =/= C ,
                                    if ( ( m ` t ) = 1 , 0 , 1 ) ,
                                    0
                                  )
                                )
                                ->
                                (
                                  (
                                    o = 1
                                    ->
                                    A. i e. { 0 , 1 }
                                      (
                                        i = if (
                                          t = C ,
                                          1 ,
                                          ( m ` t )
                                        )
                                        ->
                                        (
                                          (
                                            i = 1
                                            ->
                                            (
                                              p =/= C
                                              /\
                                              (
                                                (
                                                  ( c ` p ) = 1
                                                  ->
                                                  (
                                                    NTP4VCPop
                                                      A B C D E F G
                                                      s p t l u n x
                                                      m c q r
                                                  )
                                                )
                                                /\
                                                (
                                                  ( c ` p ) =/= 1
                                                  ->
                                                  (
                                                    NTP4VCSwing
                                                      A B C D E F G
                                                      s p t l u n x
                                                      m c q r
                                                  )
                                                )
                                              )
                                            )
                                          )
                                          /\
                                          (
                                            i =/= 1
                                            ->
                                            (
                                              NTP4VCPush
                                                A B C D E F G
                                                s p t l u n x
                                                m c q r
                                            )
                                          )
                                        )
                                      )
                                  )
                                  /\
                                  (
                                    o =/= 1
                                    ->
                                    (
                                      NTP4VCPost
                                        A C D E F G n x m B
                                    )
                                  )
                                )
                              )
                          )
  ) $.
$}

ntp4vc-initial-definition $a |- (
  NTP4VCInitial A B C D E F G H I J
) <-> (
  E =/= C
  /\
  (
    NTP4VCInv
      A B C D E F G
      (/)
      C
      E
      (/)
      ( NTP4VCUpdate J E (/) A )
      F G H I D D
  )
) $.

ntp4vc-schorr-waite-vc-definition $a |- (
  NTP4VCSchorrWaiteVC A B C D E F G H I J
) <-> (
  ( NTP4VCInitial A B C D E F G H I J )
  /\
  ( NTP4VCLoop A B C D E F G )
) $.

${
  $d n x A B C D E F G H I J K $.

  $( Source parameters:
     A=loc, B=default inhabitant, C=null, D=graph, E=root,
     F=left, G=right, H=m, I=c, J=path_from_root. $)

  ntp4vc-location-carrier-nonempty $e |- A =/= (/) $.
  ntp4vc-default-location $e |- B e. A $.
  ntp4vc-null-location $e |- C e. A $.
  ntp4vc-graph-finite $e |- D e. ( NTP4VCFSet A ) $.
  ntp4vc-root-location $e |- E e. A $.
  ntp4vc-left-function $e |- F e. ( A ^m A ) $.
  ntp4vc-right-function $e |- G e. ( A ^m A ) $.
  ntp4vc-mark-function $e |- H e. ( { 0 , 1 } ^m A ) $.
  ntp4vc-direction-function $e |- I e. ( { 0 , 1 } ^m A ) $.
  ntp4vc-path-map $e |- J e. ( ( Word A ) ^m A ) $.

  ntp4vc-fact0 $e |- E =/= C $.
  ntp4vc-fact1 $e |- E e. D $.
  ntp4vc-fact2 $e |- A. n e. A
    (
      n e. D
      ->
      (
        n =/= C
        /\
        (
          (
            ( F ` n ) = C
            \/
            ( F ` n ) e. D
          )
          /\
          (
            ( G ` n ) = C
            \/
            ( G ` n ) e. D
          )
        )
      )
    ) $.
  ntp4vc-fact3 $e |- A. x e. A
    (
      x e. D
      ->
      ( H ` x ) =/= 1
    ) $.

  ntp4vc-pearl-schorr-waite-schorr-waite-vc $a |- (
    NTP4VCSchorrWaiteVC A B C D E F G H I J
  ) $.
$}
