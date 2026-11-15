$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/queens_NQueensSetsTermination_tqtvc: the N-queens set-based
  termination verification condition preserves the remaining-choice subset
  invariant and establishes strict cardinal decreases after removing the
  selected minimum integer. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NTP4VCFSet is exactly the source carrier of finite sets of integers.
  NTP4VCMinElt uses restricted definite description for the unique least
  member of a finite nonempty integer set. The source invokes min_elt only
  under the explicit nonempty premise retained below, so this definition is
  extensionally identical there.

  Source insertion and removal are singleton union and set difference.
  Cardinality is SetMM finite cardinality, and the source succ and pred set
  specifications remain pointwise biconditionals over the full integer
  domain. Proposition-valued conditionals are rendered by their equivalent
  pairs of guarded implications. The otherwise unused source integers f and
  o8 retain their original universal scopes. The final $a declaration is
  Metamath's native unproved statement encoding; this database has no $p
  proof declaration.
$)

$c NTP4VCFSet NTP4VCMinElt $.

ntp4vc-fset-syntax $a class NTP4VCFSet $.
ntp4vc-min-elt-syntax $a class ( NTP4VCMinElt A ) $.

${
  ntp4vc-fset-definition $a |- NTP4VCFSet = {
    s e. Fin | s C_ ZZ
  } $.
$}

${
  $d d x A $.

  ntp4vc-min-elt-definition $a |- (
    NTP4VCMinElt A
  ) = (
    iota_ d e. A A. x e. A d <_ x
  ) $.
$}

${
  $d d e f i p q r s t u v x
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source theorem parameters A=a, B=o1, C=b, D=o2, E=c. $)
  ntp4vc-a-fset $e |- A e. NTP4VCFSet $.
  ntp4vc-o1-fset $e |- B e. NTP4VCFSet $.
  ntp4vc-b-fset $e |- C e. NTP4VCFSet $.
  ntp4vc-o2-fset $e |- D e. NTP4VCFSet $.
  ntp4vc-c-fset $e |- E e. NTP4VCFSet $.

  ntp4vc-fact0 $e |- A =/= (/) $.
  ntp4vc-fact1 $e |- B = ( A \ C ) $.
  ntp4vc-fact2 $e |- D = ( B \ E ) $.

  ntp4vc-pearl-queens-nqueens-sets-termination-vc $a |- (
    D C_ ( ( A \ C ) \ E )
    /\
    A. f e. ZZ A. e e. NTP4VCFSet
      (
        e C_ ( ( A \ C ) \ E )
        ->
        (
          e =/= (/)
          ->
          (
            e =/= (/)
            /\
            A. p e. NTP4VCFSet
              (
                (
                  p = ( E u. { ( NTP4VCMinElt e ) } )
                  /\
                  (
                    (
                      ( NTP4VCMinElt e ) e. E
                      ->
                      ( # ` p ) = ( # ` E )
                    )
                    /\
                    (
                      -. ( NTP4VCMinElt e ) e. E
                      ->
                      ( # ` p ) = ( ( # ` E ) + 1 )
                    )
                  )
                )
                ->
                A. q e. NTP4VCFSet
                  (
                    A. i e. ZZ
                      (
                        i e. q
                        <->
                        (
                          0 <_ i
                          /\
                          ( i + 1 ) e. p
                        )
                      )
                    ->
                    A. r e. NTP4VCFSet
                      (
                        (
                          r = ( C u. { ( NTP4VCMinElt e ) } )
                          /\
                          (
                            (
                              ( NTP4VCMinElt e ) e. C
                              ->
                              ( # ` r ) = ( # ` C )
                            )
                            /\
                            (
                              -. ( NTP4VCMinElt e ) e. C
                              ->
                              ( # ` r ) = ( ( # ` C ) + 1 )
                            )
                          )
                        )
                        ->
                        A. s e. NTP4VCFSet
                          (
                            A. i e. ZZ
                              (
                                i e. s
                                <->
                                (
                                  1 <_ i
                                  /\
                                  ( i - 1 ) e. r
                                )
                              )
                            ->
                            A. t e. NTP4VCFSet
                              (
                                (
                                  t = ( A \ { ( NTP4VCMinElt e ) } )
                                  /\
                                  (
                                    (
                                      ( NTP4VCMinElt e ) e. A
                                      ->
                                      ( # ` t ) = ( ( # ` A ) - 1 )
                                    )
                                    /\
                                    (
                                      -. ( NTP4VCMinElt e ) e. A
                                      ->
                                      ( # ` t ) = ( # ` A )
                                    )
                                  )
                                )
                                ->
                                (
                                  (
                                    0 <_ ( # ` A )
                                    /\
                                    ( # ` t ) < ( # ` A )
                                  )
                                  /\
                                  A. u e. ZZ A. v e. NTP4VCFSet
                                    (
                                      (
                                        v =
                                          ( e \ {
                                            ( NTP4VCMinElt e )
                                          } )
                                        /\
                                        (
                                          (
                                            ( NTP4VCMinElt e ) e. e
                                            ->
                                            ( # ` v ) =
                                              ( ( # ` e ) - 1 )
                                          )
                                          /\
                                          (
                                            -. ( NTP4VCMinElt e ) e. e
                                            ->
                                            ( # ` v ) = ( # ` e )
                                          )
                                        )
                                      )
                                      ->
                                      (
                                        (
                                          0 <_ ( # ` e )
                                          /\
                                          ( # ` v ) < ( # ` e )
                                        )
                                        /\
                                        v C_ ( ( A \ C ) \ E )
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
