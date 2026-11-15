$(
  Statement-only formalization of "The Independence of the Parallel
  Postulate" from Hundred Theorems item 012: the real Klein disc is a model
  of Tarski's axioms 1 through 9 and 11 in which the Euclidean parallel
  axiom 10 is false. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  HT012KDisk is the open unit disc in RR X. RR. Its elements are the concrete
  representatives of the HOL Light subtype, so equality is ordinary ordered-
  pair equality. HT012Bet is Euclidean closed-segment betweenness in that
  disc. HT012Cong compares the Klein semimetric

             (1 - x dot y)^2
    -------------------------------------- - 1.
    (1 - ||x||^2) x. (1 - ||y||^2)

  The definitions below are equalities or biconditionals in set.mm, rather
  than informal typings. All point quantifiers in the final assertion are
  restricted to HT012KDisk, while X and Y in axiom 11 range over arbitrary
  sets. The last declaration is an unproved $a statement.
$)

$c HT012KDisk HT012Dist HT012Bet HT012Cong $.

ht012-kdisk-syntax $a class HT012KDisk $.
ht012-dist-syntax $a class ( A HT012Dist B ) $.
ht012-bet-syntax $a wff HT012Bet A B C $.
ht012-cong-syntax $a wff HT012Cong A B C D $.

ht012-kdisk-definition $a |- HT012KDisk =
  { z e. ( RR X. RR ) |
    (
      (
        ( ( 1st ` z ) ^ 2 )
        +
        ( ( 2nd ` z ) ^ 2 )
      )
      <
      1
    )
  } $.

ht012-distance-definition $a |- ( A HT012Dist B ) =
  (
    (
      (
        (
          1
          -
          (
            ( ( 1st ` A ) x. ( 1st ` B ) )
            +
            ( ( 2nd ` A ) x. ( 2nd ` B ) )
          )
        )
        ^ 2
      )
      /
      (
        (
          1
          -
          (
            ( ( 1st ` A ) ^ 2 )
            +
            ( ( 2nd ` A ) ^ 2 )
          )
        )
        x.
        (
          1
          -
          (
            ( ( 1st ` B ) ^ 2 )
            +
            ( ( 2nd ` B ) ^ 2 )
          )
        )
      )
    )
    -
    1
  )
  $.

${
  $d l A B C $.

  ht012-betweenness-definition $a |- (
    HT012Bet A B C
    <->
    E. l e. RR
      (
        (
          ( 0 <_ l )
          /\
          ( l <_ 1 )
        )
        /\
        B
        =
        <.
          (
            ( ( 1 - l ) x. ( 1st ` A ) )
            +
            ( l x. ( 1st ` C ) )
          )
          ,
          (
            ( ( 1 - l ) x. ( 2nd ` A ) )
            +
            ( l x. ( 2nd ` C ) )
          )
        >.
      )
  ) $.
$}

ht012-congruence-definition $a |- (
  HT012Cong A B C D
  <->
  ( A HT012Dist B ) = ( C HT012Dist D )
) $.

${
  $d a b c d e f g h p q r s t u v x y $.

hundred-independence-parallel-postulate $a |- (
  (
    A. a e. HT012KDisk
    A. b e. HT012KDisk
      HT012Cong a b b a
  )
  /\
  (
    (
      A. a e. HT012KDisk
      A. b e. HT012KDisk
      A. p e. HT012KDisk
      A. q e. HT012KDisk
      A. r e. HT012KDisk
      A. s e. HT012KDisk
        (
          (
            HT012Cong a b p q
            /\
            HT012Cong a b r s
          )
          ->
          HT012Cong p q r s
        )
    )
    /\
    (
      (
        A. a e. HT012KDisk
        A. b e. HT012KDisk
        A. c e. HT012KDisk
          (
            HT012Cong a b c c
            ->
            a = b
          )
      )
      /\
      (
        (
          A. q e. HT012KDisk
          A. a e. HT012KDisk
          A. b e. HT012KDisk
          A. c e. HT012KDisk
          E. x e. HT012KDisk
            (
              HT012Bet q a x
              /\
              HT012Cong a x b c
            )
        )
        /\
        (
          (
            A. a e. HT012KDisk
            A. b e. HT012KDisk
            A. c e. HT012KDisk
            A. d e. HT012KDisk
            A. e e. HT012KDisk
            A. f e. HT012KDisk
            A. g e. HT012KDisk
            A. h e. HT012KDisk
              (
                (
                  -. a = b
                  /\
                  (
                    HT012Bet a b c
                    /\
                    (
                      HT012Bet e f g
                      /\
                      (
                        HT012Cong a b e f
                        /\
                        (
                          HT012Cong b c f g
                          /\
                          (
                            HT012Cong a d e h
                            /\
                            HT012Cong b d f h
                          )
                        )
                      )
                    )
                  )
                )
                ->
                HT012Cong c d g h
              )
          )
          /\
          (
            (
              A. a e. HT012KDisk
              A. b e. HT012KDisk
                (
                  HT012Bet a b a
                  ->
                  a = b
                )
            )
            /\
            (
              (
                A. a e. HT012KDisk
                A. b e. HT012KDisk
                A. c e. HT012KDisk
                A. p e. HT012KDisk
                A. q e. HT012KDisk
                  (
                    (
                      HT012Bet a p c
                      /\
                      HT012Bet b q c
                    )
                    ->
                    E. x e. HT012KDisk
                      (
                        HT012Bet p x b
                        /\
                        HT012Bet q x a
                      )
                  )
              )
              /\
              (
                (
                  E. a e. HT012KDisk
                  E. b e. HT012KDisk
                  E. c e. HT012KDisk
                    (
                      -. HT012Bet a b c
                      /\
                      (
                        -. HT012Bet b c a
                        /\
                        -. HT012Bet c a b
                      )
                    )
                )
                /\
                (
                  (
                    A. p e. HT012KDisk
                    A. q e. HT012KDisk
                    A. a e. HT012KDisk
                    A. b e. HT012KDisk
                    A. c e. HT012KDisk
                      (
                        (
                          -. p = q
                          /\
                          (
                            HT012Cong a p a q
                            /\
                            (
                              HT012Cong b p b q
                              /\
                              HT012Cong c p c q
                            )
                          )
                        )
                        ->
                        (
                          HT012Bet a b c
                          \/
                          (
                            HT012Bet b c a
                            \/
                            HT012Bet c a b
                          )
                        )
                      )
                  )
                  /\
                  (
                    (
                      -.
                      A. a e. HT012KDisk
                      A. b e. HT012KDisk
                      A. c e. HT012KDisk
                      A. d e. HT012KDisk
                      A. t e. HT012KDisk
                        (
                          (
                            HT012Bet a d t
                            /\
                            (
                              HT012Bet b d c
                              /\
                              -. a = d
                            )
                          )
                          ->
                          E. x e. HT012KDisk
                          E. y e. HT012KDisk
                            (
                              HT012Bet a b x
                              /\
                              (
                                HT012Bet a c y
                                /\
                                HT012Bet x t y
                              )
                            )
                        )
                    )
                    /\
                    (
                      A. u
                      A. v
                        (
                          (
                            u C_ HT012KDisk
                            /\
                            v C_ HT012KDisk
                          )
                          ->
                          (
                            (
                              E. a e. HT012KDisk
                              A. x e. u
                              A. y e. v
                                HT012Bet a x y
                            )
                            ->
                            E. b e. HT012KDisk
                            A. x e. u
                            A. y e. v
                              HT012Bet x b y
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
