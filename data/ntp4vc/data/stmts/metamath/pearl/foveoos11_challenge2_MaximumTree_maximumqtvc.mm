$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/foveoos11_challenge2_MaximumTree_maximumqtvc: the maximum-tree
  verification condition establishes the recursive size obligations for a
  nonempty integer-labelled binary tree and states that a result assembled
  from subtree maxima is a member and an upper bound of the whole tree.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  T is exactly the source inductive carrier of finite integer-labelled binary
  trees. NTP4VCEmpty and NTP4VCNode are disjoint injective tagged
  constructors; closure, exhaustiveness, and structural induction exclude
  missing finite trees, extraneous values, and non-well-founded trees.

  S is the source integer-valued recursive size function and M is the source
  membership relation. Their displayed Empty and Node equations are the
  complete recursive definitions over T and the full integer domain ZZ.

  NTP4VCMax is integer maximum. NTP4VCMaximum says that an integer occurs in
  a given tree and bounds every integer occurring there. The two source tree
  matches are expanded into their disjoint leaf, one-nonempty-subtree, and
  two-nonempty-subtree cases; their impossible Empty branches are omitted.
  Every subtree maximum witness remains existentially quantified inside the
  original result antecedent, while result retains its universal integer
  scope. The final $a declaration is Metamath's native unproved statement
  encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCEmpty NTP4VCNode NTP4VCMax NTP4VCMaximum
  NTP4VCInitialObligation NTP4VCResultAntecedent
$.

ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-node-syntax $a class ( NTP4VCNode A B C ) $.
ntp4vc-max-syntax $a class ( NTP4VCMax A B ) $.
ntp4vc-maximum-syntax $a wff ( NTP4VCMaximum A B C ) $.
ntp4vc-initial-obligation-syntax
  $a wff ( NTP4VCInitialObligation A B C D ) $.
ntp4vc-result-antecedent-syntax
  $a wff ( NTP4VCResultAntecedent A B C D ) $.

ntp4vc-empty-def $a |- NTP4VCEmpty = <. 0 , (/) >. $.

ntp4vc-node-def $a |- ( NTP4VCNode A B C ) =
  <. 1 , <. A , <. B , C >. >. >. $.

ntp4vc-max-def $a |- ( NTP4VCMax A B ) =
  if ( A <_ B , B , A ) $.

${
  $d x A B C $.

  ntp4vc-maximum-def $a |- (
    ( NTP4VCMaximum A B C )
    <->
    (
      <. A , B >. e. C
      /\
      A. x e. ZZ
        (
          <. x , B >. e. C
          ->
          x <_ A
        )
    )
  ) $.
$}

${
  $d l o r s v x A B C D $.

  $(
    A=t, B=tree, C=mem, and D=size. This is the first source match.
    Its Empty branch is False and therefore contributes no disjunct.
  $)
  ntp4vc-initial-obligation-def $a |- (
    ( NTP4VCInitialObligation A B C D )
    <->
    (
      E. v e. ZZ
        A = ( NTP4VCNode NTP4VCEmpty v NTP4VCEmpty )
      \/
      (
        E. v e. ZZ E. s e. B
          (
            s =/= NTP4VCEmpty
            /\
            (
              A = ( NTP4VCNode NTP4VCEmpty v s )
              /\
              (
                (
                  0 <_ ( D ` A )
                  /\
                  ( D ` s ) < ( D ` A )
                )
                /\
                s =/= NTP4VCEmpty
              )
            )
          )
        \/
        (
          E. s e. B E. v e. ZZ
            (
              s =/= NTP4VCEmpty
              /\
              (
                A = ( NTP4VCNode s v NTP4VCEmpty )
                /\
                (
                  (
                    0 <_ ( D ` A )
                    /\
                    ( D ` s ) < ( D ` A )
                  )
                  /\
                  s =/= NTP4VCEmpty
                )
              )
            )
          \/
          E. l e. B E. v e. ZZ E. r e. B
            (
              l =/= NTP4VCEmpty
              /\
              (
                r =/= NTP4VCEmpty
                /\
                (
                  A = ( NTP4VCNode l v r )
                  /\
                  (
                    (
                      (
                        0 <_ ( D ` A )
                        /\
                        ( D ` r ) < ( D ` A )
                      )
                      /\
                      r =/= NTP4VCEmpty
                    )
                    /\
                    A. o e. ZZ
                      (
                        ( NTP4VCMaximum o r C )
                        ->
                        (
                          (
                            0 <_ ( D ` A )
                            /\
                            ( D ` l ) < ( D ` A )
                          )
                          /\
                          l =/= NTP4VCEmpty
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
  $d l o p r s v A B C D $.

  $(
    A=result, B=t, C=tree, and D=mem. This is the antecedent match in
    the universally quantified postcondition. Its Empty branch is False.
  $)
  ntp4vc-result-antecedent-def $a |- (
    ( NTP4VCResultAntecedent A B C D )
    <->
    (
      E. v e. ZZ
        (
          B = ( NTP4VCNode NTP4VCEmpty v NTP4VCEmpty )
          /\
          A = v
        )
      \/
      (
        E. v e. ZZ E. s e. C
          (
            s =/= NTP4VCEmpty
            /\
            (
              B = ( NTP4VCNode NTP4VCEmpty v s )
              /\
              E. o e. ZZ
                (
                  ( NTP4VCMaximum o s D )
                  /\
                  A = ( NTP4VCMax o v )
                )
            )
          )
        \/
        (
          E. s e. C E. v e. ZZ
            (
              s =/= NTP4VCEmpty
              /\
              (
                B = ( NTP4VCNode s v NTP4VCEmpty )
                /\
                E. o e. ZZ
                  (
                    ( NTP4VCMaximum o s D )
                    /\
                    A = ( NTP4VCMax o v )
                  )
              )
            )
          \/
          E. l e. C E. v e. ZZ E. r e. C
            (
              l =/= NTP4VCEmpty
              /\
              (
                r =/= NTP4VCEmpty
                /\
                (
                  B = ( NTP4VCNode l v r )
                  /\
                  E. o e. ZZ
                    (
                      ( NTP4VCMaximum o r D )
                      /\
                      E. p e. ZZ
                        (
                          ( NTP4VCMaximum p l D )
                          /\
                          A =
                            (
                              NTP4VCMax
                                p ( NTP4VCMax v o )
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
  $d l o p q r s t v x
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Exact finite inductive binary-tree carrier over the full integers. $)
  ntp4vc-tree-empty-closure $e |- NTP4VCEmpty e. T $.

  ntp4vc-tree-node-closure $e |- A. l e. T A. v e. ZZ A. r e. T
    ( NTP4VCNode l v r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCEmpty
      \/
      E. l e. T E. v e. ZZ E. r e. T
        t = ( NTP4VCNode l v r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      (
        NTP4VCEmpty e. s
        /\
        A. l e. T A. v e. ZZ A. r e. T
          (
            (
              l e. s
              /\
              r e. s
            )
            ->
            ( NTP4VCNode l v r ) e. s
          )
      )
      ->
      s = T
    ) $.

  $( Complete recursive source definitions of size and membership. $)
  ntp4vc-size-function $e |- S e. ( ZZ ^m T ) $.
  ntp4vc-mem-relation $e |- M C_ ( ZZ X. T ) $.

  ntp4vc-size-empty $e |- ( S ` NTP4VCEmpty ) = 0 $.

  ntp4vc-size-node $e |- A. l e. T A. v e. ZZ A. r e. T
    (
      S ` ( NTP4VCNode l v r )
    )
    =
    (
      ( 1 + ( S ` l ) )
      +
      ( S ` r )
    ) $.

  ntp4vc-mem-empty $e |- A. x e. ZZ
    -. <. x , NTP4VCEmpty >. e. M $.

  ntp4vc-mem-node $e |- A. x e. ZZ A. l e. T
    A. v e. ZZ A. r e. T
      (
        <. x , ( NTP4VCNode l v r ) >. e. M
        <->
        (
          <. x , l >. e. M
          \/
          (
            x = v
            \/
            <. x , r >. e. M
          )
        )
      ) $.

  $( Source theorem parameter A=t and its sole assumption fact0. $)
  ntp4vc-t-tree $e |- A e. T $.
  ntp4vc-fact0 $e |- A =/= NTP4VCEmpty $.

  ntp4vc-pearl-foveoos11-challenge2-maximum-tree-maximum-vc $a |- (
    ( NTP4VCInitialObligation A T M S )
    /\
    A. q e. ZZ
      (
        ( NTP4VCResultAntecedent q A T M )
        ->
        (
          <. q , A >. e. M
          /\
          A. x e. ZZ
            (
              <. x , A >. e. M
              ->
              x <_ q
            )
        )
      )
  ) $.
$}
