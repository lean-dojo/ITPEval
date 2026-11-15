$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/foveoos11_cm/tree_max_TreeMax_max_auxqtvc: the auxiliary tree-maximum
  verification condition propagates integer upper bounds and membership
  witnesses from the right and left subtrees to the whole binary tree.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  T is exactly the source inductive carrier of finite integer-labelled binary
  trees. NTP4VCNull and NTP4VCTree are disjoint injective tagged
  constructors; closure, exhaustiveness, and structural induction exclude
  missing finite trees, extraneous values, and non-well-founded trees.

  G and M represent the source ge_tree and mem relations. Their Null and Tree
  equations below are the complete recursive definitions over T and the full
  integer domain ZZ. NTP4VCMax is integer maximum.

  NTP4VCInitial expands the first source match into its disjoint Null and Tree
  cases. NTP4VCResultAntecedent similarly expands the match in the universally
  quantified postcondition. The repeated matches on the same Tree retain the
  source equalities l = r or r = r and l = l or r = l. The subtree-maximum
  witness o remains existentially quantified inside the result antecedent,
  while result retains its universal integer scope. The final $a declaration
  is Metamath's native unproved statement encoding; this database contains no
  $p proof declaration.
$)

$c
  NTP4VCNull NTP4VCTree NTP4VCMax
  NTP4VCInitial NTP4VCResultAntecedent
$.

ntp4vc-null-syntax $a class NTP4VCNull $.
ntp4vc-tree-syntax $a class ( NTP4VCTree A B C ) $.
ntp4vc-max-syntax $a class ( NTP4VCMax A B ) $.
ntp4vc-initial-syntax $a wff ( NTP4VCInitial A B C D E ) $.
ntp4vc-result-antecedent-syntax
  $a wff ( NTP4VCResultAntecedent A B C D E F ) $.

ntp4vc-null-def $a |- NTP4VCNull = <. 0 , (/) >. $.

ntp4vc-tree-def $a |- ( NTP4VCTree A B C ) =
  <. 1 , <. A , <. B , C >. >. >. $.

ntp4vc-max-def $a |- ( NTP4VCMax A B ) =
  if ( A <_ B , B , A ) $.

${
  $d l o r v A B C D E $.

  $(
    A=t, B=acc, C=tree, D=ge_tree, and E=mem. This is the first
    source match. Its Null branch is True.
  $)
  ntp4vc-initial-def $a |- (
    ( NTP4VCInitial A B C D E )
    <->
    (
      A = NTP4VCNull
      \/
      E. v e. ZZ E. l e. C E. r e. C
        (
          A = ( NTP4VCTree v l r )
          /\
          (
            (
              l = r
              \/
              r = r
            )
            /\
            A. o e. ZZ
              (
                (
                  <. o , r >. e. D
                  /\
                  (
                    ( NTP4VCMax v B ) <_ o
                    /\
                    (
                      o = ( NTP4VCMax v B )
                      \/
                      <. o , r >. e. E
                    )
                  )
                )
                ->
                (
                  l = l
                  \/
                  r = l
                )
              )
          )
        )
    )
  ) $.
$}

${
  $d l o r v A B C D E F $.

  $(
    A=result, B=t, C=acc, D=tree, E=ge_tree, and F=mem. This is
    the antecedent match in the universally quantified postcondition.
  $)
  ntp4vc-result-antecedent-def $a |- (
    ( NTP4VCResultAntecedent A B C D E F )
    <->
    (
      (
        B = NTP4VCNull
        /\
        A = C
      )
      \/
      E. v e. ZZ E. l e. D E. r e. D
        (
          B = ( NTP4VCTree v l r )
          /\
          E. o e. ZZ
            (
              (
                <. o , r >. e. E
                /\
                (
                  ( NTP4VCMax v C ) <_ o
                  /\
                  (
                    o = ( NTP4VCMax v C )
                    \/
                    <. o , r >. e. F
                  )
                )
              )
              /\
              (
                <. A , l >. e. E
                /\
                (
                  o <_ A
                  /\
                  (
                    A = o
                    \/
                    <. A , l >. e. F
                  )
                )
              )
            )
        )
    )
  ) $.
$}

${
  $d l o q r s t v x
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Exact finite inductive binary-tree carrier over the full integers. $)
  ntp4vc-tree-null-closure $e |- NTP4VCNull e. T $.

  ntp4vc-tree-node-closure $e |- A. v e. ZZ A. l e. T A. r e. T
    ( NTP4VCTree v l r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCNull
      \/
      E. v e. ZZ E. l e. T E. r e. T
        t = ( NTP4VCTree v l r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      (
        NTP4VCNull e. s
        /\
        A. v e. ZZ A. l e. T A. r e. T
          (
            (
              l e. s
              /\
              r e. s
            )
            ->
            ( NTP4VCTree v l r ) e. s
          )
      )
      ->
      s = T
    ) $.

  $( Complete recursive source definitions of ge_tree and membership. $)
  ntp4vc-ge-tree-relation $e |- G C_ ( ZZ X. T ) $.
  ntp4vc-mem-relation $e |- M C_ ( ZZ X. T ) $.

  ntp4vc-ge-tree-null $e |- A. x e. ZZ
    <. x , NTP4VCNull >. e. G $.

  ntp4vc-ge-tree-node $e |- A. x e. ZZ A. v e. ZZ
    A. l e. T A. r e. T
      (
        <. x , ( NTP4VCTree v l r ) >. e. G
        <->
        (
          v <_ x
          /\
          (
            <. x , l >. e. G
            /\
            <. x , r >. e. G
          )
        )
      ) $.

  ntp4vc-mem-null $e |- A. x e. ZZ
    -. <. x , NTP4VCNull >. e. M $.

  ntp4vc-mem-node $e |- A. x e. ZZ A. v e. ZZ
    A. l e. T A. r e. T
      (
        <. x , ( NTP4VCTree v l r ) >. e. M
        <->
        (
          x = v
          \/
          (
            <. x , l >. e. M
            \/
            <. x , r >. e. M
          )
        )
      ) $.

  $( Source theorem parameters A=t and B=acc. $)
  ntp4vc-t-tree $e |- A e. T $.
  ntp4vc-acc-integer $e |- B e. ZZ $.

  ntp4vc-pearl-foveoos11-cm-tree-max-tree-max-max-aux-vc $a |- (
    ( NTP4VCInitial A B T G M )
    /\
    A. q e. ZZ
      (
        ( NTP4VCResultAntecedent q A B T G M )
        ->
        (
          <. q , A >. e. G
          /\
          (
            B <_ q
            /\
            (
              q = B
              \/
              <. q , A >. e. M
            )
          )
        )
      )
  ) $.
$}
