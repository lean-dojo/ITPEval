$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/binomial_heap_BinomialHeap_get_minqtvc: the binomial-heap get-min
  verification condition shows that the recursive scan of a nonempty
  heap-ordered forest returns an element of the forest that is no greater
  than every element in it. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier elt, D is its total preorder,
  and T is the source inductive tree carrier. NTP4VCTreeMk is an injective
  tagged encoding of tree.mk, and NTP4VCElem is its element projection.
  Closure, exhaustiveness, and structural induction give T exactly the finite
  well-founded trees whose children are arbitrary finite words over T, rather
  than a finite approximation or an uninterpreted collection of tags.

  L, H, and O represent le_roots, heaps, and occ. Their base and constructor
  equations below are the complete source recursive definitions over SetMM
  words and the full integer domain ZZ. NTP4VCMem expands the source mem
  definition as strict positivity of the integer occurrence count.

  NTP4VCScanContract is the source contract for one recursive scan. Its first
  conjunct expands the match whose empty case is True and whose nonempty case
  preserves the tail heap after comparing its root with the current minimum.
  Its second conjunct expands the result match, including the internally
  existential comparison value, membership alternative, and lower-bound
  obligations. The final assertion expands the outer nonempty-list match with
  internal head and tail witnesses. Every element and list quantifier retains
  its source scope. The final $a declaration is Metamath's native unproved
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCTreeMk NTP4VCElem NTP4VCMem NTP4VCScanContract
$.

ntp4vc-tree-mk-syntax
  $a class ( NTP4VCTreeMk A B C ) $.
ntp4vc-elem-syntax
  $a class ( NTP4VCElem A ) $.
ntp4vc-mem-syntax
  $a wff ( NTP4VCMem A B C ) $.
ntp4vc-scan-contract-syntax
  $a wff ( NTP4VCScanContract A B C D E F G ) $.

ntp4vc-tree-mk-def $a |- (
  NTP4VCTreeMk A B C
) = <. 1 , <. A , <. B , C >. >. >. $.

ntp4vc-elem-def $a |- ( NTP4VCElem A ) =
  ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-mem-def $a |- (
  ( NTP4VCMem A B C )
  <->
  0 < ( C ` <. A , B >. )
) $.

${
  $d c m o q r x y z A B C D E F G $.

  $( A=m, B=l1, C=elt, D=tree, E=le, F=heaps, and G=occ. $)
  ntp4vc-scan-contract-def $a |- (
    ( NTP4VCScanContract A B C D E F G )
    <->
    (
      A. x e. C A. c e. Word D A. r e. ZZ A. q e. Word D
        (
          B =
            (
              <" ( NTP4VCTreeMk x c r ) ">
              ++
              q
            )
          ->
          A. o e. C
            (
              o =
                if
                (
                  <. x , A >. e. E ,
                  x ,
                  A
                )
              ->
              (
                q = q
                /\
                q e. F
              )
            )
        )
      /\
      A. y e. C
        (
          (
            (
              B = (/)
              /\
              y = A
            )
            \/
            E. x e. C E. c e. Word D E. r e. ZZ E. q e. Word D
              (
                B =
                  (
                    <" ( NTP4VCTreeMk x c r ) ">
                    ++
                    q
                  )
                /\
                E. o e. C
                  (
                    o =
                      if
                      (
                        <. x , A >. e. E ,
                        x ,
                        A
                      )
                    /\
                    (
                      (
                        y = o
                        \/
                        ( NTP4VCMem y q G )
                      )
                      /\
                      (
                        <. y , o >. e. E
                        /\
                        A. z e. C
                          (
                            ( NTP4VCMem z q G )
                            ->
                            <. y , z >. e. E
                          )
                      )
                    )
                  )
              )
          )
          ->
          (
            (
              y = A
              \/
              ( NTP4VCMem y B G )
            )
            /\
            (
              <. y , A >. e. E
              /\
              A. z e. C
                (
                  ( NTP4VCMem z B G )
                  ->
                  <. y , z >. e. E
                )
            )
          )
        )
    )
  ) $.
$}

${
  $d c e m q r s t x y z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source carrier elt and its total preorder le. $)
  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-le-relation $e |- D C_ ( U X. U ) $.
  ntp4vc-le-reflexive $e |- A. x e. U
    <. x , x >. e. D $.
  ntp4vc-le-transitive $e |- A. x e. U A. y e. U A. z e. U
    (
      (
        <. x , y >. e. D
        /\
        <. y , z >. e. D
      )
      ->
      <. x , z >. e. D
    ) $.
  ntp4vc-le-total $e |- A. x e. U A. y e. U
    (
      <. x , y >. e. D
      \/
      <. y , x >. e. D
    ) $.

  $(
    The source inductive tree type: constructor closure and exhaustiveness,
    plus its structural induction principle over all subsets of T.
  $)
  ntp4vc-tree-constructor-closure $e |- A. e e. U
    A. c e. Word T A. r e. ZZ
      ( NTP4VCTreeMk e c r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    E. e e. U E. c e. Word T E. r e. ZZ
      t = ( NTP4VCTreeMk e c r ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      A. e e. U A. c e. Word T A. r e. ZZ
        (
          ran c C_ s
          ->
          ( NTP4VCTreeMk e c r ) e. s
        )
      ->
      s = T
    ) $.

  $( Types of the three source recursive definitions used by the VC. $)
  ntp4vc-le-roots-relation
    $e |- L C_ ( U X. Word T ) $.
  ntp4vc-heaps-predicate
    $e |- H C_ Word T $.
  ntp4vc-occ-function
    $e |- O e. ( ZZ ^m ( U X. Word T ) ) $.

  $( le_roots equations. $)
  ntp4vc-le-roots-empty $e |- A. e e. U
    <. e , (/) >. e. L $.

  ntp4vc-le-roots-cons $e |- A. e e. U A. x e. U
    A. c e. Word T A. r e. ZZ A. q e. Word T
      (
        <.
          e ,
          (
            <" ( NTP4VCTreeMk x c r ) ">
            ++
            q
          )
        >. e. L
        <->
        (
          <. e , x >. e. D
          /\
          <. e , q >. e. L
        )
      ) $.

  $( heaps equations. $)
  ntp4vc-heaps-empty $e |- (/) e. H $.

  ntp4vc-heaps-cons $e |- A. e e. U A. c e. Word T
    A. r e. ZZ A. q e. Word T
      (
        (
          <" ( NTP4VCTreeMk e c r ) ">
          ++
          q
        ) e. H
        <->
        (
          <. e , c >. e. L
          /\
          ( c e. H /\ q e. H )
        )
      ) $.

  $( occ equations, with integer-valued occurrence counts. $)
  ntp4vc-occ-empty $e |- A. x e. U
    ( O ` <. x , (/) >. ) = 0 $.

  ntp4vc-occ-cons $e |- A. x e. U A. e e. U
    A. c e. Word T A. r e. ZZ A. q e. Word T
      (
        O ` <.
          x ,
          (
            <" ( NTP4VCTreeMk e c r ) ">
            ++
            q
          )
        >.
      )
      =
      (
        (
          if ( x = e , 1 , 0 )
          +
          ( O ` <. x , c >. )
        )
        +
        ( O ` <. x , q >. )
      ) $.

  $( Source theorem parameter A=h, followed by fact0 and fact1. $)
  ntp4vc-h-word $e |- A e. Word T $.
  ntp4vc-fact0 $e |- A e. H $.
  ntp4vc-fact1 $e |- A =/= (/) $.

  ntp4vc-pearl-binomial-heap-get-min-vc $a |-
    E. t e. T E. q e. Word T
      (
        A =
          (
            <" t ">
            ++
            q
          )
        /\
        (
          (
            A. m e. U A. s e. Word T
              (
                s e. H
                ->
                (
                  NTP4VCScanContract
                    m s U T D H O
                )
              )
            /\
            q e. H
          )
          /\
          A. y e. U
            (
              (
                (
                  y = ( NTP4VCElem t )
                  \/
                  ( NTP4VCMem y q O )
                )
                /\
                (
                  <. y , ( NTP4VCElem t ) >. e. D
                  /\
                  A. x e. U
                    (
                      ( NTP4VCMem x q O )
                      ->
                      <. y , x >. e. D
                    )
                )
              )
              ->
              (
                ( NTP4VCMem y A O )
                /\
                A. x e. U
                  (
                    ( NTP4VCMem x A O )
                    ->
                    <. y , x >. e. D
                  )
              )
            )
        )
      ) $.
$}
