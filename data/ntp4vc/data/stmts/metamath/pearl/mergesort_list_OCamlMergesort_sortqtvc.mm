$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/mergesort_list_OCamlMergesort_sortqtvc
  (ntp4vc__metamath__pearl/mergesort_list_OCamlMergesort_sortqtvc):
  the OCaml-style mergesort verification condition establishes recursive
  split and reverse-merge obligations and states that every returned list is
  sorted and permutes the requested input prefix. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier elt, R is its total preorder,
  and Word U is exactly the type of arbitrary finite zero-based U-lists.
  NTP4VCSorted defines the source inductive sorted predicate equivalently as
  pairwise R-order of all earlier and later word entries; transitivity gives
  the forward direction from adjacent ordered constructors, and consecutive
  indices give the reverse direction.

  P is prefix1 at the theorem's selected Inhabited elt instance. It remains
  an arbitrary total function from an integer and a U-list to a U-list,
  subject only to the source zero and positive-cons equations over the full
  unbounded integer domain ZZ.

  NTP4VCPerm compares every element's occurrence count, exactly characterizing
  List.Perm on finite words. NTP4VCReverse is exact word reversal.
  NTP4VCTDiv2 is signed integer division by two truncated toward zero; under
  the source hypothesis 2 <= n this is the Why3 quotient n / 2 and agrees
  with the Lean Int.tdiv export. The Rocq export's Z.rem at this position is a
  proposition-changing export defect.

  The remaining predicates only factor the original nested verification
  condition. Expanding their biconditional definitions recovers both base
  cases, every integer bound, prefix decomposition, recursive continuation,
  reverse-sorted permutation premise, reverse-merge precondition, executable
  result branch, and final universally quantified postcondition. All list
  witnesses remain internally quantified. The final $a declaration is
  Metamath's native unproved statement encoding; every preceding $a is syntax
  or a faithful definition, and this database contains no $p declaration.
$)

$c
  NTP4VCPerm NTP4VCReverse NTP4VCTDiv2 NTP4VCSorted
  NTP4VCHas2 NTP4VCHas3 NTP4VCSort2 NTP4VCSort3
  NTP4VCRecursiveObligations NTP4VCSortObligations
  NTP4VCSortRun NTP4VCSortVC
$.

ntp4vc-perm-syntax
  $a wff ( NTP4VCPerm A B C ) $.
ntp4vc-reverse-syntax
  $a class ( NTP4VCReverse A ) $.
ntp4vc-tdiv2-syntax
  $a class ( NTP4VCTDiv2 A ) $.
ntp4vc-sorted-syntax
  $a wff ( NTP4VCSorted A B C ) $.
ntp4vc-has-two-syntax
  $a wff ( NTP4VCHas2 A B ) $.
ntp4vc-has-three-syntax
  $a wff ( NTP4VCHas3 A B ) $.
ntp4vc-sort-two-syntax
  $a wff ( NTP4VCSort2 A B C D ) $.
ntp4vc-sort-three-syntax
  $a wff ( NTP4VCSort3 A B C D ) $.
ntp4vc-recursive-obligations-syntax
  $a wff ( NTP4VCRecursiveObligations A B C D E ) $.
ntp4vc-sort-obligations-syntax
  $a wff ( NTP4VCSortObligations A B C D E ) $.
ntp4vc-sort-run-syntax
  $a wff ( NTP4VCSortRun A B C D E F ) $.
ntp4vc-sort-vc-syntax
  $a wff ( NTP4VCSortVC A B C D E ) $.

${
  $d k v A B C $.

  ntp4vc-perm-definition $a |- (
    NTP4VCPerm A B C
  ) <->
  (
    (
      A e. Word C
      /\
      B e. Word C
    )
    /\
    (
      ( # ` A ) = ( # ` B )
      /\
      A. v e. C
        (
          (
            # `
            { k e. ( 0 ..^ ( # ` A ) ) | ( A ` k ) = v }
          )
          =
          (
            # `
            { k e. ( 0 ..^ ( # ` B ) ) | ( B ` k ) = v }
          )
        )
    )
  ) $.
$}

${
  $d i A $.

  ntp4vc-reverse-definition $a |- (
    NTP4VCReverse A
  ) = (
    i e. ( 0 ..^ ( # ` A ) ) |->
      ( A ` ( ( ( # ` A ) - 1 ) - i ) )
  ) $.
$}

ntp4vc-tdiv2-definition $a |- (
  NTP4VCTDiv2 A
) = if (
  A < 0 ,
  ( |^ ` ( A / 2 ) ) ,
  ( |_ ` ( A / 2 ) )
) $.

${
  $d i j A B C $.

  ntp4vc-sorted-definition $a |- (
    NTP4VCSorted A B C
  ) <->
  (
    A e. Word C
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i < j
          ->
          <. ( A ` i ) , ( A ` j ) >. e. B
        )
  ) $.
$}

${
  $d t x y A B $.

  ntp4vc-has-two-definition $a |- (
    NTP4VCHas2 A B
  ) <->
  (
    A e. Word B
    /\
    E. x e. B E. y e. B E. t e. Word B
      A = ( <" x "> ++ ( <" y "> ++ t ) )
  ) $.
$}

${
  $d t x y z A B $.

  ntp4vc-has-three-definition $a |- (
    NTP4VCHas3 A B
  ) <->
  (
    A e. Word B
    /\
    E. x e. B E. y e. B E. z e. B E. t e. Word B
      A = (
        <" x "> ++
        ( <" y "> ++ ( <" z "> ++ t ) )
      )
  ) $.
$}

${
  $d t x y A B C D $.

  ntp4vc-sort-two-definition $a |- (
    NTP4VCSort2 A B C D
  ) <->
  E. x e. D E. y e. D E. t e. Word D
    (
      A = ( <" x "> ++ ( <" y "> ++ t ) )
      /\
      (
        (
          <. x , y >. e. C
          /\
          B = ( <" x "> ++ <" y "> )
        )
        \/
        (
          -. <. x , y >. e. C
          /\
          B = ( <" y "> ++ <" x "> )
        )
      )
    ) $.
$}

${
  $d t x y z A B C D $.

  ntp4vc-sort-three-definition $a |- (
    NTP4VCSort3 A B C D
  ) <->
  E. x e. D E. y e. D E. z e. D E. t e. Word D
    (
      A = (
        <" x "> ++
        ( <" y "> ++ ( <" z "> ++ t ) )
      )
      /\
      (
        (
          (
            <. x , y >. e. C
            /\
            <. y , z >. e. C
          )
          /\
          B = (
            <" x "> ++
            ( <" y "> ++ <" z "> )
          )
        )
        \/
        (
          (
            (
              <. x , y >. e. C
              /\
              -. <. y , z >. e. C
            )
            /\
            <. x , z >. e. C
          )
          /\
          B = (
            <" x "> ++
            ( <" z "> ++ <" y "> )
          )
        )
        \/
        (
          (
            (
              <. x , y >. e. C
              /\
              -. <. y , z >. e. C
            )
            /\
            -. <. x , z >. e. C
          )
          /\
          B = (
            <" z "> ++
            ( <" x "> ++ <" y "> )
          )
        )
        \/
        (
          (
            -. <. x , y >. e. C
            /\
            <. x , z >. e. C
          )
          /\
          B = (
            <" y "> ++
            ( <" x "> ++ <" z "> )
          )
        )
        \/
        (
          (
            (
              -. <. x , y >. e. C
              /\
              -. <. x , z >. e. C
            )
            /\
            <. y , z >. e. C
          )
          /\
          B = (
            <" y "> ++
            ( <" z "> ++ <" x "> )
          )
        )
        \/
        (
          (
            (
              -. <. x , y >. e. C
              /\
              -. <. x , z >. e. C
            )
            /\
            -. <. y , z >. e. C
          )
          /\
          B = (
            <" z "> ++
            ( <" y "> ++ <" x "> )
          )
        )
      )
    ) $.
$}

${
  $d q s t x y A B C D E $.

  ntp4vc-recursive-obligations-definition $a |- (
    NTP4VCRecursiveObligations A B C D E
  ) <->
  (
    2 =/= 0
    /\
    (
      (
        0 <_ ( NTP4VCTDiv2 A )
        /\
        ( NTP4VCTDiv2 A ) <_ ( # ` B )
      )
      /\
      A. q e. Word E
        (
          B = (
            ( C ` <. ( NTP4VCTDiv2 A ) , B >. )
            ++
            q
          )
          ->
          (
            (
              (
                0 <_ A
                /\
                ( NTP4VCTDiv2 A ) < A
              )
              /\
              (
                2 <_ ( NTP4VCTDiv2 A )
                /\
                ( NTP4VCTDiv2 A ) <_ ( # ` B )
              )
            )
            /\
            A. s e. Word E
              (
                (
                  (
                    NTP4VCSorted
                      ( NTP4VCReverse s )
                      D
                      E
                  )
                  /\
                  (
                    NTP4VCPerm
                      s
                      ( C ` <. ( NTP4VCTDiv2 A ) , B >. )
                      E
                  )
                )
                ->
                (
                  (
                    (
                      0 <_ A
                      /\
                      ( A - ( NTP4VCTDiv2 A ) ) < A
                    )
                    /\
                    (
                      2 <_ ( A - ( NTP4VCTDiv2 A ) )
                      /\
                      (
                        A - ( NTP4VCTDiv2 A )
                      ) <_ ( # ` q )
                    )
                  )
                  /\
                  A. t e. Word E
                    (
                      (
                        (
                          NTP4VCSorted
                            ( NTP4VCReverse t )
                            D
                            E
                        )
                        /\
                        (
                          NTP4VCPerm
                            t
                            (
                              C `
                              <.
                                ( A - ( NTP4VCTDiv2 A ) ) ,
                                q
                              >.
                            )
                            E
                        )
                      )
                      ->
                      (
                        (
                          (
                            NTP4VCSorted
                              (/)
                              D
                              E
                          )
                          /\
                          (
                            NTP4VCSorted
                              ( NTP4VCReverse s )
                              D
                              E
                          )
                        )
                        /\
                        (
                          NTP4VCSorted
                            ( NTP4VCReverse t )
                            D
                            E
                        )
                      /\
                      (
                        A. x e. E A. y e. E
                          (
                            x e. ran (/)
                            ->
                            (
                              y e. ran s
                              ->
                              <. y , x >. e. D
                            )
                          )
                        /\
                        A. x e. E A. y e. E
                          (
                            x e. ran (/)
                            ->
                            (
                              y e. ran t
                              ->
                              <. y , x >. e. D
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

ntp4vc-sort-obligations-definition $a |- (
  NTP4VCSortObligations A B C D E
) <->
(
  (
    A = 2
    /\
    ( NTP4VCHas2 B E )
  )
  \/
  (
    A =/= 2
    /\
    (
      (
        A = 3
        /\
        ( NTP4VCHas3 B E )
      )
      \/
      (
        A =/= 3
        /\
        ( NTP4VCRecursiveObligations A B C D E )
      )
    )
  )
) $.

${
  $d q s t A B C D E F $.

  ntp4vc-sort-run-definition $a |- (
    NTP4VCSortRun A B C D E F
  ) <->
  (
    (
      A = 2
      /\
      ( NTP4VCSort2 B C E F )
    )
    \/
    (
      A =/= 2
      /\
      (
        (
          A = 3
          /\
          ( NTP4VCSort3 B C E F )
        )
        \/
        (
          A =/= 3
          /\
          E. q e. Word F
            (
              B = (
                ( D ` <. ( NTP4VCTDiv2 A ) , B >. )
                ++
                q
              )
              /\
              E. s e. Word F
                (
                  (
                    (
                      NTP4VCSorted
                        ( NTP4VCReverse s )
                        E
                        F
                    )
                    /\
                    (
                      NTP4VCPerm
                        s
                        ( D ` <. ( NTP4VCTDiv2 A ) , B >. )
                        F
                    )
                  )
                  /\
                  E. t e. Word F
                    (
                      (
                        (
                          NTP4VCSorted
                            ( NTP4VCReverse t )
                            E
                            F
                        )
                        /\
                        (
                          NTP4VCPerm
                            t
                            (
                              D `
                              <.
                                ( A - ( NTP4VCTDiv2 A ) ) ,
                                q
                              >.
                            )
                            F
                        )
                      )
                      /\
                      (
                        ( NTP4VCSorted C E F )
                        /\
                        (
                          NTP4VCPerm
                            C
                            ( ( (/) ++ s ) ++ t )
                            F
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
  $d r A B C D E $.

  ntp4vc-sort-vc-definition $a |- (
    NTP4VCSortVC A B C D E
  ) <->
  (
    ( NTP4VCSortObligations A B C D E )
    /\
    A. r e. Word E
      (
        ( NTP4VCSortRun A B r C D E )
        ->
        (
          ( NTP4VCSorted r D E )
          /\
          (
            NTP4VCPerm
              r
              ( C ` <. A , B >. )
              E
          )
        )
      )
  ) $.
$}

${
  $d k t w x y z L N P R U $.

  $( Source arbitrary inhabited carrier elt and total preorder le. $)
  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-le-relation $e |- R C_ ( U X. U ) $.

  ntp4vc-le-reflexive $e |- A. x e. U
    <. x , x >. e. R $.

  ntp4vc-le-transitive $e |- A. x e. U A. y e. U A. z e. U
    (
      (
        <. x , y >. e. R
        /\
        <. y , z >. e. R
      )
      ->
      <. x , z >. e. R
    ) $.

  ntp4vc-le-total $e |- A. x e. U A. y e. U
    (
      <. x , y >. e. R
      \/
      <. y , x >. e. R
    ) $.

  $( Source operation prefix1 and its complete displayed equations. $)
  ntp4vc-prefix-function
    $e |- P e. ( ( Word U ) ^m ( ZZ X. Word U ) ) $.

  ntp4vc-prefix-zero $e |- A. w e. Word U
    ( P ` <. 0 , w >. ) = (/) $.

  ntp4vc-prefix-positive-cons $e |- A. k e. ZZ A. x e. U
    A. t e. Word U
      (
        0 < k
        ->
        (
          P ` <. k , ( <" x "> ++ t ) >.
        )
        =
        (
          <" x "> ++ ( P ` <. ( k - 1 ) , t >. )
        )
      ) $.

  $( Source theorem parameters N=n and L=l, followed by fact0 and fact1. $)
  ntp4vc-n-integer $e |- N e. ZZ $.
  ntp4vc-l-word $e |- L e. Word U $.
  ntp4vc-fact0 $e |- 2 <_ N $.
  ntp4vc-fact1 $e |- N <_ ( # ` L ) $.

  ntp4vc-pearl-mergesort-list-ocamlmergesort-sort-vc
    $a |- ( NTP4VCSortVC N L P R U ) $.
$}
