$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2021_dll_to_bst_Top_size_altqtvc
  (ntp4vc__metamath__pearl/verifythis_2021_dll_to_bst_Top_size_altqtvc):
  the iterative doubly-linked-list size verification condition preserves the
  list-segment invariant, decreases the remaining-length variant on each
  non-null step, and identifies the null exit index. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source location carrier. W is the arbitrary
  inhabited source implementation carrier t loc, and F is the unrestricted
  source projection to_fmap from W to finite partial U-to-U maps; retaining W
  and F avoids replacing the source implementation type by maps themselves.
  G is the shared inhabitant used by the exported totalized sequence and map
  lookups, and E is the distinguished null location.

  SetMM Word U is exactly the type of arbitrary finite zero-based U-valued
  sequences. NTP4VCFMap U is exactly the finite partial maps from U to U.
  NTP4VCToNat, NTP4VCAt, and NTP4VCLookup reproduce the exported integer
  conversion and totalized lookups. NTP4VCValid and NTP4VCDll directly expand
  the source predicates, preserving all integer bounds, map-domain facts,
  pairwise distinctness, internal links, and both boundary links.

  NTP4VCSizeAltStep is the source proposition-valued conditional. Its two
  guarded disjuncts are exhaustive: the non-null branch retains next-map
  membership, the let-bound lookup equality, both exact variant inequalities,
  and the advanced dll invariant; the null branch retains len = length s.
  Substitution of the let-bound next location is definitional, and under the
  retained domain guard the partial-map value is exactly the source
  Option.the lookup. The final assertion repeats fact0 and universally
  quantifies the full integer and location domains exactly as in the VC.

  The final $a declaration is Metamath's native unproved statement encoding.
  Every auxiliary $a is syntax or a faithful definition required to state the
  verification condition, and this database contains no $p proof declaration.
$)

$c
  NTP4VCFMap NTP4VCToNat NTP4VCAt NTP4VCLookup
  NTP4VCValid NTP4VCDll NTP4VCSizeAltStep
$.

ntp4vc-fmap-syntax
  $a class ( NTP4VCFMap A ) $.
ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B C ) $.
ntp4vc-lookup-syntax
  $a class ( NTP4VCLookup A B C ) $.
ntp4vc-valid-syntax
  $a wff ( NTP4VCValid A B C D E ) $.
ntp4vc-dll-syntax
  $a wff ( NTP4VCDll A B C D E F G H ) $.
ntp4vc-size-alt-step-syntax
  $a wff ( NTP4VCSizeAltStep A B C D E F G ) $.

${
  $d f A $.

  ntp4vc-fmap-definition $a |- (
    NTP4VCFMap A
  ) = {
    f e. _V |
      (
        Fun f
        /\
        (
          (
            dom f e. Fin
            /\
            dom f C_ A
          )
          /\
          ran f C_ A
        )
      )
  } $.
$}

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B C
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  C
) $.

ntp4vc-lookup-definition $a |- (
  NTP4VCLookup A B C
) = if (
  B e. dom A ,
  ( A ` B ) ,
  C
) $.

${
  $d i j A B C D E $.

  ntp4vc-valid-definition $a |- (
    NTP4VCValid A B C D E
  ) <->
  A. i e. ZZ
    (
      (
        0 <_ i
        /\
        i < ( # ` C )
      )
      ->
      (
        (
          ( NTP4VCAt C i D ) =/= E
          /\
          ( NTP4VCAt C i D ) e. dom A
        )
        /\
        (
          ( NTP4VCAt C i D ) e. dom B
          /\
          A. j e. ZZ
            (
              (
                i < j
                /\
                j < ( # ` C )
              )
              ->
              ( NTP4VCAt C i D ) =/= ( NTP4VCAt C j D )
            )
        )
      )
    ) $.
$}

${
  $d i A B C D E F G H $.

  ntp4vc-dll-definition $a |- (
    NTP4VCDll A B C D E F G H
  ) <->
  (
    (
      NTP4VCValid A B C G H
      /\
      (
        0 <_ E
        /\
        (
          E <_ F
          /\
          F <_ ( # ` C )
        )
      )
    )
    /\
    (
      D
      =
      if (
        E = ( # ` C ) ,
        H ,
        ( NTP4VCAt C E G )
      )
      /\
      (
        A. i e. ZZ
          (
            (
              E <_ i
              /\
              i < ( F - 1 )
            )
            ->
            (
              NTP4VCLookup
                B
                ( NTP4VCAt C i G )
                G
            )
            =
            ( NTP4VCAt C ( i + 1 ) G )
          )
        /\
        (
          A. i e. ZZ
            (
              (
                E < i
                /\
                i < F
              )
              ->
              (
                NTP4VCLookup
                  A
                  ( NTP4VCAt C i G )
                  G
              )
              =
              ( NTP4VCAt C ( i - 1 ) G )
            )
          /\
          (
            (
              E < F
              ->
              (
                NTP4VCLookup
                  B
                  ( NTP4VCAt C ( F - 1 ) G )
                  G
              )
              =
              if (
                F = ( # ` C ) ,
                H ,
                ( NTP4VCAt C F G )
              )
            )
            /\
            (
              E < F
              ->
              (
                NTP4VCLookup
                  A
                  ( NTP4VCAt C E G )
                  G
              )
              =
              if (
                E = 0 ,
                H ,
                ( NTP4VCAt C ( E - 1 ) G )
              )
            )
          )
        )
      )
    )
  ) $.
$}

ntp4vc-size-alt-step-definition $a |- (
  NTP4VCSizeAltStep A B C D E F G
) <->
(
  (
    E =/= G
    /\
    (
      E e. dom B
      /\
      (
        (
          NTP4VCLookup B E F
        ) = ( B ` E )
        ->
        (
          (
            0 <_ ( ( # ` C ) - D )
            /\
            (
              ( # ` C ) - ( D + 1 )
            )
            <
            (
              ( # ` C ) - D
            )
          )
          /\
          (
            NTP4VCDll
              A
              B
              C
              ( NTP4VCLookup B E F )
              ( D + 1 )
              ( # ` C )
              F
              G
          )
        )
      )
    )
  )
  \/
  (
    E = G
    /\
    D = ( # ` C )
  )
) $.

${
  $d f i j l p
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Exact source carriers, projection, parameters, and sole precondition. $)
  ntp4vc-location-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-default-location $e |- G e. U $.
  ntp4vc-null-location $e |- E e. U $.

  ntp4vc-implementation-carrier-nonempty $e |- W =/= (/) $.
  ntp4vc-to-fmap-function $e |- F e. ( ( NTP4VCFMap U ) ^m W ) $.

  ntp4vc-prev-implementation $e |- A e. W $.
  ntp4vc-next-implementation $e |- B e. W $.
  ntp4vc-source-sequence $e |- C e. Word U $.
  ntp4vc-source-head $e |- D e. U $.

  ntp4vc-fact0 $e |- (
    NTP4VCDll
      ( F ` A )
      ( F ` B )
      C
      D
      0
      ( # ` C )
      G
      E
  ) $.

  ntp4vc-pearl-verifythis-2021-dll-to-bst-top-size-alt-vc $a |- (
    NTP4VCDll
      ( F ` A )
      ( F ` B )
      C
      D
      0
      ( # ` C )
      G
      E
    /\
    A. l e. ZZ A. p e. U
      (
        (
          NTP4VCDll
            ( F ` A )
            ( F ` B )
            C
            p
            l
            ( # ` C )
            G
            E
        )
        ->
        (
          NTP4VCSizeAltStep
            ( F ` A )
            ( F ` B )
            C
            l
            p
            G
            E
        )
      )
  ) $.
$}
