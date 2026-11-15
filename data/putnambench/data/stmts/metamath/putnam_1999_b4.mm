$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1999_b4: a positive real function with positive first three
  derivatives, continuous differentiability through order three, and third
  derivative bounded above by the function has first derivative everywhere
  less than twice the function. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is the class of all total real-valued functions. Membership in
  ( ( C^n ` RR ) ` 3 ) is set.mm's native assertion of global continuous
  differentiability through order three, and the entries of ( RR Dn F ) are
  the iterated real derivatives. The positivity and upper-bound assumptions
  and the strict conclusion all retain their universal scope over RR. The
  final declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d F x $.

  putnambench-putnam-1999-b4 $a |-
    A. F e. ( RR ^m RR )
      (
        (
          F e. ( ( C^n ` RR ) ` 3 )
          /\
          A. x e. RR
            (
              0 < ( F ` x )
              /\
              0 < ( ( ( RR Dn F ) ` 1 ) ` x )
              /\
              0 < ( ( ( RR Dn F ) ` 2 ) ` x )
              /\
              0 < ( ( ( RR Dn F ) ` 3 ) ` x )
              /\
              ( ( ( RR Dn F ) ` 3 ) ` x ) <_ ( F ` x )
            )
        )
        ->
        A. x e. RR
          (
            ( ( ( RR Dn F ) ` 1 ) ` x )
            <
            ( 2 x. ( F ` x ) )
          )
      )
  $.
$}
