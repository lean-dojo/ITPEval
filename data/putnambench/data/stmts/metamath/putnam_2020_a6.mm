$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2020_a6: the least uniform upper bound of a family of finite
  real sine sums indexed by positive integers is pi / 4. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN is set.mm's class of positive integers, so N has exactly the source
  domain. The interval 0 ... N is inclusive, and the displayed summand is
  the source definition of f_N(x), with all arithmetic embedded in the
  reals. The set in the ordered supremum contains exactly the attained
  values f_N(x) for positive N and real x.

  Set.mm's sin and _pi are the real sine and pi constants on these
  arguments, and sup(A, RR, <) is the real-order supremum. Thus the final
  declaration states directly that the smallest uniform upper bound is
  pi / 4. It is the single unproved $a corpus statement; this database
  contains no $p proof declaration.
$)

${
  $d N n x y $.

  putnambench-putnam-2020-a6 $a |-
    sup
      (
        {
          y e. RR |
            E. N e. NN
              E. x e. RR
                y
                =
                (
                  sum_ n e. ( 0 ... N )
                    (
                      (
                        (
                          ( N + ( 1 / 2 ) )
                          -
                          n
                        )
                        /
                        (
                          ( N + 1 )
                          x.
                          ( ( 2 x. n ) + 1 )
                        )
                      )
                      x.
                      (
                        sin
                        `
                        (
                          ( ( 2 x. n ) + 1 )
                          x.
                          x
                        )
                      )
                    )
                )
        } ,
        RR ,
        <
      )
    =
    ( _pi / 4 )
  $.
$}
