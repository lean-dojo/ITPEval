$(
  @{
    @d N k x $@
    @d k ph x y $@
    induction-sum2kp1npqsqm1.0 @e |- ( ph -> N e. NN ) $@
    @( (Contributed by Stanislas Polu, 22-Sep-2020.) @)
    induction-sum2kp1npqsqm1 @p |- ( ph -> sum_ k e. ( 1 ... N ) ( ( 2 x. k ) + 1 
  ) = ( ( ( N + 1 ) ^ 2 ) - 1 ) ) @=
      ? @.
  @}
$)
