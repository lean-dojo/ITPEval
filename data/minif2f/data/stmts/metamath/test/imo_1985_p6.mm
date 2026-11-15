$(
  @{
    imo-1985-p6.0 @e |- ( ph -> F : ( NN X. RR+ ) --> RR ) $@
    imo-1985-p6.1 @e |- ( ph -> A. x e. RR+ ( 1 F x ) = x ) $@
    imo-1985-p6.2 @e |- ( ph -> A. x e. RR+ A. n e. NN
      ( ( n + 1 ) F x ) = ( ( n F x ) x. ( ( n F x ) + ( 1 / n ) ) ) ) $@
    @( (Contributed by Kunhao Zheng, 9-Aug-2021.) @)
    imo-1985-p6 @p |- ( ph -> E! a e. RR+ A. n e. NN ( 0 < ( n F a ) /\ ( n F a ) < ( ( n + 1 ) F a ) /\ ( ( n + 1 ) F a ) < 1 ) ) @=
      ? @.
  @}
$)
