$(
  @{
    mathd-algebra-480.0 @e |- ( ph -> F : RR --> RR ) $@
    mathd-algebra-480.1 @e |- ( ph -> A. x e. RR
      ( x < 0 -> ( F ` x ) = ( -u ( x ^ 2 ) - 1 ) ) ) $@
    mathd-algebra-480.2 @e |- ( ph -> A. x e. RR
      ( ( 0 <_ x /\ x < 4 ) -> ( F ` x ) = 2 ) ) $@
    mathd-algebra-480.3 @e |- ( ph -> A. x e. RR
      ( 4 <_ x -> ( F ` x ) = ( sqrt ` x ) ) ) $@
    @( (Contributed by Kunhao Zheng, 9-Aug-2021.) @)
    mathd-algebra-480 @p |- ( ph -> ( F ` _pi ) = 2 ) @=
      ? @.
  @}
$)
