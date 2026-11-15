(*
  Authors: Wenda Li
*)

theory amc12a_2020_p4
  imports Complex_Main 
begin

theorem amc12a_2020_p4:
  shows "card {n :: nat.
    \<exists>a b c d :: nat.
      1 \<le> a \<and> a \<le> 9 \<and> even a \<and>
      b \<le> 9 \<and> even b \<and>
      c \<le> 9 \<and> even c \<and>
      d \<le> 9 \<and> even d \<and>
      n = 10 * (10 * (10 * a + b) + c) + d \<and> 5 dvd n} = 100"
  by sorry

end
