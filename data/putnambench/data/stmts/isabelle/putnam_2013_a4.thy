theory putnam_2013_a4 imports Complex_Main

begin

theorem putnam_2013_a4:
  fixes n k :: "nat"
    and Zsum Nsum :: "real"
    and circle :: "nat \<Rightarrow> nat"
    and Z N :: "(nat \<times> nat) \<Rightarrow> nat"
    and ws :: "nat \<Rightarrow> (nat \<times> nat)"
  defines "Zsum \<equiv> (1 / real_of_nat k) * (\<Sum>j\<in>{0..<k}. Z (ws j))"
    and "Nsum \<equiv> (1 / real_of_nat k) * (\<Sum>j\<in>{0..<k}. N (ws j))"
  assumes npos : "n \<ge> 1"
    and kpos : "k \<ge> 1"
    and hcircle : "\<forall> i :: nat. circle i \<in> {0 :: nat..1}"
    and hZ : "\<forall>w \<in> {0..n-1} \<times> {0..n}.
      Z w = (\<Sum>l :: nat \<in> {0..<snd w}. if circle ((fst w + l) mod n) = 0 then 1 else 0)"
    and hN : "\<forall>w \<in> {0..n-1} \<times> {0..n}.
      N w = (\<Sum>l :: nat \<in> {0..<snd w}. if circle ((fst w + l) mod n) = 1 then 1 else 0)"
    and hws : "\<forall>j \<in> {0..<k}. ws j \<in> {0..n-1} \<times> {0..n}"
    and Zle1 : "\<forall> w \<in> {0..n-1} \<times> {0..n}. \<forall> w' \<in> {0..n-1} \<times> {0..n}. (snd w) = (snd w') \<longrightarrow> \<bar>int (Z w) - int (Z w')\<bar> \<le> 1"
    and hNZsum : "round Nsum = Nsum \<and> round Zsum = Zsum"
  shows "\<exists>w \<in> {0..n-1} \<times> {0..n}.
    real (Z w) = Zsum \<and> real (N w) = Nsum"
  sorry

end
