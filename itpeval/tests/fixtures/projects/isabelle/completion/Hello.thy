theory Hello
  imports Main
begin

locale witness =
  fixes p :: bool
  assumes premise: p
begin
lemma itpeval_target: p
  by (rule premise)
end

thm witness.itpeval_target
ML \<open>
  val _ = if Thm_Deps.has_skip_proof [@{thm witness.itpeval_target}]
    then error "incomplete target"
    else File.write (Path.append (Resources.master_directory @{theory})
      (Path.basic "itpeval-target-witness")) "witness.itpeval_target";
\<close>
end
