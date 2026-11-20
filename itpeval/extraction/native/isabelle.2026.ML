structure ITPEval_Theory =
struct
  val project = getenv "ITPEVAL_PROJECT" ^ "/"
  fun in_project thy =
    String.isPrefix project (File.absolute_path (Resources.master_directory thy) ^ "/")
  val theories = filter in_project (Context.ancestors_of @{theory})
  val position = Name_Space.the_entry_pos
  fun fact_names thy = map (#1 o #2) (Global_Theory.dest_thm_names thy)
end
