(* Observe the typed goal without consuming its branch. *)
fn goal as (hypotheses, conclusion) => fn context =>
  let
    fun fits remaining [] = true
      | fits remaining (term :: rest) =
          let val size = HolKernel.term_size term in
            size <= remaining andalso fits (remaining - size) rest
          end
  in
    if fits ITPEVAL_TERM_LIMIT (conclusion :: hypotheses) then
      (hhExportFof.fof_export_pbfile ITPEVAL_FOF_PATH (boolSyntax.list_mk_imp goal, []);
       ALL_TAC goal context)
    else raise Fail "HOL4 goal exceeds the exporter size budget"
  end
