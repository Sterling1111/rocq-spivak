let _ = Mltop.add_known_module "calculus.auto_int_plugin"

# 3 "src/g_auto_int.mlg"
 
open Pp
open Stdarg
module Tacentries = Ltac_plugin.Tacentries

# 10 "src/g_auto_int.ml"

let () = Tacentries.tactic_extend "calculus.auto_int_plugin" "ml_call_auto_int" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("ml_call_auto_int", Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Tacentries.TyNil))), 
           (fun cert_name f_term ist -> 
# 10 "src/g_auto_int.mlg"
                                                             
    Proofview.Goal.enter (fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      
      (try
        let cert_term = Auto_int_main.run_auto_int env sigma f_term in
        let name = Names.Name cert_name in
        Tactics.pose_tac name cert_term
      with Failure msg ->
        Tacticals.tclZEROMSG (str msg))
    )
  
# 33 "src/g_auto_int.ml"
)))]

