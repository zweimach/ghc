module DynFlags.DumpFlags where

import DynFlags.Type

import qualified EnumSet

data DumpFlag
-- See Note [Updating flag description in the User's Guide]

   -- debugging flags
   = Opt_D_dump_cmm
   | Opt_D_dump_cmm_from_stg
   | Opt_D_dump_cmm_raw
   | Opt_D_dump_cmm_verbose
   -- All of the cmm subflags (there are a lot!) automatically
   -- enabled if you run -ddump-cmm-verbose
   -- Each flag corresponds to exact stage of Cmm pipeline.
   | Opt_D_dump_cmm_cfg
   | Opt_D_dump_cmm_cbe
   | Opt_D_dump_cmm_switch
   | Opt_D_dump_cmm_proc
   | Opt_D_dump_cmm_sp
   | Opt_D_dump_cmm_sink
   | Opt_D_dump_cmm_caf
   | Opt_D_dump_cmm_procmap
   | Opt_D_dump_cmm_split
   | Opt_D_dump_cmm_info
   | Opt_D_dump_cmm_cps
   -- end cmm subflags
   | Opt_D_dump_asm
   | Opt_D_dump_asm_native
   | Opt_D_dump_asm_liveness
   | Opt_D_dump_asm_regalloc
   | Opt_D_dump_asm_regalloc_stages
   | Opt_D_dump_asm_conflicts
   | Opt_D_dump_asm_stats
   | Opt_D_dump_asm_expanded
   | Opt_D_dump_llvm
   | Opt_D_dump_core_stats
   | Opt_D_dump_deriv
   | Opt_D_dump_ds
   | Opt_D_dump_foreign
   | Opt_D_dump_inlinings
   | Opt_D_dump_rule_firings
   | Opt_D_dump_rule_rewrites
   | Opt_D_dump_simpl_trace
   | Opt_D_dump_occur_anal
   | Opt_D_dump_parsed
   | Opt_D_dump_parsed_ast
   | Opt_D_dump_rn
   | Opt_D_dump_rn_ast
   | Opt_D_dump_shape
   | Opt_D_dump_simpl
   | Opt_D_dump_simpl_iterations
   | Opt_D_dump_spec
   | Opt_D_dump_prep
   | Opt_D_dump_stg
   | Opt_D_dump_call_arity
   | Opt_D_dump_stranal
   | Opt_D_dump_str_signatures
   | Opt_D_dump_tc
   | Opt_D_dump_tc_ast
   | Opt_D_dump_types
   | Opt_D_dump_rules
   | Opt_D_dump_cse
   | Opt_D_dump_worker_wrapper
   | Opt_D_dump_rn_trace
   | Opt_D_dump_rn_stats
   | Opt_D_dump_opt_cmm
   | Opt_D_dump_simpl_stats
   | Opt_D_dump_cs_trace -- Constraint solver in type checker
   | Opt_D_dump_tc_trace
   | Opt_D_dump_ec_trace -- Pattern match exhaustiveness checker
   | Opt_D_dump_if_trace
   | Opt_D_dump_vt_trace
   | Opt_D_dump_splices
   | Opt_D_th_dec_file
   | Opt_D_dump_BCOs
   | Opt_D_dump_vect
   | Opt_D_dump_ticked
   | Opt_D_dump_rtti
   | Opt_D_source_stats
   | Opt_D_verbose_stg2stg
   | Opt_D_dump_hi
   | Opt_D_dump_hi_diffs
   | Opt_D_dump_mod_cycles
   | Opt_D_dump_mod_map
   | Opt_D_dump_view_pattern_commoning
   | Opt_D_verbose_core2core
   | Opt_D_dump_debug
   | Opt_D_dump_json
   | Opt_D_ppr_debug
   | Opt_D_no_debug_output
   deriving (Eq, Show, Enum)

-- | Test whether a 'DumpFlag' is set
dopt :: DumpFlag -> DynFlags -> Bool
dopt f dflags = (f `EnumSet.member` dumpFlags dflags)
             || (verbosity dflags >= 4 && enableIfVerbose f)
    where enableIfVerbose Opt_D_dump_tc_trace               = False
          enableIfVerbose Opt_D_dump_rn_trace               = False
          enableIfVerbose Opt_D_dump_cs_trace               = False
          enableIfVerbose Opt_D_dump_if_trace               = False
          enableIfVerbose Opt_D_dump_vt_trace               = False
          enableIfVerbose Opt_D_dump_tc                     = False
          enableIfVerbose Opt_D_dump_rn                     = False
          enableIfVerbose Opt_D_dump_shape                  = False
          enableIfVerbose Opt_D_dump_rn_stats               = False
          enableIfVerbose Opt_D_dump_hi_diffs               = False
          enableIfVerbose Opt_D_verbose_core2core           = False
          enableIfVerbose Opt_D_verbose_stg2stg             = False
          enableIfVerbose Opt_D_dump_splices                = False
          enableIfVerbose Opt_D_th_dec_file                 = False
          enableIfVerbose Opt_D_dump_rule_firings           = False
          enableIfVerbose Opt_D_dump_rule_rewrites          = False
          enableIfVerbose Opt_D_dump_simpl_trace            = False
          enableIfVerbose Opt_D_dump_rtti                   = False
          enableIfVerbose Opt_D_dump_inlinings              = False
          enableIfVerbose Opt_D_dump_core_stats             = False
          enableIfVerbose Opt_D_dump_asm_stats              = False
          enableIfVerbose Opt_D_dump_types                  = False
          enableIfVerbose Opt_D_dump_simpl_iterations       = False
          enableIfVerbose Opt_D_dump_ticked                 = False
          enableIfVerbose Opt_D_dump_view_pattern_commoning = False
          enableIfVerbose Opt_D_dump_mod_cycles             = False
          enableIfVerbose Opt_D_dump_mod_map                = False
          enableIfVerbose Opt_D_dump_ec_trace               = False
          enableIfVerbose _                                 = True
