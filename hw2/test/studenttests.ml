open Util.Assert
open X86
open Simulator
open Gradedtests
open Asm

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let mov_ri =
 test_machine
 [
 InsB0 (Movq, Asm.[ ~$42; ~%Rax ]);
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 ]


 
(* WHAT DOES THIS PROGRAM DO?
  Given a number n, let's compute the summation of (j^n * n!) from j = 1 to n
  We may want to stop before our summation hits a certain value, call it v, and so we check that
  This program incorporates arithmetic, nested for loops, conditional branching, and mimicry of lists
  Contacted Varun to ensure this test case is sufficient for a non-trivial program
*)

let non_trivial_program n v = [ 
                        text "outerloop"
                                [ Movq,  [~$1; ~%R11]        
                                ; Cmpq,  [~%Rbx; ~%Rdi]       
                                ; J Eq,  [~$$"done"]          
                                ]
                        ; text "innerloop"
                                [ Cmpq,  [~%Rcx; ~%Rdi]       
                                ; J Eq,  [~$$"increment_outerloop"]
                                ; Movq,  [~%Rbx; ~%R09]
                                ; Imulq, [~%Rcx; ~%R09]
                                ; Imulq, [~%R09; ~%R11]
                                ; Incq,  [~%Rcx]
                                ; Jmp,   [~$$"innerloop"]
                                ]
                        ; text "increment_outerloop"
                                [ Movq,  [~%R10; ~%R12]
                                ; Addq,  [~%R11; ~%R12]
                                ; Cmpq,  [~%Rsi; ~%R12]
                                ; J Ge,  [~$$"done"]
                                ; Addq,  [~%R11; ~%R10]
                                ; Incq,  [~%Rbx]
                                ; Movq,  [~$1; ~%Rcx]
                                ; Jmp,   [~$$"outerloop"]
                                ]
                        ; gtext "main"
                                [ Movq,  [~$0; ~%R10]          
                                ; Cmpq,  [~$n; ~$1]
                                ; J Gt,  [~$$"done"]
                                ; Movq,  [~$n; ~%Rdi]
                                ; Movq,  [~$v; ~%Rsi]
                                ; Movq,  [~$1; ~%Rbx]
                                ; Movq,  [~$1; ~%Rcx]
                                ; Jmp,   [~$$"outerloop"]
                                ]
                        ; text "done"
                                [ Movq,  [~%R10; ~%Rax]
                                ; Retq,  []
                                ]
                    ]

(* STUDENT TESTS *)
(* ------------------------------------------------ *)

(* HELPER FUNCTION *)
let insert_insfrag (ins : sbyte list) =
  List.concat
    (List.map
       (fun b ->
         [ b; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag; InsFrag ])
       ins)
              
    (* negq *)
        let cc_negq = (* OF = true when Int64.min_int *)
          [ InsB0 (Movq, [Imm (Lit (Int64.min_int)); ~%Rax ])
          ; InsB0 (Negq, [~%Rax]);
          ] |> insert_insfrag |> test_machine
    (* addq *)
        let cc_addq_1 = (* ZF *)
          [ InsB0 (Movq, [Imm (Lit 1L); ~%Rcx ])
          ; InsB0 (Negq, [~%Rcx])
          ; InsB0 (Movq, [Imm (Lit 1L); ~%Rax ])
          ; InsB0 (Addq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_addq_2 = (* SF *)
          [ InsB0 (Movq, [Imm (Lit 3L); ~%Rcx ])
          ; InsB0 (Negq, [~%Rcx])
          ; InsB0 (Movq, [Imm (Lit 1L); ~%Rax ])
          ; InsB0 (Addq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_addq_3 = (* OF for pos + pos = neg *)
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rcx ])
          ; InsB0 (Movq, [Imm (Lit 1L); ~%Rax ])
          ; InsB0 (Addq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_addq_4 = (* OF for neg + neg = pos *)
          [ InsB0 (Movq, [Imm (Lit 1L); ~%Rcx ])
          ; InsB0 (Negq, [~%Rcx])
          ; InsB0 (Movq, [Imm (Lit (Int64.min_int)); ~%Rax ])
          ; InsB0 (Addq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
    (* subq *)
        let cc_subq_1 = (* ZF *)
          [ InsB0 (Movq, [Imm (Lit 3L); ~%Rcx ])
          ; InsB0 (Movq, [Imm (Lit 3L); ~%Rax ])
          ; InsB0 (Subq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_subq_2 = (* SF *)
          [ InsB0 (Movq, [Imm (Lit 5L); ~%Rcx ])
          ; InsB0 (Movq, [Imm (Lit 1L); ~%Rax ])
          ; InsB0 (Subq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_subq_3 = (* OF for -dest - (src) = val *)
          [ InsB0 (Movq, [Imm (Lit 100L); ~%Rcx ])
          ; InsB0 (Movq, [Imm (Lit Int64.min_int); ~%Rax ])
          ; InsB0 (Subq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_subq_4 = (* OF for dest - (-src) = -val *)
          [ InsB0 (Movq, [Imm (Lit Int64.min_int); ~%Rcx ])
          ; InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rax ])
          ; InsB0 (Subq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
    (* imulq *)
        let cc_imulq_1 = (* OF => goes into negatives *)
          [ InsB0 (Movq, [Imm (Lit 3037000499L); ~%Rax ])
          ; InsB0 (Movq, [Imm (Lit 4294967297L); ~%Rcx ])
          ; InsB0 (Imulq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_imulq_2 = (* OF => goes into positives *)
          [ InsB0 (Movq, [Imm (Lit 8500000000000000000L); ~%Rax ])
          ; InsB0 (Movq, [Imm (Lit 3L); ~%Rcx ])
          ; InsB0 (Imulq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
    (* incq *)
        let cc_incq_1 = (* ZF *)
          [ InsB0 (Movq, [Imm (Lit 1L); ~%Rax ])
          ; InsB0 (Negq, [~%Rax])
          ; InsB0 (Incq, [~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_incq_2 = (* SF *)
          [ InsB0 (Movq, [Imm (Lit 5L); ~%Rax ])
          ; InsB0 (Negq, [~%Rax])
          ; InsB0 (Incq, [~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_incq_3 = (* OF *)
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rax ])
          ; InsB0 (Incq, [~%Rax]);
          ] |> insert_insfrag |> test_machine
    (* decq *)
        let cc_decq_1 = (* ZF *)
          [ InsB0 (Movq, [Imm (Lit 1L); ~%Rax ])
          ; InsB0 (Decq, [~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_decq_2 = (* SF *)
          [ InsB0 (Movq, [Imm (Lit 0L); ~%Rax ])
          ; InsB0 (Decq, [~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_decq_3 = (* OF *)
          [ InsB0 (Movq, [Imm (Lit Int64.min_int); ~%Rax ])
          ; InsB0 (Decq, [~%Rax]);
          ] |> insert_insfrag |> test_machine
    (* notq *)
        let cc_notq = (* no flags set! *)
          [ InsB0 (Movq, [Imm (Lit 1L); ~%Rax])
          ; InsB0 (Notq, [~%Rax])
          ] |> insert_insfrag |> test_machine   
    (* andq *)
        let cc_andq_1 = (* ZF *)
          [ InsB0 (Movq, [Imm (Lit 5L); ~%Rcx ])
          ; InsB0 (Movq, [Imm (Lit 2L); ~%Rax ])
          ; InsB0 (Andq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_andq_2 = (* SF *)
          [ InsB0 (Movq, [Imm (Lit Int64.min_int); ~%Rax ])
          ; InsB0 (Movq, [Imm (Lit 9223372036854775808L); ~%Rcx ])
          ; InsB0 (Negq, [~%Rcx])
          ; InsB0 (Andq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_andq_3 = (* ZF set, SF not set *)
          [ InsB0 (Movq, [Imm (Lit Int64.min_int); ~%Rax ])
          ; InsB0 (Movq, [Imm (Lit 1L); ~%Rcx ])
          ; InsB0 (Andq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
    (* orq *)
        let cc_orq_1 = (* ZF *)
          [ InsB0 (Movq, [Imm (Lit 0L); ~%Rcx ])
          ; InsB0 (Movq, [Imm (Lit 0L); ~%Rax ])
          ; InsB0 (Orq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_orq_2 = (* SF *)
          [ InsB0 (Movq, [Imm (Lit Int64.min_int); ~%Rax ])
          ; InsB0 (Movq, [Imm (Lit 1L); ~%Rcx ])
          ; InsB0 (Negq, [~%Rcx])
          ; InsB0 (Orq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
    (* xorq *)
        let cc_xorq_1 = (* ZF *)
          [ InsB0 (Movq, [Imm (Lit 50L); ~%Rcx ])
          ; InsB0 (Movq, [Imm (Lit 50L); ~%Rax ])
          ; InsB0 (Xorq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_xorq_2 = (* SF set *)
          [ InsB0 (Movq, [Imm (Lit Int64.min_int); ~%Rax ])
          ; InsB0 (Movq, [Imm (Lit 1L); ~%Rcx ])
          ; InsB0 (Xorq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_xorq_3 = (* ZF set, SF not set *)
          [ InsB0 (Movq, [Imm (Lit 200L); ~%Rax ])
          ; InsB0 (Movq, [Imm (Lit 200L); ~%Rcx ])
          ; InsB0 (Xorq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
    (* sarq *)
        let cc_sarq_1 = (* flags unaffected *)
          [ InsB0 (Movq, [Imm (Lit 200L); ~%Rax])
          ; InsB0 (Sarq, [~$0; ~%Rax])
          ] |> insert_insfrag |> test_machine  
        let cc_sarq_2 = (* OF set to 0, but ZF raised *)
          [ InsB0 (Movq, [Imm (Lit 0L); ~%Rax])
          ; InsB0 (Sarq, [~$1; ~%Rax])
          ] |> insert_insfrag |> test_machine  
        let cc_sarq_3 = (* SF raised *)
          [ InsB0 (Movq, [Imm (Lit Int64.min_int); ~%Rax])
          ; InsB0 (Sarq, [~$3; ~%Rax])
          ] |> insert_insfrag |> test_machine  
        let cc_sarq_4 = (* OF raised then unaffected *)
          [ InsB0 (Movq, [Imm (Lit Int64.min_int); ~%Rax ])
          ; InsB0 (Decq, [~%Rax])
          ; InsB0 (Movq, [Imm (Lit Int64.min_int); ~%Rcx])
          ; InsB0 (Sarq, [~$3; ~%Rcx])
          ] |> insert_insfrag |> test_machine  
    (* shlq *)
        let cc_shlq_1 = (* flags unaffected *)
          [ InsB0 (Movq, [Imm (Lit (-7L)); ~%Rax])
          ; InsB0 (Shlq, [~$0; ~%Rax])
          ] |> insert_insfrag |> test_machine 
        let cc_shlq_2 = (* SF *)
          [ InsB0 (Movq, [Imm (Lit (-7L)); ~%Rax])
          ; InsB0 (Shlq, [~$2; ~%Rax])
          ] |> insert_insfrag |> test_machine 
        let cc_shlq_3 = (* OF not set *)
          [ InsB0 (Movq, [Imm (Lit 7L); ~%Rax])
          ; InsB0 (Shlq, [~$1; ~%Rax])
          ] |> insert_insfrag |> test_machine 
        let cc_shlq_4 = (* OF set and ZF set *)
          [ InsB0 (Movq, [Imm (Lit Int64.min_int); ~%Rax])
          ; InsB0 (Shlq, [~$1; ~%Rax])
          ] |> insert_insfrag |> test_machine 
    (* shrq *)
        (* we don't need to ever test SF because we'll always insert 0s in msb *)
        let cc_shrq_1 = (* flags unaffected *)
          [ InsB0 (Movq, [Imm (Lit 7L); ~%Rax])
          ; InsB0 (Shrq, [~$0; ~%Rax])
          ] |> insert_insfrag |> test_machine 
        let cc_shrq_2 = (* ZF *)
          [ InsB0 (Movq, [Imm (Lit 2L); ~%Rax])
          ; InsB0 (Shrq, [~$2; ~%Rax])
          ] |> insert_insfrag |> test_machine 
        let cc_shrq_3 = (* OF *)
          [ InsB0 (Movq, [Imm (Lit Int64.min_int); ~%Rax])
          ; InsB0 (Shrq, [~$3; ~%Rax])
          ] |> insert_insfrag |> test_machine 
    (* setb *)
        let cc_setb = (* no flags should be set by set eq; they may be set by cmpq, however *)
          [ InsB0 (Cmpq, [Imm (Lit 2L); Imm (Lit 3L) ])
          ; InsB0 (Set Eq, [~%Rax])
          ] |> insert_insfrag |> test_machine
    (* leaq *)
        let cc_leaq = (* no flags should be set! *)
          [ InsB0 (Movq, [Ind1 (Lit 0x400000L); ~%Rax])
          ] |> insert_insfrag |> test_machine   
    (* movq *)
        let cc_movq = (* no flags should be set! *)
          [ InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rax])
          ] |> insert_insfrag |> test_machine   
    (* pushq *)
        let cc_pushq = (* no flags should be set! *)
          [ InsB0 (Pushq, [~%Rsp])
          ] |> insert_insfrag |> test_machine   
    (* popq *)
        let cc_popq = (* no flags should be set! *)
          [ InsB0 (Popq, [~%Rax])
          ] |> insert_insfrag |> test_machine   
    (* cmpq *)
        let cc_cmpq_1 = (* ZF *)
          [ InsB0 (Cmpq, [Imm (Lit 2L); Imm (Lit 2L) ])
          ] |> insert_insfrag |> test_machine
        let cc_cmpq_2 = (* SF [src1, src2] => src2 - src1 *)
          [ InsB0 (Cmpq, [Imm (Lit 3L); Imm (Lit 2L) ])
          ] |> insert_insfrag |> test_machine
        let cc_cmpq_3 = (* OF for -src2 - (src1) = val *)
          [ InsB0 (Movq, [Imm (Lit 100L); ~%Rcx ])
          ; InsB0 (Movq, [Imm (Lit Int64.min_int); ~%Rax ])
          ; InsB0 (Cmpq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
        let cc_cmpq_4 = (* OF for src2 - (-src1) = -val *)
          [ InsB0 (Movq, [Imm (Lit Int64.min_int); ~%Rcx ])
          ; InsB0 (Movq, [Imm (Lit Int64.max_int); ~%Rax ])
          ; InsB0 (Cmpq, [~%Rcx; ~%Rax]);
          ] |> insert_insfrag |> test_machine
    (* jmp *)
        let cc_jmp = (* no flags should be set! *)
          [ InsB0 (Movq, [Imm (Lit 0x400008L); ~%Rax])
          ; InsB0 (Movq, [~%Rax; ~%Rcx])
          ; InsB0 (Jmp, [~%Rcx])
          ] |> insert_insfrag |> test_machine   
    (* callq *)
        let cc_callq = (* no flags should be set! *)
          [ InsB0 (Movq, [Imm (Lit 0x400008L); ~%Rcx])
          ; InsB0 (Callq, [~%Rcx])
          ] |> insert_insfrag |> test_machine   
    (* retq *)
        let cc_retq = (* no flags should be set! *)
          [ InsB0 (Retq, [])
          ] |> insert_insfrag |> test_machine   


let csou_test (n:int) (m:mach) (fo',fs',fz') =
  cc_test (Printf.sprintf "expected OF:%b SF:%b ZF:%b" fo' fs' fz')
    n m (fo',not fs',not fz')
    (fun m -> m.flags.fo = fo' && m.flags.fs = fs' && m.flags.fz = fz')

(* EXAM THE TESTS *)
let provided_tests : suite = [
  Test ("Student-Provided Big Test for Part III: Score recorded as PartIIITestCase", [
    (* return val from first iteration: 1^4 * 4! = 24; we never want our result bigger than 25 *)
    ("non-trivial 1", program_test (non_trivial_program 5 25) 24L);   
    (* return val from the second iteration: (1^4 * 4!) + (2^4 * 4!) = 408; we never want our result bigger than 410 *)
    ("non-trivial 2", program_test (non_trivial_program 5 410) 408L); 
    (* do the second iteration but let it be over our specified threshold, so return val from first iteration *)
    ("non-trivial 3", program_test (non_trivial_program 5 50) 24L); 
    (* go to the very end of the program *)
    ("non-trivial 4", program_test (non_trivial_program 5 9000) 8496L); 
    (* try out another program but where n is different *)
    ("non-trivial 5", program_test (non_trivial_program 4 220) 216L); 
    (* edge case: make sure that n > 1, and if its not, return 0 *)
    ("non-trivial 6", program_test (non_trivial_program 0 0) 0L); 
    ("non-trivial 7", program_test (non_trivial_program 1 0) 0L); 
    (* edge case: if we overflow, also return 0*)
    ("non-trivial 7", program_test (non_trivial_program 100 (Int64.to_int Int64.max_int)) 0L);
    ("non-trivial 8", program_test (non_trivial_program 500 (Int64.to_int Int64.max_int)) 0L);
  ]);

  Test ("Student-Provided Tests", [
    (* negq *)
    ("cc_negq", cs_test 2 cc_negq (true, true, false));
    (* addq *)
    ("cc_addq_1", cs_test 4 cc_addq_1 (false, false, true));
    ("cc_addq_2", cs_test 4 cc_addq_2 (false, true, false));
    ("cc_addq_3", cs_test 3 cc_addq_3 (true, true, false));
    ("cc_addq_4", cs_test 4 cc_addq_4 (true, false, false));
    (* subq *)
    ("cc_subq_1", cs_test 3 cc_subq_1 (false, false, true));
    ("cc_subq_2", cs_test 3 cc_subq_2 (false, true, false));
    ("cc_subq_3", cs_test 3 cc_subq_3 (true, false, false));
    ("cc_subq_4", cs_test 3 cc_subq_4 (true, true, false));
    (* imulq *)
    ("cc_imulq_1", cs_test 3 cc_imulq_1 (true, true, false));
    ("cc_imulq_2", cs_test 3 cc_imulq_2 (true, false, false));
    (* incq *)
    ("cc_incq_1", cs_test 3 cc_incq_1 (false, false, true));
    ("cc_incq_2", cs_test 3 cc_incq_2 (false, true, false));
    ("cc_incq_3", cs_test 2 cc_incq_3 (true, true, false));
    (* decq *)
    ("cc_decq_1", cs_test 2 cc_decq_1 (false, false, true));
    ("cc_decq_2", cs_test 2 cc_decq_2 (false, true, false));
    ("cc_decq_3", cs_test 2 cc_decq_3 (true, false, false));
    (* notq *)
    ("notq_1", cc_test "" 2 cc_notq (false, false, false) 
    (fun m -> not m.flags.fo && not m.flags.fs && not m.flags.fz));
    (* andq *)
    ("cc_andq_1", cs_test 3 cc_andq_1 (false, false, true));
    ("cc_andq_2", cs_test 4 cc_andq_2 (false, true, false));
    ("cc_andq_3", cs_test 3 cc_andq_3 (false, false, true));
    (* orq *)
    ("cc_orq_1", cs_test 3 cc_orq_1 (false, false, true));
    ("cc_orq_2", cs_test 4 cc_orq_2 (false, true, false));
    (* xorq *)
    ("cc_xorq_1", cs_test 3 cc_xorq_1 (false, false, true));
    ("cc_xorq_2", cs_test 3 cc_xorq_2 (false, true, false));
    ("cc_xorq_3", cs_test 3 cc_xorq_3 (false, false, true));
    (* sarq *) 
    ("cc_sarq_1", cc_test "" 2 cc_sarq_1 (false, false, false) 
    (fun m -> not m.flags.fo && not m.flags.fs && not m.flags.fz));
    ("cc_sarq_2", cs_test 2 cc_sarq_2 (false, false, true));
    ("cc_sarq_3", csou_test 2 cc_sarq_3 (false, true, false));
    ("cc_sarq_4", csou_test 2 cc_sarq_4 (true, false, false));
    (* shlq *)
    ("cc_shlq_1", cc_test "" 2 cc_shlq_1 (false, false, false) 
    (fun m -> not m.flags.fo && not m.flags.fs && not m.flags.fz));
    ("cc_shlq_2", csou_test 2 cc_shlq_2 (false, true, false));
    ("cc_shlq_3", csou_test 2 cc_shlq_3 (false, false, false));
    ("cc_shlq_4", csou_test 2 cc_shlq_4 (true, false, true));
    (* shrq *)
    ("cc_shrq_1", cc_test "" 2 cc_shrq_1 (false, false, false) 
    (fun m -> not m.flags.fo && not m.flags.fs && not m.flags.fz));
    ("cc_shrq_2", csou_test 2 cc_shrq_2 (false, false, true));
    ("cc_shrq_3", csou_test 2 cc_shrq_3 (true, false, false));
    (* setb *)
    ("cc_setb", cc_test "" 2 cc_setb (false, false, false) 
    (fun m -> not m.flags.fo && not m.flags.fs && not m.flags.fz));
    (* leaq *)
    ("cc_leaq", cc_test "" 1 cc_leaq (false, false, false) 
    (fun m -> not m.flags.fo && not m.flags.fs && not m.flags.fz));
    (* movq *)
    ("cc_movq", cc_test "" 1 cc_movq (false, false, false) 
    (fun m -> not m.flags.fo && not m.flags.fs && not m.flags.fz));
    (* pushq *)
    ("cc_pushq", cc_test "" 1 cc_pushq (false, false, false) 
    (fun m -> not m.flags.fo && not m.flags.fs && not m.flags.fz));
    (* popq *)
    ("cc_popq", cc_test "" 1 cc_popq (false, false, false) 
    (fun m -> not m.flags.fo && not m.flags.fs && not m.flags.fz));
    (* cmpq *)
    ("cc_cmpq_1", cs_test 1 cc_cmpq_1 (false, false, true));
    ("cc_cmpq_2", cs_test 1 cc_cmpq_2 (false, true, false));
    ("cc_cmpq_3", cs_test 3 cc_cmpq_3 (true, false, false));
    ("cc_cmpq_4", cs_test 3 cc_cmpq_4 (true, true, false));
    (* jmp *)
    ("cc_jmp", cc_test "" 3 cc_jmp (false, false, false) 
    (fun m -> not m.flags.fo && not m.flags.fs && not m.flags.fz));
    (* callq *)
    ("cc_callq", cc_test "" 2 cc_callq (false, false, false) 
    (fun m -> not m.flags.fo && not m.flags.fs && not m.flags.fz));
    (* retq *)
    ("cc_retq", cc_test "" 1 cc_retq (false, false, false) 
    (fun m -> not m.flags.fo && not m.flags.fs && not m.flags.fz));
  ]);
] 
