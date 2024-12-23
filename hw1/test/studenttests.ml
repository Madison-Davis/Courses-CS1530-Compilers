open Util.Assert
open Hellocaml

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let student_tests : suite = [
  Test ("Student-Provided Tests For Problem 1-3", [
    ("case1", assert_eqf (fun () -> 42) prob3_ans );
    ("case2", assert_eqf (fun () -> 25) (prob3_case2 17) );
    ("case3", assert_eqf (fun () -> prob3_case3) 64);
  ]);


  (* What to test beyond what was given as prior tests?  test some other types!
   1. test embedded tuples
   2. test floats
   3. test embedded lists
  *)
  Test ("Student-Provided Tests For Problem 2-1", [
    ("third_of_three1", assert_eqf (fun () -> third_of_three (1. , 2. , (1,2,3))) (1,2,3));
    ("third_of_three2", assert_eqf (fun () -> third_of_three (1. , 2. , 3.)) 3.);
    ("third_of_three3", assert_eqf (fun () -> third_of_three ((),"a",[(1,2);(3,4);(5,6)])) [(1,2);(3,4);(5,6)]);
  ]);


  (* What to test beyond what was given as prior tests?  test some other types!
   1. test lists with floats
   2. test lists with bools
   3. test level 1 embedded tuples
   4. test level 2 embedded tuples
   5. test embedded lists
  *)
  Test ("Student-Provided Tests For Problem 3-4", [
    ("rev_t1", assert_eqf (fun () -> rev_t [1.;2.]) [2.;1.]);
    ("rev_t2", assert_eqf (fun () -> rev_t [true; false; false]) [false;false;true]);
    ("rev_t3", assert_eqf (fun () -> rev_t [(1,2);(2,3)]) [(2,3);(1,2)]);
    ("rev_t4", assert_eqf (fun () -> rev_t [(1,(2,3));(2,(3,4))]) [(2,(3,4));(1,(2,3))]);
    ("rev_t5", assert_eqf (fun () -> rev_t [[1;2];[2;3];[3;4];[4;5]]) [[4;5];[3;4];[2;3];[1;2]]);
  ]);


  (* What to test beyond what was given as prior tests?
   1. Multiple variables within a single expression
   2. Fail when one variable exists in the ctxt# but another does not
  *)
  Test ("Student-Provided Tests For Problem 4-3", [
    ("interpret1", assert_eqf (fun () -> interpret ctxt2 (Mult(Var "x", Add(Var "y", Neg(Const 0L))))) 14L);
    ("interpret2", (fun () -> try ignore (interpret ctxt1 (Mult(Var "x", Add(Var "y", Neg(Const 0L))))); failwith "bad interpret" with Not_found -> ()));
  ]);


  (* What to test beyond what was given as prior tests?
    1. Negate: zero
    2. Negate: make sure we don't negate a non-zero constant  (we're be evaluating at that point)
    3. Negate: double negative = same expression
    4. Negate: make sure we don't negate a variable  (we're be evaluating at that point)
    5. Multiply: var with 1
    6. Multiply: two constants
    7. Multiply: make sure we don't multiply out variables
    8. Add: var with 0
    9. Add: make sure we don't add out 1 variables
    10. Add: make sure we don't add out multiple variables
    11. Advanced: nested add/mult/neg following tests #1, #5, and #7 constants only
    12. Advanced: nested add/mult/neg following tests #1, #5, and #7 incorporating variables
    13. Advanced: same idea as 10 but switch order
    14. Advanced: same idea as 11 but switch order
  *)

  Test ("Student-Provided Tests For Problem 4-4", [
    ("optimize1", assert_eqf (fun () -> optimize (Neg(Const 0L))) (Const 0L));
    ("optimize2", assert_eqf (fun () -> optimize (Neg(Const 3L))) ((Neg(Const 3L))));
    ("optimize3", assert_eqf (fun () -> optimize (Neg(Neg(Const 3L)))) (Const 3L));
    ("optimize4", assert_eqf (fun () -> optimize (Neg(Var "x"))) ((Neg(Var "x"))));
    ("optimize5", assert_eqf (fun () -> optimize (Mult(Const 1L, Var "x"))) (Var "x"));
    ("optimize6", assert_eqf (fun () -> optimize (Mult(Const 2L, Const 3L))) (Const 6L));
    ("optimize7", assert_eqf (fun () -> optimize (Mult(Const 2L, Var "x"))) (Mult(Const 2L, Var "x")));
    ("optimize8", assert_eqf (fun () -> optimize (Add(Const 0L, Var "x"))) (Var "x"));
    ("optimize9", assert_eqf (fun () -> optimize (Add(Var "x", Const 2L))) (Add(Var "x", Const 2L)));
    ("optimize10", assert_eqf (fun () -> optimize (Add(Var "x", Var "y"))) (Add(Var "x", Var "y")));
    ("optimize11", assert_eqf (fun () -> optimize (Add(Const 0L, Mult(Const 1L, Neg(Const 0L))))) (Const 0L));
    ("optimize12", assert_eqf (fun () -> optimize (Add(Var "x", Mult(Const 1L, Neg(Const 0L))))) (Var "x"));
    ("optimize13", assert_eqf (fun () -> optimize (Mult(Const 0L, Add(Const 1L, Neg(Const 0L))))) (Const 0L));
    ("optimize14", assert_eqf (fun () -> optimize (Mult(Var "x", Add(Const 1L, Neg(Const 0L))))) (Var "x"));
  ]);


  (* What to test beyond what was given as prior tests?
     1. Simple IMul with constants
     2. Simple Neg with vars
     3. Simple Add with constants and vars
     4. Nested Operations with constants
     4. Triple nested Operations with constants and variables
     Remember that we're pushing onto a STACK, which is LIFO, such that the newest added is at the "top" and oldest at "bottom"
     Thus, for an operation like IMul or IAdd, we need the most recently added top two on the stack, and INeg just the most recently added, then append result to top of stack
  *)

  Test ("Student-Provided Tests For Problem 5", [
    ("compile1", assert_eqf (fun () -> compile (Mult (Const 2L, Const 3L))) ([ IPushC 2L; IPushC 3L; IMul ]));
    ("compile2", assert_eqf (fun () -> compile (Neg (Var "y"))) ([ IPushV "y"; INeg ]));
    ("compile3", assert_eqf (fun () -> compile (Add (Const 1L, Var "x"))) ([ IPushC 1L; IPushV "x"; IAdd ]));
    ("compile4", assert_eqf (fun () -> compile (Mult (Const 2L, Add (Const 1L, Const 3L)))) ([ IPushC 2L; IPushC 1L; IPushC 3L; IAdd; IMul ]));
    ("compile5", assert_eqf (fun () -> compile (Neg (Mult (Const 2L, Add (Var "x", Const 3L))))) ([ IPushC 2L; IPushV "x"; IPushC 3L; IAdd; IMul; INeg ]));
  ]);
] 
