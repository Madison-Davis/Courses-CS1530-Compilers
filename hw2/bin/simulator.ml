(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next sevent bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | _ -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false


(* TO-DO *)
(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = fun x ->
  match x with
  | Eq -> fz
  | Neq -> if fz then false else true
  | Gt -> if fz then (fo = fs) && false else (fo = fs) && true
  | Ge -> (fo = fs)
  | Lt -> (fo <> fs) (* fo and fs have to be opposites, ie. 1/0 or 0/1 *)
  | Le -> (fo <> fs) || fz


(* TO-DO *)
(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
   if addr >= mem_top then None
   else if addr < mem_bot then None
   else 
    let hex_value = Int64.sub addr mem_bot in
      Some (Int64.to_int hex_value)


(* TO-DO *)
(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags *)

(* Here, ChatGPT helped me understand what is the 'option' type and how to handle it via pattern matching *)


(* HELPER FUNCTION: HANDLE MAP_ADDR OPTION PATTERN MATCHING *)
let get_index (addr) = 
  match (map_addr addr) with
  | Some i -> i
  | None -> raise X86lite_segfault
    
(* HELPER FUNCTION: GRAB THE VALUE *)
let get_value (m:mach) (src1:operand) : int64 = 
  match src1 with
    | Imm (Lit s) -> s
    | Reg r -> m.regs.(rind r)
    (* Ind1 = a literal address where first byte is a piece of data/number *)
    | Ind1 (Lit s) -> 
      let content : mem = Array.sub (m.mem) (get_index s) 8 in
      int64_of_sbytes (Array.to_list content)
    (* Ind2 = a register that contains an address we need to look at *)
    | Ind2 r -> 
      let addr_in_reg = m.regs.(rind r) in
      let index = get_index addr_in_reg in
      let content : mem = Array.sub (m.mem) (index) 8 in
      int64_of_sbytes (Array.to_list content)
    (* Ind3 = look at the part in memory that is  *)
    | Ind3 ((Lit imm), r) -> 
      let addr_in_reg = m.regs.(rind r) in
      let index = get_index addr_in_reg in
      let content : mem = Array.sub (m.mem) (index) 8 in
      int64_of_sbytes (Array.to_list content)
    | _ -> failwith "src1 unidentifiable value"

(* HELPER FUNCTION: PLACE VALUE IN MEMORY *)
let place_value (m:mach) (content:quad) (dest:operand) = 
  match dest with
  | Reg r -> 
    m.regs.(rind r) <- content
  | Ind1 (Lit r) -> 
    (* Array.blit = insertion of an Array (in this case, our content) into another Array (mem) *)
    Array.blit (Array.of_list (sbytes_of_int64 content)) 0 (m.mem) (get_index r) 8
  | Ind2 r -> 
    let dest_addr = m.regs.(rind r) in 
    Array.blit (Array.of_list (sbytes_of_int64 content)) 0 (m.mem) (get_index dest_addr) 8
  | Ind3 ((Lit imm), r) -> 
    let partial_dest_addr = m.regs.(rind r) in 
    let dest_addr = Int64.add partial_dest_addr imm in
    Array.blit (Array.of_list (sbytes_of_int64 content)) 0 (m.mem) (get_index dest_addr) 8;
  | _ -> failwith "Place Value: invalid placement of data"

(* HELPER FUNCTION: CALCULATE IND ADDRESS *)
let calc_addr (m:mach) (addr:operand) : quad = 
  match addr with
  | Ind1 (Lit i) -> i
  | Ind2 r -> m.regs.(rind r)
  | Ind3 ((Lit i), r) ->
    let partial_dest_addr = m.regs.(rind r) in 
    Int64.add partial_dest_addr i
  | _ -> failwith "Leaq: not supposed to calculate addr from a non-ind or label"


(* DO A STEP *)
let step (m:mach) : unit =
  
  (* HELPER FUNCTIONS: SET THE FLAGS *)
  let set_flags_arithmetic (value : quad) (overflow : bool) = 
    m.flags.fz <- value = 0L;
    m.flags.fs <- value < 0L;
    m.flags.fo <- overflow = true; 
  in
  let set_flags_logic (value : quad) = 
    m.flags.fz <- value = 0L;
    m.flags.fs <- value < 0L;
    m.flags.fo <- false;
  in

  (* FIND THE INSTRUCTION *)
  let rip_content = m.regs.(rind Rip) in
    let mem_index = map_addr rip_content in
        begin match mem_index with
        | None -> raise X86lite_segfault
        | Some index -> let byte = m.mem.(index) in 
          begin match byte with
          | InsFrag -> failwith "Step: Not an instruction"
          | Byte c -> failwith "Step: Not an instruction"
          | InsB0 (op, args) -> 

            

            begin match (op, args) with
              (* ARITHMETIC INSTRUCTIONS *)
              | Negq,  [dest] -> 
                    let dest_val = get_value m dest in
                    let results = Int64_overflow.neg dest_val in
                    place_value m results.value dest;
                    m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);
                    m.flags.fz <- results.value = 0L;
                    m.flags.fs <- results.value < 0L;
                    m.flags.fo <- dest_val = Int64.min_int
              | Incq,  [src1] -> 
                    let src1_val = get_value m src1 in
                    let results = Int64_overflow.add src1_val 1L in
                    place_value m results.value src1;
                    m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);
                    set_flags_arithmetic results.value results.overflow;
              | Decq,  [src1] -> 
                    let src1_val = get_value m src1 in
                    let results = Int64_overflow.sub src1_val 1L in
                    place_value m results.value src1;
                    m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);
                    set_flags_arithmetic results.value results.overflow;
              | Imulq, [src1;src2] -> 
                    let src1_val = get_value m src1 in
                    let src2_val = get_value m src2 in
                    let results = Int64_overflow.mul src2_val src1_val in
                    place_value m results.value src2;
                    m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);
                    (* imulq sf and zf are undefined,
                      so we can do whatever we want with them
                      in our case, let's just set them as usual  *)
                    set_flags_arithmetic results.value results.overflow;
              | Addq,  [src1;src2] -> 
                    let src1_val = get_value m src1 in
                    let src2_val = get_value m src2 in
                    let results = Int64_overflow.add src2_val src1_val in
                    place_value m results.value src2;
                    m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);
                    (* overflow happens when pos + pos = neg OR neg + neg = pos  *)
                    set_flags_arithmetic results.value results.overflow;
              | Subq,  [src1;dest] -> 
                    let src1_val = get_value m src1 in
                    let dest_val = get_value m dest in
                    let results = Int64_overflow.sub dest_val src1_val in
                    place_value m results.value dest;
                    m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);
                    (* overflow happens when:
                      values are diff -/+
                      and result is same sign as subtracthend (src)
                      -dest - (src) = val
                      dest - (-src) = -val *)
                    set_flags_arithmetic results.value results.overflow;
              


              (* LOGIC INSTRUCTIONS *)
              | Notq, [src1] -> 
                    let src1_val = get_value m src1 in
                    let result = Int64.lognot src1_val in
                    place_value m result src1;
                    m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);
              | Andq, [src1;src2] -> 
                    let src1_val = get_value m src1 in
                    let src2_val = get_value m src2 in
                    let result = Int64.logand src2_val src1_val in
                    place_value m result src2;
                    m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);
                    set_flags_logic result;
              | Orq,  [src1;src2] -> 
                    let src1_val = get_value m src1 in
                    let src2_val = get_value m src2 in
                    let result = Int64.logor src2_val src1_val in
                    place_value m result src2;
                    m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);
                    set_flags_logic result;
              | Xorq, [src1;src2] ->
                    let src1_val = get_value m src1 in
                    let src2_val = get_value m src2 in
                    let result = Int64.logxor src2_val src1_val in
                    place_value m result src2;
                    m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);
                    set_flags_logic result;



              (* DATA MOVEMENT INSTRUCTIONS *)
              | Leaq, [ind;dst] -> 
                    let ind_addr = calc_addr m ind in
                    place_value m ind_addr dst
              | Movq, [src1;src2] -> 
                    let src1_val = get_value m src1 in
                    place_value m src1_val src2;
                    m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);
              | Pushq, [src1] -> 
                    (* rsp <= rsp - 8 *)
                    let src1_val = get_value m src1 in
                    let new_rsp = Int64.sub (m.regs.(rind Rsp)) 8L in
                    m.regs.(rind Rsp) <- new_rsp;
                    (* mem[the new rsp] <= src *)
                    Array.blit (Array.of_list (sbytes_of_int64 src1_val)) 0 (m.mem) (get_index new_rsp) 8;
                    m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);
              | Popq,  [dst] -> 
                    (* Ind2 Rsp so as to get the memory of Rsp *)
                    let rsp_val = get_value m (Ind2 Rsp) in 
                    let new_rsp = Int64.add (m.regs.(rind Rsp)) 8L in
                    (* dest <= mem[rsp] *)
                    place_value m rsp_val dst;
                    (* rsp <= rsp + 8 *)
                    m.regs.(rind Rsp) <- new_rsp;
                    m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);
                    
                    


              (* BIT-MANIPULATION INSTRUCTIONS *)
              | Sarq, [amt;dst] -> 
                  let amt_val = get_value m amt in
                  let dst_val = get_value m dst in
                  let result = Int64.shift_right dst_val (Int64.to_int amt_val) in
                  place_value m result dst;
                  m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);
                  if amt_val = 1L then m.flags.fo <- false;
                  if amt_val <> 0L then begin
                    m.flags.fz <- result = 0L;
                    m.flags.fs <- result < 0L;
                  end;
              | Shlq, [amt;dst] -> 
                  let amt_val = get_value m amt in
                  let dst_val = get_value m dst in
                  let result = Int64.shift_left dst_val (Int64.to_int amt_val) in
                  place_value m result dst;
                  m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);

                  let top_two_msb (n : quad) : quad = 
                    (* top two msb will be put in the 0s and 1s place *)
                    let mask = Int64.shift_left 3L 62 in
                    let result : quad = Int64.logand n mask in
                    let result_shifted_back : quad = Int64.shift_right_logical result 62 in
                    result_shifted_back
                  in
                  let original_two_msb : quad = top_two_msb dst_val in
                  let final_two_msb : quad = top_two_msb result in

                  if amt_val = 1L then 
                    if original_two_msb = 0L || original_two_msb = 3L then 
                      m.flags.fo <- false
                    else
                      m.flags.fo <- true;
                  if amt_val <> 0L then begin
                    m.flags.fz <- result = 0L;
                    m.flags.fs <- result < 0L;
                  end;
              | Shrq, [amt;dst] -> 
                  let amt_val = get_value m amt in
                  let dst_val = get_value m dst in

                  let msb (n : quad) : quad = 
                    let mask = Int64.shift_left 1L 63 in
                    let result = Int64.logand n mask in
                    if result = 0L then 0L else 1L; 
                  in
                  let msb_original : quad = msb dst_val in
                  let result : quad = Int64.shift_right_logical dst_val (Int64.to_int amt_val) in
                  let msb_result : quad = msb result in
                  
                  place_value m result dst;
                  m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);
                  if amt_val = 1L then m.flags.fo <- if msb_original = 0L then false else true;
                  if amt_val <> 0L then begin
                    m.flags.fz <- result = 0L;
                    m.flags.fs <- if msb_result = 0L then false else true;
                  end;
              | Set condition, [dst] -> 
                  let result = interp_cnd m.flags condition in
                  let number = get_value m dst in
                  let lowest_bit = Int64.logand number 1L in
                  if result = true then 
                  let insert_1 = Int64.logor number lowest_bit in
                  place_value m insert_1 dst
                  else 
                  let insert_0 = Int64.logor number lowest_bit in
                  place_value m insert_0 dst



              (* CONTROL FLOW INSTRUCTIONS *)
              | Jmp, [src1] -> 
                    let src1_val = get_value m src1 in
                    m.regs.(rind Rip) <- src1_val
              | J condition, [src1] -> 
                    let src1_val = get_value m src1 in
                    let result = interp_cnd m.flags condition in
                    if result = true then 
                    m.regs.(rind Rip) <- src1_val
                    else 
                    m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);   
              | Callq, [src1] -> 
                    (* CALLQ = pushq rip *)
                    (* rsp <= rsp - 8 *)
                    let new_rsp = Int64.sub (m.regs.(rind Rsp)) 8L in
                    m.regs.(rind Rsp) <- new_rsp;
                    m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L;
                    (* mem[rsp] <= src*)
                    let index = get_index m.regs.(rind Rsp) in
                    let value = m.regs.(rind Rip) in
                    let data = sbytes_of_data @@ Quad (Lit value) in
                    Array.blit (Array.of_list data) 0 (m.mem) index (List.length data);
                    (* rip = source *)
                    let src1_val : int64 = get_value m src1 in
                    m.regs.(rind Rip) <- src1_val;
              | Cmpq,  [src1;src2] -> 
                    let src1_val = get_value m src1 in
                    let src2_val = get_value m src2 in
                    let results = Int64_overflow.sub src2_val src1_val in
                    m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);   
                    set_flags_arithmetic results.value results.overflow;
              | _ -> 
                (* RETQ = pop rip *)
                (* DEST <= Mem[rsp] *)
                let rsp_val = get_value m (Ind2 Rsp) in
                m.regs.(rind Rip) <- rsp_val;
                (* rsp = rsp + 8 *)
                let new_rsp = Int64.add (m.regs.(rind Rsp)) 8L in
                m.regs.(rind Rsp) <- new_rsp;
            end
          end
        end
        
 


(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do 
    step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)
let assemble (p:prog) : exec =


  (* PART 1: SEPARATE INTO SEGMENTS *)
  (* --------------------------------------------------------------- *)
  
  let grab_text segment_acc (elem : elem) : elem list = 
    match elem.asm with
    | Text ins -> segment_acc @ [elem]
    | Data ins -> segment_acc
  in

  let grab_data segment_acc (elem : elem) : elem list = 
    match elem.asm with
    | Text ins -> segment_acc
    | Data ins -> segment_acc @ [elem]
  in

  let text_segments : elem list = List.fold_left grab_text [] p in
  let data_segments : elem list = List.fold_left grab_data [] p in


  (* PART 2: COUNT SIZES *)
  (* --------------------------------------------------------------- *)

  let calculate_segment_size (start_value : int) (elem : elem) : int = 
    begin match elem.asm with
    | Data data_list ->
          let rec sum acc =  function
          | [] -> acc
          | hd :: tl -> 
            begin match hd with
            | Asciz str -> sum (acc + String.length str + 1) tl  (* size of a string is its length + 1 *)
            | Quad int64 -> sum (acc + 8) tl (* size of a quad is 8 bytes *)
            end
          in
          sum start_value data_list
    | Text text_list -> 
          let rec sum acc =  function
          | [] -> acc
          | hd :: tl -> sum (acc + 8) tl (* each instruction is 8 bytes long, one of which is InsB0 *)
          in
          sum start_value text_list
    end    
  in

  let text_segment_sizes_accumulating_incl_last : int list = 
    let text_segment_sizes = List.map (fun elem -> calculate_segment_size 0 elem) text_segments in
    let (_, accumulated) = List.fold_left (fun (acc, acc_list) size -> 
      let new_acc = acc + size in
      (new_acc, acc_list @ [new_acc])
    ) (0, [0]) text_segment_sizes in 
    accumulated
  in

  let text_segment_sizes_accumulating : int list = List.rev (List.tl (List.rev text_segment_sizes_accumulating_incl_last)) in
  let end_of_text_segment : int = List.hd (List.rev text_segment_sizes_accumulating_incl_last) in

  let data_segment_sizes_accumulating : int list = 
    let data_segment_sizes = List.map (fun elem -> calculate_segment_size end_of_text_segment elem) data_segments in
    let (_, accumulated) = List.fold_left (fun (acc, acc_list) size -> 
      let new_acc = acc + size in
      (new_acc, acc_list @ [new_acc])
    ) (0, [end_of_text_segment]) data_segment_sizes in
    accumulated
  in

  let text_segment_start_pos : quad = mem_bot in
  let data_segment_start_pos : quad = Int64.add mem_bot (Int64.of_int (List.nth data_segment_sizes_accumulating 0)) in
  

  (* PART 3: LABELS *)
  (* --------------------------------------------------------------- *)
  
  (* CHECK FOR REDEFINED LABELS *)
  let check_dup (value : lbl) (lst : lbl list) =
    if List.mem value lst then
      raise (Redefined_sym value)
    else
      lst @ [value]
  in
  let text_segments_labels : lbl list =
    List.fold_left
      (fun acc text_seg ->
          check_dup text_seg.lbl acc
      ) [] text_segments
  in
  let data_segments_labels : lbl list =
    List.fold_left
      (fun acc data_seg ->
          check_dup data_seg.lbl acc
      ) [] data_segments
  in

  (* STEPS: given an elem list,
     Helper Function 1. change that elem list to an ins list
     Helper Function 2. modify the ins list for a single label
     Helper Function 3. process all labels *)

  (* (HELPER FUNCTION 1) *)
  let elem_list_to_ins_list (elem_list : elem list) : ins list =
    let ins_list_list : ins list list = List.map (fun elem ->
      match elem.asm with
      | Text instructions -> instructions
      | _ -> failwith "Expected Text, not Data"
    ) elem_list in 
    List.flatten (ins_list_list)
  in

  (* (HELPER FUNCTION 2) *)
  let modify_label_ins_list (all_instructions : ins list) (label : lbl) (label_offset : int ) = 
    let addr = Int64.add mem_bot (Int64.of_int label_offset) in
    (* UPDATE EACH INSTRUCTION INDIVIDUALLY BY MATCHING OPERANDS*)
    List.map (
      fun (instruction : ins) -> 
        match instruction with
        | (op, operand_list) -> 
          let updated_operands = 
            List.map (
            fun operand -> 
              match operand with
              | Imm (Lbl l) -> if label = l 
                then Imm (Lit addr)
                else operand
              | Ind1 (Lbl l) -> if label = l
                then Ind1 (Lit addr)
                else operand
              | Ind3 (Lbl l, other) -> if label = l
                then Ind3 (Lit addr, other)
                else operand
              | _ -> operand
            ) operand_list in 
            (op, updated_operands)
    ) all_instructions
  in

  (* (HELPER FUNCTION 3) *)
  let rec process_labels (labels : lbl list) (label_offsets : int list) (ins_list : ins list) : ins list =
    match labels, label_offsets with
    | [], _ | _, [] -> ins_list  (* Base case: no more labels or offsets to check *)
    | label :: rest_labels, offset :: rest_offsets ->
      let modified_ins_list = modify_label_ins_list ins_list label offset in
      process_labels rest_labels rest_offsets modified_ins_list
  in

  (* PERFORM STEPS 1-3 ON ALL LABELS AND ALL OFFSETS *)
  let all_labels : lbl list = text_segments_labels @ data_segments_labels in
  let all_offsets : int list = text_segment_sizes_accumulating @ data_segment_sizes_accumulating in
  let label_offsets : int list = List.rev (List.tl (List.rev all_offsets)) in

  (* CHECK FOR UNDEFINED LABELS PART 1 *)
  if (List.exists (fun x -> x = "main") all_labels) = false then raise (Undefined_sym "main");
  let text_segments_no_labels_unchecked =
    let ins_list = elem_list_to_ins_list text_segments in
    process_labels all_labels label_offsets ins_list 
  in

  (* CHECK FOR UNDEFINED LABELS PART 2 *)
  let check_for_undefined_labels (instructions : ins list) =
    List.map (fun (instruction : ins) ->
      match instruction with
      | (op, operands) ->
        let new_operands =
            List.map (fun operand ->
            match operand with
            | Imm (Lbl lbl) -> raise (Undefined_sym lbl)
            | Ind1 (Lbl lbl) -> raise (Undefined_sym lbl)
            | Ind3 (Lbl lbl, _) -> raise (Undefined_sym lbl)
            | _ -> operand
          ) operands
        in
        (op, new_operands)
    ) instructions
  in
  let text_segments_no_labels = check_for_undefined_labels text_segments_no_labels_unchecked in

  (* FIND THE ENTRY POINT LABEL *)
  let rec find_entry (labels : lbl list) (index : int )= 
    match labels with
    | [] -> -1
    | hd :: tl ->
      if hd = "main" then index
      else find_entry tl (index +  1)
  in
  let entry_point : quad = 
    let index = find_entry all_labels 0 in
    if index = -1 then failwith "no valid entry point" 
    else Int64.add mem_bot (Int64.of_int (List.nth label_offsets index))  
  in


  (* PART 4: CONVERT OUR INSTRUCTIONS AND DATA INTO SBYTES *) 
  (* --------------------------------------------------------------- *)
  let sbytes_from_ins_list (ins_list : ins list) : sbyte list = 
    let result = List.map 
    ( fun instruction -> sbytes_of_ins instruction
    ) ins_list
    in List.flatten result
  in

  let sbytes_from_data_list (data_list : elem list) : sbyte list = 
    let result = List.concat_map (fun elem ->
      match elem.asm with
      | Data data_stuff -> List.map (fun data -> sbytes_of_data data) data_stuff
      | _ -> failwith "sbytes_from_data_list: attempt to convert non-data"
    ) data_list
    in
    List.flatten (result)
  in

  let sbytes_text : sbyte list = sbytes_from_ins_list (text_segments_no_labels) in
  let sbytes_data : sbyte list = sbytes_from_data_list data_segments in

  
  (* PART 5: PUT IT ALL TOGETHER! *)
  (* --------------------------------------------------------------- *)
  let exec : exec = { entry = entry_point; text_pos = text_segment_start_pos; data_pos = data_segment_start_pos; text_seg = sbytes_text; data_seg = sbytes_data} in
  exec
  



(* Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
*)
let load {entry; text_pos; data_pos; text_seg; data_seg} : mach = 
  
  (* ALLOCATE MEMORY AND INSERT TEXT SEG, DATA SEG *)
  let mem = (Array.make mem_size (Byte '\x00')) in
  Array.blit (Array.of_list text_seg) 0 mem (get_index text_pos) (List.length text_seg);
  Array.blit (Array.of_list data_seg) 0 mem (get_index data_pos) (List.length data_seg);
  
  (* CREATE INITIAL REGISTER STATE *)
  let regs = Array.make nregs 0L in
  regs.(rind Rip) <- entry;
  regs.(rind Rsp) <- Int64.sub mem_top 8L; 

  (* SET UP EXIT ADDRESS *)
  let addr = regs.(rind Rsp) in
  let addr_index = get_index addr in
  let data = sbytes_of_data @@ Quad (Lit exit_addr) in
  Array.blit (Array.of_list data) 0 mem addr_index (List.length data);

  let mach : mach = { flags = {fo = false; fs = false; fz = false};
    regs = regs;
    mem = mem
  } in mach