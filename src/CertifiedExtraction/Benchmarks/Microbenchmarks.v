Require Import CertifiedExtraction.Benchmarks.MicrobenchmarksSetup.

Definition Microbenchmarks_Carrier : Type := sum (list W) (list (list W)).

Definition Microbenchmarks_Env : Env Microbenchmarks_Carrier :=
  (GLabelMap.empty (FuncSpec _))
    ### ("std", "rand") ->> (Axiomatic FRandom)
    ### ("list[W]", "nil") ->> (Axiomatic (FacadeImplementationOfConstructor (list W) nil))
    ### ("list[W]", "push") ->> (Axiomatic (FacadeImplementationOfMutation_SCA (list W) cons))
    ### ("list[W]", "pop") ->> (Axiomatic (List_pop W))
    ### ("list[W]", "delete") ->> (Axiomatic (FacadeImplementationOfDestructor (list W)))
    ### ("list[W]", "empty?") ->> (Axiomatic (List_empty W))
    ### ("list[list[W]]", "nil") ->> (Axiomatic (FacadeImplementationOfConstructor (list (list W)) nil))
    ### ("list[list[W]]", "push") ->> (Axiomatic (FacadeImplementationOfMutation_ADT (list W) (list (list W)) cons))
    ### ("list[list[W]]", "pop") ->> (Axiomatic (List_pop (list W)))
    ### ("list[list[W]]", "delete") ->> (Axiomatic (FacadeImplementationOfDestructor (list (list W))))
    ### ("list[list[W]]", "empty?") ->> (Axiomatic (List_empty (list W))).

Example micro_plus :
  ParametricExtraction
    #vars      x y
    #program   ret (Word.wplus x y)
    #arguments [[`"x" <-- x as _ ]] :: [[`"y" <-- y as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_plus).

(* Output:
     = ("out" <- Var "x" + Var "y")%facade
     : Stmt *)

Example micro_plus_minus :
  ParametricExtraction
    #vars      x y
    #program   ret (Word.wplus x (Word.wminus y x))
    #arguments [[`"x" <-- x as _ ]] :: [[`"y" <-- y as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_plus_minus).

(* Output:
     = ("r" <- Var "y" - Var "x";
        "out" <- Var "x" + Var "r")%facade
     : Stmt *)

Example micro_min :
  ParametricExtraction
    #vars      x y
    #program   ret (if Word.wlt_dec x y then x else y)
    #arguments [[`"x" <-- x as _ ]] :: [[`"y" <-- y as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_min).

(* Output:
     = ("test" <- Var "x" < Var "y";
        If Const (Word.natToWord 32 1) = Var "test" Then
          "out" <- Var "x"
        Else
          "out" <- Var "y"
        EndIf)%facade
     : Stmt *)

Example micro_max :
  ParametricExtraction
    #vars      x y
    #program   ret (if Word.wlt_dec x y then y else x)
    #arguments [[`"x" <-- x as _ ]] :: [[`"y" <-- y as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_max).

(* Output:
     = ("test" <- Var "x" < Var "y";
        If Const (Word.natToWord 32 1) = Var "test" Then
          "out" <- Var "y"
        Else
          "out" <- Var "x"
        EndIf)%facade
     : Stmt *)

Example micro_squared_max :
  ParametricExtraction
    #vars      x y
    #program   ret (if Word.wlt_dec x y then Word.wmult y y else Word.wmult x x)
    #arguments [[`"x" <-- x as _ ]] :: [[`"y" <-- y as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_squared_max).

(* Output:
     = ("test" <- Var "x" < Var "y";
        If Const (Word.natToWord 32 1) = Var "test" Then
          "out" <- Var "y" * Var "y"
        Else
          "out" <- Var "x" * Var "x"
        EndIf)%facade
     : Stmt *)

Example micro_make_singleton :
  ParametricExtraction
    #vars      x y
    #program   ret (x :: y :: nil)
    #arguments [[`"x" <-- x as _ ]] :: [[`"y" <-- y as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_make_singleton).

(* Output:
     = ("arg" <- Var "x";
        "arg0" <- Var "y";
        "out" <- "list[W]"."nil"();
        call "list[W]"."push"("out", "arg0");
        call "list[W]"."push"("out", "arg"))%facade
     : Stmt *)

Example micro_duplicate_word :
  ParametricExtraction
    #vars      x
    #program   ret (x :: x :: nil)
    #arguments [[`"x" <-- x as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

(* Output:
     = ("arg" <- Var "x";
        "arg0" <- Var "arg";
        "out" <- "list[W]"."nil"();
        call "list[W]"."push"("out", "arg0");
        call "list[W]"."push"("out", "arg"))%facade
     : Stmt *)

Time Eval lazy in (extract_facade micro_duplicate_word).

Example micro_sort_pair_1 :
  ParametricExtraction
    #vars      x y
    #program   ret (if Word.wlt_dec x y then x :: y :: nil else y :: x :: nil)
    #arguments [[`"x" <-- x as _ ]] :: [[`"y" <-- y as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_sort_pair_1).

(* Output:
     = ("test" <- Var "x" < Var "y";
        If Const (Word.natToWord 32 1) = Var "test" Then
          "arg" <- Var "x";
          "arg0" <- Var "y";
          "out" <- "list[W]"."nil"();
          call "list[W]"."push"("out", "arg0");
          call "list[W]"."push"("out", "arg")
        Else
          "arg" <- Var "y";
          "arg0" <- Var "x";
          "out" <- "list[W]"."nil"();
          call "list[W]"."push"("out", "arg0");
          call "list[W]"."push"("out", "arg")
        EndIf)%facade
     : Stm *)

Example micro_sort_pair_2 :
  ParametricExtraction
    #vars      x y
    #program   ret ((if Word.wlt_dec x y then x else y) :: (if Word.wlt_dec x y then y else x) :: nil)
    #arguments [[`"x" <-- x as _ ]] :: [[`"y" <-- y as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_sort_pair_2).

(* Output:
     = ("test" <- Var "x" < Var "y";
        If Const (Word.natToWord 32 1) = Var "test" Then
          "arg" <- Var "x"
        Else
          "arg" <- Var "y"
        EndIf;
        "test" <- Var "x" < Var "y";
        If Const (Word.natToWord 32 1) = Var "test" Then
          "arg0" <- Var "y"
        Else
          "arg0" <- Var "x"
        EndIf;
        "out" <- "list[W]"."nil"();
        call "list[W]"."push"("out", "arg0");
        call "list[W]"."push"("out", "arg"))%facade
     : Stm *)

Example micro_double :
  ParametricExtraction
    #vars      seq
    #program   ret (revmap (fun w => Word.wmult w 2) seq)
    #arguments [[`"seq" <-- seq as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_double).

(* Output:
     = ("out" <- "list[W]"."nil"();
        "test" <- "list[W]"."empty?"("seq");
        While ("test" = 0)
            "head" <- "list[W]"."pop"("seq");
            "r" <- Const 2;
            "head'" <- Var "head" * Var "r";
            call "list[W]"."push"("out", "head'");
            "test" <- "list[W]"."empty?"("seq");
        "test" <- "list[W]"."delete"("seq");
        __)%facade
     : Stm *)

Definition nibble_power_of_2_p (w: W) :=
  Eval simpl in bool2w (Inb w (map Word.NToWord [[[1; 2; 4; 8]]]%N)).

Ltac _compile_early_hook ::= progress unfold nibble_power_of_2_p.

Example micro_nibble_power_of_2 :
  ParametricExtraction
    #vars      x
    #program   ret (nibble_power_of_2_p (Word.wplus x 1))
    #arguments [[`"x" <-- x as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_nibble_power_of_2).

(* Output:
     = ("r" <- Const 1;
        "l" <- Var "x" + Var "r";
        "r" <- Const (Word.NToWord 1);
        "test" <- Var "l" = Var "r";
        If Const (Word.natToWord 32 1) = Var "test" Then
          "out" <- Const (Word.natToWord 32 1)
        Else
          "r" <- Const 1;
          "l" <- Var "x" + Var "r";
          "r" <- Const (Word.NToWord 2);
          "test0" <- Var "l" = Var "r";
          If Const (Word.natToWord 32 1) = Var "test0" Then
            "out" <- Const (Word.natToWord 32 1)
          Else
            "r" <- Const 1;
            "l" <- Var "x" + Var "r";
            "r" <- Const (Word.NToWord 4);
            "test1" <- Var "l" = Var "r";
            If Const (Word.natToWord 32 1) = Var "test1" Then
              "out" <- Const (Word.natToWord 32 1)
            Else
              "r" <- Const 1;
              "l" <- Var "x" + Var "r";
              "r" <- Const (Word.NToWord 8);
              "test2" <- Var "l" = Var "r";
              If Const (Word.natToWord 32 1) = Var "test2" Then
                "out" <- Const (Word.natToWord 32 1)
              Else
                "out" <- Const (Word.natToWord 32 0)
              EndIf
            EndIf
          EndIf
        EndIf)%facade
     : Stm *)

Ltac _compile_early_hook ::= fail.

Example micro_nibble_power_of_2__intrinsic :
  ParametricExtraction
    #vars      x
    #program   ret (nibble_power_of_2_p (Word.wplus x 1))
    #arguments [[`"x" <-- x as _ ]] :: Nil
    #env       Microbenchmarks_Env ### ("intrinsics", "nibble_pow2") ->> (Axiomatic (FacadeImplementationWW _ nibble_power_of_2_p)).
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_nibble_power_of_2__intrinsic).

(* Output:
     = ("r" <- Const 1;
        "arg" <- Var "x" + Var "r";
        "out" <- "intrinsics"."nibble_pow2"("arg"))%facade
     : Stm *)

Example micro_fold_plus :
  ParametricExtraction
    #vars      seq
    #program   ret (fold_left (@Word.wplus 32) seq 0)
    #arguments [[`"seq" <-- seq as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_fold_plus).

(* Output:
     = ("out" <- Const 0;
        "test" <- "list[W]"."empty?"("seq");
        While ("test" = 0)
            "head" <- "list[W]"."pop"("seq");
            "out" <- Var "out" + Var "head";
            "test" <- "list[W]"."empty?"("seq");
        call "list[W]"."delete"("seq");
        __)%facade
     : Stm *)

Example micro_fold_plus_x :
  ParametricExtraction
    #vars      seq x
    #program   ret (fold_left (@Word.wplus 32) seq x)
    #arguments [[`"seq" <-- seq as _ ]] :: [[`"x" <-- x as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

(* Output:
     = ("out" <- Var "x";
        "test" <- "list[W]"."empty?"("seq");
        While ("test" = 0)
            "head" <- "list[W]"."pop"("seq");
            "out" <- Var "out" + Var "head";
            "test" <- "list[W]"."empty?"("seq");
        call "list[W]"."delete"("seq");
        __)%facade
     : Stm *)

Time Eval lazy in (extract_facade micro_fold_plus_x).

Ltac _compile_early_hook ::= rewrite List_rev_as_fold.

Example micro_fold_reverse :
  ParametricExtraction
    #vars      seq
    #program   ret (List.rev seq)
    #arguments [[`"seq" <-- seq as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_fold_reverse).

(* Output:
     = ("out" <- "list[list[W]]"."nil"();
        "test" <- "list[list[W]]"."empty?"("seq");
        While ("test" = 0)
            "head" <- "list[list[W]]"."pop"("seq");
            call "list[list[W]]"."push"("out", "head");
            "test" <- "list[list[W]]"."empty?"("seq");
        call "list[list[W]]"."delete"("seq");
        __)%facade
     : Stm *)

Example micro_fold_flatten_rev :
  ParametricExtraction
    #vars      seqs
    #program   ret (fold_left (fun acc seq => fold_left (fun acc' x => x :: acc') seq acc) seqs nil)
    #arguments [[`"seqs" <-- seqs as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_fold_flatten_rev).

(* Output:
     = ("out" <- "list[W]"."nil"();
        "test" <- "list[list[W]]"."empty?"("seqs");
        While ("test" = 0)
            "head" <- "list[list[W]]"."pop"("seqs");
            "test0" <- "list[W]"."empty?"("head");
            While ("test0" = 0)
                "head0" <- "list[W]"."pop"("head");
                call "list[W]"."push"("out", "head0");
                "test0" <- "list[W]"."empty?"("head");
            call "list[W]"."delete"("head");
            __;
            "test" <- "list[list[W]]"."empty?"("seqs");
        call "list[list[W]]"."delete"("seqs");
        __)%facade
     : Stm *)

Ltac _compile_random :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (?tenv, Cons ?k Random ?tenv') =>
              match k with
              | NTNone => let vrandom := gensym "random" in
                         apply ProgOk_Transitivity_Name_SCA with vrandom
              | _ => idtac
              end;
                first [ call_tactic_after_moving_head_binding_to_separate_goal ltac:(apply CompileCallRandom)
                      | apply miniChomp'; apply CompileDeallocSCA_discretely ]
            end).

Ltac _compile_early_hook ::= _compile_random.

Example micro_pick_random :
  ParametricExtraction
    #program Random
    #env     Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_pick_random).

(* Output:
     = ("out" <- "std"."rand"())%facade
     : Stm *)

Example micro_sum_random :
  ParametricExtraction
    #program ( r1 <- Random;
               r2 <- Random;
               ret (Word.wplus r1 r2) )
    #env     Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_sum_random).

(* Output:
     = ("random" <- "std"."rand"();
        "random0" <- "std"."rand"();
        "out" <- Var "random" + Var "random0")%facade
     : Stm *)

Example micro_push_random :
  ParametricExtraction
    #vars      seq: list W
    #program ( r <- Random;
               ret (r :: seq) )
    #arguments [[`"out" <-- seq as _ ]] :: Nil
    #env     Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_push_random).

(* Output:
     = ("random" <- "std"."rand"();
        "arg" <- Var "random";
        call "list[W]"."push"("out", "arg"))%facade
     : Stm *)

Example micro_randomize :
  ParametricExtraction
    #vars      seq: list W
    #program   fold_left (fun acc elem => ( a <- acc;
                                         r <- Random;
                                         ret (r :: a) )%comp) seq (ret nil)
    #arguments [[`"seq" <-- seq as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_randomize).

(* Output:
     = ("out" <- "list[W]"."nil"();
        "test" <- "list[W]"."empty?"("seq");
        While ("test" = 0)
            "head" <- "list[W]"."pop"("seq");
            "random" <- "std"."rand"();
            "arg" <- Var "random";
            call "list[W]"."push"("out", "arg");
            __;
            "test" <- "list[W]"."empty?"("seq");
        call "list[W]"."delete"("seq");
        __)%facade
     : Stm *)

Example micro_double_larger_than_random :
  ParametricExtraction
    #vars      seq
    #program   ( threshold <- Random;
                 ret (revmap (fun w => if Word.wlt_dec threshold w then
                                      Word.wmult w 2
                                    else
                                      w)
                             seq) )
    #arguments [[`"seq" <-- seq as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_double_larger_than_random).

(* Output:
     = ("random" <- "std"."rand"();
        "out" <- "list[W]"."nil"();
        "test" <- "list[W]"."empty?"("seq");
        While ("test" = 0)
            "head" <- "list[W]"."pop"("seq");
            "test0" <- Var "random" < Var "head";
            If Const (Word.natToWord 32 1) = Var "test0" Then
              "r" <- Const 2;
              "head'" <- Var "head" * Var "r"
            Else
              "head'" <- Var "head"
            EndIf;
            call "list[W]"."push"("out", "head'");
            "test" <- "list[W]"."empty?"("seq");
        "test" <- "list[W]"."delete"("seq");
        __)%facade
     : Stm *)

Example micro_duplicate_all :
  ParametricExtraction
    #vars      (seq: list W)
    #program   ( ret (fold_left (fun acc w => w :: w :: acc)
                                seq nil) )
    #arguments [[`"seq" <-- seq as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_duplicate_all).

(* Output:
     = ("out" <- "list[W]"."nil"();
        "test" <- "list[W]"."empty?"("seq");
        While ("test" = 0)
            "head" <- "list[W]"."pop"("seq");
            "arg" <- Var "head";
            call "list[W]"."push"("out", "arg");
            "arg" <- Var "head";
            call "list[W]"."push"("out", "arg");
            __;
            "test" <- "list[W]"."empty?"("seq");
        call "list[W]"."delete"("seq");
        __)%facade
     : Stm *)

Example micro_increment_zeroes :
  ParametricExtraction
    #vars      (seq: list W)
    #program   ( ret (fold_left (fun acc w => (if Word.weqb w (Word.natToWord 32 0) then
                                              (Word.natToWord 32 1)
                                            else
                                              w) :: acc)
                                seq nil) )
    #arguments [[`"seq" <-- seq as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_increment_zeroes).

(* Output:
     = ("out" <- "list[W]"."nil"();
        "test" <- "list[W]"."empty?"("seq");
        While ("test" = 0)
            "head" <- "list[W]"."pop"("seq");
            "test0" <- Var "head" = Var "test";
            If Const (Word.natToWord 32 1) = Var "test0" Then
              "arg" <- Const (Word.natToWord 32 1)
            Else
              "arg" <- Var "head"
            EndIf;
            call "list[W]"."push"("out", "arg");
            __;
            "test" <- "list[W]"."empty?"("seq");
        call "list[W]"."delete"("seq");
        __)%facade
     : Stm *)

Example micro_read_baseN :
  ParametricExtraction
    #vars      (seq: list W) N
    #program   ( ret (fold_left (fun acc w => (Word.wmult w N) :: acc)
                                seq nil) )
    #arguments [[`"seq" <-- seq as _ ]] :: [[`"N" <-- N as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_read_baseN).

(* Output:
     = ("out" <- "list[W]"."nil"();
        "test" <- "list[W]"."empty?"("seq");
        While ("test" = 0)
            "head" <- "list[W]"."pop"("seq");
            "arg" <- Var "head" * Var "N";
            call "list[W]"."push"("out", "arg");
            __;
            "test" <- "list[W]"."empty?"("seq");
        call "list[W]"."delete"("seq");
        __)%facade
     : Stm *)

Example micro_drop_larger_than_random :
  ParametricExtraction
    #vars      seq
    #program   ( threshold <- Random;
                 ret (fold_left (fun acc w => if Word.wlt_dec threshold w then
                                             acc
                                           else
                                             w :: acc)
                                seq nil) )
    #arguments [[`"seq" <-- seq as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_drop_larger_than_random).

(* Output:
     = ("random" <- "std"."rand"();
        "out" <- "list[W]"."nil"();
        "test" <- "list[W]"."empty?"("seq");
        While ("test" = 0)
            "head" <- "list[W]"."pop"("seq");
            "test0" <- Var "random" < Var "head";
            If Const (Word.natToWord 32 1) = Var "test0" Then
              __
            Else
              call "list[W]"."push"("out", "head")
            EndIf;
            "test" <- "list[W]"."empty?"("seq");
        call "list[W]"."delete"("seq");
        __)%facade
     : Stm *)
