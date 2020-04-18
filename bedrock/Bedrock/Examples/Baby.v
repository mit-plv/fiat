Require Import Bedrock.Examples.AutoSep.

(** * The simplest function *)

Definition diverger := bmodule "diverger" {{
  bfunction "diverger"() [SPEC reserving 0
    PRE[_] [| True |]
    POST[_] [| False |] ]
    Diverge
  end
}}.

(* Eval compute in compile diverger. *)

Theorem divergerOk : moduleOk diverger.
  vcgen; sep_auto.
Qed.

(* Print Assumptions divergerOk. *)


(** * A function with a private local variable *)

Definition seven := bmodule "seven" {{
  bfunction "seven"("x") [SPEC reserving 1
    PRE[_] [| True |]
    POST[R] [| R = $7 |] ]
    "x" <- 7;;
    Return "x"
  end
}}.

Theorem sevenOk : moduleOk seven.
  vcgen; sep_auto.
Qed.


(** * A function with both parameters and private local variables *)

Definition triple := bmodule "triple" {{
  bfunction "triple"("x", "y") [SPEC("x") reserving 1
    PRE[V] [| True |]
    POST[R] [| R = $3 ^* V "x" |] ]
    "y" <- "x" + "x";;
    "y" <- "y" + "x";;
    Return "y"
  end
}}.

Theorem tripleOk : moduleOk triple.
  vcgen; (sep_auto; words).
Qed.


(** * Immediate return *)

Definition immedS : spec := SPEC reserving 0
  PRE[_] [| True |]
  POST[_] [| True |].

Definition immed := bmodule "immed" {{
  bfunction "immed"() [immedS]
    Return 0
  end
}}.

(* Eval compute in compile immed. *)

Theorem immedOk : moduleOk immed.
  vcgen; sep_auto.
Qed.

(* Print Assumptions immedOk. *)

Definition immedTest := bimport [[ "immed"!"immed" @ [immedS] ]]
  bmodule "main" {{
    bfunction "main"() [SPEC reserving 1
      PRE[_] [| True |]
      POST[_] [| True |] ]
      Call "immed"!"immed"()
      [PRE[_] [| True |]
       POST[_] [| True|] ];;
      Return 0
    end
  }}.

(* Eval compute in compile immedTest. *)

Theorem immedTestOk : moduleOk immedTest.
  vcgen; (sep_auto; words).
Qed.

(* Print Assumptions immedTestOk. *)

Definition immedProg := link immed immedTest.

(* Eval compute in compile immedProg. *)

Theorem immedProgOk : moduleOk immedProg.
  link immedOk immedTestOk.
Qed.

(* Print Assumptions immedProgOk. *)

(** Let's also test with a version that reserves more stack space than needed. *)

Definition immedTestBig := bimport [[ "immed"!"immed" @ [immedS] ]]
  bmodule "main" {{
    bfunction "main"() [SPEC reserving 5
      PRE[_] [| True |]
      POST[_] [| True |] ]
      Call "immed"!"immed"()
      [PRE[_] [| True |]
       POST[_] [| True|] ];;
      Return 0
    end
  }}.

(* Eval compute in compile immedTest. *)

Theorem immedTestBigOk : moduleOk immedTestBig.
  vcgen; (sep_auto; words).
Qed.


(** * Incrementer *)

Definition incS : spec := SPEC("x") reserving 0
  PRE[V] [| True |]
  POST[R] [| R = V "x" ^+ $1 |].

Definition inc := bmodule "inc" {{
  bfunction "inc"("x") [incS]
    Return "x" + 1
  end
}}.

(* Eval compute in compile inc. *)

Theorem incOk : moduleOk inc.
  vcgen; sep_auto.
Qed.

Definition incTest := bimport [[ "inc"!"inc" @ [incS] ]]
  bmodule "main" {{
    bfunction "main"("y") [SPEC reserving 3
      PRE[_] [| True |]
      POST[R] [| R = $10 |] ]
      "y" <-- Call "inc"!"inc"(7)
      [PRE[_, R] Emp
       POST[R'] [| R' = R ^+ $2 |] ];;
      "y" <- "y" + 2;;
      Return "y"
    end
  }}.

Theorem incTestOk : moduleOk incTest.
  vcgen; (sep_auto; words).
Qed.


(** * Always-0, in a convoluted way *)

Definition always0S : spec := SPEC("x") reserving 0
  PRE[_] [| True |]
  POST[R] [| R = $0 |].

Definition always0 := bmodule "always0" {{
  bfunction "always0"("x") [always0S]
    If ("x" = 0) {
      Skip
    } else {
      "x" <- 0
    };;
    Return "x"
  end
}}.

(* Eval compute in compile always0. *)

Theorem always0Ok : moduleOk always0.
  vcgen; sep_auto.
Qed.
