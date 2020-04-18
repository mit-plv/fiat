Require Import Bedrock.Bedrock Bedrock.Platform.Xml.
Export Bedrock Xml.


(** * Requests *)

Definition ptype (name : string) (p : pat) : pat := (
  "value"/(name/p)
)%pat.

Definition pint := ptype "int".
Definition pi4 := ptype "i4".
Definition pboolean := ptype "boolean".
Definition pstring := ptype "string".

Notation "!int x" := (pint x%pat) (at level 0, x at level 0) : pat_scope.
Notation "!i4 x" := (pi4 x%pat) (at level 0, x at level 0) : pat_scope.
Notation "!boolean x" := (pboolean x%pat) (at level 0, x at level 0) : pat_scope.
Notation "!string x" := ("value"/x%pat)%pat (at level 0, x at level 0) : pat_scope.
Notation "!any x" := ("value"/x%pat)%pat (at level 0, x at level 0) : pat_scope.

Fixpoint params' (ps : list pat) : pat :=
  match ps with
    | nil => ""
    | p :: nil => "param"/p
    | p :: ps' => ("param"/p);;params' ps'
  end%pat.

Definition params (ps : list pat) : pat := (
  "params"/(params' ps)
)%pat.

Definition request (methodName : string) (ps : list pat) : pat := (
  "methodCall"/(
    "methodName"/methodName
    & params ps
  )
)%pat.


(** * Responses *)

Inductive outcome := Success | UserError | ServerError.

Definition outcomeToXml (o : outcome) : xml :=
  match o with
    | Success => "1"
    | UserError => "-1"
    | ServerError => "0"
  end.

Coercion outcomeToXml : outcome >-> xml.

Definition response (o : outcome) (msg body : xml) : action := (
  Write <*> "methodResponse" </>
    <*> "params" </>
      <*> "param" </>
        <*> "value" </>
          <*> "array" </>
            <*> "data" </>
              <*> "value" </>
                <*> "int" </>
                  o
                </>
              </>,
              <*> "value" </>
                <*> "string" </>
                  msg
                </>
              </>,
              <*> "value" </>
                body
              </>
            </>
          </>
        </>
      </>
    </>
  </>
)%action.

Notation "'Response' o 'Message' msg 'Body' body 'end'" :=
  (response o msg%out body%out)
  (at level 0, o at level 0, msg at level 0, body at level 0) : action_scope.

Definition rarray (body : xml) : xml := (
  <*> "array" </>
    <*> "data" </>
      body
    </>
  </>
)%out.

Definition rarrayL (body : list xml) : xml := (
  <*> "array" </>
    XTag "data" (map (fun xm => XTag "value" (xm :: nil)) body)
  </>
)%out.

Definition rarrayStar (body : list xml) : xml := (
  <*> "array" </>
    XTag "data" body
  </>
)%out.

Definition afrom tab cond body := (
  rarray From tab Where cond Write (<*> "value" </> body </>)
)%out.

Definition afrom' tab cond body := (
  rarray From tab Where cond Write body
)%out.

Notation "'Array' x1 , .. , xN 'end'" :=
  (rarrayL (cons x1%out .. (cons xN%out nil) ..))
  (at level 0) : out_scope.

Notation "'Array' 'end'" :=
  (rarrayL nil)
  (at level 0) : out_scope.

Notation "Array* x1 , .. , xN 'end'" :=
  (rarrayStar (cons x1%out .. (cons xN%out nil) ..))
  (at level 0) : out_scope.

Notation "'Value' body 'end'" :=
  (<*> "value" </> body </>)%out
  (at level 0) : out_scope.

Definition rtype (name : string) (body : xml) := (
  <*> name </>
    body
  </>
)%out.

Definition rint := rtype "int".
Definition rboolean := rtype "boolean".
Definition rstring := rtype "string".

Notation "!int x" := (rint x%out) (at level 0, x at level 0) : out_scope.
Notation "!boolean x" := (rboolean x%out) (at level 0, x at level 0) : out_scope.
Notation "!string x" := (rstring x%out) (at level 0, x at level 0) : out_scope.

Definition rtrue := rboolean "1".
Definition rfalse := rboolean "0".

Notation "!true" := rtrue : out_scope.
Notation "!false" := rfalse : out_scope.

Definition runit := XTag "struct" nil.

Notation "!unit" := runit : out_scope.

Notation "'ArrayFrom' tab 'Where' cond 'Write' o" :=
  (afrom tab cond%condition o%out)
  (at level 0, tab at level 0, cond at level 0, o at level 0) : out_scope.

Notation "'ArrayFrom' tab 'Write' o" :=
  (afrom tab nil o%out)
  (at level 0, tab at level 0, o at level 0) : out_scope.

Notation "'ArrayFromOpt' tab 'Where' cond 'Write' o" :=
  (afrom' tab cond%condition o%out)
  (at level 0, tab at level 0, cond at level 0, o at level 0) : out_scope.

Notation "'ArrayFromOpt' tab 'Write' o" :=
  (afrom' tab nil o%out)
  (at level 0, tab at level 0, o at level 0) : out_scope.

Definition ignore := ""%out.


(** * Actions *)

Definition commandRequest (methodName : xml) (ps : list xml) : xml :=
  <*> "methodCall" </>
    <*> "methodName" </>
      methodName
    </>,
    XTag "params"
      (map (fun p => <*> "param" </> <*> "value" </> p </> </>) ps)
  </>%out.

Notation "'Callback' url 'Command' cmd ( p1 , .. , pN )" :=
  (SendTo url%out (commandRequest cmd%out (cons p1%out .. (cons pN%out nil) ..)))
  (at level 0, url at level 0, cmd at level 0) : action_scope.


(** * Combined notation *)

Notation "'RosCommand' cmd () 'Do' a 'end'" :=
  (Rule (request cmd nil) a%action)
  (at level 0, cmd at level 0) : program_scope.

Notation "'RosCommand' cmd ( p1 , .. , pN ) 'Do' a 'end'" :=
  (Rule (request cmd (cons p1%pat .. (cons pN%pat nil) ..)) a%action)
  (at level 0, cmd at level 0) : program_scope.

Notation "'Unimplemented' cmd ( p1 , .. , pN )" := (
  Rule (request cmd (cons p1%pat .. (cons pN%pat nil) ..))
  Response UserError
    Message "Command not implemented yet."
    Body ignore
  end%action
)%program
(at level 0, cmd at level 0) : program_scope.



(** * Instrumenting programs to support XML-RPC multicall *)

Fixpoint makeMulticallParams (p : pat) : pat :=
  match p with
    | Tag "param" p' => p'
    | Ordered p1 p2 => Ordered (makeMulticallParams p1) (makeMulticallParams p2)
    | _ => p
  end.

Fixpoint makeMulticallAction (a : action) : action :=
  match a with
    | Seq a1 a2 =>
      Seq (makeMulticallAction a1) (makeMulticallAction a2)

    | IfExists tab cond _then _else =>
      IfExists tab cond (makeMulticallAction _then) (makeMulticallAction _else)

    | Output (XTag "methodResponse"
        (XTag "params"
          (XTag "param"
            (xm :: nil) :: nil) :: nil)) =>
      Output (XTag "value"
        (XTag "array"
          (XTag "data"
            (xm :: nil) :: nil) :: nil))

    | _ => a
  end.

Fixpoint makeMulticall (pr : program) : program :=
  match pr with
    | PSeq pr1 pr2 => PSeq (makeMulticall pr1) (makeMulticall pr2)
    | Rule ("methodCall"/(
              "methodName"/methodName
            & "params"/ps))%pat a =>
      Match
        "methodCall"/(
          "methodName"/"system.multicall"
          & "params"/(
            "param"/(
              "value"/(
                "array"/(
                  "data"/(
                    "value"/(
                      "struct"/(
                        "member"/(
                          "name"/"params"
                          & "value"/(
                            "array"/(
                              "data"/(
                                makeMulticallParams ps
                              )
                            )
                          )
                        )
                        & "member"/(
                          "name"/"methodName"
                          & "value"/(
                              "string"/methodName
                            )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      Do
        makeMulticallAction a
      end
    | Rule p _ => Rule p (Write "")%action
  end%program.

Definition addMulticall (pr : program) : program := (
  Match
    "methodCall"/(
      "methodName"/"system.multicall"
    )
  Do
    Write "<methodResponse><params><param><value><array><data>"
  end;;
  pr;;
  makeMulticall pr;;
  Match
    "methodCall"/(
      "methodName"/"system.multicall"
    )
  Do
    Write "</data></array></value></param></params></methodResponse>"
  end
)%program.

Notation "'ROS' pr" := (addMulticall pr%program)
  (at level 0, pr at level 0).

Notation "'SimpleROS' pr" := pr%program
  (at level 0, pr at level 0).
