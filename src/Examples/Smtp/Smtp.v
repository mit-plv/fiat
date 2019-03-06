Require Import Fiat.QueryStructure.Automation.AutoDB Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT.

Definition UUID := nat.
Definition Data := String.

Inductive State : Set :=
| S_Helo
| S_Mail
| S_Rcpt
| S_Data
| S_Inactive.

Record Reply :=
  { status:    string;
    message:   string }.

Definition sCONNECTIONS := "Connections".
Definition sID := "_id".
Definition sSTATE := "State".
Definition sDOMAIN := "Domain".
Definition sMAILFROM := "MailFrom".
Definition sRCPTTO := "RcptTo".
Definition sBODY := "Body".

Definition ConnectionSchema :=
  Query Structure Schema
        [ relation sCONNECTIONS has
                   schema <sID :: UUID,
                           sSTATE :: State,
                           sDOMAIN :: string,
                           sMAILFROM :: string,
                           sRCPTTO :: list string,
                           sBODY :: string> ]
        enforcing [].
(* some of the RIs
state = S_Helo <-> domain = nil
state = S_Helo \/ state = S_Mail -> mail_from = rcpt_to = body = nil
state = S_Rcpt -> mail_from != nil /\ rcpt_to = body = nil
state = S_Morercpt -> mail_from != nil /\ rcpt_to != nil /\ body = nil
state = S_Data -> mail_from != nil /\ rcpt_to != nil *)

Definition Connection := TupleDef ConnectionSchema sCONNECTIONS.

Definition SmtpSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      Method "GetState" : rep x UUID -> rep x option State,
      Method "GetConnection" : rep x UUID -> rep x option Connection,
      Method "AddConnection" : rep x Connection -> rep x bool,
      Method "KillConnection" : rep x UUID -> rep x bool,
      Method "Helo" : rep x (UUID * string) -> rep x Reply,
      Method "Mail" : rep x (UUID * string) -> rep x Reply,
      Method "Rcpt" : rep x (UUID * string) -> rep x Reply,
      Method "Data" : rep x (UUID) -> rep x Reply,
      Method "MoreData" : rep x (UUID * string) -> rep x Reply,
      Method "Rset" : rep x (UUID) -> rep x bool,
      Method "Quit" : rep x (UUID) -> rep x bool
    }.

Definition standardReply (success: bool) : Reply :=
  if success
  then {| status := "250"; message := "Requested mail action okay, completed" |}
  else {| status := "503"; message := "Bad sequence of commands" |}.
Definition nonEmpty {A: Type} (l: list A) := negb (beq_nat (length l) 0).
Definition standardReplyExists {A: Type} (l: list A) := standardReply (nonEmpty l).

Locate "_ ++ _".

Definition SmtpSpec : ADT SmtpSig :=
  Def ADT {
    rep := QueryStructure ConnectionSchema,
    Def Constructor "Init" (_: unit) : rep := empty,,

    query "GetState" (r : rep, id: UUID) : option State :=
      q <- (For (c in r!sCONNECTIONS)
                Where (id = c!sID)
                Return (c!sSTATE));
      ret (hd_error q),

    query "GetConnection" (r : rep, id: UUID) : option Connection :=
      q <- (For (c in r! sCONNECTIONS)
                For (c in r! sCONNECTIONS)
                Where (id = c!sID)
                Return (c));
      ret (hd_error q),

    update "AddConnection" (r : rep, conn: Connection) : bool :=
      Insert conn into r!sCONNECTIONS,

    update "KillConnection" (r : rep, id: UUID) : bool :=
      q <- Delete c from r!sCONNECTIONS where c!sID = id;
      let (updated, deleted) := q in
      ret (updated, nonEmpty deleted),

    update "Helo" (r : rep, arg: UUID * string) : Reply :=
      let (id, domain) := arg in
      q <- Update c from r!sCONNECTIONS as d
        making (d!sSTATE = S_Mail /\ d!sDOMAIN = domain)
        where (c!sID = id /\ c!sSTATE = S_Helo);
      let (updated, affected) := q in
      ret (updated, standardReplyExists(affected)),

    update "Mail" (r : rep, arg: UUID * string) : Reply :=
      let (id, mailfrom) := arg in
      q <- Update c from r!sCONNECTIONS as c'
        making c!sSTATE = S_Rcpt /\ c!sMAILFROM = mailfrom
        where (c!sID = id /\ c!sSTATE = S_Mail);
      let (updated, affected) := q in
      ret (updated, standardReplyExists(affected)),

    update "Rcpt" (r : rep, arg: UUID * string) : Reply :=
      let (id, rcptto) := arg in
      q <- Update c from r!sCONNECTIONS as c'
        making c'!sRCPTTO = rcptto :: c!sRCPTTO
      where (c!sID = id /\ c!sSTATE = S_Rcpt);
      let (updated, affected) := q in
      ret (updated, standardReplyExists(affected)),

    update "Data" (r : rep, id: UUID) : Reply :=
      q <- Update c from r!sCONNECTIONS as c'
        making c'!sSTATE = S_Data
      where (c!sID = id
             /\ c!sSTATE = S_Rcpt
             /\ nonEmpty(c!sRCPTTO) = true);
      let (updated, affected) := q in
      ret (updated, standardReplyExists(affected)),

    update "MoreData" (r : rep, arg: UUID * string) : Reply :=
      let (id, data) := arg in
      q <- Update c from r!sCONNECTIONS as c'
        making c'!sBODY = append data c!sBODY
        where (c!sID = id /\ c!sSTATE = S_Data);
      let (updated, affected) := q in
      ret (updated, standardReplyExists(affected)),

    update "Rset" (r : rep, id: UUID) : bool :=
      q <- Update c from r!sCONNECTIONS as c'
             making c'!sSTATE = S_Mail
             /\ c'!sMAILFROM = ""
             /\ c'!sRCPTTO = @nil string
             /\ c'!sBODY = ""
        where (c!sID = id /\ c!sSTATE <> S_Helo /\ c!sSTATE <> S_Inactive);
      let (updated, affected) := q in
      ret (updated, nonEmpty(affected)),

    update "Quit" (r : rep, id: UUID) : bool :=
      q <- Update c from r!sCONNECTIONS as c'
        making (c'!sSTATE = S_Inactive /\ c'!sMAILFROM = "" /\ c'!sRCPTTO = @nil string /\ c'!sBODY = "")
        where (c!sID = id);
      let (updated, affected) := q in
      ret (updated, nonEmpty(affected))
}.
