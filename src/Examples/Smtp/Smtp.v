Require Import AutoDB BagADT.

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

Definition SmtpSpec : ADT SmtpSig :=
  QueryADTRep ConnectionSchema {
    Def Constructor "Init" (_: unit) : rep := empty,

    query "GetState" (id: UUID) : option State :=
      q <- (For (c in sCONNECTIONS)
                Where (id = c!sID)
                Return (c!sSTATE));
      ret (hd_error q),

    query "GetConnection" (id: UUID) : option Connection :=
      q <- (For (c in sCONNECTIONS)
                For (c in sCONNECTIONS)
                Where (id = c!sID)
                Return (c));
      ret (hd_error q),

    update "AddConnection" (conn: Connection) : bool :=
      Insert conn into sCONNECTIONS,

    update "KillConnection" (id: UUID) : bool :=
      q <- Delete c from sCONNECTIONS where c!sID = id;
      let (updated, deleted) := q in
      ret (updated, nonEmpty deleted),

    update "Helo" (arg: UUID * string) : Reply :=
      let (id, domain) := arg in
      q <- Update c from sCONNECTIONS
        making [ sSTATE |= S_Mail; sDOMAIN |= domain ]
        where (c!sID = id /\ c!sSTATE = S_Helo);
      let (updated, affected) := q in
      ret (updated, standardReplyExists(affected)),

    update "Mail" (arg: UUID * string) : Reply :=
      let (id, mailfrom) := arg in
      q <- Update c from sCONNECTIONS
        making [ sSTATE |= S_Rcpt; sMAILFROM |= mailfrom ]
        where (c!sID = id /\ c!sSTATE = S_Mail);
      let (updated, affected) := q in
      ret (updated, standardReplyExists(affected)),

    update "Rcpt" (arg: UUID * string) : Reply :=
      let (id, rcptto) := arg in
      q <-
Update c from sCONNECTIONS
        making sRCPTTO :+= rcptto
        where (c!sID = id /\ c!sSTATE = S_Rcpt);
      let (updated, affected) := q in
      ret (updated, standardReplyExists(affected)),

    update "Data" (id: UUID) : Reply :=
      q <- Update c from sCONNECTIONS
        making sSTATE |= S_Data
        where (c!sID = id /\ c!sSTATE = S_Rcpt /\ nonEmpty(c!sRCPTTO) = true);
      let (updated, affected) := q in
      ret (updated, standardReplyExists(affected)),

    update "MoreData" (arg: UUID * string) : Reply :=
      let (id, data) := arg in
      q <- Update c from sCONNECTIONS
        making sBODY ++= data
        where (c!sID = id /\ c!sSTATE = S_Data);
      let (updated, affected) := q in
      ret (updated, standardReplyExists(affected)),

    update "Rset" (id: UUID) : bool :=
      q <- Update c from sCONNECTIONS
        making [ sSTATE |= S_Mail; sMAILFROM |= ""; sRCPTTO |= @nil string; sBODY |= "" ]
        where (c!sID = id /\ c!sSTATE <> S_Helo /\ c!sSTATE <> S_Inactive);
      let (updated, affected) := q in
      ret (updated, nonEmpty(affected)),

    update "Quit" (id: UUID) : bool :=
      q <- Update c from sCONNECTIONS
        making [ sSTATE |= S_Inactive; sMAILFROM |= ""; sRCPTTO |= @nil string; sBODY |= "" ]
        where c!sID = id;
      let (updated, affected) := q in
      ret (updated, nonEmpty(affected))
}.
