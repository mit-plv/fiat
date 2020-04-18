Require Import Bedrock.Bedrock Bedrock.Platform.Xml Bedrock.Platform.XmlProg.

Module M.
  Definition buf_size := 1024%N.
  Definition outbuf_size := 2%N.
  Definition heapSize := (1024 * 1024 * 25)%N.

  Definition ts := {| Name := "params";
    Address := ((1024 * 1024 + 50 + 2) * 4)%N;
    Schema := "key" :: "value" :: nil
  |} :: nil.

  Definition pr := (
    Match
      "methodCall"/(
        "methodName"/"get"
        & "params"/(
          "param"/(
            "value"/(
              "string"/$"key"
            )
          )
        )
      )
    Do
      Write <*> "methodResponse" </>
        <*> "params" </>
          <*> "param" </>
            <*> "value" </>
              <*> "array" </>
                <*> "data" </>
                  <*> "value" </>
                    <*> "int" </>
                      "1"
                    </>
                  </>,
                  <*> "value" </>
                    <*> "string" </>
                      "Value is"
                    </>
                  </>,
                  <*> "value" </>
                    From "params" Where ("key" = $"key") Write
                      <*> "string" </>
                        "params"#"value"
                      </>
                  </>
                </>
              </>
            </>
          </>
        </>
      </>
    end;;
    Match
      "methodCall"/(
        "methodName"/"set"
        & "params"/(
          "param"/(
            "value"/(
              "string"/$"key"
            )
          );;
          "param"/(
            "value"/(
              "string"/$"value"
            )
          )
        )
      )
    Do
      Insert "params" ($"key", $"value");;
      Write <*> "methodResponse" </>
        <*> "params" </>
          <*> "param" </>
            <*> "value" </>
              <*> "array" </>
                <*> "data" </>
                  <*> "value" </>
                    <*> "int" </>
                      "1"
                    </>
                  </>,
                  <*> "value" </>
                    <*> "string" </>
                      "OK"
                    </>
                  </>,
                  <*> "value" </>
                    <*> "int" </>
                      "1"
                    </>
                  </>
                </>
              </>
            </>
          </>
        </>
      </>
    end;;
    Match
      "methodCall"/(
        "methodName"/"delete"
        & "params"/(
          "param"/(
            "value"/(
              "string"/$"key"
            )
          )
        )
      )
    Do
      Delete "params" Where ("key" = $"key");;
      Write <*> "methodResponse" </>
        <*> "params" </>
          <*> "param" </>
            <*> "value" </>
              <*> "array" </>
                <*> "data" </>
                  <*> "value" </>
                    <*> "int" </>
                      "1"
                    </>
                  </>,
                  <*> "value" </>
                    <*> "string" </>
                      "OK"
                    </>
                  </>,
                  <*> "value" </>
                    <*> "int" </>
                      "1"
                    </>
                  </>
                </>
              </>
            </>
          </>
        </>
      </>
    end
  )%program.

  Theorem Wf : wf ts pr buf_size outbuf_size.
    wf.
  Qed.

  Definition port : W := 8080%N.
  Definition numWorkers : W := 10.
End M.

Module E := Make(M).
