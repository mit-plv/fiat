Require Import Bedrock.Platform.tests.Ros Bedrock.Platform.XmlProg.

Module M.
  Definition buf_size := (15 * 1024)%N.
  Definition outbuf_size := (25 * 1024)%N.
  Definition heapSize := (1024 * 1024 * 200)%N.

  Definition dbaddr (n : nat) := ((heapSize + 50 + 2 + N.of_nat n) * 4)%N.

  Definition ts :=
    {| Name := "params";
      Address := dbaddr 0;
      Schema := "key" :: "value" :: nil
    |}
    :: {| Name := "paramSubscribers";
      Address := dbaddr 1;
      Schema := "key" :: "subscriber_api" :: nil |}

    :: {| Name := "nodes";
      Address := dbaddr 2;
      Schema := "caller_id" :: "caller_api" :: nil
    |}

    :: {| Name := "services";
      Address := dbaddr 3;
      Schema := "service" :: "node_id" :: "service_api" :: nil
    |}

    :: {| Name := "topics";
      Address := dbaddr 4;
      Schema := "topic" :: "topic_type" :: nil |}
    :: {| Name := "publishers";
      Address := dbaddr 5;
      Schema := "topic" :: "node_id" :: "publisher_api" :: nil |}
    :: {| Name := "subscribers";
      Address := dbaddr 6;
      Schema := "topic" :: "node_id" :: "subscriber_api" :: nil |}
    :: {| Name := "topicsWithPublishers";
      Address := dbaddr 7;
      Schema := "topic" :: "topic_type" :: nil |}
    :: {| Name := "topicsWithSubscribers";
      Address := dbaddr 8;
      Schema := "topic" :: "topic_type" :: nil |}

    :: nil.

  Definition registerNode := (
    Delete "nodes" Where ("caller_id" = $"caller_id");;
    Insert "nodes" ($"caller_id", $"caller_api")
  )%action.

  Definition pr := ROS (
    (** * Parameter server <http://www.ros.org/wiki/ROS/Parameter_Server_API> *)

    (* Remove a parameter setting. *)
    RosCommand "deleteParam"(!string $"caller_id", !string $"key")
    Do
      Delete "params" Where ("key" = $"key");;
      Response Success
        Message "Parameter deleted."
        Body ignore
      end
    end;;

    (* Set the value of a parameter. *)
    RosCommand "setParam"(!string $"caller_id", !string $"key", !any $$"value")
    Do
      Delete "params" Where ("key" = $"key");;
      Insert "params" ($"key", $"value");;

      From "paramSubscribers" Where ("key" = $"key") Do
        Callback "paramSubscribers"#"subscriber_api"
        Command "paramUpdate"(!string "/master", !string $"key", $"value");;

      Response Success
        Message "Parameter set."
        Body ignore
      end
    end;;

    (* Get the value of a parameter. *)
    RosCommand "getParam"(!string $"caller_id", !string $"key")
    Do
      IfHas "params" Where ("key" = $"key") then
        Response Success
          Message "Parameter value is:"
          Body
            From "params" Where ("key" = $"key") Write
              "params"#"value"
        end
      else
        Response UserError
          Message "Parameter not found."
          Body ignore
        end
      end
    end;;

    (* Search for a parameter name relative to the caller's namespace. *)
    Unimplemented "searchParam"(!string $"caller_id", !string $"key");;

    (* Sign up to receive notifications when a parameter value changes. *)
    RosCommand "subscribeParam"(!string $"caller_id", !string $"caller_api", !string $"key")
    Do
      registerNode;;
      Insert "paramSubscribers" ($"key", $"caller_api");;
      IfHas "params" Where ("key" = $"key") then
        Response Success
          Message "Parameter value is:"
          Body
            From "params" Where ("key" = $"key") Write
              "params"#"value"
        end
      else
        Response Success
          Message "Parameter not set yet."
          Body !unit
        end
      end
    end;;

    (* Cancel a subscription. *)
    RosCommand "unsubscribeParam"(!string $"caller_id", !string $"caller_api", !string $"key")
    Do
      IfHas "paramSubscribers" Where (("key" = $"key") && ("subscriber_api" = $"caller_api")) then
        Delete "paramSubscribers" Where (("key" = $"key") && ("subscriber_api" = $"caller_api"));;
        Response Success
          Message "You are now unsubscribed."
          Body !int "1"
        end
      else
        Response Success
          Message "You weren't subscribed to begin with."
          Body !int "0"
        end
      end
    end;;

    (* Check if a parameter has a value. *)
    RosCommand "hasParam"(!string $"caller_id", !string $"key")
    Do
      IfHas "params" Where ("key" = $"key") then
        Response Success
          Message "Parameter is set."
          Body !true
        end
      else
        Response Success
          Message "Parameter is not set."
          Body !false
        end
      end
    end;;

    (* List all parameters that are set. *)
    RosCommand "getParamNames"(!string $"caller_id")
    Do
      Response Success
        Message "Parameter names are:"
        Body
          ArrayFrom "params" Write
            !string "params"#"key"
      end
    end;;

    (** * Master <http://www.ros.org/wiki/ROS/Master_API> *)

    (** ** Register/unregister *)

    (* Announce willingness to provide a service. *)
    RosCommand "registerService"(!string $"caller_id", !string $"service",
      !string $"service_api", !string $"caller_api")
    Do
      IfHas "services" Where ("service" = $"service") then
        Response UserError
          Message "That service is already being provided."
          Body ignore
        end
      else
        registerNode;;
        Insert "services" ($"service", $"caller_id", $"service_api");;
        Response Success
          Message "Service registered."
          Body ignore
        end
      end
    end;;

    (* Rescind willingness to provide a service. *)
    RosCommand "unregisterService"(!string $"caller_id", !string $"service",
      !string $"service_api")
    Do
      IfHas "services" Where ("service" = $"service") then
        Delete "services" Where ("service" = $"service");;
        Response Success
          Message "Service unregistered."
          Body !int "1"
        end
      else
        Response Success
          Message "Service was not registered in the first place."
          Body !int "0"
        end
      end
    end;;

    (* Subscribe to a topic. *)
    RosCommand "registerSubscriber"(!string $"caller_id", !string $"topic",
      !string $"topic_type", !string $"caller_api")
    Do
      IfHas "topics" Where (("topic" = $"topic") && ("topic_type" = $"topic_type")) then
        IfHas "subscribers" Where (("topic" = $"topic") && ("subscriber_api" = $"caller_api")) then
          Response UserError
            Message "You are already subscribed to that topic."
            Body ignore
          end
        else
          registerNode;;
          Insert "subscribers" ($"topic", $"caller_id", $"caller_api");;
          IfHas "topicsWithSubscribers" Where ("topic" = $"topic") then
            Write ""
          else
            Insert "topicsWithSubscribers" ($"topic", $"topic_type")
          end;;
          Response Success
            Message "You are now subscribed.  Publishers are:"
            Body
              ArrayFrom "publishers" Where ("topic" = $"topic") Write
                !string "publishers"#"publisher_api"
          end
        end
      else
        IfHas "topics" Where ("topic" = $"topic") then
          Response UserError
            Message "That topic exists but with a different type."
            Body ignore
          end
        else
          registerNode;;
          Insert "topics" ($"topic", $"topic_type");;
          Insert "topicsWithSubscribers" ($"topic", $"topic_type");;
          Insert "subscribers" ($"topic", $"caller_id", $"caller_api");;
          Response Success
            Message "You are now subscribed.  Publishers are:"
            Body Array end
          end
        end
      end
    end;;

    (* Unsubscribe from a topic. *)
    RosCommand "unregisterSubscriber"(!string $"caller_id", !string $"topic",
      !string $"caller_api")
    Do
      IfHas "subscribers" Where (("topic" = $"topic") && ("subscriber_api" = $"caller_api")) then
        Delete "subscribers" Where (("topic" = $"topic") && ("subscriber_api" = $"caller_api"));;
        IfHas "subscribers" Where ("topic" = $"topic") then
          Write ""
        else
          Delete "topicsWithSubscribers" Where ("topic" = $"topic")
        end;;
        Response Success
          Message "You are now unsubscribed."
          Body !int "1"
        end
      else
        Response Success
          Message "You weren't subscribed to begin with."
          Body !int "0"
        end
      end
    end;;

    (* Register intent to publish on a topic. *)
    RosCommand "registerPublisher"(!string $"caller_id", !string $"topic",
      !string $"topic_type", !string $"caller_api")
    Do
      IfHas "topics" Where (("topic" = $"topic") && ("topic_type" = $"topic_type")) then
        IfHas "publishers" Where (("topic" = $"topic") && ("publisher_api" = $"caller_api")) then
          Response UserError
            Message "You are already publishing to that topic."
            Body ignore
          end
        else
          registerNode;;
          Insert "publishers" ($"topic", $"caller_id", $"caller_api");;
          IfHas "topicsWithPublishers" Where ("topic" = $"topic") then
            Write ""
          else
            Insert "topicsWithPublishers" ($"topic", $"topic_type")
          end;;

          From "subscribers" Where ("topic" = $"topic") Do
            Callback "subscribers"#"subscriber_api"
            Command "publisherUpdate"(!string "/master", !string $"topic",
              ArrayFrom "publishers" Where ("topic" = $"topic") Write
                !string "publishers"#"publisher_api");;

          Response Success
            Message "You are now publishing.  Subscribers are:"
            Body
              ArrayFrom "subscribers" Where ("topic" = $"topic") Write
                !string "subscribers"#"subscriber_api"
          end
        end
      else
        IfHas "topics" Where ("topic" = $"topic") then
          Response UserError
            Message "That topic exists but with a different type."
            Body ignore
          end
        else
          registerNode;;
          Insert "topics" ($"topic", $"topic_type");;
          Insert "topicsWithPublishers" ($"topic", $"topic_type");;
          Insert "publishers" ($"topic", $"caller_id", $"caller_api");;
          Response Success
            Message "You are now publishing.  Subscribers are:"
            Body Array end
          end
        end
      end
    end;;

    (* Unregister intent to publish on a topic. *)
    RosCommand "unregisterPublisher"(!string $"caller_id", !string $"topic",
      !string $"caller_api")
    Do
      IfHas "publishers" Where (("topic" = $"topic") && ("publisher_api" = $"caller_api")) then
        Delete "publishers" Where (("topic" = $"topic") && ("publisher_api" = $"caller_api"));;
        IfHas "publishers" Where ("topic" = $"topic") then
          Write ""
        else
          Delete "topicsWithPublishers" Where ("topic" = $"topic")
        end;;
        Response Success
          Message "You are now unregistered."
          Body !int "1"
        end
      else
        Response Success
          Message "You weren't publishing to begin with."
          Body !int "0"
        end
      end
    end;;


    (** ** Name service and system state *)

    (* Get the XML-RPC URI for a node name. *)
    RosCommand "lookupNode"(!string $"caller_id", !string $"node_name")
    Do
      IfHas "nodes" Where ("caller_id" = $"node_name") then
        Response Success
          Message "Node URI is:"
          Body
            From "nodes" Where ("caller_id" = $"node_name") Write
              !string "nodes"#"caller_api"
        end
      else
        Response UserError
          Message "Node not found."
          Body ignore
        end
      end
    end;;

    (* List published topics in a particular namespace. *)
    (* [Currently ignores the namespace.] *)
    RosCommand "getPublishedTopics"(!string $"caller_id", !string $"subgraph")
    Do
      Response Success
        Message "Topics with publishers are:"
        Body
          ArrayFrom "topicsWithPublishers" Write
            Array
              !string "topicsWithPublishers"#"topic",
              !string "topicsWithPublishers"#"topic_type"
            end
      end
    end;;

    (* List all known topic types. *)
    RosCommand "getTopicTypes"(!string $"caller_id")
    Do
      Response Success
        Message "Topics are:"
        Body
          ArrayFrom "topics" Write
            Array
              !string "topics"#"topic",
              !string "topics"#"topic_type"
            end
      end
    end;;

    (* Dump of all relevant service/topic state. *)
    RosCommand "getSystemState"(!string $"caller_id")
    Do
      Response Success
        Message "System state is:"
        Body
          Array
            ArrayFrom "topicsWithPublishers" Write
              Array
                !string "topicsWithPublishers"#"topic",
                ArrayFromOpt "publishers" Write
                  Join "publishers"#"topic" to "topicsWithPublishers"#"topic";;;
                  Value
                    !string "publishers"#"node_id"
                  end
              end,

            ArrayFrom "topicsWithSubscribers" Write
              Array
                !string "topicsWithSubscribers"#"topic",
                ArrayFromOpt "subscribers" Write
                  Join "subscribers"#"topic" to "topicsWithSubscribers"#"topic";;;
                  Value
                    !string "subscribers"#"node_id"
                  end
              end,

            ArrayFrom "services" Write
              Array
                !string "services"#"service",
                Array
                  !string "services"#"node_id"
                end
              end
          end
      end
    end;;

    (* Get the master's URI. *)
    RosCommand "getUri"(!string $"caller_id")
    Do
      Response Success
        Message "My URI is:"
        Body !string "http://localhost:11311"
      end
    end;;

    (* Find the node providing a service. *)
    RosCommand "lookupService"(!string $"caller_id", !string $"service")
    Do
      IfHas "services" Where ("service" = $"service") then
        Response Success
          Message "Service provider is:"
          Body
            From "services" Where ("service" = $"service") Write
              !string "services"#"service_api"
        end
      else
        Response UserError
          Message "No one is providing that service."
          Body ignore
        end
      end
    end;;


    (** ** Master methods not documented on the ROS wiki *)

    (* Return an arbitrary number (which is clearly not what the designers intended,
     * but which works fine, and which extends to systems without UNIX-style PIDs). *)
    RosCommand "getPid"(!string $"caller_id")
    Do
      Response Success
        Message "Here's a fake PID for you."
        Body !string "0"
      end
    end;;

    (* Terminate the server. *)
    RosCommand "shutdown"(!string $"caller_id", !string $"msg")
    Do
      Halt
    end
  ).

  Theorem Wf : wf ts pr buf_size outbuf_size.
  Admitted.
    (*wf.
  Qed.*)
  (* This proof script requires particularly much memory, so uncomment if you're willing to use about 16 GB of RAM. *)

  Definition port : W := 12345%N.
  Definition numWorkers : W := 10.
End M.

Module E := Make(M).
