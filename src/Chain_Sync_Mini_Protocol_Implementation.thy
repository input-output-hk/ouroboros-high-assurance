(*
 TODO:

  \<^item> Reuse domain theories (e.g., blocks, chains)

 *)

theory Chain_Sync_Mini_Protocol_Implementation
  imports "Thorn_Calculus.Thorn_Calculus-Processes"
begin

text \<open> Crypto \<close>

typedecl hash

axiomatization
where
  hash_countability: "OFCLASS(hash, countable_class)"

instance hash :: countable
  by (fact hash_countability)

text \<open> Timing \<close>

type_synonym slot = nat

text \<open> Blocks \<close>

datatype block =
    GenesisBlock
  | HeaderBlock "slot \<times> hash option"

instance block :: countable
  by countable_datatype

text \<open> Chains \<close>

type_synonym chain = "block list"

type_synonym chain_index = nat

abbreviation (input)
  tip_index :: "chain \<Rightarrow> chain_index"
where
  "tip_index \<C> \<equiv> length \<C> - 1"

abbreviation (input)
  tip :: "chain \<Rightarrow> block"
where
  "tip \<C> \<equiv> \<C> ! (tip_index \<C>)"

abbreviation (input)
  genesis_index :: "chain_index"
where
  "genesis_index \<equiv> 0"

text \<open> State machines \<close>

(* TODO: Perhaps add a new state StAborted for when the protocol is aborted. *)
datatype state =
    StIdle
  | StCanAwait
  | StMustReply
  | StDone

datatype message =
    MsgDone
  | MsgRequestNext
  | MsgRollForward block block (* TODO: Find out what the tip is sent for. *)
  | MsgAwaitReply

instance message :: countable
  by countable_datatype

text \<open> Producer \<close>

type_synonym
  producer_parameters
    = "state \<comment> \<open>current state\<close>
    \<times> chain \<comment> \<open>current chain\<close>
    \<times> chain_index \<comment> \<open>read pointer\<close>"

definition
  producer
    :: "message channel family
    \<Rightarrow>  producer_parameters channel family
    \<Rightarrow>  process family"
where
  "producer c pc =
    pc \<triangleright>\<^sup>\<infinity> (st, \<C>, read_ptr). (
      case st of
        StDone \<Rightarrow>
          \<zero> \<comment> \<open>NOTE: Actually the process does not stop here but no longer responds\<close>
      | StMustReply \<Rightarrow>
          \<zero> \<comment> \<open>NOTE: Here the producer waits for updates\<close>
      | _ \<Rightarrow>
          c \<triangleright> msg. (
            case (st, msg) of
              (StIdle, MsgDone) \<Rightarrow>
                pc \<triangleleft> (StDone, \<C>, read_ptr)
            | (StIdle, MsgRequestNext) \<Rightarrow>
                if read_ptr \<le> tip_index \<C>
                  then
                    c \<triangleleft> MsgRollForward (\<C> ! read_ptr) (tip \<C>)
                    \<parallel>
                    pc \<triangleleft> (StCanAwait, \<C>, Suc read_ptr)
                  else
                    c \<triangleleft> MsgAwaitReply
                    \<parallel>
                    pc \<triangleleft> (StMustReply, \<C>, read_ptr)
            | (_, _) \<Rightarrow>
                \<zero> \<comment> \<open>Unexpected message, protocol is aborted\<close>
          )
    )"

text \<open> Consumer \<close>

type_synonym
  consumer_parameters
    = "state \<comment> \<open>current state\<close>
    \<times> chain \<comment> \<open>current chain\<close>"

(* FIXME: It doesn't seem to be clear when the consumer should send the MsgDone message. *)
definition
  consumer
    :: "message channel family
    \<Rightarrow>  consumer_parameters channel family
    \<Rightarrow>  process family"
where
  "consumer c cc =
    cc \<triangleright>\<^sup>\<infinity> (st, \<C>). (
      case st of
        StIdle \<Rightarrow>
          c \<triangleleft> MsgRequestNext
          \<parallel>
          cc \<triangleleft> (StCanAwait, \<C>)
      | StCanAwait \<Rightarrow>
          c \<triangleright> msg. (
            case msg of
              MsgRollForward header pTip \<Rightarrow>
                cc \<triangleleft> (StIdle, \<C> @ [header])
            | MsgAwaitReply \<Rightarrow>
                cc \<triangleleft> (StMustReply, \<C>)
            | _ \<Rightarrow>
                \<zero> \<comment> \<open>Unexpected message, protocol is aborted\<close>
          )
      | StMustReply \<Rightarrow>
          \<zero> \<comment> \<open>NOTE: Here the consumer waits for updates from the producer\<close>
    )"

definition
  protocol
    :: "message channel family
    \<Rightarrow>  chain \<comment> \<open>producer's current chain\<close>
    \<Rightarrow>  process family"
where
  "protocol c \<C>\<^sub>p =
    \<nu> pc cc. (
      producer c pc \<parallel> pc \<triangleleft> (StIdle, \<C>\<^sub>p, Suc genesis_index)
      \<parallel>
      consumer c cc \<parallel> cc \<triangleleft> (StIdle, [GenesisBlock])
    )"

end
