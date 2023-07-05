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

type_synonym slot = int

abbreviation
  genesis_slot :: slot
where
  "genesis_slot \<equiv> -1"

text \<open> Blocks \<close>

datatype block =
    GenesisBlock
  | HeaderBlock \<open>slot\<close> \<open>hash option\<close>

instance block :: countable
  by countable_datatype

primrec
  block_slot :: "block \<Rightarrow> slot"
where
  "block_slot GenesisBlock = genesis_slot"
| "block_slot (HeaderBlock slot _) = slot"

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

text \<open> Points \<close>

type_synonym point = slot (* FIXME: Add hash *)

text \<open> State machines \<close>

(* TODO: Perhaps add a new state StAborted for when the protocol is aborted. *)
datatype state =
    StIdle
  | StIntersect
  | StCanAwait
  | StMustReply
  | StDone

datatype message =
    MsgDone
  | MsgRequestNext
  | MsgRollForward \<open>block\<close> \<open>block\<close> (* TODO: Find out what the tip is sent for. *)
  | MsgRollBackward \<open>point\<close> \<open>block\<close> (* TODO: Find out what the tip is sent for. *)
  | MsgAwaitReply
  | MsgFindIntersect \<open>point list\<close>
  | MsgIntersectFound \<open>point\<close> \<open>block\<close> (* TODO: Find out what the tip is sent for. *)
  | MsgIntersectNotFound \<open>block\<close> (* TODO: Find out what the tip is sent for. *)

instance message :: countable
  by countable_datatype

text \<open> Producer \<close>

type_synonym
  producer_parameters
    = "state \<comment> \<open>current state\<close>
    \<times> chain \<comment> \<open>current chain\<close>
    \<times> chain_index \<comment> \<open>read pointer\<close>
    \<times> bool \<comment> \<open>whether the next response to @{const MsgRequestNext} should be @{const MsgRollBackward}\<close>"

definition
  best_intersection_point :: "chain \<Rightarrow> point list \<Rightarrow> point option"
where
  [simp]: "best_intersection_point \<C> points = (
    let
      intersection_points = List.set points \<inter> List.set (map block_slot \<C>)
    in
      if intersection_points = {} then None else Some (Max intersection_points))"

(* NOTE: Assumes that \<exists>index \<in> {0..<length \<C>}. block_slot (\<C> ! index) = slot *)
definition
  index_from_slot :: "slot \<Rightarrow> chain \<Rightarrow> chain_index"
where
  [simp]: "index_from_slot slot \<C> = hd [index. (block, index) \<leftarrow> zip \<C> [0..<length \<C>], block_slot block = slot]"

definition
  producer
    :: "message channel family
    \<Rightarrow>  message channel family
    \<Rightarrow>  producer_parameters channel family
    \<Rightarrow>  process family"
where
  "producer CP PC I =
    I \<triangleright>\<^sup>\<infinity> (st, \<C>, read_ptr, must_rollback). (
      case st of
        StDone \<Rightarrow>
          \<zero> \<comment> \<open>NOTE: Actually the process does not stop here but no longer responds\<close>
      | StMustReply \<Rightarrow>
          \<zero> \<comment> \<open>NOTE: Here the producer waits for updates\<close>
      | _ \<Rightarrow>
          CP \<triangleright> msg. (
            case (st, msg) of
              (StIdle, MsgDone) \<Rightarrow>
                I \<triangleleft> (StDone, \<C>, read_ptr, must_rollback)
            | (StIdle, MsgFindIntersect points) \<Rightarrow> (
                \<comment> \<open>NOTE: StIntersect is only transient, so not used\<close>
                case best_intersection_point \<C> points of
                  None \<Rightarrow>
                    PC \<triangleleft> MsgIntersectNotFound (tip \<C>)
                    \<parallel>
                    I \<triangleleft> (StIdle, \<C>, read_ptr, must_rollback)
                | Some point_intersect \<Rightarrow>
                    PC \<triangleleft> MsgIntersectFound point_intersect (tip \<C>)
                    \<parallel>
                    I \<triangleleft> (StIdle, \<C>, index_from_slot point_intersect \<C>, True))
            | (StIdle, MsgRequestNext) \<Rightarrow>
                if must_rollback
                  then
                    PC \<triangleleft> MsgRollBackward (block_slot (\<C> ! read_ptr)) (tip \<C>)
                    \<parallel>
                    I \<triangleleft> (StIdle, \<C>, read_ptr + 1, False)
                  else
                    if read_ptr \<le> tip_index \<C>
                      then
                        PC \<triangleleft> MsgRollForward (\<C> ! read_ptr) (tip \<C>)
                        \<parallel>
                        I \<triangleleft> (StCanAwait, \<C>, Suc read_ptr, must_rollback)
                      else
                        PC \<triangleleft> MsgAwaitReply
                        \<parallel>
                        I \<triangleleft> (StMustReply, \<C>, read_ptr, must_rollback)
            | (_, _) \<Rightarrow>
                \<zero> \<comment> \<open>Unexpected message, protocol is aborted\<close>
          )
    )"

text \<open> Consumer \<close>

type_synonym
  consumer_parameters
    = "state \<comment> \<open>current state\<close>
    \<times> chain \<comment> \<open>current chain\<close>"

(* FIXME: Implement *)
consts candidate_points :: "chain \<Rightarrow> point list"

definition
  rollback_to :: "chain \<Rightarrow> point \<Rightarrow> chain"
where
  [simp]: "rollback_to \<C> point = takeWhile (\<lambda>block. block_slot block \<le> point) \<C>"

(* FIXME: It doesn't seem to be clear when the consumer should send the MsgDone message. *)
definition
  consumer
    :: "message channel family
    \<Rightarrow>  message channel family
    \<Rightarrow>  consumer_parameters channel family
    \<Rightarrow>  chain option
    \<Rightarrow>  process family"
where
  "consumer CP PC I o\<C> =
    (
    case o\<C> of
      None \<Rightarrow> \<comment> \<open>No local chain, start from genesis block\<close>
        I \<triangleleft> (StIdle, [GenesisBlock])
    | Some \<C> \<Rightarrow> \<comment> \<open>Local chain, find intersection point\<close>
        \<comment> \<open>NOTE: StIntersect is only transient, so not used\<close>
        CP \<triangleleft> MsgFindIntersect (candidate_points \<C>)
        \<parallel>
        (
        PC \<triangleright> msg. (
          case msg of
            MsgIntersectNotFound tip_point \<Rightarrow>
              \<zero> \<comment> \<open>FIXME: Abort? Not clear from document\<close>
          | MsgIntersectFound _ _ \<Rightarrow>
              \<comment> \<open>TODO: According to the document, the consumer can expect the next update to be
                  MsgRollBackward, so no need to handle the response here. Confirm.\<close>
              I \<triangleleft> (StIdle, \<C>)
          )
        )
    )
    \<parallel>
    I \<triangleright>\<^sup>\<infinity> (st, \<C>). (
      case st of
        StIdle \<Rightarrow>
          CP \<triangleleft> MsgRequestNext
          \<parallel>
          I \<triangleleft> (StCanAwait, \<C>)
      | StCanAwait \<Rightarrow>
          PC \<triangleright> msg. (
            case msg of
              MsgRollForward header tip_point \<Rightarrow>
                I \<triangleleft> (StIdle, \<C> @ [header])
            | MsgRollBackward rollback_point tip_point \<Rightarrow>
                I \<triangleleft> (StIdle, rollback_to \<C> rollback_point)
            | MsgAwaitReply \<Rightarrow>
                I \<triangleleft> (StMustReply, \<C>)
            | _ \<Rightarrow>
                \<zero> \<comment> \<open>Unexpected message, protocol is aborted\<close>
          )
      | StMustReply \<Rightarrow>
          \<zero> \<comment> \<open>NOTE: Here the consumer waits for updates from the producer\<close>
    )"

definition
  protocol
    :: "message channel family
    \<Rightarrow>  message channel family
    \<Rightarrow>  chain \<comment> \<open>producer's current chain\<close>
    \<Rightarrow>  chain option \<comment> \<open>consumer's current chain\<close>
    \<Rightarrow>  process family"
where
  "protocol CP PC \<C>\<^sub>p o\<C>\<^sub>c =
    \<nu> IC IP. (
      producer CP PC IP \<parallel> IP \<triangleleft> (StIdle, \<C>\<^sub>p, Suc genesis_index, False)
      \<parallel>
      consumer CP PC IC o\<C>\<^sub>c
    )"

end
