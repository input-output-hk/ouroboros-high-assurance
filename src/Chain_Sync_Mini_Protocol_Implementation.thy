(*
 TODO:

  \<^item> Reuse domain theories (e.g., blocks, chains)

 *)

theory Chain_Sync_Mini_Protocol_Implementation
  imports
    "Thorn_Calculus.Thorn_Calculus-Processes"
    "HOL-Library.Sublist"
begin

no_notation Sublist.parallel (infixl "\<parallel>" 50)

text \<open> Crypto \<close>

typedecl hash

axiomatization
where
  hash_countability: "OFCLASS(hash, countable_class)"
and
  hash_linear_order: "OFCLASS(hash, linorder_class)"

instance hash :: countable
  by (fact hash_countability)

instance hash :: linorder
  by (fact hash_linear_order)

text \<open> Blocks \<close>

datatype block = Block (hash: \<open>hash\<close>)

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

text \<open> Points \<close>

type_synonym point = hash

definition
  block_point :: "block \<Rightarrow> point"
where
  [simp]: "block_point \<equiv> hash"

text \<open> State machines \<close>

datatype state =
    StIdle
  | StIntersect
  | StCanAwait
  | StMustReply
  | StDone

(* TODO: Find out what the tip is sent for. *)
datatype message =
    MsgDone
  | MsgRequestNext
  | MsgRollForward \<open>block\<close> \<open>block\<close>
  | MsgRollBackward \<open>point\<close> \<open>block\<close>
  | MsgAwaitReply
  | MsgFindIntersect \<open>point list\<close>
  | MsgIntersectFound \<open>point\<close> \<open>block\<close>
  | MsgIntersectNotFound \<open>block\<close>

instance message :: countable
  by countable_datatype

type_synonym update = "chain option"

text \<open> Producer \<close>

type_synonym
  producer_parameters
    = "state \<comment> \<open>current state\<close>
    \<times> chain \<comment> \<open>current chain\<close>
    \<times> chain_index \<comment> \<open>read pointer\<close>
    \<times> bool \<comment> \<open>whether the next response to @{const MsgRequestNext} should be @{const MsgRollBackward}\<close>
    \<times> point list option \<comment> \<open>points sent by consumer in @{const MsgFindIntersect}\<close>"

definition
  best_intersection_point :: "chain \<Rightarrow> point list \<Rightarrow> point option"
where
  [simp]: "best_intersection_point \<C> points = (
    let
      intersection_points = List.set points \<inter> List.set (map hash \<C>)
    in
      if intersection_points = {} then None else Some (Max intersection_points)
  )"

(* NOTE: Assumes that \<exists>index \<in> {0..<length \<C>}. hash (\<C> ! index) = h *)
definition
  index_from_hash :: "hash \<Rightarrow> chain \<Rightarrow> chain_index"
where
  [simp]: "index_from_hash h \<C> = hd [index. (block, index) \<leftarrow> zip \<C> [0..<length \<C>], hash block = h]"

(* TODO: The document seems to assume that there is always a common prefix, thus there is always a last common point. Confirm. *)
definition
  last_common_point :: "chain \<Rightarrow> chain \<Rightarrow> point"
where
  [simp]: "last_common_point \<C>\<^sub>1 \<C>\<^sub>2 = block_point (last (longest_common_prefix \<C>\<^sub>1 \<C>\<^sub>2))"

definition
  new_chain_switcher
    :: "message channel family
    \<Rightarrow>  producer_parameters channel family
    \<Rightarrow>  chain
    \<Rightarrow>  producer_parameters
    \<Rightarrow>  process family"
where
  [simp]: "new_chain_switcher PC I \<C>\<^sub>n\<^sub>e\<^sub>w pp = (
    let
      (_, \<C>, read_ptr, must_rollback, o_points) = pp
    in
      if read_ptr < length (longest_common_prefix \<C> \<C>\<^sub>n\<^sub>e\<^sub>w)
        then
          PC \<triangleleft> MsgRollForward (\<C>\<^sub>n\<^sub>e\<^sub>w ! read_ptr) (tip \<C>\<^sub>n\<^sub>e\<^sub>w)
          \<parallel>
          I \<triangleleft> (StIdle, \<C>\<^sub>n\<^sub>e\<^sub>w, read_ptr + 1, must_rollback, o_points)
        else
          let
            rollback_point = last_common_point \<C> \<C>\<^sub>n\<^sub>e\<^sub>w ;
            new_read_ptr = index_from_hash rollback_point \<C>\<^sub>n\<^sub>e\<^sub>w + 1
          in
            PC \<triangleleft> MsgRollBackward rollback_point (tip \<C>\<^sub>n\<^sub>e\<^sub>w)
            \<parallel>
            I \<triangleleft> (StIdle, \<C>\<^sub>n\<^sub>e\<^sub>w, new_read_ptr, False, o_points)
  )"

definition
  producer
    :: "message channel family
    \<Rightarrow>  message channel family
    \<Rightarrow>  producer_parameters channel family
    \<Rightarrow>  update channel family
    \<Rightarrow>  process family"
where
  "producer CP PC I U =
    I \<triangleright>\<^sup>\<infinity> (st, \<C>, read_ptr, must_rollback, o_points). (
      case st of
        StDone \<Rightarrow>
          \<zero>
      | StIdle \<Rightarrow>
          CP \<triangleright> msg. (
            case msg of
              MsgDone \<Rightarrow>
                I \<triangleleft> (StDone, \<C>, read_ptr, must_rollback, o_points)
            | MsgFindIntersect points \<Rightarrow>
                I \<triangleleft> (StIntersect, \<C>, read_ptr, must_rollback, Some points)
            | MsgRequestNext \<Rightarrow>
                I \<triangleleft> (StCanAwait, \<C>, read_ptr, must_rollback, o_points)
            | _ \<Rightarrow>
                \<zero> \<comment> \<open>Unexpected message, protocol is aborted\<close>
          )
      | StIntersect \<Rightarrow> (
          case best_intersection_point \<C> (the o_points) of
            None \<Rightarrow>
              PC \<triangleleft> MsgIntersectNotFound (tip \<C>)
              \<parallel>
              I \<triangleleft> (StIdle, \<C>, read_ptr, must_rollback, None::point list option)
          | Some intersection_point \<Rightarrow>
              PC \<triangleleft> MsgIntersectFound intersection_point (tip \<C>)
              \<parallel>
              I \<triangleleft> (StIdle, \<C>, index_from_hash intersection_point \<C>, True, None::point list option)
        )
      | StCanAwait \<Rightarrow>
          U \<triangleright> msg. (
            case msg of
              None \<Rightarrow>
                \<comment> \<open>Continue using existing chain\<close>
                if must_rollback
                  then
                    PC \<triangleleft> MsgRollBackward (block_point (\<C> ! read_ptr)) (tip \<C>)
                    \<parallel>
                    I \<triangleleft> (StIdle, \<C>, read_ptr + 1, False, o_points)
                  else
                    if read_ptr \<le> tip_index \<C>
                      then
                        PC \<triangleleft> MsgRollForward (\<C> ! read_ptr) (tip \<C>)
                        \<parallel>
                        I \<triangleleft> (StIdle, \<C>, read_ptr + 1, must_rollback, o_points)
                      else
                        PC \<triangleleft> MsgAwaitReply
                        \<parallel>
                        I \<triangleleft> (StMustReply, \<C>, read_ptr, must_rollback, o_points)
            | Some \<C>\<^sub>n\<^sub>e\<^sub>w \<Rightarrow>
                \<comment> \<open>Continue with new chain\<close>
                new_chain_switcher PC I \<C>\<^sub>n\<^sub>e\<^sub>w (st, \<C>, read_ptr, must_rollback, o_points)
          )
      | StMustReply \<Rightarrow>
          U \<triangleright> msg. (
            case msg of
              None \<Rightarrow>
                \<comment> \<open>Continue waiting for updates\<close>
                I \<triangleleft> (StMustReply, \<C>, read_ptr, must_rollback, o_points)
            | Some \<C>\<^sub>n\<^sub>e\<^sub>w \<Rightarrow>
                \<comment> \<open>Continue with new chain\<close>
                new_chain_switcher PC I \<C>\<^sub>n\<^sub>e\<^sub>w (st, \<C>, read_ptr, must_rollback, o_points)
          )
    )"

text \<open> Consumer \<close>

type_synonym
  consumer_parameters
    = "state \<comment> \<open>current state\<close>
    \<times> chain \<comment> \<open>current chain\<close>
    \<times> bool \<comment> \<open>whether it's the initialization phase\<close>"

(* FIXME: Implement *)
consts candidate_points :: "chain \<Rightarrow> point list"

definition
  rollback_to :: "chain \<Rightarrow> point \<Rightarrow> chain"
where
  [simp]: "rollback_to \<C> point = takeWhile (\<lambda>block. hash block \<le> point) \<C>"

definition
  shutdown
    :: "message channel family
    \<Rightarrow>  consumer_parameters channel family
    \<Rightarrow>  consumer_parameters
    \<Rightarrow>  process family"
where
  [simp]: "shutdown CP I params = (
    let
      (_, \<C>, is_init) = params
    in
      CP \<triangleleft> MsgDone
      \<parallel>
      I \<triangleleft> (StDone, \<C>, is_init)
  )"

definition
  chain_replicator
    :: "message channel family
    \<Rightarrow>  message channel family
    \<Rightarrow>  consumer_parameters channel family
    \<Rightarrow>  consumer_parameters
    \<Rightarrow>  process family"
where
  [simp]: "chain_replicator CP PC I params = (
    let
      (st, \<C>, is_init) = params
    in
      PC \<triangleright> msg. (
        case msg of
          MsgRollForward header tip_point \<Rightarrow>
            I \<triangleleft> (StIdle, \<C> @ [header], is_init)
        | MsgRollBackward rollback_point tip_point \<Rightarrow>
            I \<triangleleft> (StIdle, rollback_to \<C> rollback_point, is_init)
        | MsgAwaitReply \<Rightarrow>
            I \<triangleleft> (StMustReply, \<C>, is_init)
        | _ \<Rightarrow> \<comment> \<open>Unexpected message, protocol is aborted\<close>
            shutdown CP I (st, \<C>, is_init)
      )
  )"

(* FIXME: Should the consumer send the MsgDone message only when an unexpected message is received? *)
definition
  consumer
    :: "message channel family
    \<Rightarrow>  message channel family
    \<Rightarrow>  consumer_parameters channel family
    \<Rightarrow>  process family"
where
  "consumer CP PC I =
    I \<triangleright>\<^sup>\<infinity> (st, \<C>, is_init). (
      case st of
        StDone \<Rightarrow>
          \<zero>
      | StIdle \<Rightarrow>
          if is_init
            then
              if \<C> = []
                then \<comment> \<open>No local chain, start from genesis block\<close>
                  I \<triangleleft> (StIdle, \<C>, False)
                else \<comment> \<open>Local chain, find intersection point\<close>
                  I \<triangleleft> (StIntersect, \<C>, False)
            else
              CP \<triangleleft> MsgRequestNext
              \<parallel>
              I \<triangleleft> (StCanAwait, \<C>, is_init)
      | StIntersect \<Rightarrow>
          CP \<triangleleft> MsgFindIntersect (candidate_points \<C>)
          \<parallel>
          (
            PC \<triangleright> msg. (
              case msg of
                MsgIntersectNotFound tip_point \<Rightarrow>
                  shutdown CP I (StDone, \<C>, is_init) \<comment> \<open>FIXME: Abort? Not clear from document\<close>
              | MsgIntersectFound _ _ \<Rightarrow>
                  \<comment> \<open>TODO: According to the document, the consumer can expect the next update to be
                      MsgRollBackward, so no need to handle the response here. Confirm.\<close>
                  I \<triangleleft> (StIdle, \<C>, is_init)
              | _ \<Rightarrow> \<comment> \<open>Unexpected message, protocol is aborted\<close>
                  shutdown CP I (StDone, \<C>, is_init)
            )
          )
      | StCanAwait \<Rightarrow>
        chain_replicator CP PC I (st, \<C>, is_init)
      | StMustReply \<Rightarrow>
        chain_replicator CP PC I (st, \<C>, is_init)
    )"

definition
  protocol
    :: "message channel family
    \<Rightarrow>  message channel family
    \<Rightarrow>  update channel family
    \<Rightarrow>  chain \<comment> \<open>producer's current chain\<close>
    \<Rightarrow>  chain \<comment> \<open>consumer's current chain\<close>
    \<Rightarrow>  process family"
where
  "protocol CP PC U \<C>\<^sub>p \<C>\<^sub>c =
    \<nu> IC IP. (
      producer CP PC IP U \<parallel> IP \<triangleleft> (StIdle, \<C>\<^sub>p, 0, False, None::block list option)
      \<parallel>
      consumer CP PC IC \<parallel> IC \<triangleleft> (StIdle, \<C>\<^sub>c, True)
    )"

end
