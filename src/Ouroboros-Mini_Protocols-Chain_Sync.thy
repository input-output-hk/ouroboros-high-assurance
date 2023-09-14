section \<open>Chain-Sync Mini-Protocol\<close>

text \<open>
  The theory in this section implements the chain synchronization mini-protocol.
\<close>

theory "Ouroboros-Mini_Protocols-Chain_Sync"
  imports
    "Ouroboros-Mini_Protocols"
    "HOL-Library.BNF_Corec"
begin

subsection \<open>Cryptographic Primitives\<close>

typedecl hash

axiomatization
where
  hash_linear_order: "OFCLASS(hash, linorder_class)"

instance hash :: linorder
  by (fact hash_linear_order)

subsection \<open>Blocks\<close>

datatype block = Block (hash: \<open>hash\<close>)

subsection \<open>Chains\<close>

type_synonym chain = "block list"

type_synonym chain_index = nat

abbreviation (input) tip_index :: "chain \<Rightarrow> chain_index" where
  "tip_index \<C> \<equiv> length \<C> - 1"

abbreviation (input) tip :: "chain \<Rightarrow> block" where
  "tip \<C> \<equiv> \<C> ! (tip_index \<C>)"

subsection \<open>Points\<close>

type_synonym point = hash

definition block_point :: "block \<Rightarrow> point" where
  [simp]: "block_point \<equiv> hash"

subsection \<open>Protocol Parameters\<close>

datatype phase =
  is_intersection_finding: IntersectionFinding |
  is_chain_update: ChainUpdate

type_synonym consumer_parameters = "
  chain \<comment> \<open>current chain\<close> \<times>
  phase \<comment> \<open>current phase\<close> \<times>
  (chain \<Rightarrow> point list)" \<comment> \<open>function for selecting candidate points\<close>

type_synonym producer_parameters = "
  chain \<comment> \<open>current chain\<close> \<times>
  chain_index \<comment> \<open>read pointer\<close> \<times>
  bool \<comment> \<open>whether the next response to \<open>RequestNext\<close> should be \<open>RollBackward\<close>\<close>"

locale chain_sync =
  fixes initial_params\<^sub>c :: consumer_parameters
    and initial_params\<^sub>p :: producer_parameters

subsection \<open>Parties\<close>

datatype party =
  Producer |
  Consumer

subsection \<open>State Machines\<close>

datatype state =
  Idle |
  Intersect |
  CanAwait

datatype message =
  is_next_request: RequestNext |
  is_roll_forward: RollForward \<open>block\<close> \<open>block\<close> |
  is_roll_backward: RollBackward \<open>point\<close> \<open>block\<close> |
  is_await_reply: AwaitReply |
  is_find_intersect: FindIntersect \<open>point list\<close> |
  is_intersect_found: IntersectFound \<open>point\<close> \<open>block\<close> |
  is_intersect_not_found: IntersectNotFound \<open>block\<close>

fun agent_in_state' where
  "agent_in_state' Idle = Consumer" |
  "agent_in_state' _ = Producer"

inductive can_finish_in_state' where
  "can_finish_in_state' Idle"

declare can_finish_in_state'.simps [simp]

primrec next_state' where
  "next_state' Idle m = (
    partial_case m of
      FindIntersect _ \<Rightarrow> Intersect |
      RequestNext \<Rightarrow> CanAwait)" |
  "next_state' Intersect m = (
    partial_case m of
      IntersectFound _ _ \<Rightarrow> Idle |
      IntersectNotFound _ \<Rightarrow> Idle)" |
  "next_state' CanAwait m = (
    partial_case m of
      RollForward _ _ \<Rightarrow> Idle |
      RollBackward _ _ \<Rightarrow> Idle |
      AwaitReply \<Rightarrow> Idle)" \<comment> \<open>only for this initial implementation\<close>

definition state_machine where
  [simp]: "state_machine = \<lparr>
    initial_state = Idle,
    agent_in_state = agent_in_state',
    can_finish_in_state = can_finish_in_state',
    next_state = next_state'
  \<rparr>"

sublocale chain_sync \<subseteq> protocol_state_machine \<open>state_machine\<close> .

subsection \<open>Programs\<close>

definition rollback_to :: "chain \<Rightarrow> point \<Rightarrow> chain" where
  [simp]: "rollback_to \<C> point = takeWhile (\<lambda>block. hash block \<le> point) \<C>"

corec consumer_program where
  "consumer_program params = (
    let (\<C>, phase, candidate_points) = params in
    case phase of
      IntersectionFinding \<Rightarrow>
        \<up> Cont (FindIntersect (candidate_points \<C>));
        \<down> M; (partial_case M of
          Cont (IntersectNotFound _) \<Rightarrow>
            \<up> Done;
            \<bottom> |
          Cont (IntersectFound _ _) \<Rightarrow>
            consumer_program (\<C>, ChainUpdate, candidate_points)
        ) |
      ChainUpdate \<Rightarrow>
        \<up> Cont RequestNext;
        \<down> M; (partial_case M of
          Cont (RollForward header _) \<Rightarrow>
            consumer_program ((\<C> @ [header]), phase, candidate_points) |
          Cont (RollBackward rollback_point _) \<Rightarrow>
            consumer_program ((rollback_to \<C> rollback_point), phase, candidate_points) |
          Cont AwaitReply \<Rightarrow> \<comment> \<open>consumer is up to date\<close>
            \<up> Done;
            \<bottom>
        )
    )"

definition best_intersection_point :: "chain \<Rightarrow> point list \<Rightarrow> point option" where
  [simp]: "best_intersection_point \<C> points = (
    let
      intersection_points = List.set points \<inter> List.set (map hash \<C>)
    in
      if intersection_points = {} then None else Some (Max intersection_points)
  )"

(* NOTE: Assumes that \<exists>index \<in> {0..<length \<C>}. hash (\<C> ! index) = h *)
definition index_from_hash :: "hash \<Rightarrow> chain \<Rightarrow> chain_index" where
  [simp]: "index_from_hash h \<C> = hd [index. (block, index) \<leftarrow> zip \<C> [0..<length \<C>], hash block = h]"

corec producer_program where
  "producer_program params = (
    let (\<C>, read_ptr, must_rollback) = params in
    \<down> M; (partial_case M of
      Done \<Rightarrow>
        \<bottom> |
      Cont (FindIntersect points) \<Rightarrow> (
        case best_intersection_point \<C> points of
          None \<Rightarrow>
            \<up> Cont (IntersectNotFound (tip \<C>));
            producer_program (\<C>, read_ptr, must_rollback) |
          Some intersection_point \<Rightarrow>
            \<up> Cont (IntersectFound intersection_point (tip \<C>));
            producer_program (\<C>, index_from_hash intersection_point \<C>, True)) |
      Cont RequestNext \<Rightarrow>
        if must_rollback then
          \<up> Cont (RollBackward (block_point (\<C> ! read_ptr)) (tip \<C>));
          producer_program (\<C>, read_ptr + 1, False)
        else
          if read_ptr \<le> tip_index \<C> then
            \<up> Cont (RollForward (\<C> ! read_ptr) (tip \<C>));
            producer_program (\<C>, read_ptr + 1, must_rollback)
          else
            \<up> Cont AwaitReply;
            producer_program (\<C>, read_ptr, must_rollback) \<comment> \<open>consumer is up to date\<close>
    )
  )"

context chain_sync
begin

primrec program where
  "program Consumer = consumer_program initial_params\<^sub>c" |
  "program Producer = producer_program initial_params\<^sub>p"

end

sublocale chain_sync \<subseteq> protocol_programs \<open>possibilities\<close> \<open>program\<close>
proof
  have "consumer_program initial_params\<^sub>c \<Colon>\<^bsub>Consumer\<^esub> Cont possibilities"
    by
      (coinduction arbitrary: initial_params\<^sub>c rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: consumer_program.code
        extra_splits: or_done.splits message.splits phase.splits
      )
  moreover
  have "producer_program initial_params\<^sub>p \<Colon>\<^bsub>Producer\<^esub> Cont possibilities"
    by
      (coinduction arbitrary: initial_params\<^sub>p rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: producer_program.code
        extra_splits: or_done.splits message.splits
      )
  ultimately show "program p \<Colon>\<^bsub>p\<^esub> Cont possibilities" for p
    by (cases p) simp_all
qed

subsection \<open>The End\<close>

end
