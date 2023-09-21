section \<open>Chain Synchronization Mini-Protocol\<close>

text \<open>
  The theory in this section implements the chain synchronization mini-protocol.
\<close>

theory "Ouroboros-Mini_Protocols-Chain_Sync"
  imports
    "Ouroboros-Mini_Protocols"
    "HOL-Library.BNF_Corec"
begin

locale chain_sync =
  fixes initial_items\<^sub>c :: "'i list"
  fixes initial_items\<^sub>s :: "'i list"
  fixes candidate_points :: "'i list \<Rightarrow> 'p list"
  fixes best_intersection_point :: "'i list \<Rightarrow> 'p list \<Rightarrow> 'p option"
  fixes point_of :: "'i \<Rightarrow> 'p"

subsection \<open>Parties\<close>

datatype party =
  Client |
  Server

subsection \<open>State Machine\<close>

datatype state =
  Idle |
  Intersect |
  CanAwait

datatype ('i, 'p) message =
  is_next_request: RequestNext |
  is_roll_forward: RollForward \<open>'i\<close> |
  is_roll_backward: RollBackward \<open>'p\<close> |
  is_await_reply: AwaitReply |
  is_find_intersect: FindIntersect \<open>'p list\<close> |
  is_intersect_found: IntersectFound \<open>'p\<close> |
  is_intersect_not_found: IntersectNotFound

fun agent_in_state' where
  "agent_in_state' Idle = Client" |
  "agent_in_state' _ = Server"

inductive can_finish_in_state' where
  "can_finish_in_state' Idle"

declare can_finish_in_state'.simps [simp]

primrec next_state' where
  "next_state' Idle m = (partial_case m of
    FindIntersect _ \<Rightarrow> Intersect |
    RequestNext \<Rightarrow> CanAwait
  )" |
  "next_state' Intersect m = (partial_case m of
    IntersectFound _ \<Rightarrow> Idle |
    IntersectNotFound \<Rightarrow> Idle
  )" |
  "next_state' CanAwait m = (partial_case m of
    RollForward _ \<Rightarrow> Idle |
    RollBackward _ \<Rightarrow> Idle |
    AwaitReply \<Rightarrow> Idle \<comment> \<open>only for this initial implementation\<close>
  )"

definition state_machine where
  [simp]: "state_machine = \<lparr>
    initial_state = Idle,
    agent_in_state = agent_in_state',
    can_finish_in_state = can_finish_in_state',
    next_state = next_state'
  \<rparr>"

sublocale chain_sync \<subseteq> protocol_state_machine \<open>state_machine\<close> .

subsection \<open>Programs\<close>

datatype phase =
  is_intersection_finding: IntersectionFinding |
  is_items_update: ItemsUpdate

definition roll_back_to :: "'i list \<Rightarrow> 'p \<Rightarrow> ('i \<Rightarrow> 'p) \<Rightarrow> 'i list" where
  [simp]: "roll_back_to \<I> p \<psi> = (THE \<I>\<^sub>1. \<exists>\<I>\<^sub>2. \<I> = \<I>\<^sub>1 @ \<I>\<^sub>2 \<and> \<psi> (last \<I>\<^sub>1) = p)"

corec client_program where
  "client_program ph \<kappa> \<psi> \<I> = (
    case ph of
      IntersectionFinding \<Rightarrow>
        \<up> Cont (FindIntersect (\<kappa> \<I>));
        \<down> M; (partial_case M of
          Cont IntersectNotFound \<Rightarrow>
            \<up> Done;
            \<bottom> |
          Cont (IntersectFound _) \<Rightarrow>
            client_program ItemsUpdate \<kappa> \<psi> \<I>
        ) |
      ItemsUpdate \<Rightarrow>
        \<up> Cont RequestNext;
        \<down> M; (partial_case M of
          Cont (RollForward i) \<Rightarrow>
            client_program ph \<kappa> \<psi> (\<I> @ [i]) |
          Cont (RollBackward p) \<Rightarrow>
            client_program ph \<kappa> \<psi> (roll_back_to \<I> p \<psi>) |
          Cont AwaitReply \<Rightarrow> \<comment> \<open>client is up to date\<close>
            \<up> Done;
            \<bottom>
        )
    )"

definition index_of :: "'p \<Rightarrow> 'i list \<Rightarrow> ('i \<Rightarrow> 'p) \<Rightarrow> nat" where
  [simp]: "index_of p \<I> \<psi> = (THE k. \<psi> (\<I> ! k) = p)"

corec server_program where
  "server_program rp mrb \<rho> \<psi> \<I> =
    \<down> M; (partial_case M of
      Done \<Rightarrow>
        \<bottom> |
      Cont (FindIntersect ps) \<Rightarrow> (
        case \<rho> \<I> ps of
          None \<Rightarrow>
            \<up> Cont IntersectNotFound;
            server_program rp mrb \<rho> \<psi> \<I> |
          Some p \<Rightarrow>
            \<up> Cont (IntersectFound p);
            server_program (index_of p \<I> \<psi>) True \<rho> \<psi> \<I>
      ) |
      Cont RequestNext \<Rightarrow>
        if mrb then
          \<up> Cont (RollBackward (\<psi> (\<I> ! rp)));
          server_program (Suc rp) False \<rho> \<psi> \<I>
        else
          if rp < length \<I> then
            \<up> Cont (RollForward (\<I> ! rp));
            server_program (Suc rp) mrb \<rho> \<psi> \<I>
          else \<comment> \<open>client is up to date\<close>
            \<up> Cont AwaitReply;
            server_program rp mrb \<rho> \<psi> \<I>
    )"

context chain_sync
begin

primrec program where
  "program Client = client_program IntersectionFinding candidate_points point_of initial_items\<^sub>c" |
  "program Server = server_program 0 False best_intersection_point point_of initial_items\<^sub>s"

end

sublocale chain_sync \<subseteq> protocol_programs \<open>possibilities\<close> \<open>program\<close>
proof
  have "
    client_program phase candidate_points point_of initial_items\<^sub>c
    \<Colon>\<^bsub>Client\<^esub>
    Cont possibilities" for phase
    by
      (coinduction arbitrary: initial_items\<^sub>c phase rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: client_program.code
        extra_splits: or_done.splits message.splits phase.splits
      )
  moreover
  have "
    server_program read_ptr must_roll_back best_intersection_point point_of initial_items\<^sub>s
    \<Colon>\<^bsub>Server\<^esub>
    Cont possibilities" for read_ptr and must_roll_back
    by
      (coinduction arbitrary: initial_items\<^sub>s read_ptr must_roll_back rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: server_program.code
        extra_splits: or_done.splits message.splits option.splits
      )
  ultimately show "program p \<Colon>\<^bsub>p\<^esub> Cont possibilities" for p
    by (cases p) simp_all
qed

subsection \<open>The End\<close>

end
