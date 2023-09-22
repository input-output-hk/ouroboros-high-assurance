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
  fixes point_of :: "'i \<Rightarrow> 'p"
  fixes candidate_points :: "'i list \<Rightarrow> 'p list"
  fixes initial_client_chain :: "'i list"
  fixes initial_server_chain :: "'i list"

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
  is_find_intersect: FindIntersect \<open>'p list\<close> |
  is_intersect_found: IntersectFound \<open>'p\<close> |
  is_intersect_not_found: IntersectNotFound |
  is_request_next: RequestNext |
  is_roll_forward: RollForward \<open>'i\<close> |
  is_roll_backward: RollBackward \<open>'p\<close> |
  is_await_reply: AwaitReply

primrec agent_in_state' where
  "agent_in_state' Idle = Client" |
  "agent_in_state' Intersect = Server" |
  "agent_in_state' CanAwait = Server"

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

definition roll_back :: "('i \<Rightarrow> 'p) \<Rightarrow> 'i list \<Rightarrow> 'p \<Rightarrow> 'i list" where
  [simp]: "roll_back \<psi> \<C> p = (THE \<C>\<^sub>1. (\<exists>\<C>\<^sub>2. \<C> = \<C>\<^sub>1 @ \<C>\<^sub>2) \<and> \<psi> (last \<C>\<^sub>1) = p)"

datatype phase =
  is_intersection_finding: IntersectionFinding |
  is_chain_update: ChainUpdate

corec client_program where
  "client_program ph \<kappa> \<psi> \<C> = (
    case ph of
      IntersectionFinding \<Rightarrow>
        \<up> Cont (FindIntersect (\<kappa> \<C>));
        \<down> M; (partial_case M of
          Cont IntersectNotFound \<Rightarrow>
            \<up> Done;
            \<bottom> |
          Cont (IntersectFound _) \<Rightarrow>
            client_program ChainUpdate \<kappa> \<psi> \<C>
        ) |
      ChainUpdate \<Rightarrow>
        \<up> Cont RequestNext;
        \<down> M; (partial_case M of
          Cont (RollForward i) \<Rightarrow>
            client_program ph \<kappa> \<psi> (\<C> @ [i]) |
          Cont (RollBackward p) \<Rightarrow>
            client_program ph \<kappa> \<psi> (roll_back \<psi> \<C> p) |
          Cont AwaitReply \<Rightarrow> \<comment> \<open>client is up to date\<close>
            \<up> Done;
            \<bottom>
        )
    )"

definition index_of :: "'p \<Rightarrow> 'i list \<Rightarrow> ('i \<Rightarrow> 'p) \<Rightarrow> nat" where
  [simp]: "index_of p \<C> \<psi> = (THE k. \<psi> (\<C> ! k) = p)"

definition first_intersection_point :: "('i \<Rightarrow> 'p) \<Rightarrow> 'p list \<Rightarrow> 'i list \<Rightarrow> 'p option" where
  [simp]: "first_intersection_point \<psi> ps \<C>  = find (\<lambda>p. p \<in> set (map \<psi> \<C>)) ps"

corec server_program where
  "server_program rp mrb \<psi> \<C> =
    \<down> M; (partial_case M of
      Done \<Rightarrow>
        \<bottom> |
      Cont (FindIntersect ps) \<Rightarrow> (
        case first_intersection_point \<psi> ps \<C> of
          None \<Rightarrow>
            \<up> Cont IntersectNotFound;
            server_program rp mrb \<psi> \<C> |
          Some p \<Rightarrow>
            \<up> Cont (IntersectFound p);
            server_program (index_of p \<C> \<psi>) True \<psi> \<C>
      ) |
      Cont RequestNext \<Rightarrow>
        if mrb then
          \<up> Cont (RollBackward (\<psi> (\<C> ! rp)));
          server_program (Suc rp) False \<psi> \<C>
        else
          if rp < length \<C> then
            \<up> Cont (RollForward (\<C> ! rp));
            server_program (Suc rp) mrb \<psi> \<C>
          else \<comment> \<open>client is up to date\<close>
            \<up> Cont AwaitReply;
            server_program rp mrb \<psi> \<C>
    )"

context chain_sync
begin

primrec program where
  "program Client = client_program IntersectionFinding candidate_points point_of initial_client_chain" |
  "program Server = server_program 0 False point_of initial_server_chain"

end

sublocale chain_sync \<subseteq> protocol_programs \<open>possibilities\<close> \<open>program\<close>
proof
  have "
    client_program phase candidate_points point_of initial_client_chain
    \<Colon>\<^bsub>Client\<^esub>
    Cont possibilities" for phase
    by
      (coinduction arbitrary: initial_client_chain phase rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: client_program.code
        extra_splits: or_done.splits message.splits phase.splits
      )
  moreover
  have "
    server_program read_ptr must_roll_back point_of initial_server_chain
    \<Colon>\<^bsub>Server\<^esub>
    Cont possibilities" for read_ptr and must_roll_back
    by
      (coinduction arbitrary: initial_server_chain read_ptr must_roll_back rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: server_program.code
        extra_splits: or_done.splits message.splits option.splits
      )
  ultimately show "program p \<Colon>\<^bsub>p\<^esub> Cont possibilities" for p
    by (cases p) simp_all
qed

subsection \<open>The End\<close>

end
