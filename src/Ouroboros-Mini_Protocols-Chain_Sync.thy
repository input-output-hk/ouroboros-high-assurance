section \<open>Chain Synchronization Mini-Protocol\<close>

text \<open>
  The theory in this section implements the chain synchronization mini-protocol.
\<close>

theory "Ouroboros-Mini_Protocols-Chain_Sync"
  imports
    "Ouroboros-Mini_Protocols"
    "HOL-Library.BNF_Corec"
    "HOL-Library.Sublist"
begin

locale chain_sync =
  fixes point :: "'i \<Rightarrow> 'q"
  fixes candidate_points :: "'i list \<Rightarrow> 'q list"
  fixes initial_client_chain :: "'i list"
  fixes initial_server_chain :: "'i list"
  assumes initial_client_chain_is_not_empty:
    "initial_client_chain \<noteq> []"
  assumes initial_server_chain_is_not_empty:
    "initial_server_chain \<noteq> []"

text \<open>
  We use~\<^typ>\<open>'i\<close> to refer to items stored in chains, which are normally either headers or
  blocks, and~\<^typ>\<open>'q\<close> to refer to points.
\<close>

subsection \<open>Parties\<close>

datatype party =
  Client |
  Server

subsection \<open>State Machine\<close>

datatype state =
  Idle |
  Intersect |
  CanAwait

datatype ('i, 'q) message =
  is_find_intersect: FindIntersect \<open>'q list\<close> |
  is_intersect_found: IntersectFound \<open>'q\<close> |
  is_intersect_not_found: IntersectNotFound |
  is_request_next: RequestNext |
  is_roll_forward: RollForward \<open>'i\<close> |
  is_roll_backward: RollBackward \<open>'q\<close> |
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

definition roll_back :: "('i \<Rightarrow> 'q) \<Rightarrow> 'i list \<Rightarrow> 'q \<Rightarrow> 'i list" where
  [simp]: "roll_back \<psi> C q = (THE C'. prefix C' C \<and> \<psi> (last C') = q)"

datatype phase =
  is_intersection_finding: IntersectionFinding |
  is_chain_update: ChainUpdate

corec client_program where
  "client_program \<psi> \<kappa> C \<phi> = (case \<phi> of
    IntersectionFinding \<Rightarrow>
      \<up> Cont (FindIntersect (\<kappa> C));
      \<down> M; (partial_case M of
        Cont IntersectNotFound \<Rightarrow>
          \<up> Done;
          \<bottom> |
        Cont (IntersectFound _) \<Rightarrow>
          client_program \<psi> \<kappa> C ChainUpdate
      ) |
    ChainUpdate \<Rightarrow>
      \<up> Cont RequestNext;
      \<down> M; (partial_case M of
        Cont (RollForward i) \<Rightarrow>
          client_program \<psi> \<kappa> (C @ [i]) \<phi> |
        Cont (RollBackward q) \<Rightarrow>
          client_program \<psi> \<kappa> (roll_back \<psi> C q) \<phi> |
        Cont AwaitReply \<Rightarrow> \<comment> \<open>only for this initial implementation\<close>
          \<up> Done;
          \<bottom>
      )
  )"

definition index :: "('i \<Rightarrow> 'q) \<Rightarrow> 'q \<Rightarrow> 'i list \<Rightarrow> nat" where
  [simp]: "index \<psi> q C = (THE k. \<psi> (C ! k) = q)"

definition first_intersection_point :: "('i \<Rightarrow> 'q) \<Rightarrow> 'q list \<Rightarrow> 'i list \<Rightarrow> 'q option" where
  [simp]: "first_intersection_point \<psi> qs C  = find (\<lambda>q. q \<in> \<psi> ` set C) qs"

corec server_program where
  "server_program \<psi> C k b =
    \<down> M; (partial_case M of
      Done \<Rightarrow>
        \<bottom> |
      Cont (FindIntersect qs) \<Rightarrow>
        (case first_intersection_point \<psi> qs C of
          None \<Rightarrow>
            \<up> Cont IntersectNotFound;
            server_program \<psi> C k b |
          Some q \<Rightarrow>
            \<up> Cont (IntersectFound q);
            server_program \<psi> C (index \<psi> q C) True
        ) |
      Cont RequestNext \<Rightarrow>
        if b then
          \<up> Cont (RollBackward (\<psi> (C ! k)));
          server_program \<psi> C k False
        else if Suc k < length C then
          \<up> Cont (RollForward (C ! Suc k));
          server_program \<psi> C (Suc k) b
        else \<comment> \<open>only for this initial implementation\<close>
          \<up> Cont AwaitReply;
          server_program \<psi> C k b
    )"

context chain_sync
begin

primrec program where
  "program Client = client_program point candidate_points initial_client_chain IntersectionFinding" |
  "program Server = server_program point initial_server_chain 0 False"

end

sublocale chain_sync \<subseteq> protocol_programs \<open>possibilities\<close> \<open>program\<close>
proof
  have "
    client_program point candidate_points initial_client_chain phase
    \<Colon>\<^bsub>Client\<^esub>
    Cont possibilities"
    for phase
    by
      (coinduction arbitrary: initial_client_chain phase rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: client_program.code
        extra_splits: phase.splits or_done.splits message.splits
      )
  moreover
  have "
    server_program point initial_server_chain read_ptr must_roll_back
    \<Colon>\<^bsub>Server\<^esub>
    Cont possibilities"
    for read_ptr and must_roll_back
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
