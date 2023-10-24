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

hide_const (open) ZFC_in_HOL.set

locale chain_sync =
  fixes point :: "'i::embeddable \<Rightarrow> 'q"
  fixes candidate_intersection_points :: "'i list \<Rightarrow> 'q list"
  fixes initial_client_chain :: "'i list"
  fixes server_chain_updates :: "'i list sync_channel"
  assumes initial_client_chain_is_not_empty:
    "initial_client_chain \<noteq> []"

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
  CanAwait |
  MustReply

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
  "agent_in_state' CanAwait = Server" |
  "agent_in_state' MustReply = Server"

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
    AwaitReply \<Rightarrow> MustReply
  )" |
  "next_state' MustReply m = (partial_case m of
    RollForward _ \<Rightarrow> Idle |
    RollBackward _ \<Rightarrow> Idle
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
  [simp]: "roll_back \<psi> C q = (THE C'. C' \<noteq> [] \<and> prefix C' C \<and> \<psi> (last C') = q)"

datatype client_phase =
  is_intersection_finding: IntersectionFinding |
  is_chain_update: ChainUpdate

corec client_program where
  "client_program \<psi> \<kappa> C \<phi> = (case \<phi> of
    IntersectionFinding \<Rightarrow>
      \<up> Cont (FindIntersect (\<kappa> C));
      \<down> M. (partial_case M of
        Cont IntersectNotFound \<Rightarrow>
          \<up> Done;
          \<bottom> |
        Cont (IntersectFound _) \<Rightarrow>
          client_program \<psi> \<kappa> C ChainUpdate
      ) |
    ChainUpdate \<Rightarrow>
      \<up> Cont RequestNext;
      \<down> M. (partial_case M of
        Cont (RollForward i) \<Rightarrow>
          client_program \<psi> \<kappa> (C @ [i]) \<phi> |
        Cont (RollBackward q) \<Rightarrow>
          client_program \<psi> \<kappa> (roll_back \<psi> C q) \<phi> |
        Cont AwaitReply \<Rightarrow>
          \<down> M. (partial_case M of
            Cont (RollForward i) \<Rightarrow>
              client_program \<psi> \<kappa> (C @ [i]) \<phi> |
            Cont (RollBackward q) \<Rightarrow>
              client_program \<psi> \<kappa> (roll_back \<psi> C q) \<phi>
          )
      )
  )"

definition index :: "('i \<Rightarrow> 'q) \<Rightarrow> 'q \<Rightarrow> 'i list \<Rightarrow> nat" where
  [simp]: "index \<psi> q C = (THE k. k < length C \<and> \<psi> (C ! k) = q)"

definition first_intersection_point :: "('i \<Rightarrow> 'q) \<Rightarrow> 'q list \<Rightarrow> 'i list \<rightharpoonup> 'q" where
  [simp]: "first_intersection_point \<psi> qs C  = find (\<lambda>q. q \<in> \<psi> ` set C) qs"

definition chain_switch :: "('i \<Rightarrow> 'q) \<Rightarrow> 'i list \<Rightarrow> nat \<Rightarrow> 'i list \<Rightarrow> ('i, 'q) message \<times> nat" where
  [simp]: "chain_switch \<psi> C k C' =
  (
    if prefix C C' then
      (RollForward (C' ! Suc k), Suc k)
    else
      let C\<^sub>p = longest_common_prefix C C' in
      (RollBackward (\<psi> (last C\<^sub>p)), length C\<^sub>p - 1)
  )"

datatype server_phase =
  is_client_lagging: ClientLagging |
  is_client_catch_up: ClientCatchUp

primrec server_state_in_phase where
  "server_state_in_phase ClientLagging = Idle" |
  "server_state_in_phase ClientCatchUp = MustReply"

corec server_program' where
  "server_program' \<psi> u k b C \<phi> = (case \<phi> of
    ClientCatchUp \<Rightarrow>
      u \<rightarrow> C'.
      (
        if C' = C then \<comment> \<open>keep waiting for updates\<close>
          server_program' \<psi> u k b C \<phi>
        else \<comment> \<open>changes found, switch to C'\<close>
          let (M', k') = chain_switch \<psi> C k C' in
          \<up> Cont M';
          server_program' \<psi> u k' b C' ClientLagging
      ) |
    ClientLagging \<Rightarrow>
      \<down> M. (partial_case M of
        Done \<Rightarrow>
          \<bottom> |
        Cont (FindIntersect qs) \<Rightarrow>
          (case first_intersection_point \<psi> qs C of
            None \<Rightarrow>
              \<up> Cont IntersectNotFound;
              server_program' \<psi> u k b C \<phi> |
            Some q \<Rightarrow>
              \<up> Cont (IntersectFound q);
              server_program' \<psi> u (index \<psi> q C) True C \<phi>
          ) |
        Cont RequestNext \<Rightarrow>
          u \<rightarrow> C'.
          (
            if C' = C then \<comment> \<open>no changes, continue with C\<close>
              if b then
                \<up> Cont (RollBackward (\<psi> (C ! k)));
                server_program' \<psi> u k False C \<phi>
              else if Suc k < length C then
                \<up> Cont (RollForward (C ! Suc k));
                server_program' \<psi> u (Suc k) b C \<phi>
              else \<comment> \<open>client caught up\<close>
                \<up> Cont AwaitReply;
                server_program' \<psi> u k b C ClientCatchUp
            else \<comment> \<open>changes found, switch to C'\<close>
              let (M', k') = chain_switch \<psi> C k C' in
              \<up> Cont M';
              server_program' \<psi> u k' b C' \<phi>
          )
      )
  )"

definition server_program where
  [simp]: "server_program \<psi> u k b \<phi> = u \<rightarrow> C. server_program' \<psi> u k b C \<phi>"\<comment> \<open>\<^term>\<open>C \<noteq> []\<close> assumed\<close>

context chain_sync
begin

primrec program where
  "program Client =
    client_program point candidate_intersection_points initial_client_chain IntersectionFinding" |
  "program Server =
    server_program point server_chain_updates 0 False ClientLagging"

end

sublocale chain_sync \<subseteq> protocol_programs \<open>possibilities\<close> \<open>program\<close>
proof
  have "
    client_program point candidate_intersection_points initial_client_chain phase
    \<Colon>\<^bsub>Client\<^esub>
    Cont possibilities"
    for phase
    by
      (coinduction arbitrary: initial_client_chain phase rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: client_program.code
        extra_splits: client_phase.splits or_done.splits message.splits
      )
  moreover
  have "
    server_program' point server_chain_updates read_pointer must_roll_back initial_server_chain phase
    \<Colon>\<^bsub>Server\<^esub>
    Cont \<lbrakk>state_machine\<lparr>initial_state := server_state_in_phase phase\<rparr>\<rbrakk>"
    for read_pointer and must_roll_back and initial_server_chain and phase
    by
      (coinduction
        arbitrary: read_pointer must_roll_back initial_server_chain phase
        rule: up_to_embedding_is_sound
      )
      (state_machine_bisimulation
        program_expansion: server_program'.code
        extra_splits: server_phase.splits or_done.splits message.splits option.splits
      )
  then have "program Server \<Colon>\<^bsub>Server\<^esub> Cont possibilities"
    unfolding possibilities_def
    by
      (simp, intro import_conformance)
      (metis comp_apply server_state_in_phase.simps(1))
  ultimately show "program p \<Colon>\<^bsub>p\<^esub> Cont possibilities" for p
    by (cases p) simp_all
qed

subsection \<open>The End\<close>

end
