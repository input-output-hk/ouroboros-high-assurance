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
  fixes client_chains :: "'i list sync_channel"
  fixes server_chains :: "'i list sync_channel"
  assumes initial_client_chain_is_not_empty:
    "initial_client_chain \<noteq> []"

text \<open>
  We use~\<^typ>\<open>'i\<close> to refer to items stored in chains, which are normally either headers or
  blocks, and~\<^typ>\<open>'q\<close> to refer to points.
\<close>

text \<open>
  We assume that the environment only sends to \<^term>\<open>server_chains\<close> and only sends to it
  non-empty lists whose first elements are the same.
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

corec client_main_loop where
  "client_main_loop \<psi> u \<kappa> C \<phi> = (case \<phi> of
    IntersectionFinding \<Rightarrow>
      \<up> Cont (FindIntersect (\<kappa> C));
      \<down> M. (partial_case M of
        Cont IntersectNotFound \<Rightarrow>
          \<up> Done;
          \<bottom> |
        Cont (IntersectFound _) \<Rightarrow>
          client_main_loop \<psi> u \<kappa> C ChainUpdate
      ) |
    ChainUpdate \<Rightarrow>
      u \<leftarrow> C;
      \<up> Cont RequestNext;
      \<down> M. (partial_case M of
        Cont (RollForward i) \<Rightarrow>
          client_main_loop \<psi> u \<kappa> (C @ [i]) \<phi> |
        Cont (RollBackward q) \<Rightarrow>
          client_main_loop \<psi> u \<kappa> (roll_back \<psi> C q) \<phi> |
        Cont AwaitReply \<Rightarrow>
          \<down> M. (partial_case M of
            Cont (RollForward i) \<Rightarrow>
              client_main_loop \<psi> u \<kappa> (C @ [i]) \<phi> |
            Cont (RollBackward q) \<Rightarrow>
              client_main_loop \<psi> u \<kappa> (roll_back \<psi> C q) \<phi>
          )
      )
  )"

definition index :: "('i \<Rightarrow> 'q) \<Rightarrow> 'q \<Rightarrow> 'i list \<Rightarrow> nat" where
  [simp]: "index \<psi> q C = (THE k. k < length C \<and> \<psi> (C ! k) = q)"

definition first_intersection_point :: "('i \<Rightarrow> 'q) \<Rightarrow> 'q list \<Rightarrow> 'i list \<rightharpoonup> 'q" where
  [simp]: "first_intersection_point \<psi> qs C  = find (\<lambda>q. q \<in> \<psi> ` set C) qs"

datatype ('i, 'p) server_step =
  is_wait: Wait |
  is_progress: Progress \<open>('i, 'p) message\<close> \<open>'i list\<close>

definition server_step :: "('i \<Rightarrow> 'q) \<Rightarrow> 'i list \<Rightarrow> 'i list \<Rightarrow> ('i, 'q) server_step" where
  [simp]: "server_step \<psi> C\<^sub>c C\<^sub>s =
    (
      if C\<^sub>c = C\<^sub>s then
        Wait
      else if prefix C\<^sub>c C\<^sub>s then
        let C\<^sub>c' = C\<^sub>c @ [C\<^sub>s ! length C\<^sub>c] in
        Progress (RollForward (last C\<^sub>c')) C\<^sub>c'
      else
        let C\<^sub>c' = longest_common_prefix C\<^sub>c C\<^sub>s in
        Progress (RollBackward (\<psi> (last C\<^sub>c'))) C\<^sub>c'
    )"

datatype server_phase =
  is_client_syncing: Client_Syncing |
  is_client_in_sync: Client_In_Sync

primrec base_state_in_server_phase where
  "base_state_in_server_phase Client_Syncing = Idle" |
  "base_state_in_server_phase Client_In_Sync = MustReply"

corec server_main_loop where
  "server_main_loop \<psi> u b C\<^sub>c \<phi> = (case \<phi> of
    Client_Syncing \<Rightarrow>
      \<down> M. (partial_case M of
        Done \<Rightarrow>
          \<bottom> |
        Cont (FindIntersect qs) \<Rightarrow>
          u \<rightarrow> C\<^sub>s.
          (case first_intersection_point \<psi> qs C\<^sub>s of
            None \<Rightarrow>
              \<up> Cont IntersectNotFound;
              server_main_loop \<psi> u b C\<^sub>c \<phi> |
            Some q \<Rightarrow>
              \<up> Cont (IntersectFound q);
              server_main_loop \<psi> u True (take (Suc (index \<psi> q C\<^sub>s)) C\<^sub>s) \<phi>
          ) |
        Cont RequestNext \<Rightarrow>
          (
            if b then
              \<up> Cont (RollBackward (\<psi> (last C\<^sub>c)));
              server_main_loop \<psi> u False C\<^sub>c \<phi>
            else
              u \<rightarrow> C\<^sub>s.
              (case server_step \<psi> C\<^sub>c C\<^sub>s of
                Wait \<Rightarrow>
                  \<up> Cont AwaitReply;
                  server_main_loop \<psi> u b C\<^sub>c Client_In_Sync |
                Progress m C\<^sub>c' \<Rightarrow>
                  \<up> Cont m;
                  server_main_loop \<psi> u b C\<^sub>c' \<phi>
              )
          )
      ) |
    Client_In_Sync \<Rightarrow>
      u \<rightarrow> C\<^sub>s.
      (case server_step \<psi> C\<^sub>c C\<^sub>s of
        Wait \<Rightarrow>
          server_main_loop \<psi> u b C\<^sub>c \<phi> |
        Progress m C\<^sub>c' \<Rightarrow>
          \<up> Cont m;
          server_main_loop \<psi> u b C\<^sub>c' Client_Syncing
      )
  )"

context chain_sync
begin

primrec program where
  "program Client =
    client_main_loop
      point
      client_chains
      candidate_intersection_points
      initial_client_chain
      IntersectionFinding" |
  "program Server =
    server_chains \<rightarrow> C\<^sub>s.
    server_main_loop
      point
      server_chains
      False
      [hd C\<^sub>s]
      Client_Syncing"

end

sublocale chain_sync \<subseteq> protocol_programs \<open>possibilities\<close> \<open>program\<close>
proof
  have "
    client_main_loop point client_chains candidate_intersection_points initial_client_chain \<phi>
    \<Colon>\<^bsub>Client\<^esub>
    Cont \<lbrakk>state_machine\<rbrakk>"
    for \<phi>
    by
      (coinduction arbitrary: initial_client_chain \<phi> rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: client_main_loop.code
        extra_splits: client_phase.splits or_done.splits message.splits
      )
  then have "program Client \<Colon>\<^bsub>Client\<^esub> Cont possibilities"
    by (simp add: protocol_state_machine.possibilities_def)
  moreover
  have "
    server_main_loop point server_chains b C\<^sub>c \<phi>
    \<Colon>\<^bsub>Server\<^esub>
    Cont \<lbrakk>state_machine \<lparr>initial_state := base_state_in_server_phase \<phi>\<rparr>\<rbrakk>"
    for b and C\<^sub>c and \<phi>
    by
      (coinduction arbitrary: b C\<^sub>c \<phi> rule: up_to_embedding_is_sound)
      (state_machine_bisimulation
        program_expansion: server_main_loop.code
        extra_splits: server_phase.splits or_done.splits message.splits option.splits server_step.splits
      )
  then have "program Server \<Colon>\<^bsub>Server\<^esub> Cont possibilities"
    unfolding program.simps(2)
    by
      (intro import_conformance)
      (metis
        possibilities_def
        state_machine_def
        state_machine.simps(6)
        base_state_in_server_phase.simps(1)
        comp_apply
      )
  ultimately show "program p \<Colon>\<^bsub>p\<^esub> Cont possibilities" for p
    by (cases p) simp_all

qed

subsection \<open>The End\<close>

end
