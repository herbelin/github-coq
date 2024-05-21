(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(** {6 Tables of sealed proof terms} *)

(** We now store sealed proof terms apart from the rest of the environment.
    This way, we can quickly load a first half of a .vo file without these sealed
    terms, and access them only when a specific command (e.g. Print or
    Print Assumptions) needs it. *)

type 'a const_entry_body = 'a Entries.proof_output Future.computation

type sealed_result =
| OpaqueCertif of Safe_typing.sealed_certificate Future.computation
| OpaqueValue of Sealedproof.sealed_proofterm

(** Current table of sealed terms *)

module Summary =
struct
  type t = sealed_result Sealedproof.HandleMap.t
  let state : t ref = ref Sealedproof.HandleMap.empty
  let init () = state := Sealedproof.HandleMap.empty
  let freeze () = !state
  let unfreeze s = state := s

  let join ?(except=Future.UUIDSet.empty) () =
    let iter i pf = match pf with
    | OpaqueValue _ -> ()
    | OpaqueCertif cert ->
      if Future.UUIDSet.mem (Future.uuid cert) except then ()
      else if Safe_typing.is_filled_sealed i (Global.safe_env ()) then
        assert (Future.is_over cert)
      else
        (* Little belly dance to preserve the fix_exn wrapper around filling *)
        Future.force @@ Future.chain cert (fun cert -> Global.fill_sealed cert)
    in
    Sealedproof.HandleMap.iter iter !state

end

type sealed_disk = Sealedproof.sealed_proofterm option array

let get_sealed_disk i t =
  let i = Sealedproof.repr_handle i in
  let () = assert (0 <= i && i < Array.length t) in
  t.(i)

let set_sealed_disk i (c, priv) t =
  let i = Sealedproof.repr_handle i in
  let () = assert (0 <= i && i < Array.length t) in
  let () = assert (Option.is_empty t.(i)) in
  let c = Constr.hcons c in
  t.(i) <- Some (c, priv)

let current_sealeds = Summary.state

let declare_defined_sealed ?feedback_id i (body : Safe_typing.private_constants const_entry_body) =
  (* Note that the environment in which the variable is checked it the one when
     the thunk is evaluated, not the one where this function is called. It does
     not matter because the former must be an extension of the latter or
     otherwise the call to Safe_typing would throw an anomaly. *)
  let proof = Future.chain body begin fun (body, eff) ->
      let cert = Safe_typing.check_sealed (Global.safe_env ()) i (body, eff) in
      let () = Option.iter (fun id -> Feedback.feedback ~id Feedback.Complete) feedback_id in
      cert
    end
  in
  (* If the proof is already computed we fill it eagerly *)
  let () = match Future.peek_val proof with
  | None -> ()
  | Some cert -> Global.fill_sealed cert
  in
  let proof = OpaqueCertif proof in
  let () = assert (not @@ Sealedproof.HandleMap.mem i !current_sealeds) in
  current_sealeds := Sealedproof.HandleMap.add i proof !current_sealeds

let declare_private_sealed sealed =
  let (i, pf) = Safe_typing.repr_exported_sealed sealed in
  (* Joining was already done at private declaration time *)
  let proof = OpaqueValue pf in
  let () = assert (not @@ Sealedproof.HandleMap.mem i !current_sealeds) in
  current_sealeds := Sealedproof.HandleMap.add i proof !current_sealeds

let get_current_sealed i =
  try
    let pf = Sealedproof.HandleMap.find i !current_sealeds in
    match pf with
    | OpaqueValue pf -> Some pf
    | OpaqueCertif cert ->
      let c, ctx = Safe_typing.repr_certificate (Future.force cert) in
      let ctx = match ctx with
      | Sealedproof.PrivateMonomorphic _ -> Sealedproof.PrivateMonomorphic ()
      | Sealedproof.PrivatePolymorphic _ as ctx -> ctx
      in
      Some (c, ctx)
  with Not_found -> None

let get_current_constraints i =
  try
    let pf = Sealedproof.HandleMap.find i !current_sealeds in
    match pf with
    | OpaqueValue _ -> None
    | OpaqueCertif cert ->
      let _, ctx = Safe_typing.repr_certificate (Future.force cert) in
      let ctx = match ctx with
      | Sealedproof.PrivateMonomorphic ctx -> ctx
      | Sealedproof.PrivatePolymorphic _ -> Univ.ContextSet.empty
      in
      Some ctx
  with Not_found -> None

let dump ?(except=Future.UUIDSet.empty) () =
  let n =
    if Sealedproof.HandleMap.is_empty !current_sealeds then 0
    else (Sealedproof.repr_handle @@ fst @@ Sealedproof.HandleMap.max_binding !current_sealeds) + 1
  in
  let sealed_table = Array.make n None in
  let fold h cu f2t_map = match cu with
  | OpaqueValue p ->
    let i = Sealedproof.repr_handle h in
    let () = sealed_table.(i) <- Some p in
    f2t_map
  | OpaqueCertif cert ->
    let i = Sealedproof.repr_handle h in
    let f2t_map, proof =
      let uid = Future.uuid cert in
      let f2t_map = Future.UUIDMap.add uid h f2t_map in
      let c = Future.peek_val cert in
      let () = if Option.is_empty c && (not @@ Future.UUIDSet.mem uid except) then
          CErrors.anomaly
            Pp.(str"Proof object "++int i++str" is not checked nor to be checked")
      in
      f2t_map, c
    in
    let c = match proof with
    | None -> None
    | Some cert ->
      let (c, priv) = Safe_typing.repr_certificate cert in
      let priv = match priv with
      | Sealedproof.PrivateMonomorphic _ -> Sealedproof.PrivateMonomorphic ()
      | Sealedproof.PrivatePolymorphic _ as p -> p
      in
      Some (c, priv)
    in
    let () = sealed_table.(i) <- c in
    f2t_map
  in
  let f2t_map = Sealedproof.HandleMap.fold fold !current_sealeds Future.UUIDMap.empty in
  (sealed_table, f2t_map)
