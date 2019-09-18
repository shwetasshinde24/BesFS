Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import SGX.State.
Import Coq.Lists.List.ListNotations.

Section SGX_FS.

  Definition Fid : Set := nat.

  Definition Did : Set := nat.

  Definition Pgid : Set := nat.

  Definition Memid : Set := nat.

  Record Permission :=
    {
      readable: bool;
      writable: bool;
      executable: bool;
    }.

  Record Meta :=
    {
      permission : Permission;
      size : nat;
    }.

  Inductive Tree := Fnode: Fid -> Tree | Dnode: Did -> list Tree -> Tree.

  Section TREE_IND2.

    Variable P: Tree -> Prop.
    Variable tree_ind' : forall (t: Tree), P t.
    Variable tree_ind2_Hdir: forall did treeL,
        Forall P treeL -> P (Dnode did treeL).

    Fixpoint tree_ind2_list (treeL: list Tree) (did: Did): P (Dnode did treeL).
      apply tree_ind2_Hdir. induction treeL.
      - constructor.
      - constructor.
        + apply tree_ind'.
        + apply IHtreeL.
    Defined.

  End TREE_IND2.

  Fixpoint tree_ind2 (P: Tree -> Prop)
           (Hfile: forall fid, P (Fnode fid))
           (Hdir: forall did treeL,
               Forall P treeL -> P (Dnode did treeL))
           (t: Tree) {struct t} : P t.
    refine
      match t with
      | Fnode fid => _
      | Dnode did treeL => _
      end.
    - apply Hfile.
    - specialize (tree_ind2 P Hfile Hdir). apply tree_ind2_list.
      + apply tree_ind2.
      + apply Hdir.
  Defined.

  Definition Byte : Set := Ascii.ascii.

  Definition Page := list Byte.

  Fixpoint byte_list_to_string (l: list Byte) : string :=
    match l with
    | nil => EmptyString
    | a :: l' => String a (byte_list_to_string l')
    end.

  Fixpoint string_to_byte_list (s: string): list Byte :=
    match s with
    | EmptyString => nil
    | String a s' => a :: string_to_byte_list s'
    end.

  Check (Dnode 2 [Fnode 5 ; Fnode 6; Dnode 5 []]).

  Record FData :=
    {
      nameF : string;
      metaF : Meta;
      pageIdsF : list Pgid;
    }.

  Record DData :=
    {
      nameD : string;
      metaD : Permission;
    }.

  (* Parameter oh : list Fid. *)

  Definition Path := list string.

  Inductive ErrCode :=
  | eSucc
  | eBadF
  | eInval
  | eIsDir
  | eNameTooLong
  | eNFile
  | eNoEnt
  | eNoSpc
  | eNotEmpty
  | eBadPage
  | eBadName
  | eNoDir
  | eExists
  | eAcces
  | eNotDir
  | eMapFailed.

  Inductive MmapMode :=
  | mapAnon
  | mapFile
  | mapShared
  | mapPrivate.

  Definition MmapedMemory := list Page.

  Open Scope string_scope.

  Record FileSystem : Set :=
    {
      layout : Tree;
      open_handles : list (Fid * nat);
      virtual_memory : list Page;
      f_map : Fid -> FData;
      d_map : Did -> DData;
      fnode_ctr: nat;
      dnode_ctr: nat;
      mmap_handles : list (Memid * nat * Permission);
      mmap_memory : MmapedMemory;
    }.

  Definition memory_upper_bound : nat := Z.to_nat 65536%Z.

  Inductive LogCommand: Set :=
    Call_VRead : Fid -> nat -> (string * ErrCode) -> LogCommand
  | Call_VWrite : Fid -> string -> nat -> ErrCode -> LogCommand
  | Call_VOpen: Path -> string -> ErrCode -> LogCommand
  | Call_VClose: Fid -> ErrCode -> LogCommand
  | Call_VLSeek: Fid -> nat -> ErrCode -> LogCommand
  | Call_VMkdir: Path -> string -> Permission -> ErrCode -> LogCommand
  | Call_VRmdir: Path -> ErrCode -> LogCommand
  | Call_MKFS: string -> LogCommand
  | Call_VCreate: Path -> string -> Permission -> ErrCode -> LogCommand
  | Call_VChmod: Path -> Permission -> ErrCode -> LogCommand
  | Call_VReadDir: Path -> ErrCode -> LogCommand
  | Call_VStat: Fid -> ErrCode -> LogCommand
  | Call_VTruncate: Fid -> nat -> string -> ErrCode -> LogCommand
  | Call_VRemove: Path -> string -> ErrCode -> LogCommand
  | Call_AllocMem: MmapedMemory -> nat -> list Memid -> LogCommand
  | Call_DeallocMem: MmapedMemory -> Memid -> nat -> bool -> LogCommand.

  Definition FSState := (FileSystem * list LogCommand)%type.

  Definition trivialFS : FSState :=
    (Build_FileSystem
       (Fnode O) nil nil
       (fun _ => Build_FData EmptyString
                             (Build_Meta (Build_Permission false false false) O) nil)
       (fun _ => Build_DData EmptyString (Build_Permission false false false)) O 1 nil nil,
     nil).

  Definition mkfs (disk_name: string) : FSState :=
    (Build_FileSystem
       (Dnode O nil) nil nil
       (fun _ => Build_FData EmptyString
                             (Build_Meta (Build_Permission false false false) O) nil)
       (fun did => if Nat.eq_dec did O
                   then Build_DData disk_name (Build_Permission true true true)
                   else Build_DData EmptyString
                                    (Build_Permission false false false)) O 1 nil nil,
     Call_MKFS disk_name :: nil).

  Definition getOpenHandles: State FSState (list (Fid * nat)) :=
    fun x => ((@open_handles (fst x)), x).

  Definition putOpenHandles: list (Fid * nat) -> State FSState unit :=
    fun oh x =>
      let (fs, logs) := x in
      (tt, (Build_FileSystem
              fs.(layout) oh fs.(virtual_memory) fs.(f_map)
              fs.(d_map) fs.(fnode_ctr) fs.(dnode_ctr)
              fs.(mmap_handles) fs.(mmap_memory), logs)).

  Definition putVirtualMemory: list Page -> State FSState unit :=
    fun vm x =>
      let (fs, logs) := x in
      (tt, (Build_FileSystem fs.(layout) fs.(open_handles) vm
            fs.(f_map) fs.(d_map) fs.(fnode_ctr) fs.(dnode_ctr)
            fs.(mmap_handles) fs.(mmap_memory), logs)).

  Definition putFMap: (Fid -> FData) -> State FSState unit :=
    fun fmap x =>
      let (fs, logs) := x in
      (tt, (Build_FileSystem fs.(layout) fs.(open_handles) fs.(virtual_memory)
            fmap fs.(d_map) fs.(fnode_ctr) fs.(dnode_ctr)
            fs.(mmap_handles) fs.(mmap_memory), logs)).

  Definition putLayout: Tree -> State FSState unit :=
    fun tree x =>
      let (fs, logs) := x in
      (tt, (Build_FileSystem tree fs.(open_handles) fs.(virtual_memory)
            fs.(f_map) fs.(d_map) fs.(fnode_ctr) fs.(dnode_ctr)
            fs.(mmap_handles) fs.(mmap_memory), logs)).

  Definition putMmapHandles: list (Memid * nat * Permission) -> State FSState unit :=
    fun h x =>
      let (fs, logs) := x in
      (tt, (Build_FileSystem fs.(layout) fs.(open_handles) fs.(virtual_memory)
            fs.(f_map) fs.(d_map) fs.(fnode_ctr) fs.(dnode_ctr)
            h fs.(mmap_memory), logs)).

  Definition putMmapMemory: MmapedMemory -> State FSState unit :=
    fun m x =>
      let (fs, logs) := x in
      (tt, (Build_FileSystem fs.(layout) fs.(open_handles) fs.(virtual_memory)
            fs.(f_map) fs.(d_map) fs.(fnode_ctr) fs.(dnode_ctr)
            fs.(mmap_handles) m, logs)).

  Definition getTree: State FSState Tree := fun x => ((fst x).(layout), x).
  Definition getFS: State FSState FileSystem := fun x => (fst x, x).
  Definition getFMap: State FSState (Fid -> FData) := fun x => ((fst x).(f_map), x).

  Definition externalCall {s: Type}:
    (s -> LogCommand) -> (nat -> s) -> State FSState s :=
    fun cmd f state => let (fs, logs) := state in
                       let v := f (length logs) in (v, (fs, cmd v :: logs)).

  Definition testExternalCall: State FSState nat :=
    do n3 <- externalCall (Call_VClose 4) (fun x => eSucc);
      do ss <- get;
      return_ (length (snd ss)).

  Compute (testExternalCall trivialFS).

  Definition psize := Z.to_nat 4000%Z.
  Definition block_size := Z.to_nat 4096%Z.

  Parameter v_read: Fid -> nat -> nat -> (string * ErrCode).
  Parameter v_write: Fid -> string -> nat -> nat -> ErrCode.
  Parameter v_lseek : Fid -> nat -> nat -> ErrCode.
  Parameter v_close: Fid -> nat -> ErrCode.
  Parameter v_open: Path -> string -> nat -> ErrCode.
  (* Definition v_open (a: Path) (b: string) (c: nat) := eSucc. *)
  Parameter v_create: Path -> string -> Permission -> nat -> ErrCode.
  Parameter v_chmod: Path -> Permission -> nat -> ErrCode.
  Parameter v_remove: Path -> string -> nat -> ErrCode.
  (* Definition v_create (a: Path) (b: string) (c: Permission) (d: nat) := eSucc. *)
  Parameter v_mkdir: Path -> string -> Permission -> nat -> ErrCode.
  Parameter v_rmdir: Path -> nat -> ErrCode.
  Parameter v_readdir: Path -> nat -> ErrCode.
  Parameter v_stat: Fid -> nat -> ErrCode.
  Parameter v_truncate: Fid -> nat -> string -> nat -> ErrCode.
  Parameter decrypt_page: string -> string.
  Parameter encrypt_page : string -> string.
  Parameter verify_page: string -> bool.
  Parameter extract_page : string -> string.
  Parameter truncate_page: string -> nat -> nat -> string.
  Parameter allocate_memory: MmapedMemory -> nat -> nat -> list Memid.
  Parameter deallocate_memory: MmapedMemory -> Memid -> nat -> nat -> bool.

  (* TODO *)
  (*   1. Add counter to v_func *)
  (*   2. Record returned value in log *)
  (*   3. Define a clearner externalCall.                                      *)

  Definition isNotSucc (err: ErrCode) : {err <> eSucc} + {err = eSucc}.
  Proof. destruct err; [right; auto | left; intro s; inversion s..]. Defined.

  Fixpoint replace_handler (fid: Fid) (pos: nat) (lst: list (Fid * nat)) :=
    match lst with
    | nil => nil
    | (id, p) :: rest => if (Nat.eq_dec fid id)
                         then (id, pos) :: rest
                         else (id, p) :: replace_handler fid pos rest
    end.

  Definition pos_to_vpage (pos: nat) : nat := pos / psize.

  Definition pos_to_vlen (pos: nat) (len : nat) : nat :=
    ((pos + len)/psize - (pos / psize) + 1) * block_size.

  (* TODO: pos + len should <= the total size of the file, the same as seek *)

  Definition fs_parameter (n: nat): Type :=
    match n with
    |  O => Fid * nat
    |  1 => Path * string
    |  2 => Fid
    |  3 => Fid * string * nat
    |  4 => Fid * nat
    |  5 => Path * string * Permission
    |  6 => Path * string * Permission
    |  7 => Path
    |  8 => Path * string
    |  9 => Path * Permission
    | 10 => Path
    | 11 => Fid
    | 12 => Fid * nat
    | _ => unit
    end.

  Definition fs_result (n: nat) : Type :=
    match n with
    |  O => string * ErrCode
    |  1 => Fid * ErrCode
    |  2 => ErrCode
    |  3 => ErrCode
    |  4 => ErrCode
    |  5 => ErrCode
    |  6 => ErrCode
    |  7 => ErrCode
    |  8 => ErrCode
    |  9 => ErrCode
    | 10 => list string * ErrCode
    | 11 => string * Permission *nat * list Pgid * ErrCode
    | 12 => ErrCode
    | _ => unit
    end.

  Definition fs_read (arg : fs_parameter O) : State FSState (fs_result O) :=
    let (fId, len) := arg in
    do oh <- getOpenHandles;
      let opos := find (fun x => Nat.eqb (fst x) fId) oh in
      match opos with
      | None => return_ ("", eBadF)
      | Some (_, pos) =>
        do fmap <- getFMap;
        if le_dec (fmap fId).(metaF).(size) (pos + len)
        then return_ ("", eInval)
        else do err <- externalCall (Call_VLSeek fId (pos_to_vpage pos))
                (v_lseek fId (pos_to_vpage pos));
             if (isNotSucc err)
             then return_ ("", err)
             else
               let new_len := pos_to_vlen pos len in
               do readR <- externalCall (Call_VRead fId new_len) (v_read fId new_len);
               let (str, err) := readR in
               if (isNotSucc err)
               then return_ ("", err)
               else
                 let new_str := decrypt_page str in
                 if (verify_page new_str)
                 then
                   let extracted_str := extract_page new_str in
                   let truncated_str := truncate_page extracted_str pos (pos + len) in
                   let new_open_handles := replace_handler fId (pos + len) oh in
                   putOpenHandles new_open_handles >>
                                  return_ (truncated_str, eSucc)
                 else return_ ("", eBadPage)
      end.

  Definition DData_eqb (dd: DData) (dname: string) : bool :=
    if (string_dec dd.(nameD) dname) then true else false.

  Definition root_eq (dmap: Did -> DData) (tree: Tree) (dname : string) : bool :=
    match tree with
    | Fnode _ => false
    | Dnode d _ => DData_eqb (dmap d) dname
    end.

  Fixpoint findDir (dmap: Did -> DData) (tree : Tree) (p: Path) : option Tree :=
    match tree with
    | Fnode _ => None
    | Dnode did li =>
      match p with
      | nil => Some tree
      | d :: rest => match find (fun x => root_eq dmap x d) li with
                     | None => None
                     | Some t => findDir dmap t rest
                     end
      end
    end.

  Definition sampleTree := Dnode 0 [Dnode 1 []; Dnode 2 [Dnode 4 [Fnode 4; Dnode 5 [];
  Dnode 6 []; Dnode 7 [Dnode 8 [Dnode 9 []; Fnode 1; Fnode 2; Fnode 3]]]]; Dnode 3 []].

  (* Compute (findDir sampleTree [2; 4; 7; 8]). *)

  Fixpoint collectBareFids (li : list Tree) : list Fid :=
    match li with
    | nil => nil
    | Fnode id :: rest => id :: collectBareFids rest
    | Dnode _ _ :: rest => collectBareFids rest
    end.

  Fixpoint collectDids (t: Tree) : list Did :=
    match t with
    | Fnode _ => nil
    | Dnode did l => did :: flat_map collectDids l
    end.

  Fixpoint collectFids (t: Tree) : list Fid :=
    match t with
    | Fnode id => id :: nil
    | Dnode _ l => flat_map collectFids l
    end.

  Definition treeName
             (fmap: Fid -> FData) (dmap: Did -> DData) (tree: Tree) : string :=
    match tree with
    | Fnode fId => (fmap fId).(nameF)
    | Dnode did _ => (dmap did).(nameD)
    end.

  Inductive NoDupNameTree: (Fid -> FData) -> (Did -> DData) -> Tree -> Prop :=
  | File_NDNT: forall fmap dmap fId, NoDupNameTree fmap dmap (Fnode fId)
  | Dir_NDNT: forall fmap dmap root treeL,
      Forall (NoDupNameTree fmap dmap) treeL ->
      NoDup (map (treeName fmap dmap) treeL) ->
      NoDupNameTree fmap dmap (Dnode root treeL).

  Definition isDir (t : Tree) : Prop := exists d l, t = Dnode d l.

  Definition pad_size (len: nat): nat :=
    let q := len / block_size in
    if Nat.eq_dec (len mod block_size) O then q else S q.

  Definition Disjoint (h1 h2: (Memid * nat * Permission)): Prop :=
    match h1 with
    | ((s1, len1), _) => match h2 with
                         | ((s2, len2), _) => s1 + pad_size len1 <= s2 \/
                                              s2 + pad_size len2 <= s1
                         end
    end.

  Inductive NoOverlap: list (Memid * nat * Permission) -> Prop :=
  | NoOverlap_nil: NoOverlap nil
  | NoOverlap_cons: forall x l, (forall y, In y l -> Disjoint x y) ->
                                NoOverlap l -> NoOverlap (x :: l).

  Definition NotNullHandles (x: (Memid * nat * Permission)) : Prop :=
    match x with | (_, len, _) => len <> O end.

  Definition NoNull (l: list (Memid * nat * Permission)): Prop :=
    Forall NotNullHandles l.

  Definition good_file_system (fs: FileSystem) : Prop :=
    NoDupNameTree fs.(f_map) fs.(d_map) fs.(layout) /\
    NoDup (collectDids fs.(layout)) /\
    NoDup (collectFids fs.(layout)) /\
    (forall el, In el (collectDids fs.(layout)) -> fs.(dnode_ctr) > el) /\
    (forall el, In el (collectFids fs.(layout)) -> fs.(fnode_ctr) > el) /\
    NoDup (map fst fs.(open_handles)) /\
    isDir fs.(layout) /\
    (forall fId1 fId2 pgId1 pgId2,
        fId1 <> fId2 ->
        In pgId1 (fs.(f_map) fId1).(pageIdsF) ->
        In pgId2 (fs.(f_map) fId2).(pageIdsF) -> pgId1 <> pgId2) /\
    (forall fId pgId, In pgId (fs.(f_map) fId).(pageIdsF) ->
                      pgId < memory_upper_bound) /\ NoOverlap (mmap_handles fs) /\
    (forall mem, In mem (mmap_memory fs) -> length mem = block_size) /\
    NoNull (mmap_handles fs).

  Compute (collectBareFids [Dnode 9 []; Fnode 1; Fnode 2; Fnode 3]).

  Compute (collectDids sampleTree).

  Compute (collectFids sampleTree).

  Definition findFids (dmap: Did -> DData) (tree: Tree) (p: Path) : list Fid :=
    match findDir dmap tree p with
    | None => []
    | Some (Fnode _) => []
    | Some (Dnode d li) => collectBareFids li
    end.

  Definition fdata_eqb (fd: FData) (fname: string) : bool :=
    if (string_dec fd.(nameF) fname) then true else false.

  Definition findMatchedFid (fs: FileSystem) (p: Path) (fname: string) : option Fid :=
    find (fun x => fdata_eqb (fs.(f_map) x) fname) (findFids fs.(d_map) fs.(layout) p).

  Section FileInTree.
    Context (fmap : Fid -> FData).
    Context (dmap : Did -> DData).

    Inductive file_in_fnode: string -> Tree -> Prop :=
      FIF: forall fname fId, (fmap fId).(nameF) = fname ->
                             file_in_fnode fname (Fnode fId).

    Inductive file_in_tree: Path -> string -> Tree -> Prop :=
    | Empty_path_in_dnode: forall root fname treeL,
        Exists (file_in_fnode fname) treeL -> file_in_tree [] fname (Dnode root treeL)
    | Cons_path_in_dnode: forall root fname dname dlist treeL,
        (exists did treeL',
            In (Dnode did treeL') treeL /\
            (dmap did).(nameD) = dname /\
            file_in_tree dlist fname (Dnode did treeL')) ->
        file_in_tree (dname :: dlist) fname (Dnode root treeL).

    Inductive file_in_tree_with_id: Path -> string -> Tree -> Fid -> Prop :=
    | Empty_path_fitwi: forall root fname treeL id,
        In (Fnode id) treeL -> (fmap id).(nameF) = fname ->
        file_in_tree_with_id [] fname (Dnode root treeL) id
    | Cons_path_fitwi: forall root fname dname dlist treeL id,
        (exists did treeL',
            In (Dnode did treeL') treeL /\
            (dmap did).(nameD) = dname /\
            file_in_tree_with_id dlist fname (Dnode did treeL') id) ->
        file_in_tree_with_id (dname :: dlist) fname (Dnode root treeL) id.

  End FileInTree.

  Definition testDmap (did: Did) :=
    match did with
    | O => Build_DData "0" (Build_Permission false false false)
    | S O => Build_DData "1" (Build_Permission false false false)
    | S (S O) => Build_DData "2" (Build_Permission false false false)
    | S (S (S O)) => Build_DData "3" (Build_Permission false false false)
    | S (S (S (S O))) => Build_DData "4" (Build_Permission false false false)
    | _ => Build_DData "5" (Build_Permission false false false)
    end.

  Goal file_in_tree (fun _ => Build_FData "file"
       (Build_Meta (Build_Permission false false false) O) nil) testDmap
       ["2" ; "4"] "file" sampleTree.
  Proof.
    unfold sampleTree. constructor. exists 2, ([Dnode 4 [Fnode 4; Dnode 5 [];
    Dnode 6 []; Dnode 7 [Dnode 8 [Dnode 9 []; Fnode 1; Fnode 2; Fnode 3]]]]). split.
    - right. left. auto.
    - split.
      + constructor; auto.
      + constructor. exists 4, [Fnode 4; Dnode 5 []; Dnode 6 []; Dnode 7 [Dnode 8
        [Dnode 9 []; Fnode 1; Fnode 2; Fnode 3]]]. split. 1: left; auto.
        split; constructor; auto. apply Exists_cons_hd. constructor. simpl. auto.
  Qed.

  Axiom truncate_page_length: forall str n1 n2,
      n1 <= n2 -> String.length (truncate_page str n1 n2) = n2 - n1.

  Definition fs_open (arg: fs_parameter 1) : State FSState (fs_result 1) :=
    let (path, fname) := arg in
    do fs <- getFS;
      match findMatchedFid fs path fname with
      | None => return_ (0, eBadF)
      | Some fId =>
        let opos := find (fun x => Nat.eqb (fst x) fId) fs.(open_handles) in
        match opos with
        | Some _ => return_ (fId, eBadF)
        | None =>
          do err <- externalCall (Call_VOpen path fname) (v_open path fname);
            match err with
            | eSucc => putOpenHandles ((fId, 0) :: fs.(open_handles)) >>
                                      return_ (fId, eSucc)
            | _ => return_ (fId, err)
            end
        end
      end.

  (* Compute (fs_open ("root" :: nil) "" (mkfs "root")). *)

  Definition prod_dec {A B: Type} (a_dec: forall x y: A, {x = y} + {x <> y})
             (b_dec: forall x y: B, {x = y} + {x <> y}) (n m: (A * B)) : {n = m} + {n <> m}.
  Proof.
    destruct n as [na nb]. destruct m as [ma mb]. destruct (a_dec na ma).
    - subst. destruct (b_dec nb mb).
      + subst. left; auto.
      + right. intro. apply n. inversion H. auto.
    - right. intro. apply n. inversion H. auto.
  Defined.

  Definition fs_close (fId: fs_parameter 2): State FSState (fs_result 2) :=
    do oh <- getOpenHandles;
      let opos := find (fun x => Nat.eqb (fst x) fId) oh in
      match opos with
      | None => return_ eBadF
      | Some t =>
        do err <- externalCall (Call_VClose fId) (v_close fId);
          match err with
          | eSucc =>
            putOpenHandles (remove (prod_dec Nat.eq_dec Nat.eq_dec) t oh) >>
                           return_ eSucc
          | _ => return_ err
          end
      end.

  Definition counter (fs: FSState) := length (snd fs).

  Definition openhandleFS (fs: FSState) := @open_handles (fst fs).
  Definition layoutFS (fs: FSState) := @layout (fst fs).
  Definition vmFS (fs: FSState) := @virtual_memory (fst fs).
  Definition fMapFS (fs: FSState) := @f_map (fst fs).
  Definition dMapFS (fs: FSState) := @d_map (fst fs).
  Definition fCntFS (fs: FSState) := @fnode_ctr (fst fs).
  Definition dCntFS (fs: FSState) := @dnode_ctr (fst fs).
  Definition logFS (fs: FSState) := snd fs.
  Definition fsFS (fs: FSState) := fst fs.
  Definition memHandleFS (fs: FSState) := @mmap_handles (fst fs).
  Definition memoryFS (fs: FSState) := @mmap_memory (fst fs).

  Definition f_map_append_page (fmap: Fid -> FData) (fId : Fid)
             (page : Pgid) : (Fid -> FData) :=
    fun id : Fid =>
      if Nat.eq_dec id fId
      then let fd := fmap fId in
           Build_FData fd.(nameF) fd.(metaF) (fd.(pageIdsF) ++ (page :: nil))
      else fmap id.

  Parameter get_next_free_vpg: (Fid -> FData) -> Pgid.

  Axiom get_next_free_vpg_axiom: forall (fmap: Fid -> FData) (fId: Fid),
      ~ In (get_next_free_vpg fmap) (fmap fId).(pageIdsF) /\
      get_next_free_vpg fmap <= memory_upper_bound.

  Fixpoint upd_nth {A: Type} (l: list A) (n: nat) (v: A) :=
    match l with
    | nil => nil
    | a :: l' => match n with
                 | O => v :: l'
                 | S m => a :: upd_nth l' m v
                 end
    end.

  Compute upd_nth [1; 2; 3; 4; 5] 2 1000.

  Definition inputOrder (i1 i2 : string) := String.length i1 < String.length i2.

  Lemma inputOrder_wf': forall len i, String.length i <= len -> Acc inputOrder i.
  Proof.
    induction len; intros; constructor; intros;
      unfold inputOrder in * |-; [exfalso | apply IHlen]; intuition.
  Qed.

  Lemma inputOrder_wf : well_founded inputOrder.
  Proof. red; intro; eapply inputOrder_wf'; eauto. Defined.

  Lemma substring_length: forall n m s, String.length (substring n m s) <= m.
  Proof.
    intros. revert n m. induction s; intros; simpl.
    - destruct n. destruct m. auto. simpl. intuition. simpl. intuition.
    - destruct n. destruct m; simpl. auto. intuition. intuition.
  Qed.

  Lemma help_write_to_vm: forall (buf0 : string) (pos0 : nat),
      buf0 <> "" ->
      S (String.length
           (substring (psize - pos0 mod psize)
                      (String.length buf0 - (psize - pos0 mod psize)) buf0)) <=
      String.length buf0.
  Proof.
    intros. rename H into n. assert (pos0 mod psize < psize) by
        (apply Nat.mod_upper_bound; unfold psize; compute; intuition).
    assert (0 < psize - pos0 mod psize) by omega.
    remember (psize - pos0 mod psize) as i. clear Heqi H.
    pose proof (substring_length i (String.length buf0 - i) buf0).
    transitivity (S (String.length buf0 - i)). 1: intuition.
    remember (String.length buf0) as l. assert (0 < l). destruct buf0.
    1: exfalso; auto. simpl in Heql. intuition.
    clear H Heql. omega.
  Qed.

  Fixpoint override {A: Type} (l: list A) (pos: nat) (l' : list A) : list A :=
    match l with
    | nil => match pos with
             | O => l'
             | S _ => nil
             end
    | a :: rl => match pos with
                 | O => match l' with
                        | nil => l
                        | b :: rl' => b :: override rl O rl'
                        end
                 | S m => a :: override rl m l'
                 end
    end.

  Compute override [] 0 [5; 6; 7].

  Compute override [1; 2; 3; 4] 1 [5; 6].

  Definition write_to_virtual_memory : string -> nat -> Fid -> (Fid -> FData) -> list Page -> sum (list Page * (Fid -> FData)) ErrCode.
    refine (
        Fix inputOrder_wf (fun _ => nat -> Fid -> (Fid -> FData) -> list Page -> sum (list Page * (Fid -> FData)) ErrCode)
            (fun (buf: string) (write_to_vm: forall buf', inputOrder buf' buf -> nat -> Fid -> (Fid -> FData) -> list Page -> sum (list Page * (Fid -> FData)) ErrCode) (pos: nat) (fId: Fid) (fmap: Fid -> FData) (vm: list Page) =>
               if string_dec buf EmptyString
               then inl (vm, fmap)
               else let len := String.length buf in
                    let new_vm := vm in
                    let new_map := fmap in
                    let pg_offset := pos mod psize in
                    let pgn := if Nat.eq_dec pg_offset O then pos / psize + 1 else pos / psize in
                    let vpg := nth pgn (fmap fId).(pageIdsF) memory_upper_bound in
                    let vpg_ret :=
                        if Bool.bool_dec (andb (Nat.eqb vpg memory_upper_bound) (Nat.eqb pg_offset O)) true
                        then (get_next_free_vpg new_map, true) else (vpg, false) in
                    let vpg := fst vpg_ret in
                    if Nat.eq_dec vpg memory_upper_bound
                    then inr eNoSpc
                    else if le_dec memory_upper_bound vpg
                         then inr eInval
                         else let new_map := if Sumbool.sumbool_of_bool (snd vpg_ret)
                                             then f_map_append_page new_map fId vpg
                                             else new_map in
                              let curr_page_cont := nth vpg new_vm nil in
                              let b1 := substring 0 (psize - pg_offset) buf in
                              let buf := substring (psize - pg_offset) (len - (psize - pg_offset)) buf in
                              let new_curr_pg_cont := override curr_page_cont pg_offset (string_to_byte_list b1) in
                              let new_vm := upd_nth new_vm vpg new_curr_pg_cont in
                              let pos := pos + psize - pg_offset in
                              write_to_vm buf _ pos fId new_map new_vm)
      ).
    hnf. subst buf. subst len. subst pg_offset. clear -n. apply help_write_to_vm. apply n.
  Defined.

  Fixpoint getSublist {A: Type} (n m: nat) (l: list A) : list A :=
    match n with
    | 0 =>
      match m with
      | 0 => nil
      | S m' =>
        match l with
        | nil => l
        | c :: s' => c :: getSublist 0 m' s'
        end
      end
    | S n' => match l with
              | nil => l
              | _ :: s' => getSublist n' m s'
              end
    end.

  Definition get_write_pages (fId: Fid) (fmap: Fid -> FData) (vm: list Page) (pos: nat) (len: nat): list Pgid :=
    let end_pos := if Nat.eq_dec ((pos + len) mod psize) O
                   then (pos + len) / psize
                   else (pos + len) / psize + 1 in
    let start_pos := pos / psize in
    getSublist start_pos (end_pos - start_pos + 1) (fmap fId).(pageIdsF).

  Definition get_vmpg_no (page_no : nat) (fId: Fid) (fmap : Fid -> FData) : nat :=
    nth  page_no (fmap fId).(pageIdsF) memory_upper_bound.

  Definition change_f_map_pages
             (fmap: Fid -> FData) (fId : Fid) (pages : list Pgid) : (Fid -> FData) :=
    fun id : Fid => if Nat.eq_dec id fId
                    then let fd := fmap fId in Build_FData fd.(nameF) fd.(metaF) pages
                    else fmap id.

  Definition change_f_map_size
             (fmap: Fid -> FData) (fId : Fid) (new_size : nat) : (Fid -> FData) :=
    fun id : Fid => if Nat.eq_dec id fId
                    then let fd := fmap fId in Build_FData fd.(nameF) (Build_Meta fd.(metaF).(permission) new_size) fd.(pageIdsF)
                    else fmap id.

  Definition change_f_map_permission
             (fmap: Fid -> FData) (fId : Fid) (p : Permission) : (Fid -> FData) :=
    fun id : Fid => if Nat.eq_dec id fId
                    then let fd := fmap fId in Build_FData fd.(nameF) (Build_Meta p fd.(metaF).(size)) fd.(pageIdsF)
                    else fmap id.

  Definition change_f_map
             (fmap: Fid -> FData) (fId : Fid) (fdata: FData) : (Fid -> FData) :=
    fun id : Fid => if Nat.eq_dec id fId then fdata else fmap id.

  Definition get_new_size (fId: Fid) (fmap: Fid -> FData) (new_vm: list Page): nat :=
    fold_right
      Init.Nat.add O (map (fun n => length(nth n new_vm nil)) (fmap fId).(pageIdsF)).

  Definition get_encrypted_buf (pages: list Pgid) (new_vm: list Page) : string :=
    encrypt_page
      (byte_list_to_string (concat (map (fun n => nth n new_vm nil) pages))).

  Local Open Scope bool_scope.

  Definition fs_write (arg: fs_parameter 3) : State FSState (fs_result 3) :=
    let (fidBuf, pos) := arg in
    let (fId, buf) := fidBuf in
    do fs <- getFS;
      let opos := find (fun x => Nat.eqb (fst x) fId) fs.(open_handles) in
      match opos with
      | None => return_ eBadF
      | Some _ =>
        let fsize := (fs.(f_map) fId).(metaF).(size) in
        if (Nat.leb fsize pos) && ((negb (Nat.eqb pos O)) || (negb (Nat.eqb fsize O)))
        then return_ eInval
        else match write_to_virtual_memory buf pos fId fs.(f_map) fs.(virtual_memory) with
             | inr err => return_ err
             | inl (new_vm, new_f_map) =>
               let len := String.length buf in
               let pages := get_write_pages fId new_f_map new_vm pos len in
               let encrypted_pages := get_encrypted_buf pages new_vm in
               do err <- externalCall (Call_VLSeek fId (pos_to_vpage pos)) (v_lseek fId (pos_to_vpage pos));
                 if (isNotSucc err)
                 then return_ err
                 else
                   let new_len := pos_to_vlen pos len in
                   do err <- externalCall (Call_VWrite fId encrypted_pages new_len) (v_write fId encrypted_pages new_len);
                     if (isNotSucc err)
                     then return_ err
                     else
                       let new_open_handles := replace_handler fId (pos + len) fs.(open_handles) in
                       putOpenHandles new_open_handles >>
                                      putVirtualMemory new_vm >>
                                      putFMap (change_f_map_size new_f_map fId (max (new_f_map fId).(metaF).(size) (pos + len))) >>
                                      return_ eSucc
             end
      end.

  (* max (new_f_map fId).(metaF).(size) (pos + len) *)

  Definition size_changed (fId: Fid) (fs postFS: FSState) (pos len: nat): Prop :=
    ((fMapFS postFS) fId).(metaF).(size) = max (((fMapFS fs) fId).(metaF).(size)) (pos + len).

  Definition fs_seek (arg: fs_parameter 4) : State FSState (fs_result 4) :=
    let (fId, pos) := arg in
    do fs <- getFS;
      let opos := find (fun x => Nat.eqb (fst x) fId) fs.(open_handles) in
      match opos with
      | None => return_ eBadF
      | Some _ =>
        let fsize := (fs.(f_map) fId).(metaF).(size) in
        if (Nat.leb fsize pos) && ((negb (Nat.eqb pos O)) || (negb (Nat.eqb fsize O)))
        then return_ eInval
        else
          do err <- externalCall (Call_VLSeek fId (pos_to_vpage pos)) (v_lseek fId (pos_to_vpage pos));
          if (isNotSucc err)
          then return_ err
          else let new_open_handles := replace_handler fId pos fs.(open_handles) in
               putOpenHandles new_open_handles >>
                              return_ eSucc
      end.

  Fixpoint addFnodeToTree (tree: Tree) (did: Did) (fId: Fid) : Tree :=
    match tree with
    | Fnode _ => tree
    | Dnode did' li => if Nat.eq_dec did did'
                       then Dnode did (Fnode fId :: li)
                       else Dnode did' (map (fun t => addFnodeToTree t did fId) li)
    end.

  Compute (addFnodeToTree (addFnodeToTree (addFnodeToTree (addFnodeToTree sampleTree 9 5) 8 6) 0 7) 1 8).

  Definition get_next_free_fid : State FSState Fid :=
    fun x =>
      let (fs, logs) := x in
      (fs.(fnode_ctr), (Build_FileSystem fs.(layout) fs.(open_handles)
       fs.(virtual_memory) fs.(f_map) fs.(d_map) (fs.(fnode_ctr) + 1)
       fs.(dnode_ctr) fs.(mmap_handles) fs.(mmap_memory), logs)).

  Definition fs_create (arg: fs_parameter 5) : State FSState (fs_result 5) :=
    let (pf, p) := arg in
    let (path, fname) := pf in
    if string_dec fname EmptyString
    then return_ eBadName
    else
      do fs <- getFS;
      match findMatchedFid fs path fname with
      | Some _ => return_ eExists
      | None => match findDir fs.(d_map) fs.(layout) (app path (fname :: nil)) with
                | Some _ => return_ eIsDir
                | None => let parentdir := findDir fs.(d_map) fs.(layout) path in
                          match parentdir with
                          | None => return_ eNoDir
                          | Some tr => match tr with
                                       | Fnode _ => return_ eBadF
                                       | Dnode did li =>
                                         if bool_eq ((fs.(d_map) did).(metaD).(writable)) false
                                         then return_ eAcces
                                         else
                                           do err <- externalCall (Call_VCreate path fname p) (v_create path fname p);
                                           if (isNotSucc err)
                                           then return_ err
                                           else do newFId <- get_next_free_fid;
                                           let newFData := Build_FData fname (Build_Meta p O) nil in
                                           putFMap (change_f_map (fs.(f_map)) newFId newFData) >>
                                                   putLayout (addFnodeToTree fs.(layout) did newFId) >>
                                                   return_ eSucc
                                       end
                          end
                end
      end.

  Definition get_next_free_did : State FSState Did :=
    fun x =>
      let (fs, logs) := x in
      (fs.(dnode_ctr), (Build_FileSystem fs.(layout) fs.(open_handles)
       fs.(virtual_memory) fs.(f_map) fs.(d_map) fs.(fnode_ctr)
       (fs.(dnode_ctr) + 1) fs.(mmap_handles) fs.(mmap_memory), logs)).

  Definition putDMap: (Did -> DData) -> State FSState unit :=
    fun dmap x =>
      let (fs, logs) := x in
      (tt, (Build_FileSystem fs.(layout) fs.(open_handles) fs.(virtual_memory)
            fs.(f_map) dmap fs.(fnode_ctr) fs.(dnode_ctr) fs.(mmap_handles)
            fs.(mmap_memory), logs)).

  Definition change_d_map (dmap: Did -> DData) (dId : Did) (ddata: DData) : (Did -> DData) :=
    fun id : Did => if Nat.eq_dec id dId then ddata else dmap id.

  Definition change_d_map_permission (dmap: Did -> DData) (dId : Did) (p: Permission) : (Did -> DData) :=
    fun id : Did => if Nat.eq_dec id dId
                    then let dd := dmap id in (Build_DData dd.(nameD) p)
                    else dmap id.

  Fixpoint addDidToTree (tree: Tree) (did: Did) (child_did: Did) : Tree :=
    match tree with
    | Fnode _ => tree
    | Dnode did' li => if Nat.eq_dec did did'
                       then Dnode did (Dnode child_did nil :: li)
                       else Dnode did' (map (fun t => addDidToTree t did child_did) li)
    end.

  Definition fs_mkdir (arg: fs_parameter 6): State FSState (fs_result 6) :=
    let (pd, p) := arg in
    let (path, dname) := pd in
    if string_dec dname EmptyString
    then return_ eBadName
    else
      do fs <- getFS;
      match findMatchedFid fs path dname with
      | Some _ => return_ eNotDir
      | None => match findDir fs.(d_map) fs.(layout) (app path (dname :: nil)) with
                | Some _ => return_ eExists
                | None => let parentdir := findDir fs.(d_map) fs.(layout) path in
                          match parentdir with
                          | None => return_ eNoEnt
                          | Some tr => match tr with
                                       | Fnode _ => return_ eBadF
                                       | Dnode did li =>
                                         if bool_eq ((fs.(d_map) did).(metaD).(writable)) false
                                         then return_ eAcces
                                         else
                                           do err <- externalCall (Call_VMkdir path dname p) (v_mkdir path dname p);
                                           if (isNotSucc err)
                                           then return_ err
                                           else do newDid <- get_next_free_did;
                                           let newDData := Build_DData dname p in
                                           putDMap (change_d_map (fs.(d_map)) newDid newDData) >>
                                                   putLayout (addDidToTree fs.(layout) did newDid) >>
                                                   return_ eSucc
                                       end
                          end
                end
      end.

  Compute (fst (mkfs "root")).(layout).

  Compute let fss := (mkfs "root") in let fs := fst fss in findDir fs.(d_map) fs.(layout) [].

  Fixpoint removeDirFromList (trees: list Tree) (did: Did) : list Tree :=
    match trees with
    | nil => nil
    | (Dnode did' _) as x :: l => if Nat.eq_dec did' did then removeDirFromList l did else x :: removeDirFromList l did
    | x :: l => x :: removeDirFromList l did
    end.

  Fixpoint removeDirFromTree (tree: Tree) (parentDid : Did) (did: Did) : Tree :=
    match tree with
    | Fnode _ => tree
    | Dnode did' li => if Nat.eq_dec parentDid did'
                       then Dnode did' (removeDirFromList li did)
                       else Dnode did' (map (fun t => removeDirFromTree t parentDid did) li)
    end.

  Definition fs_rmdir (path: fs_parameter 7) : State FSState (fs_result 7) :=
    match path with
    | nil => return_ eInval
    | _ => do fs <- getFS;
             match findDir fs.(d_map) fs.(layout) path with
             | None => return_ eNoEnt
             | Some (Fnode _) => return_ eNoEnt
             | Some (Dnode did l) =>
               match l with
               | x :: l' => return_ eNotEmpty
               | nil => match findDir fs.(d_map) fs.(layout) (removelast path) with
                        | None => return_ eNoEnt
                        | Some (Fnode _) => return_ eNoEnt
                        | Some (Dnode parentId l') =>
                          match (fs.(d_map) parentId).(metaD).(writable) with
                          | false => return_ eAcces
                          | true =>
                            do err <- externalCall (Call_VRmdir path) (v_rmdir path);
                              (if isNotSucc err
                               then return_ err
                               else putDMap (change_d_map fs.(d_map) did (Build_DData EmptyString (Build_Permission false false false))) >>
                                            putLayout (removeDirFromTree fs.(layout) parentId did) >>
                                            return_ eSucc)
                          end
                        end
               end
             end
    end.

  Fixpoint removeFnodeFromList (trees : list Tree) (fId : Fid) : list Tree :=
    match trees with
    | nil => nil
    | Fnode f as x :: l => if Nat.eq_dec f fId
                           then removeFnodeFromList l fId
                           else x :: removeFnodeFromList l fId
    | x :: l => x :: removeFnodeFromList l fId
    end.

  Fixpoint removeFnodeFromTree (tree: Tree) (did: Did) (fId: Fid) : Tree :=
    match tree with
    | Fnode _ => tree
    | Dnode did' li => if Nat.eq_dec did did'
                       then Dnode did (removeFnodeFromList li fId)
                       else Dnode did' (map (fun t => removeFnodeFromTree t did fId) li)
    end.

  Definition fs_remove (arg: fs_parameter 8): State FSState (fs_result 8) :=
    let (path, fname) := arg in
    if string_dec fname ""
    then return_ eBadName
    else
      do fs <- getFS;
      match findMatchedFid fs path fname with
      | None => return_ eNoEnt
      | Some fId =>
        match findDir (d_map fs) (layout fs) path with
        | None => return_ eNotDir
        | Some (Fnode _) => return_ eBadF
        | Some (Dnode did _) =>
          if bool_eq (writable (metaD (d_map fs did))) false
          then return_ eAcces
          else
            do err <-
               externalCall (Call_VRemove path fname) (v_remove path fname);
            (if isNotSucc err
             then return_ err
             else
               (putFMap (change_f_map (f_map fs) fId (Build_FData EmptyString (Build_Meta (Build_Permission false false false) O) nil))) >>
                                                                                                                                         putLayout (removeFnodeFromTree (layout fs) did fId) >>
                                                                                                                                         return_ eSucc)
        end
      end.

  Definition foot (l: Path) : string := last l EmptyString.

  Definition fs_chmod (arg: fs_parameter 9) : State FSState (fs_result 9) :=
    let (path, p) := arg in
    do fs <- getFS;
      let flag := match findDir fs.(d_map) fs.(layout) path with
                  | Some (Fnode _) => None
                  | Some (Dnode did _) => Some (true, did)
                  | None => match path with
                            | nil => None
                            | _ => match findMatchedFid fs (removelast path) (foot path) with
                                   | None => None
                                   | Some fId => Some (false, fId)
                                   end
                            end
                  end in
      match flag with
      | None => return_ eNoEnt
      | Some (x, id) =>
        do err <- externalCall (Call_VChmod path p) (v_chmod path p);
          (if isNotSucc err
           then return_ err
           else match x with
                | true => putDMap (change_d_map_permission fs.(d_map) id p) >> return_ eSucc
                | false => putFMap (change_f_map_permission fs.(f_map) id p) >> return_ eSucc
                end)
      end.

  Definition fs_readdir (path: fs_parameter 10) : State FSState (fs_result 10) :=
    do fs <- getFS;
      match findDir fs.(d_map) fs.(layout) path with
      | None => return_ (nil, eBadF)
      | Some (Fnode _) => return_ (nil, eBadF)
      | Some (Dnode did l) =>
        do err <- externalCall (Call_VReadDir path) (v_readdir path);
          (if isNotSucc err
           then return_ (nil, err)
           else return_ (map (treeName fs.(f_map) fs.(d_map)) l, eSucc))
      end.

  Definition ttf : Permission := Build_Permission true true false.
  Definition fff : Permission := Build_Permission false false false.

  Definition fs_fstat (fId: fs_parameter 11): State FSState (fs_result 11) :=
    do fs <- getFS;
      do oh <- getOpenHandles;
      let opos := find (fun x => Nat.eqb (fst x) fId) oh in
      match opos with
      | None => return_ ((EmptyString, fff, O, nil), eBadF)
      | Some (_, pos) =>
        do err <- externalCall (Call_VStat fId) (v_stat fId);
          (if isNotSucc err
           then return_ ((EmptyString, fff, O, nil), err)
           else let fd := fs.(f_map) fId in
                return_ ((fd.(nameF), fd.(metaF).(permission), fd.(metaF).(size), fd.(pageIdsF)), eSucc))
      end.

  (* TODO: check the pointer in open handles *)

  Definition fs_truncate (arg: fs_parameter 12): State FSState (fs_result 12) :=
    let (fId, len) := arg in
    do fs <- getFS;
      match find (fun x : nat * nat => Nat.eqb (fst x) fId) (open_handles fs) with
      | None => return_ eBadF
      | Some _ =>
        let fsize := size (metaF (f_map fs fId)) in
        if (fsize <? len) && (negb (Nat.eqb len 0) || negb (Nat.eqb fsize 0))
        then return_ eInval
        else if (Nat.eqb fsize len)
             then return_ eSucc
             else let new_last_page := if Nat.eq_dec (len mod psize) O then len / psize else len / psize + 1 in
                  let last_page_content := encrypt_page (truncate_page (byte_list_to_string
                                                                          (nth (nth new_last_page (fs.(f_map) fId).(pageIdsF) O) fs.(virtual_memory) nil)) O (len mod psize)) in
                  let ext_write_pos := len / psize * block_size in
                  do err <- externalCall (Call_VTruncate fId ext_write_pos last_page_content) (v_truncate fId ext_write_pos last_page_content);
                  (if isNotSucc err
                   then return_ err
                   else putFMap (change_f_map_pages (change_f_map_size fs.(f_map) fId len) fId (getSublist O new_last_page (fs.(f_map) fId).(pageIdsF))) >>
                                return_ eSucc)
      end.

  Lemma mmap_mode_eq_dec: forall m1 m2: MmapMode, {m1 = m2} + {~ m1 = m2}.
  Proof. intros. destruct m1, m2; try (left; easy); try (right; easy). Qed.

  Fixpoint check_if_continuous (addrs: list Memid) : bool :=
    match addrs with
    | nil => true
    | n :: l' => match l' with
                 | nil => true
                 | m :: l'' => if Nat.eq_dec m (S n)
                               then check_if_continuous l'
                               else false
                 end
    end.

  Compute (check_if_continuous [2; 3; 4; 5; 6; 7]).

  Compute (check_if_continuous [2; 3; 4; 5; 6; 8]).

  Definition check_size (addr_len total_len: nat): bool :=
    if Nat.eq_dec addr_len O
    then false
    else if ge_dec (addr_len * block_size) total_len
         then if lt_dec ((pred addr_len) * block_size) total_len
              then true
              else false
         else false.

  Compute (check_size O 5).
  Compute (check_size 1 4000).

  Fixpoint check_range (addrs: list Memid) (len: nat): bool :=
    match addrs with
    | nil => true
    | x :: l => if lt_dec x len
                then check_range l len
                else false
    end.

  Compute (check_range [1;2;3;4;5] 6).
  Compute (check_range [1;2;3;4;5] 5).

  Definition write_zeroes (addrs: list Memid) (mem: MmapedMemory) : MmapedMemory :=
    match addrs with
    | nil => mem
    | x :: _ => let len := length addrs in
                app (app (firstn x mem) (repeat (repeat Ascii.zero block_size) len))
                    (skipn (x + len) mem)
    end.

  Definition interval_between (n start len: nat) : bool :=
    if le_dec start n then if lt_dec n (start + len) then true else false else false.

  Definition interval_overlap (s1 len1 s2 len2: nat): bool :=
    interval_between s1 s2 len2 || interval_between s2 s1 len1.

  Fixpoint check_overlap (start: Memid) (addrs_len: nat)
           (handles: list (Memid * nat * Permission)): bool :=
    match handles with
    | nil => false
    | ((s2, t_len), _) :: l =>
      if interval_overlap start addrs_len s2 (pad_size t_len)
      then true
      else check_overlap start addrs_len l
    end.

  Definition mmap (len: nat) (perm: Permission) (flag: MmapMode):
    State FSState (Memid * ErrCode):=
    do fs <- getFS;
      if mmap_mode_eq_dec flag mapAnon
      then let mem := mmap_memory fs in
           do mmap_address <- externalCall (Call_AllocMem mem len)
              (allocate_memory mem len);
             let addrs_len := length mmap_address in
             let head_addr := hd O mmap_address in
             if check_if_continuous mmap_address &&
                check_size addrs_len len &&
                check_range mmap_address (length mem) &&
                negb (check_overlap head_addr addrs_len (mmap_handles fs))
             then putMmapMemory (write_zeroes mmap_address mem) >>
                  putMmapHandles ((head_addr, len, perm) :: (mmap_handles fs)) >>
                  return_ (head_addr, eSucc)
           else return_ (O, eMapFailed)
      else return_ (O, eMapFailed).

  Definition neqMmapHandle (mid: Memid) (len: nat)
             (h: Memid * nat * Permission) : bool :=
    match h with | (s, lens, _) => negb (Nat.eqb mid s) || negb (Nat.eqb len lens) end.

  Definition munmap (mid: Memid) (len: nat): State FSState ErrCode :=
    do fs <- getFS;
      if forallb (neqMmapHandle mid len) (mmap_handles fs)
      then return_ eInval
      else let mem := mmap_memory fs in
           do succ <- externalCall (Call_DeallocMem mem mid len)
              (deallocate_memory mem mid len);
             if succ
             then putMmapHandles (filter (neqMmapHandle mid len) (mmap_handles fs)) >>
                  return_ eSucc
             else return_ eInval.

  Definition newFS1 : FSState := snd (fs_create ([], "foo.txt", ttf) (mkfs "root")).

  (* Compute (fs_create [] "bar.txt" ttf newFS1). *)

  Lemma find_Fid_In: forall (l: list (Fid * nat)) fId p,
      find (fun x : nat * nat => Nat.eqb (fst x) fId) l = Some p -> In fId (map fst l).
  Proof.
    induction l; intros; simpl in *. 1: inversion H.
    destruct (Nat.eqb (@fst nat nat a) fId) eqn: ?; [left | right].
    - rewrite Nat.eqb_eq in Heqb. auto.
    - apply (IHl _ p); auto.
  Qed.

  Lemma find_Fid_In': forall (l: list (Fid * nat)) fId p,
      find (fun x : nat * nat => Nat.eqb (fst x) fId) l = Some p -> In p l /\ fst p = fId.
  Proof.
    induction l; intros; simpl in *. 1: inversion H.
    destruct (Nat.eqb (@fst nat nat a) fId) eqn: ?.
    - inversion H. subst a. rewrite Nat.eqb_eq in Heqb. intuition.
    - specialize (IHl _ _ H). intuition.
  Qed.

  Lemma find_Fid_None: forall (l : list (Fid * nat)) fId,
      In fId (map fst l) -> find (fun x  => Nat.eqb (fst x) fId) l = None -> False.
  Proof.
    induction l; intros; simpl in *; auto.
    destruct (Nat.eqb (@fst nat nat a) fId) eqn: ?. 1: inversion H0. destruct H.
    - rewrite Nat.eqb_neq in Heqb. auto.
    - apply (IHl fId); auto.
  Qed.

  Lemma fs_close_not_found: forall fId (fs: FSState) err postFS,
      ~ In fId (map fst (openhandleFS fs)) -> (err, postFS) = (fs_close fId fs) ->
      postFS = fs /\ err = eBadF.
  Proof.
    intros. destruct fs. unfold fs_close in H0. destruct f eqn:?. simpl in H0.
    destruct (find (fun x : nat * nat => Nat.eqb (fst x) fId) open_handles0) eqn:?.
    - exfalso. clear H0. unfold openhandleFS in H. unfold open_handles in H.
      simpl in H. apply H. apply (find_Fid_In _ _ p); auto.
    - inversion H0. auto.
  Qed.

  Ltac rm_if := match goal with | [ |- context [if ?A then _ else _]] =>
                                  destruct A; auto end.

  Ltac rm_if_eqn := match goal with | [ |- context [if ?A then _ else _]] =>
                                      destruct A eqn: ?; auto end.

  Ltac rm_hif := match goal with |[_ : context [if ?A then _ else _] |- _ ] =>
                                  destruct A end.

  Ltac rm_hif_eqn H := match goal with |[H : context [if ?A then _ else _] |- _ ] =>
                                        destruct A eqn:? end.

  Ltac rm_hmatch := match goal with
                    |[_ : context [match ?A with | _ => _ end] |- _ ] =>
                     destruct A eqn:? end.

  Lemma find_Fid_remove: forall (l: list (Fid * nat)) p fId,
      NoDup (map fst l) -> find (fun x : nat * nat => Nat.eqb (fst x) fId) l = Some p ->
      ~ In fId (map fst (remove (prod_dec Nat.eq_dec Nat.eq_dec) p l)).
  Proof.
    induction l; intros; simpl in *. 1: inversion H0. rm_hmatch.
    - inversion H0. subst a. clear H0. rewrite Nat.eqb_eq in Heqb. rm_if.
      rewrite NoDup_cons_iff in H. destruct H. subst fId. intro. apply H. clear -H1.
      induction l; simpl in *; auto. rm_hif.
      + subst. left; auto.
      + simpl in H1. destruct H1; [left | right; apply IHl]; auto.
    - rewrite NoDup_cons_iff in H. destruct H. specialize (IHl _ _ H1 H0).
      rm_if. simpl map. intro; apply IHl. simpl in H2. destruct H2; auto.
      subst fId. exfalso. rewrite Nat.eqb_neq in Heqb. apply Heqb; auto.
  Qed.

  Lemma remove_not_in {A: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}):
    forall l x, ~ In x l -> remove eq_dec x l = l.
  Proof.
    induction l; intros; simpl; auto. destruct (eq_dec x a). subst.
    exfalso; apply H, in_eq. f_equal. apply IHl. intro; apply H. apply in_cons. auto.
  Qed.

  Lemma find_Fid_Permutation: forall (l: list (Fid * nat)) p fId,
      NoDup (map fst l) -> find (fun x : nat * nat => Nat.eqb (fst x) fId) l = Some p ->
      Permutation (map fst l)
                  (fId :: map fst (remove (prod_dec Nat.eq_dec Nat.eq_dec) p l)).
  Proof.
    induction l; intros; simpl in *. 1: inversion H0. rm_hmatch.
    - inversion H0. subst a. clear H0. rewrite Nat.eqb_eq in Heqb. rm_if.
      2: exfalso; apply n; reflexivity. unfold Fid in *. rewrite Heqb. constructor.
      rewrite NoDup_cons_iff in H. destruct H.
      assert (~ In p l) by (intro; apply H; apply (in_map fst) in H1; assumption).
      pose proof (remove_not_in (prod_dec Nat.eq_dec Nat.eq_dec) _ _ H1).
      rewrite H2. reflexivity.
    - rewrite NoDup_cons_iff in H. destruct H. specialize (IHl _ _ H1 H0). rm_if.
      + exfalso. apply Nat.eqb_neq in Heqb. apply find_Fid_In' in H0.
        destruct H0. subst p. auto.
      + simpl.
        transitivity (fst a :: fId ::
                          map fst (remove (prod_dec Nat.eq_dec Nat.eq_dec) p l)).
        2: constructor. constructor. assumption.
  Qed.

  (* We need a stronger condition for open_handles *)
  Lemma fs_close_found: forall fId (fs: FSState) err postFS,
      NoDup (map fst (openhandleFS fs)) ->
      In fId (map fst (openhandleFS fs)) ->
      v_close fId (counter fs) = eSucc ->
      (err, postFS) = (fs_close fId fs) ->
      (~ In fId (map fst (openhandleFS postFS))) /\
      layoutFS fs = layoutFS postFS /\
      vmFS fs = vmFS postFS /\
      fMapFS fs = fMapFS postFS /\
      dMapFS fs = dMapFS postFS /\
      err = eSucc.
  Proof.
    intros. destruct fs. unfold counter, openhandleFS,
                         layoutFS, vmFS, fMapFS, dMapFS in *.
    simpl in *. rename H2 into Heqp. unfold fs_close in Heqp.
    destruct f eqn:?. simpl in *.
    destruct (find (fun x : nat * nat => Nat.eqb (fst x) fId) open_handles0) eqn:?.
    - unfold externalCall in Heqp.
      destruct (v_close fId (Datatypes.length l)) eqn: ?; [|inversion H1..].
      unfold putOpenHandles in Heqp. inversion Heqp. split; [|intuition]. simpl.
      apply find_Fid_remove; auto.
    - exfalso. apply (find_Fid_None open_handles0 fId); auto.
  Qed.

  Lemma fs_close_failed: forall fId (fs: FSState) v_err err postFS,
      In fId (map fst (openhandleFS fs)) ->
      v_err = v_close fId (counter fs) -> v_err <> eSucc ->
      (err, postFS) = fs_close fId fs -> err = v_err /\ fst fs = fst postFS.
  Proof.
    intros. destruct fs. rename H2 into Heqp. unfold fs_close in Heqp. simpl in *.
    destruct (find (fun x : nat * nat => Nat.eqb (fst x) fId) f.(open_handles)) eqn:?.
    - unfold externalCall in Heqp. unfold counter in H0.
      simpl in H0. destruct postFS. simpl.
      destruct (v_close fId (Datatypes.length l)) eqn:? ;
        [exfalso; intuition| subst v_err; inversion Heqp; auto..].
    - exfalso. destruct f eqn:? . unfold openhandleFS in H. unfold open_handles in *.
      simpl in *. apply (find_Fid_None open_handles0 fId); auto.
  Qed.

  Lemma fs_close_ok: forall fId (fs: FSState) err postFS,
       good_file_system (fsFS fs) ->
      (err, postFS) = fs_close fId fs ->
      (~ In fId (map fst (openhandleFS fs)) /\ postFS = fs /\ err = eBadF) \/
      (In fId (map fst (openhandleFS fs)) /\ (~ In fId (map fst (openhandleFS postFS)))
       /\ (Permutation (map fst (openhandleFS fs))
                       (fId :: map fst (openhandleFS postFS))) /\
       layoutFS fs = layoutFS postFS /\ vmFS fs = vmFS postFS /\
       fMapFS fs = fMapFS postFS /\ dMapFS fs = dMapFS postFS /\ err = eSucc /\
       fnode_ctr (fsFS fs) = fnode_ctr (fsFS postFS) /\
       dnode_ctr (fsFS fs) = dnode_ctr (fsFS postFS) /\
       mmap_handles (fsFS fs) = mmap_handles (fsFS postFS) /\
       mmap_memory (fsFS fs) = mmap_memory (fsFS postFS) /\
       logFS postFS = Call_VClose fId eSucc :: logFS fs) \/
      (In fId (map fst (openhandleFS fs)) /\ err <> eSucc /\ fst fs = fst postFS /\
       logFS postFS = Call_VClose fId err :: logFS fs).
  Proof.
    intros. unfold fs_close in H0. simpl in H0. rm_hmatch.
    - right. pose proof Heqo. apply find_Fid_In in Heqo. destruct fs.
      simpl in H0. rm_hmatch; [|right; inversion H0; simpl; intuition; inversion H2..].
      left. simpl in H0. inversion H0.
      unfold openhandleFS, layoutFS, vmFS, fMapFS, dMapFS, logFS. simpl.
      split; [|split; [|split; [|split; [|split; [|split; [|split;[|split]]]]]]]; auto.
      * apply find_Fid_remove; auto. destruct H. intuition.
      * simpl fst in H1. destruct H as [_ [_ [_ [_ [_ [? _]]]]]]. simpl in *.
        apply find_Fid_Permutation; assumption.
    - left. inversion H0. intuition. eapply find_Fid_None; eauto.
  Qed.

  Lemma fs_read_not_found: forall fId len (fs: FSState) err buf postFS,
      ~ In fId (map fst (openhandleFS fs)) ->
      (buf, err, postFS) = (fs_read (fId, len) fs) -> postFS = fs /\ err = eBadF.
  Proof.
    intros. destruct fs. unfold fs_read in H0. destruct f eqn:?. simpl in H0.
    destruct (find (fun x : nat * nat => Nat.eqb (fst x) fId) open_handles0) eqn:?.
    - exfalso. clear H0. unfold openhandleFS in H. unfold open_handles in H.
      simpl in H. apply H. apply (find_Fid_In _ _ p); auto.
    - inversion H0. auto.
  Qed.

  Lemma replace_handler_preserve_fst: forall l fId pos,
      map fst (replace_handler fId pos l) = map fst l.
  Proof.
    induction l; intros; simpl; auto. destruct a.
    destruct (Nat.eq_dec fId f); simpl; auto. f_equal. apply IHl.
  Qed.

  Lemma replace_handler_replaces: forall l fId pos1 pos2,
      In (fId, pos1) l -> In (fId, pos2) (replace_handler fId pos2 l).
  Proof.
    induction l; intros; simpl; auto. destruct a. simpl in H. destruct H.
    - inversion H. subst f. subst n. destruct (Nat.eq_dec fId fId).
      2: exfalso; apply n; auto. left; auto.
    - destruct (Nat.eq_dec fId f). 1: subst f; left; auto. right.
      apply (IHl _ pos1); auto.
  Qed.

  Lemma In_find_fId_the_same: forall (l: list (Fid * nat)) fId p1 p2,
      NoDup (map fst l) -> In (fId, p1) l -> In (fId, p2) l -> p1 = p2.
  Proof.
    induction l; intros; simpl in *. 1: exfalso; auto. destruct H0, H1.
    - rewrite H1 in H0. inversion H0; auto.
    - subst a. simpl in H. apply (in_map fst) in H1. simpl in H1.
      rewrite NoDup_cons_iff in H. destruct H. exfalso; auto.
    - subst a. simpl in H. apply (in_map fst) in H0. simpl in H0.
      rewrite NoDup_cons_iff in H. destruct H. exfalso; auto.
    - simpl in H. apply NoDup_cons_iff in H. destruct H. apply (IHl fId); auto.
  Qed.

  Lemma fs_read_ok: forall fId len (fs: FSState) err buf postFS,
      (buf, err, postFS) = (fs_read (fId, len) fs) ->
      NoDup (map fst (openhandleFS fs)) ->
      (~ In fId (map fst (openhandleFS fs)) /\ postFS = fs /\ err = eBadF) \/
      (exists pos, In (fId, pos) (openhandleFS fs) /\ (pos + len) >= (fMapFS fs fId).(metaF).(size) /\
                   postFS = fs /\ err = eInval) \/
      (In fId (map fst (openhandleFS fs)) /\ buf = "" /\ err <> eSucc /\
       fsFS postFS = fsFS fs /\
       exists p1 p2 vlseek_ret,
         hd_error (logFS postFS) = Some (Call_VLSeek p1 p2 vlseek_ret) /\
         err = vlseek_ret /\
         logFS postFS = Call_VLSeek p1 p2 vlseek_ret :: logFS fs) \/
      (In fId (map fst (openhandleFS fs)) /\ buf = "" /\ fsFS postFS = fsFS fs /\
       exists vread_ret p1 p2,
         err = snd vread_ret /\
         hd_error (logFS postFS) = Some (Call_VRead p1 p2 vread_ret) /\
         snd vread_ret <> eSucc /\
         exists p3 p4, logFS postFS =
                       Call_VRead p1 p2 vread_ret ::
                                  Call_VLSeek p3 p4 eSucc :: logFS fs) \/
      (In fId (map fst (openhandleFS fs)) /\ buf = "" /\ fsFS postFS = fsFS fs /\
       err = eBadPage /\
       exists vread_ret p1 p2,
         hd_error (logFS postFS) = Some (Call_VRead p1 p2 vread_ret) /\
         snd vread_ret = eSucc /\
         exists p3 p4,
           logFS postFS = Call_VRead p1 p2 vread_ret ::
                                     Call_VLSeek p3 p4 eSucc :: logFS fs) \/
      (In fId (map fst (openhandleFS fs)) /\ err = eSucc /\ String.length buf = len /\
       layoutFS fs = layoutFS postFS /\ vmFS fs = vmFS postFS /\
       fMapFS fs = fMapFS postFS /\
       dMapFS fs = dMapFS postFS /\
       fnode_ctr (fsFS fs) = fnode_ctr (fsFS postFS) /\
       dnode_ctr (fsFS fs) = dnode_ctr (fsFS postFS) /\
       mmap_handles (fsFS fs) = mmap_handles (fsFS postFS) /\
       mmap_memory (fsFS fs) = mmap_memory (fsFS postFS) /\
       map fst (openhandleFS postFS) = map fst (openhandleFS fs) /\
       (forall pos, In (fId, pos) (openhandleFS fs) ->
                    In (fId, pos + len) (openhandleFS postFS)) /\
       exists vread_ret p1 p2,
         hd_error (logFS postFS) = Some (Call_VRead p1 p2 vread_ret) /\
         snd vread_ret = eSucc /\
         exists p3 p4, logFS postFS = Call_VRead p1 p2 vread_ret ::
                                                 Call_VLSeek p3 p4 eSucc :: logFS fs).
  Proof.
    intros. destruct (in_dec Nat.eq_dec fId (map fst (openhandleFS fs))).
    - right. pose proof H. unfold fs_read in H1. simpl in H1. rm_hmatch.
      + destruct p as [? pos]. destruct fs. simpl in H1. rm_hif.
        * left. exists pos. inversion H1. intuition. apply find_Fid_In' in Heqo.
          destruct Heqo. simpl in H6. subst n. auto.
        * right. simpl in H1. rm_hif.
          -- left. inversion H1. simpl. split; [|split; [|split; [|split]]]; auto.
          exists fId, (pos_to_vpage pos),
          (v_lseek fId (pos_to_vpage pos) (Datatypes.length l)). intuition.
          -- simpl in H1. right.
             destruct (v_read fId (pos_to_vlen pos len) (S (Datatypes.length l))) as
                 [str errR]. destruct (isNotSucc errR) eqn: ?.
             ++ left. inversion H1. simpl in *. split; [|split; [|split]]; auto.
                exists (str, errR), fId, (pos_to_vlen pos len). simpl.
                split; [|split; [|split]]; auto. exists fId, (pos_to_vpage pos).
                rewrite <- e. auto.
             ++ right. destruct (verify_page (decrypt_page str)).
                ** right. simpl in H1. inversion H1. destruct f. simpl.
                   unfold openhandleFS, layoutFS, vmFS, fMapFS, dMapFS, logFS, snd.
                   simpl.
                   split; [|split; [|split; [|split; split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]]; auto.
                   --- rewrite truncate_page_length; intuition.
                   --- simpl. rewrite replace_handler_preserve_fst; auto.
                   --- unfold open_handles in *. unfold openhandleFS in *. simpl in *.
                       intros. clear -Heqo H0 H2. apply find_some in Heqo.
                       destruct Heqo. rewrite Nat.eqb_eq in H1. simpl in H1. subst n.
                       assert (pos = pos0) by (eapply In_find_fId_the_same; eauto).
                       subst pos0. apply (replace_handler_replaces _ _ pos); auto.
                   --- exists (str, errR), fId, (pos_to_vlen pos len).
                       split; [|split]; auto. rewrite e.
                       exists fId, (pos_to_vpage pos); auto.
                ** left. inversion H1. simpl in *.
                   split; [|split; [|split; [|split]]]; auto.
                   exists (str, errR), fId, (pos_to_vlen pos len). simpl.
                   split; [|split]; auto. exists fId, (pos_to_vpage pos). rewrite e. auto.
      + exfalso. unfold openhandleFS in i. destruct fs. destruct f.
        unfold open_handles in *. simpl in *. eapply find_Fid_None; eauto.
    - left. split; auto. eapply fs_read_not_found; eauto.
  Qed.

  Lemma collectBareFids_app: forall l1 l2,
      collectBareFids (l1 ++ l2) = (collectBareFids l1 ++ collectBareFids l2)%list.
  Proof.
    induction l1; intros; simpl; auto. destruct a. 2: apply IHl1.
    simpl. rewrite IHl1. auto.
  Qed.

  Lemma find_app_not_in: forall {A} (f: A -> bool) l1 l2,
      (forall x, In x l1 -> f x = false) -> find f (l1 ++ l2) = find f l2.
  Proof.
    intros. induction l1; simpl; auto. destruct (f a) eqn: ?.
    - assert (In a (a :: l1)) by (simpl; intuition). specialize (H a H0).
      rewrite H in Heqb. inversion Heqb.
    - apply IHl1. intros. apply H. simpl; intuition.
  Qed.

  Lemma findFids_the_same: forall fmap dmap d l d' l' dname path,
      NoDupNameTree fmap dmap (Dnode d l) -> In (Dnode d' l') l ->
      nameD (dmap d') = dname ->
      findFids dmap (Dnode d' l') path = findFids dmap (Dnode d l) (dname :: path).
  Proof.
    intros. unfold findFids.
    cut (findDir dmap (Dnode d' l') path = findDir dmap (Dnode d l) (dname :: path)).
    1: intro S; rewrite S; auto. simpl.
    cut (find (fun x : Tree => root_eq dmap x dname) l = Some (Dnode d' l')).
    1: intro S; rewrite S; auto. inversion H. clear -H0 H1 H7. apply in_split in H0.
    destruct H0 as [l1 [l2 ?]]. subst l. rewrite find_app_not_in.
    - simpl. unfold DData_eqb. rewrite H1. destruct (string_dec dname dname); auto.
      exfalso; apply n; auto.
    - rewrite map_app, map_cons in H7. apply NoDup_remove_2 in H7.
      unfold treeName in H7 at 1. rewrite H1 in H7. rewrite in_app_iff in H7.
      intros. unfold root_eq. destruct x; auto. unfold DData_eqb. rm_if. exfalso.
      apply H7. left. apply in_split in H. destruct H as [l3 [l4 ?]]. clear H7.
      subst l1. rewrite map_app, map_cons.
      rewrite in_app_iff. right. left. unfold treeName. auto.
  Qed.

  Lemma file_in_tree_with_id_eq: forall fmap dmap name tree path,
      file_in_tree fmap dmap path name tree <->
      exists fid, file_in_tree_with_id fmap dmap path name tree fid.
  Proof.
    intros fmap dmap name. induction tree using tree_ind2; intros.
    1: split; intros; [|destruct H]; inversion H. rewrite Forall_forall in H.
    destruct path.
    - split; intro; [|destruct H0 as [fId ?]]; inversion H0; subst.
      + rewrite Exists_exists in H4. destruct H4. destruct H1. inversion H2.
        subst. exists fId. constructor; auto.
      + constructor. rewrite Exists_exists. exists (Fnode fId).
        split; auto. constructor; auto.
    - split; intro; [|destruct H0 as [fId ?]]; inversion H0;
        subst; [|rename H7 into H4]; destruct H4 as [did' [treeL' [? [? ?]]]].
      + rewrite H in H3; auto. destruct H3 as [fId ?]. exists fId. constructor.
        exists did', treeL'. intuition.
      + constructor. exists did', treeL'. intuition. rewrite H; auto. exists fId; auto.
  Qed.

  Lemma file_in_tree_none : forall fs path fname,
      NoDupNameTree (f_map fs) (d_map fs) (layout fs) ->
      findMatchedFid fs path fname = None ->
      ~ file_in_tree (f_map fs) (d_map fs) path fname (layout fs).
  Proof.
    intros fs. unfold findMatchedFid. remember (layout fs). clear Heqt. revert fs.
    induction t using tree_ind2; repeat intro. 1: inversion H1. destruct path.
    - inversion H2. subst fname0 root treeL0. rewrite Exists_exists in H6.
      destruct H6 as [? [? ?]]. inversion H4. subst fname0 x.
      pose proof (find_none _ _ H1 fId). simpl in H6. unfold fdata_eqb in H6.
      rewrite H5 in H6.
      assert (In fId (findFids (d_map fs) (Dnode did treeL) [])). {
        unfold findFids. simpl. apply in_split in H3. destruct H3 as [l1 [l2 ?]].
        rewrite H3. rewrite collectBareFids_app. simpl.
        rewrite in_app_iff. right. left. auto.
      } specialize (H6 H7). rm_hif; intuition.
    - inversion H2. subst s dlist fname0 root treeL0.
      destruct H6 as [did' [treeL' [? [? ?]]]]. rewrite Forall_forall in H.
      specialize (H _ H3 fs path fname). apply H; auto.
      + inversion H0. rewrite Forall_forall in H10. apply H10; auto.
      + rewrite <- H1. f_equal. apply findFids_the_same with (fmap := f_map fs); auto.
  Qed.

  Lemma file_in_tree_with_id_none : forall fs path fname id,
      NoDupNameTree (f_map fs) (d_map fs) (layout fs) ->
      findMatchedFid fs path fname = None ->
      ~ file_in_tree_with_id (f_map fs) (d_map fs) path fname (layout fs) id.
  Proof.
    intros. apply (file_in_tree_none fs path fname) in H0; auto.
    intro; apply H0. rewrite file_in_tree_with_id_eq. exists id; auto.
  Qed.

  Lemma collectBareFids_In: forall id l, In id (collectBareFids l) -> In (Fnode id) l.
  Proof.
    intros. induction l; simpl in *; auto.
    destruct a; [simpl in H; destruct H; [subst f; left | right; apply IHl] |
                 right; apply IHl]; auto.
  Qed.

  Lemma file_in_tree_with_id_some : forall fs path fname id,
      NoDupNameTree (f_map fs) (d_map fs) (layout fs) ->
      findMatchedFid fs path fname = Some id ->
      file_in_tree_with_id (f_map fs) (d_map fs) path fname (layout fs) id.
  Proof.
    intros fs. unfold findMatchedFid. remember (layout fs). clear Heqt.
    revert fs. induction t using tree_ind2; intros.
    - assert (findFids (d_map fs) (Fnode fid) path = []) by
          (unfold findFids; destruct path; simpl; auto).
      rewrite H1 in H0. simpl in H0. inversion H0.
    - destruct path; pose proof H1; apply find_some in H1; destruct H1;
        unfold fdata_eqb in H3; rm_hif; inversion H3; unfold findFids in H1;
          simpl in H1; constructor; auto.
      + apply collectBareFids_In; auto.
      + destruct (find (fun x : Tree => root_eq (d_map fs) x s) treeL) eqn:? .
        2: inversion H1. apply find_some in Heqo. destruct Heqo.
        unfold root_eq in H5. destruct t.
        1: inversion H5. unfold DData_eqb in H5. rm_hif. 2: inversion H5. clear H3 H5.
        exists d, l. intuition. rewrite Forall_forall in H. apply H; auto.
        * inversion H0. rewrite Forall_forall in H8. apply H8; auto.
        * rewrite <- H2. f_equal.
          apply findFids_the_same with (fmap := f_map fs); auto.
  Qed.

  Lemma file_in_tree_some : forall fs path fname id,
      NoDupNameTree (f_map fs) (d_map fs) (layout fs) ->
      findMatchedFid fs path fname = Some id ->
      file_in_tree (f_map fs) (d_map fs) path fname (layout fs).
  Proof.
    intros. pose proof (file_in_tree_with_id_some fs _ _ _ H H0).
    rewrite file_in_tree_with_id_eq. exists id; auto.
  Qed.

  Lemma fs_open_ok: forall path fname fs fId err postFS,
      (fId, err, postFS) = (fs_open (path, fname) fs) ->
      NoDup (map fst (openhandleFS fs)) ->
      NoDupNameTree (fMapFS fs) (dMapFS fs) (layoutFS fs) ->
      (~ file_in_tree (fMapFS fs) (dMapFS fs) path fname (layoutFS fs) /\
       fId = O /\ err = eBadF /\ fs = postFS) \/
      (file_in_tree (fMapFS fs) (dMapFS fs) path fname (layoutFS fs) /\
       In fId (map fst (openhandleFS fs)) /\ err = eBadF /\ fs = postFS) \/
      (file_in_tree (fMapFS fs) (dMapFS fs) path fname (layoutFS fs) /\
       ~ In fId (map fst (openhandleFS fs)) /\ fst fs = fst postFS /\ err <> eSucc /\
       (exists p errR,
           hd_error (logFS postFS) = Some (Call_VOpen path p errR) /\
           err = errR /\ logFS postFS = Call_VOpen path p errR :: logFS fs)) \/
      (file_in_tree (fMapFS fs) (dMapFS fs) path fname (layoutFS fs) /\
       ~ In fId (map fst (openhandleFS fs)) /\ err = eSucc /\
       layoutFS fs = layoutFS postFS /\ vmFS fs = vmFS postFS /\
       fMapFS fs = fMapFS postFS /\ dMapFS fs = dMapFS postFS /\
       fnode_ctr (fsFS fs) = fnode_ctr (fsFS postFS) /\
       dnode_ctr (fsFS fs) = dnode_ctr (fsFS postFS) /\
       mmap_handles (fsFS fs) = mmap_handles (fsFS postFS) /\
       mmap_memory (fsFS fs) = mmap_memory (fsFS postFS) /\
       openhandleFS postFS = (fId, 0) :: openhandleFS fs /\
       NoDup (map fst (openhandleFS postFS)) /\
       (hd_error (logFS postFS) = Some (Call_VOpen path fname eSucc) /\
        logFS postFS = Call_VOpen path fname eSucc :: logFS fs)).
  Proof.
    intros. unfold fs_open in H. simpl in H.
    destruct (findMatchedFid (fst fs) path fname) eqn: ?.
    - right; rm_hmatch.
      + left. inversion H. split; [|split; [|split]]; auto.
        * eapply file_in_tree_some; eauto.
        * eapply find_Fid_In; eauto.
      + right. destruct fs. simpl in H.
        assert (file_in_tree (fMapFS (f0, l)) (dMapFS (f0, l))
                             path fname (layoutFS (f0, l))) by
            (eapply file_in_tree_some; eauto).
        assert (~ In fId (map fst (openhandleFS (f0, l)))). {
          intro. destruct f0. unfold openhandleFS in *. simpl in *.
          assert (f = fId) by (destruct (v_open path fname (Datatypes.length l)); inversion H; auto). subst f. eapply find_Fid_None; eauto.
        } simpl. destruct (v_open path fname (Datatypes.length l)) eqn:? ;
                   [right; split; [|split]; auto |
                    left; split; [|split]; auto; inversion H; simpl;
                    intuition; [inversion H4 | exists fname, err; subst err; auto]..].
        simpl in H. inversion H. destruct f0.
        unfold openhandleFS, layoutFS, vmFS, fMapFS, dMapFS, logFS, snd in *.
        simpl in *. intuition. constructor; [subst f; intro; apply H3 |]; auto.
    - left. inversion H. intuition. eapply file_in_tree_none; eauto.
  Qed.

  Lemma f_map_append_page_preserve: forall fmap fId page id,
      id <> fId -> fmap id = f_map_append_page fmap fId page id.
  Proof. intros. unfold f_map_append_page. rm_if. exfalso; auto. Qed.

  Lemma write_to_virtual_memory_unfold:
    forall (buf: string) (pos: nat) (fId: Fid) (fmap: Fid -> FData) (vm: list Page),
      write_to_virtual_memory buf pos fId fmap vm =
      if string_dec buf EmptyString
      then inl (vm, fmap)
      else let len := String.length buf in
           let new_vm := vm in
           let new_map := fmap in
           let pg_offset := pos mod psize in
           let pgn := if Nat.eq_dec pg_offset O then pos / psize + 1 else pos / psize in
           let vpg := nth pgn (fmap fId).(pageIdsF) memory_upper_bound in
           let vpg_ret := if Bool.bool_dec (andb (Nat.eqb vpg memory_upper_bound) (Nat.eqb pg_offset O)) true then (get_next_free_vpg new_map, true) else (vpg, false) in
           let vpg := fst vpg_ret in
           if Nat.eq_dec vpg memory_upper_bound
           then inr eNoSpc
           else if le_dec memory_upper_bound vpg
                then inr eInval
                else let new_map := if Sumbool.sumbool_of_bool (snd vpg_ret) then f_map_append_page new_map fId vpg else new_map in
                     let curr_page_cont := nth vpg new_vm nil in
                     let b1 := substring 0 (psize - pg_offset) buf in
                     let buf := substring (psize - pg_offset) (len - (psize - pg_offset)) buf in
                     let new_curr_pg_cont := override curr_page_cont pg_offset (string_to_byte_list b1) in
                     let new_vm := upd_nth new_vm vpg new_curr_pg_cont in
                     let pos := pos + psize - pg_offset in
                     write_to_virtual_memory buf pos fId new_map new_vm.
  Proof.
    intros. unfold write_to_virtual_memory at 1. rewrite Fix_eq. 1: rm_if.
    intros; assert (f = g) by (extensionality y; extensionality p; auto); subst; auto.
  Qed.

  Lemma write_to_virtual_memory_err: forall a b c d e f,
      write_to_virtual_memory a b c d e = inr f -> f = eNoSpc \/ f = eInval.
  Proof.
    intros a. remember (String.length a). assert (String.length a <= n) by omega.
    clear Heqn. revert a H. induction n; intros.
    - destruct a. rewrite write_to_virtual_memory_unfold in H0.
      destruct (string_dec "" ""); [inversion H0 | exfalso; apply n; auto].
      simpl in H. exfalso; omega.
    - rewrite write_to_virtual_memory_unfold in H0. destruct (string_dec a "").
      1: inversion H0. cbv zeta in H0. rm_hif. 1: inversion H0; left; auto.
      rm_hif. 1: inversion H0; right; auto. apply IHn in H0; auto.
      transitivity (String.length a - (psize - b mod psize)).
      1: apply substring_length.
      clear -H. cut (0 < psize - b mod psize). 1: intros; omega.
      cut (b mod psize < psize). 1: intros; omega. apply Nat.mod_upper_bound.
      compute; omega.
  Qed.

  Lemma write_to_virtual_memory_fmap:
    forall (buf: string) (pos: nat) (fId: Fid) (fmap: Fid -> FData)
           (vm: list Page) new_fmap new_vm,
      write_to_virtual_memory buf pos fId fmap vm = inl (new_vm, new_fmap) ->
      forall id, id <> fId -> fmap id = new_fmap id.
  Proof.
    intros buf. remember (String.length buf).
    assert (String.length buf <= n) by omega; clear Heqn.
    revert buf H. induction n; intros.
    - destruct buf. 2: simpl in H; exfalso; omega.
      rewrite write_to_virtual_memory_unfold in H0. rm_hif. inversion H0.
      subst; auto. exfalso; apply n; auto.
    - rewrite write_to_virtual_memory_unfold in H0. rm_hif.
      1: inversion H0; subst; auto. cbv zeta in H0. rm_hif. 1: inversion H0. rm_hif.
      1: inversion H0. apply IHn with (id := id) in H0; auto.
      + rm_hif; auto. rewrite <- H0. clear -H1. apply f_map_append_page_preserve; auto.
      + transitivity (String.length buf - (psize - pos mod psize)).
        1: apply substring_length. clear -H. cut (0 < psize - pos mod psize).
        1: intros; omega. cut (pos mod psize < psize). 1: intros; omega.
        apply Nat.mod_upper_bound. compute; omega.
  Qed.

  Lemma fs_seek_ok: forall (fId: Fid) (pos: nat) (fs postFS: FSState) (err: ErrCode),
      (err, postFS) = fs_seek (fId, pos) fs ->
      (~ In fId (map fst (openhandleFS fs)) /\ postFS = fs /\ err = eBadF) \/
      (In fId (map fst (openhandleFS fs)) /\ pos >= ((fMapFS fs) fId).(metaF).(size) /\
       (pos <> O \/ ((fMapFS fs) fId).(metaF).(size) <> O) /\
       postFS = fs /\ err = eInval) \/
      (In fId (map fst (openhandleFS fs)) /\ err <> eSucc /\ fsFS postFS = fsFS fs /\
       exists p1 p2 vlseek_ret,
         err = vlseek_ret /\
         logFS postFS = Call_VLSeek p1 p2 vlseek_ret :: logFS fs) \/
      (In fId (map fst (openhandleFS fs)) /\ err = eSucc /\
       layoutFS fs = layoutFS postFS /\ vmFS fs = vmFS postFS /\
       fMapFS fs = fMapFS postFS /\ dMapFS fs = dMapFS postFS /\
       fnode_ctr (fsFS fs) = fnode_ctr (fsFS postFS) /\
       dnode_ctr (fsFS fs) = dnode_ctr (fsFS postFS) /\
       mmap_handles (fsFS fs) = mmap_handles (fsFS postFS) /\
       mmap_memory (fsFS fs) = mmap_memory (fsFS postFS) /\
       map fst (openhandleFS postFS) = map fst (openhandleFS fs) /\
       (forall cursor, In (fId, cursor) (openhandleFS fs) ->
                       In (fId, pos) (openhandleFS postFS)) /\
       exists p3 p4, logFS postFS = Call_VLSeek p3 p4 eSucc :: logFS fs).
  Proof.
    intros. unfold fs_seek in H. simpl in H. rm_hif_eqn H.
    - right. rm_hif_eqn H.
      + left. unfold fMapFS. split. 1: eapply find_Fid_In; eauto. inversion H.
        apply andb_prop in Heqb. destruct Heqb. apply leb_complete in H0. split; auto.
        apply Bool.orb_prop in H3. rewrite !Bool.negb_true_iff in H3.
        destruct H3; apply beq_nat_false in H3; intuition.
      + right. destruct fs. simpl in H. rm_hif.
        * left. split. 1: eapply find_Fid_In; eauto. inversion H. intuition.
          simpl. exists fId, (pos_to_vpage pos), err. subst err. intuition.
        * right. split. 1: eapply find_Fid_In; eauto. inversion H.
          unfold openhandleFS, layoutFS, vmFS, fMapFS, dMapFS, logFS, snd in *.
          simpl in *. intuition.
          -- apply replace_handler_preserve_fst.
          -- apply replace_handler_replaces with cursor; auto.
          -- exists fId, (pos_to_vpage pos). rewrite e. auto.
    - left. inversion H. intuition. eapply find_Fid_None; eauto.
  Qed.

  Lemma change_f_map_size_preserve_name: forall fmap fId new_size id,
      nameF (fmap id) = nameF (change_f_map_size fmap fId new_size id).
  Proof. intros. unfold change_f_map_size. rm_if. subst. simpl; auto. Qed.

  Lemma f_map_append_page_preserve_name: forall fmap fId page id,
      nameF (fmap id) = nameF (f_map_append_page fmap fId page id).
  Proof. intros. unfold f_map_append_page. rm_if. subst. simpl; auto. Qed.

  Lemma write_to_virtual_memory_fmap_preserve_name:
    forall (buf: string) (pos: nat) (fId: Fid) (fmap: Fid -> FData)
           (vm: list Page) new_fmap new_vm id,
      write_to_virtual_memory buf pos fId fmap vm = inl (new_vm, new_fmap) ->
      nameF (fmap id) = nameF (new_fmap id).
  Proof.
    intros buf. remember (String.length buf).
    assert (String.length buf <= n) by omega; clear Heqn.
    revert buf H. induction n; intros.
    - destruct buf. 2: simpl in H; exfalso; omega.
      rewrite write_to_virtual_memory_unfold in H0. rm_hif.
      inversion H0; auto. exfalso; apply n; auto.
    - rewrite write_to_virtual_memory_unfold in H0. rm_hif.
      1: inversion H0; subst; auto. cbv zeta in H0. rm_hif.
      1: inversion H0. rm_hif. 1: inversion H0. apply IHn with (id := id) in H0; auto.
      + rm_hif; auto. rewrite <- H0. rewrite <- f_map_append_page_preserve_name. auto.
      + transitivity (String.length buf - (psize - pos mod psize)).
        1: apply substring_length. clear -H. cut (0 < psize - pos mod psize).
        1: intros; omega. cut (pos mod psize < psize). 1: intros; omega.
        apply Nat.mod_upper_bound. compute; omega.
  Qed.

  Lemma change_f_map_size_preserve_permission: forall fmap fId new_size id,
      permission (metaF (fmap id)) =
      permission (metaF (change_f_map_size fmap fId new_size id)).
  Proof. intros. unfold change_f_map_size. rm_if. subst. simpl; auto. Qed.

  Lemma f_map_append_page_preserve_meta: forall fmap fId page id,
      metaF (fmap id) = metaF (f_map_append_page fmap fId page id).
  Proof. intros. unfold f_map_append_page. rm_if. subst. simpl; auto. Qed.

  Lemma write_to_virtual_memory_fmap_preserve_meta:
    forall (buf: string) (pos: nat) (fId: Fid) (fmap: Fid -> FData)
           (vm: list Page) new_fmap new_vm id,
      write_to_virtual_memory buf pos fId fmap vm = inl (new_vm, new_fmap) ->
      metaF (fmap id) = metaF (new_fmap id).
  Proof.
    intros buf. remember (String.length buf).
    assert (String.length buf <= n) by omega; clear Heqn.
    revert buf H. induction n; intros.
    - destruct buf. 2: simpl in H; exfalso; omega.
      rewrite write_to_virtual_memory_unfold in H0. rm_hif.
      inversion H0; auto. exfalso; apply n; auto.
    - rewrite write_to_virtual_memory_unfold in H0. rm_hif.
      1: inversion H0; subst; auto. cbv zeta in H0. rm_hif.
      1: inversion H0. rm_hif. 1: inversion H0. apply IHn with (id := id) in H0; auto.
      + rm_hif; auto. rewrite <- H0. rewrite <- f_map_append_page_preserve_meta. auto.
      + transitivity (String.length buf - (psize - pos mod psize)).
        1: apply substring_length. clear -H. cut (0 < psize - pos mod psize).
        1: intros; omega. cut (pos mod psize < psize). 1: intros; omega.
        apply Nat.mod_upper_bound. compute; omega.
  Qed.

  Lemma preserve_fname_NoDupNameTree:
    forall fmap1 fmap2 dmap tree,
      (forall fId, nameF (fmap1 fId) = nameF (fmap2 fId)) ->
      NoDupNameTree fmap1 dmap tree -> NoDupNameTree fmap2 dmap tree.
  Proof.
    intros. induction tree using tree_ind2; constructor; inversion H0; subst.
    - rewrite Forall_forall in *; intros. apply H1; auto.
    - cut (map (treeName fmap1 dmap) treeL = map (treeName fmap2 dmap) treeL).
      1: intros S; rewrite <- S; auto.
      apply map_ext_in. intros. destruct a; simpl; [rewrite H|]; auto.
  Qed.

  Lemma preserve_dname_NoDupNameTree:
    forall fmap dmap1 dmap2 tree,
      (forall dId, nameD (dmap1 dId) = nameD (dmap2 dId)) ->
      NoDupNameTree fmap dmap1 tree -> NoDupNameTree fmap dmap2 tree.
  Proof.
    intros. induction tree using tree_ind2; constructor; inversion H0; subst.
    - rewrite Forall_forall in *; intros. apply H1; auto.
    - cut (map (treeName fmap dmap1) treeL = map (treeName fmap dmap2) treeL).
      1: intros S; rewrite <- S; auto.
      apply map_ext_in. intros. destruct a; simpl; [|rewrite H]; auto.
  Qed.

  Lemma change_f_map_size_preserve_pgid: forall fmap fId new_size id,
      pageIdsF (change_f_map_size fmap fId new_size id) = pageIdsF (fmap id).
  Proof. intros. unfold change_f_map_size. rm_if. subst. simpl; auto. Qed.

  Lemma write_to_virtual_memory_pageIds:
    forall (buf: string) (pos: nat) (fId: Fid)
           (fmap: Fid -> FData) (vm: list Page) new_fmap new_vm,
      write_to_virtual_memory buf pos fId fmap vm = inl (new_vm, new_fmap) ->
      forall pgId, In pgId (pageIdsF (new_fmap fId)) ->
                   In pgId (pageIdsF (fmap fId)) \/
                   (pgId < memory_upper_bound /\
                    forall fId2, fId <> fId2 -> ~ In pgId (pageIdsF (new_fmap fId2))).
  Proof.
    intros buf. remember (String.length buf).
    assert (String.length buf <= n) by omega; clear Heqn.
    revert buf H. induction n; intros.
    - destruct buf. 2: simpl in H; exfalso; omega.
      rewrite write_to_virtual_memory_unfold in H0. rm_hif.
      2: exfalso; auto. inversion H0; subst. left; auto.
    - rewrite write_to_virtual_memory_unfold in H0. rm_hif.
      1: inversion H0; subst; left; auto. cbv zeta in H0.
      remember (if Nat.eq_dec (pos mod psize) 0 then pos / psize + 1 else pos / psize)
        as pgn. remember (nth pgn (pageIdsF (fmap fId)) memory_upper_bound) as vpg.
      remember (if Bool.bool_dec
                     ((Nat.eqb vpg memory_upper_bound) && (Nat.eqb (pos mod psize) O)) true then
                  (get_next_free_vpg fmap, true) else (vpg, false)) as vpg_ret.
      do 2 (rm_hif; [inversion H0|]).
      pose proof (write_to_virtual_memory_fmap _ _ _ _ _ _ _ H0).
      apply IHn with (pgId := pgId) in H0; auto.
      + destruct H0. 2: right; auto. rm_hif. 2: left; auto. rm_hif; subst vpg_ret.
        2: simpl in e; inversion e. simpl in H0. unfold f_map_append_page in H0.
        rm_hif. 2: exfalso; apply n3; auto. simpl in H0. rewrite in_app_iff in H0.
        destruct H0. 1: left; auto. simpl in H0. destruct H0.
        2: exfalso; auto. simpl in H2. right.
        pose proof (get_next_free_vpg_axiom fmap). subst pgId. split.
        * destruct (H3 fId); simpl in n1; omega.
        * intros. simpl in n0. rewrite <- H2; auto. unfold f_map_append_page. rm_if.
          destruct (H3 fId2). auto.
      + transitivity (String.length buf - (psize - pos mod psize)).
        1: apply substring_length. clear -H. cut (0 < psize - pos mod psize).
        1: intros; omega. cut (pos mod psize < psize). 1: intros; omega.
        apply Nat.mod_upper_bound. compute; omega.
  Qed.

  Lemma fs_write_ok: forall (fId : Fid) (buf : string) (pos: nat)
                            (fs : FSState) (err : ErrCode) (postFS : FSState),
      (err, postFS) = fs_write (fId, buf, pos) fs -> good_file_system (fsFS fs) ->
      (~ In fId (map fst (openhandleFS fs)) /\ postFS = fs /\ err = eBadF) \/
      (In fId (map fst (openhandleFS fs)) /\ postFS = fs /\ (err = eNoSpc \/
                                                             err = eInval)) \/
      (In fId (map fst (openhandleFS fs)) /\ err <> eSucc /\ fsFS postFS = fsFS fs /\
       exists p1 p2 vlseek_ret,
         hd_error (logFS postFS) = Some (Call_VLSeek p1 p2 vlseek_ret) /\
         err = vlseek_ret /\
         logFS postFS = Call_VLSeek p1 p2 vlseek_ret :: logFS fs) \/
      (In fId (map fst (openhandleFS fs)) /\ fsFS postFS = fsFS fs /\
       exists vwrite_ret p1 p2 p3,
         err = vwrite_ret /\ hd_error (logFS postFS) =
                             Some (Call_VWrite p1 p2 p3 vwrite_ret) /\
         vwrite_ret <> eSucc /\
         exists p4 p5,
           logFS postFS = Call_VWrite p1 p2 p3 vwrite_ret ::
                                      Call_VLSeek p4 p5 eSucc :: logFS fs) \/
      (In fId (map fst (openhandleFS fs)) /\ layoutFS fs = layoutFS postFS /\
       dMapFS fs = dMapFS postFS /\
       mmap_handles (fsFS fs) = mmap_handles (fsFS postFS) /\
       mmap_memory (fsFS fs) = mmap_memory (fsFS postFS) /\
       map fst (openhandleFS postFS) = map fst (openhandleFS fs) /\
       In (fId, pos + (String.length buf)) (openhandleFS postFS) /\
       (forall id, id <> fId -> (fMapFS fs) id = (fMapFS postFS) id) /\
       (((fMapFS fs) fId).(nameF) = ((fMapFS postFS) fId).(nameF)) /\
       (((fMapFS fs) fId).(metaF).(permission) =
        ((fMapFS postFS) fId).(metaF).(permission)) /\
       size_changed fId fs postFS pos (String.length buf) /\
       (exists p1 p2 p3,
           err = eSucc /\
           hd_error (logFS postFS) = Some (Call_VWrite p1 p2 p3 eSucc) /\
           exists p4 p5,
             logFS postFS = Call_VWrite p1 p2 p3 eSucc ::
                                        Call_VLSeek p4 p5 eSucc :: logFS fs) /\
       good_file_system (fsFS postFS)).
  Proof.
    intros. unfold fs_write in H. simpl in H. rm_hif_eqn H.
    - right. rm_hif_eqn H.
      1: left; split; [eapply find_Fid_In; eauto | inversion H; intuition]. simpl in H.
      rm_hmatch.
      + right. destruct p0 as [new_vm new_f_map]. destruct fs. simpl in H. rm_hif.
        * left. split. 1: eapply find_Fid_In; eauto. inversion H. simpl. intuition.
          exists fId, (pos_to_vpage pos),
          (v_lseek fId (pos_to_vpage pos) (Datatypes.length l)). intuition.
        * right. remember (get_encrypted_buf (get_write_pages fId new_f_map new_vm pos (String.length buf)) new_vm) as encrypted_buf. simpl in H. rm_hif.
          -- left. split. 1: eapply find_Fid_In; eauto. inversion H. simpl. intuition.
             exists err, fId, encrypted_buf, (pos_to_vlen pos (String.length buf)).
             rewrite H2. intuition. exists fId, (pos_to_vpage pos).
             rewrite e; intuition.
          -- simpl in H. right. split. 1: eapply find_Fid_In; eauto.
             simpl in H. inversion H.
             unfold openhandleFS, layoutFS, vmFS, fMapFS, dMapFS, logFS, snd in *.
             simpl in *. intuition.
             ++ apply replace_handler_preserve_fst.
             ++ apply find_some in Heqo. destruct Heqo. rewrite Nat.eqb_eq in H4.
                destruct p. simpl in H4. subst n.
                eapply replace_handler_replaces; eauto.
             ++ unfold change_f_map_size. destruct (Nat.eq_dec id fId).
                1: exfalso; auto. unfold change_f_map_pages.
                destruct (Nat.eq_dec id fId); [exfalso |]; auto.
                eapply write_to_virtual_memory_fmap; eauto.
             ++ rewrite <- change_f_map_size_preserve_name.
                eapply write_to_virtual_memory_fmap_preserve_name. eauto.
             ++ rewrite <- change_f_map_size_preserve_permission.
                erewrite write_to_virtual_memory_fmap_preserve_meta; eauto.
             ++ unfold size_changed. unfold fMapFS. simpl.
                unfold change_f_map_size. rm_if. 2: exfalso; apply n; auto. simpl.
                erewrite <- write_to_virtual_memory_fmap_preserve_meta; eauto.
             ++ clear H H3. rewrite e0.
                exists fId, encrypted_buf, (pos_to_vlen pos (String.length buf)).
                intuition. rewrite e. exists fId, (pos_to_vpage pos). auto.
             ++ clear H H3. destruct H0 as [? [? [? [? [? [? [? [? ?]]]]]]]].
                pose proof (write_to_virtual_memory_pageIds _ _ _ _ _ _ _ Heqs).
                pose proof (write_to_virtual_memory_fmap _ _ _ _ _ _ _ Heqs).
                split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]; intuition; simpl.
                ** apply preserve_fname_NoDupNameTree with new_f_map.
                   1: intros; apply change_f_map_size_preserve_name.
                   apply preserve_fname_NoDupNameTree with (f_map f).
                   1: intros; eapply write_to_virtual_memory_fmap_preserve_name; eauto.
                   auto.
                ** rewrite replace_handler_preserve_fst. auto.
                ** simpl in *. rewrite change_f_map_size_preserve_pgid in *.
                   subst pgId2. destruct (Nat.eq_dec fId1 fId); [subst fId1|];
                                  destruct (Nat.eq_dec fId2 fId); [exfalso; auto|..].
                   --- rewrite <- H10 in H16; auto. specialize (H9 _ H15).
                       destruct H9 as [? | [? ?]]. 1: eapply H7; eauto.
                       eapply H17; eauto. rewrite <- H10; auto.
                   --- subst fId. rewrite <- H10 in H15; auto. specialize (H9 _ H16).
                       destruct H9 as [? | [? ?]]. 1: eapply H7; eauto.
                       eapply H17; eauto. rewrite <- H10; auto.
                   --- rewrite <- H10 in H16, H15; auto.
                       specialize (H7 fId1 fId2 pgId1 pgId1). apply H7; auto.
                ** simpl in *. rewrite change_f_map_size_preserve_pgid in *.
                   destruct (Nat.eq_dec fId0 fId).
                   2: rewrite <- H10 in H13; auto; eapply H11; eauto. subst fId0.
                   specialize (H9 _ H13). destruct H9 as [? | [? ?]]; auto.
                   eapply H11; eauto.
      + inversion H. left. split; [eapply find_Fid_In; eauto | split]; auto.
        eapply write_to_virtual_memory_err; eauto.
    - left. inversion H. intuition. eapply find_Fid_None; eauto.
  Qed.

  Inductive path_in_tree (dmap: Did -> DData) : Path -> Tree -> Prop :=
  | Empty_path_in: forall root treeL, path_in_tree dmap [] (Dnode root treeL)
  | Cons_path_in: forall root dname dlist treeL,
      (exists did treeL', In (Dnode did treeL') treeL /\
                          (dmap did).(nameD) = dname /\
                          path_in_tree dmap dlist (Dnode did treeL')) ->
      path_in_tree dmap (dname :: dlist) (Dnode root treeL).

  Inductive path_in_tree_with_id (dmap: Did -> DData) : Path -> Tree -> Did -> Prop :=
  | Empty_piwi: forall root treeL, path_in_tree_with_id dmap [] (Dnode root treeL) root
  | Cons_piwi: forall root dname dlist treeL d,
      (exists did treeL', In (Dnode did treeL') treeL /\
                          (dmap did).(nameD) = dname /\
                          path_in_tree_with_id dmap dlist (Dnode did treeL') d) ->
      path_in_tree_with_id dmap (dname :: dlist) (Dnode root treeL) d.

  Lemma path_in_tree_with_id_some : forall dmap d l tree path,
      findDir dmap tree path = Some (Dnode d l) ->
      path_in_tree_with_id dmap path tree d.
  Proof.
    intros dmap d l. induction tree using tree_ind2; intros.
    1: destruct path; simpl in H; inversion H. destruct path.
    1: simpl in H0; inversion H0; constructor. constructor.
    simpl in H0. destruct (find (fun x : Tree => root_eq dmap x s) treeL) eqn: ?.
    2: inversion H0. apply find_some in Heqo. destruct Heqo. unfold root_eq in H2.
    destruct t. 1: inversion H2. exists d0, l0. unfold DData_eqb in H2. rm_hif.
    2: inversion H2. clear H2. split; [|split]; auto. rewrite Forall_forall in H.
    specialize (H _ H1 path). apply H; auto.
  Qed.

  Lemma findDir_not_fnode: forall dmap tree p i, findDir dmap tree p <> Some (Fnode i).
  Proof.
    intros dmap tree. induction tree using tree_ind2; repeat intro.
    1: destruct p; simpl in H; inversion H. destruct p; simpl in H0. 1: inversion H0.
    destruct (find (fun x : Tree => root_eq dmap x s) treeL) eqn: ?. 2: inversion H0.
    apply find_some in Heqo. destruct Heqo. rewrite Forall_forall in H.
    specialize (H _ H1). apply H in H0. auto.
  Qed.

  Lemma path_in_tree_with_id_eq: forall dmap path tree,
      path_in_tree dmap path tree <->
      exists id, path_in_tree_with_id dmap path tree id.
  Proof.
    intros. revert path. induction tree using tree_ind2; intros.
    1: split; intro; [|destruct H]; inversion H.
    destruct path. 1: split; intro; [exists did |]; constructor.
    rewrite Forall_forall in H.
    split; intro; [|destruct H0 as [id ?]]; inversion H0; subst; [|rename H6 into H2];
      destruct H2 as [did' [treeL' [? [? ?]]]];
      [rewrite H in H3; auto; destruct H3 as [id ?]; exists id|];
      constructor; exists did', treeL'; intuition. rewrite H; auto. exists id; auto.
  Qed.

  Lemma path_in_tree_some : forall dmap tree path t,
      findDir dmap tree path = Some t -> path_in_tree dmap path tree.
  Proof.
    intros. destruct t. 1: exfalso; eapply findDir_not_fnode; eauto.
    apply path_in_tree_with_id_some in H. rewrite path_in_tree_with_id_eq.
    exists d; auto.
  Qed.

  Lemma path_in_tree_none : forall fs path,
      NoDupNameTree (fMapFS fs) (dMapFS fs) (layoutFS fs) ->
      findDir (dMapFS fs) (layoutFS fs) path = None ->
      ~ path_in_tree (dMapFS fs) path (layoutFS fs).
  Proof.
    intros fs. destruct fs. unfold fMapFS, dMapFS, layoutFS. simpl. clear l.
    remember (layout f). clear Heqt. revert f.
    induction t using tree_ind2; intros. 1: intro; inversion H1.
    destruct path; simpl in H1. 1: inversion H1.
    rm_hmatch; intro; inversion H2; subst; destruct H4 as [did' [treeL' [? [? ?]]]].
    - apply in_split in H3. destruct H3 as [l1 [l2 ?]]. subst treeL.
      rewrite find_app_not_in in Heqo.
      + simpl in Heqo. unfold DData_eqb in Heqo.
        destruct (string_dec (nameD (d_map f did')) s); auto.
        inversion Heqo. subst. rewrite Forall_forall in H.
        assert (In (Dnode did' treeL') (l1 ++ Dnode did' treeL' :: l2)) by
            (rewrite in_app_iff; right; simpl; left; auto).
        specialize (H _ H3). revert H5. apply H; auto.
        inversion H0. rewrite Forall_forall in H9. apply H9; auto.
      + intros. unfold root_eq. destruct x; auto. unfold DData_eqb. rm_if; auto.
        inversion H0. rewrite map_app in H11. rewrite map_cons in H11.
        unfold treeName in H11 at 2. apply NoDup_remove_2 in H11. exfalso. apply H11.
        rewrite in_app_iff. left. apply in_split in H3. destruct H3 as [l3 [l4 ?]].
        subst l1. rewrite map_app, map_cons.
        rewrite in_app_iff. right. simpl. left. rewrite H4; auto.
    - apply find_none with (x := Dnode did' treeL') in Heqo; auto.
      unfold root_eq, DData_eqb in Heqo. rm_hif. 1: inversion Heqo. auto.
  Qed.

  Lemma path_in_tree_with_id_none: forall fs path id,
      NoDupNameTree (fMapFS fs) (dMapFS fs) (layoutFS fs) ->
      findDir (dMapFS fs) (layoutFS fs) path = None ->
      ~ path_in_tree_with_id (dMapFS fs) path (layoutFS fs) id.
  Proof.
    intros. intro.
    assert (exists d, path_in_tree_with_id (dMapFS fs) path (layoutFS fs) d) by
        (exists id; auto). rewrite <- path_in_tree_with_id_eq in H2.
    revert H2. apply path_in_tree_none; auto.
  Qed.

  Lemma NoDup_app_r: forall {A : Type} (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l2.
  Proof.
    induction l1; simpl; intros; auto. apply NoDup_cons_iff in H.
    apply IHl1. intuition.
  Qed.

  Lemma NoDup_app_l: forall {A : Type} (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l1.
  Proof.
    intros A l1 l2. revert l1. induction l2; intros. rewrite app_nil_r in H. apply H.
    apply NoDup_remove_1 in H. apply IHl2. apply H.
  Qed.

  Lemma NoDup_app_not_in_r: forall {A : Type} (l1 l2 : list A),
      NoDup (l1 ++ l2) -> forall y, In y l1 -> ~ In y l2.
  Proof.
    induction l1; intros. 1: inversion H0. rewrite <- app_comm_cons in H.
    apply in_inv in H0. destruct H0.
    - subst. rewrite NoDup_cons_iff in H. destruct H. intro. apply H.
      apply in_or_app. right. apply H1.
    - rewrite NoDup_cons_iff in H. destruct H. apply IHl1; auto.
  Qed.

  Lemma NoDup_app_not_in_l: forall {A : Type} (l2 l1 : list A),
      NoDup (l1 ++ l2) -> forall y, In y l2 -> ~ In y l1.
  Proof.
    induction l2; intros. 1: inversion H0. apply in_inv in H0. destruct H0.
    - subst. apply NoDup_remove_2 in H. intro; apply H. apply in_or_app. left; auto.
    - apply NoDup_remove_1 in H. apply IHl2; auto.
  Qed.

  Lemma subtree_nodup: forall t d l,
      In t l -> NoDup (collectDids (Dnode d l)) -> NoDup (collectDids t).
  Proof.
    intros. induction l. 1: inversion H. simpl in H. simpl in H0. destruct H.
    - subst a. rewrite NoDup_cons_iff in H0. destruct H0.
      apply NoDup_app_l in H0. auto.
    - apply IHl; auto. simpl. rewrite NoDup_cons_iff in H0. destruct H0. constructor.
      + intro; apply H0. rewrite in_app_iff. right; auto.
      + apply NoDup_app_r in H1. auto.
  Qed.

  Lemma subtree_did_in_merge: forall t l d,
      In d (collectDids t) -> In t l -> In d (flat_map collectDids l).
  Proof. intros. rewrite in_flat_map. exists t. intuition. Qed.

  Lemma path_in_tree_collectDids: forall dmap path t d,
      path_in_tree_with_id dmap path t d -> In d (collectDids t).
  Proof.
    intros. revert t path H. induction t using tree_ind2; intros.
    1: inversion H. destruct path; inversion H0; subst. 1: simpl; left; auto.
    destruct H6 as [did' [treeL' [? [? ?]]]]. simpl. right.
    rewrite Forall_forall in H. specialize (H _ H1 _ H3).
    eapply subtree_did_in_merge; eauto.
  Qed.

  Lemma flat_map_collectDids: forall l1 l2 t,
      flat_map collectDids (l1 ++ t :: l2) =
      (flat_map collectDids l1 ++ collectDids t ++ flat_map collectDids l2)%list.
  Proof.
    intros. rewrite flat_map_concat_map, map_app, map_cons,
            concat_app, concat_cons, <- !flat_map_concat_map; auto.
  Qed.

  Lemma path_in_tree_nonempty_neq: forall dmap path did treeL d,
      path <> nil -> NoDup (collectDids (Dnode did treeL)) ->
      path_in_tree_with_id dmap path (Dnode did treeL) d -> d <> did.
  Proof.
    intros. destruct path. 1: exfalso; auto. inversion H1. subst.
    destruct H7 as [did' [treeL' [? [? ?]]]]. apply path_in_tree_collectDids in H4.
    apply in_split in H2. destruct H2 as [l1 [l2 ?]]. simpl in H0. subst treeL.
    rewrite flat_map_collectDids in H0. rewrite NoDup_cons_iff in H0.
    destruct H0. intro. subst did. apply H0. rewrite !in_app_iff. right; left; auto.
  Qed.

  Lemma addDidToTree_in_tree: forall dmap d cnt dname p tree path,
      ~ In cnt (collectDids tree) -> NoDup (collectDids tree) ->
      path_in_tree_with_id dmap path tree d ->
      path_in_tree_with_id (change_d_map dmap cnt (Build_DData dname p))
                           (path ++ [dname])%list (addDidToTree tree d cnt) cnt.
  Proof.
    intros. revert path H H0 H1. induction tree using tree_ind2; intros.
    1: inversion H1. destruct path; inversion H2; subst.
    - simpl. rm_if. 2: exfalso; auto. constructor. exists cnt, nil.
      split; [|split]; [simpl; left | unfold change_d_map; rm_if; exfalso |
                        constructor]; auto.
    - destruct H8 as [did' [treeL' [? [? ?]]]]. simpl. rm_if.
      + exfalso. revert e. eapply (path_in_tree_nonempty_neq dmap (s :: path)); eauto.
        intro. inversion H6.
      + constructor. rewrite Forall_forall in H. specialize (H _ H3).
        assert (~ In cnt (collectDids (Dnode did' treeL'))) by
            (intro; apply H0; simpl; right;
             apply subtree_did_in_merge with (t := Dnode did' treeL'); auto).
        assert (NoDup (collectDids (Dnode did' treeL'))) by
            (apply subtree_nodup with (t := Dnode did' treeL') in H1; auto).
        specialize (H _ H6 H7 H5).
        simpl in H. pose proof H3.
        apply (in_map (fun t : Tree => addDidToTree t d cnt)) in H3.
        simpl in H3. destruct (Nat.eq_dec d did').
        * subst d. exists did', (Dnode cnt [] :: treeL').
          split; [|split; [unfold change_d_map|]]; auto.
          rm_if. simpl in H0. subst. exfalso. apply H0. right.
          apply subtree_did_in_merge with (t := Dnode cnt treeL'); auto.
          apply path_in_tree_collectDids in H5; auto.
        * exists did', (map (fun t : Tree => addDidToTree t d cnt) treeL').
          split; [|split; [unfold change_d_map|]]; auto.
          rm_if. simpl in H0. subst. exfalso. apply H0. right.
          apply subtree_did_in_merge with (t := Dnode cnt treeL'); auto.
          simpl. left; auto.
  Qed.

  Lemma treeName_eq_treeL: forall fmap dmap cnt d treeL,
      ~ In cnt (flat_map collectDids treeL) ->
      map (treeName fmap dmap) treeL =
      map (treeName fmap (change_d_map dmap cnt d)) treeL.
  Proof.
    intros. apply map_ext_in. intros. unfold change_d_map.
    destruct a; simpl; auto. rm_if. subst.
    exfalso. apply H. apply (subtree_did_in_merge (Dnode cnt l)); simpl; intuition.
  Qed.

  Lemma change_d_map_NoDupNameTree: forall fmap dmap cnt d t,
      ~ In cnt (collectDids t) -> NoDupNameTree fmap dmap t ->
      NoDupNameTree fmap (change_d_map dmap cnt d) t.
  Proof.
    intros fmap dmap cnt d. induction t using tree_ind2; intros; constructor.
    - rewrite Forall_forall in *. intros. apply H; auto.
      + intro. apply H0. simpl. right. apply subtree_did_in_merge with (t := x); auto.
      + inversion H1. subst. rewrite Forall_forall in H7. apply H7; auto.
    - inversion H1. subst.
      assert (map (treeName fmap dmap) treeL =
              map (treeName fmap (change_d_map dmap cnt d)) treeL). {
        apply map_ext_in. intros. unfold change_d_map.
        destruct a; simpl; auto. rm_if. exfalso. apply H0.
        simpl. right. rewrite in_flat_map. subst d0.
        exists (Dnode cnt l). split; simpl; intuition.
      } rewrite <- H2. auto.
  Qed.

  Lemma addDidToTree_the_same: forall d cnt tree,
      ~ In d (collectDids tree) -> addDidToTree tree d cnt = tree.
  Proof.
    intros. induction tree using tree_ind2; simpl; auto. rm_if.
    1: subst; exfalso; apply H; simpl; left; auto.
    rewrite Forall_forall in H0. f_equal. simpl in H.
    assert (treeL = map id treeL) by
        (clear; induction treeL; simpl; [|rewrite IHtreeL at 1]; auto).
    rewrite H1 at 2. clear H1. apply map_ext_in. intros. unfold id. apply H0; auto.
    intro. apply H. right. apply (subtree_did_in_merge a); auto.
  Qed.

  Lemma addDidToTree_the_same_list: forall d cnt l,
      ~ In d (flat_map collectDids l) -> map (fun t => addDidToTree t d cnt) l = l.
  Proof.
    intros. assert (l = map id l) by
        (clear; induction l; simpl; [|rewrite IHl at 1]; auto).
    rewrite H0 at 2; clear H0. apply map_ext_in. unfold id. intros.
    apply addDidToTree_the_same. intro; apply H. apply (subtree_did_in_merge a); auto.
  Qed.

  Lemma addDidToTree_map_the_same: forall l1 l2 did' treeL' d cnt,
      NoDup (flat_map collectDids (l1 ++ Dnode did' treeL' :: l2)) ->
      In d (collectDids (Dnode did' treeL')) ->
      map (fun t : Tree => addDidToTree t d cnt) (l1 ++ Dnode did' treeL' :: l2) =
      (l1 ++ (addDidToTree (Dnode did' treeL') d cnt) :: l2)%list.
  Proof.
    intros; rewrite map_app, map_cons. rewrite flat_map_collectDids in H.
    f_equal; [|f_equal]; apply addDidToTree_the_same_list.
    - apply NoDup_app_not_in_l with (y := d) in H; auto. apply in_or_app. left; auto.
    - apply NoDup_app_r in H. apply NoDup_app_not_in_r with (y := d) in H; auto.
  Qed.

  Lemma addDidToTree_NoDupNameTree: forall fmap dmap dname cnt d p tree path,
      ~ file_in_tree fmap dmap path dname tree ->
      ~ path_in_tree dmap (path ++ [dname])%list tree ->
      path_in_tree_with_id dmap path tree d -> ~ In cnt (collectDids tree) ->
      NoDupNameTree fmap dmap tree -> NoDup (collectDids tree) ->
      NoDupNameTree fmap (change_d_map dmap cnt {| nameD := dname; metaD := p |})
                    (addDidToTree tree d cnt).
  Proof.
    intros fmap dmap dname cnt d p. induction tree using tree_ind2; intros.
    1: inversion H1. destruct path; inversion H2; subst.
    - simpl in *. rm_if. 2: exfalso; auto. clear e H. constructor.
      + rewrite Forall_forall. intros. simpl in H. destruct H.
        * subst x. constructor. 1: apply Forall_nil. simpl. constructor.
        * inversion H4. subst. rewrite Forall_forall in H10. specialize (H10 _ H).
          apply change_d_map_NoDupNameTree; auto. intro. apply H3. right.
          apply (subtree_did_in_merge x); auto.
      + simpl. unfold change_d_map at 1. rm_if. 2: exfalso; auto. simpl. clear e.
        rewrite <- treeName_eq_treeL. 2: intro; apply H3; right; auto. constructor.
        2: inversion H4; auto. intro. rewrite in_map_iff in H.
        destruct H as [x [? ?]]. destruct x.
        * apply H0. constructor. rewrite Exists_exists. exists (Fnode f).
          split; auto. constructor. simpl in H. auto.
        * apply H1. constructor. exists d0, l. simpl in H. intuition. constructor.
    - destruct H11 as [did' [treeL' [? [? ?]]]]. simpl. rm_if.
      + exfalso. revert e. eapply path_in_tree_nonempty_neq; eauto.
        intro. inversion H9.
      + assert (NoDupNameTree fmap
                              (change_d_map dmap cnt {| nameD := dname; metaD := p |})
                              (addDidToTree (Dnode did' treeL') d cnt)). {
          rewrite Forall_forall in H. apply H with (path := path); try intro; auto.
          - apply H0; constructor; exists did', treeL'; intuition.
          - apply H1; simpl; constructor; exists did', treeL'; intuition.
          - apply H3; simpl; right.
            apply (subtree_did_in_merge (Dnode did' treeL')); auto.
          - inversion H4. subst. rewrite Forall_forall in H13. apply H13. auto.
          - apply (subtree_nodup _ _ _ H6 H5).
        } clear H. apply in_split in H6. destruct H6 as [l1 [l2 ?]]. subst treeL.
        apply path_in_tree_collectDids in H8.
        rewrite addDidToTree_map_the_same; auto.
        2: simpl in H5; rewrite NoDup_cons_iff in H5; destruct H5; auto.
        inversion H4. subst. constructor.
        * rewrite Forall_forall in *. intros. simpl in H3.
          rewrite flat_map_collectDids in H3. rewrite in_app_iff in H.
          destruct H; [|apply in_inv in H; destruct H];
            [apply change_d_map_NoDupNameTree | subst x |
             apply change_d_map_NoDupNameTree ]; auto.
          -- intro. apply H3. right. rewrite in_app_iff.
             left. apply (subtree_did_in_merge x); auto.
          -- apply H12. rewrite in_app_iff. left; auto.
          -- intro. apply H3. right. do 2 (rewrite in_app_iff; right).
             apply (subtree_did_in_merge x); auto.
          -- apply H12. rewrite in_app_iff. right. simpl. right; auto.
        * rewrite map_app, map_cons in *. simpl in H13. simpl in H3.
          rewrite flat_map_collectDids in H3.
          assert (treeName fmap
                           (change_d_map dmap cnt {| nameD := dname; metaD := p |})
                           (addDidToTree (Dnode did' treeL') d cnt) =
                  nameD (dmap did')). {
            simpl. rm_if; [subst d|]; simpl; unfold change_d_map; rm_if;
                     exfalso; apply H3; subst; right; rewrite !in_app_iff;
                       right; left; simpl; left; auto.
          } rewrite H; clear H.
          rewrite <- !treeName_eq_treeL; auto; intro;
            apply H3; right; rewrite !in_app_iff; [right; right | left]; auto.
  Qed.

  Lemma addDidToTree_Permutation: forall dmap cnt d tree path,
      NoDup (collectDids tree) -> path_in_tree_with_id dmap path tree d ->
      ~ In cnt (collectDids tree) ->
      Permutation (cnt :: collectDids tree) (collectDids (addDidToTree tree d cnt)).
  Proof.
    intros dmap cnt d. induction tree using tree_ind2; intros; simpl. 1: inversion H0.
    rewrite Forall_forall in H. rm_if. 1: subst; simpl in *; constructor.
    simpl. destruct path; inversion H1; subst. 1: exfalso; apply n; auto.
    destruct H8 as [did' [treeL' [? [? ?]]]]. pose proof H5. rename H6 into HS.
    apply Permutation_trans with (did :: cnt :: flat_map collectDids treeL);
      constructor. apply in_split in H3. destruct H3 as [l1 [l2 ?]]. subst treeL.
    apply path_in_tree_collectDids in H5. simpl in H0. rewrite NoDup_cons_iff in H0.
    destruct H0. rewrite addDidToTree_map_the_same; auto.
    rewrite !flat_map_collectDids, app_comm_cons, !app_assoc.
    apply Permutation_app_tail. rewrite <- app_comm_cons.
    apply Permutation_trans with
        (flat_map collectDids l1 ++ cnt :: collectDids (Dnode did' treeL'))%list.
    1: apply Permutation_middle.
    apply Permutation_app_head. apply H with (path := path); auto.
    - rewrite in_app_iff. right; simpl; left; auto.
    - rewrite flat_map_collectDids in H3. apply NoDup_app_r, NoDup_app_l in H3; auto.
    - intro; apply H2. simpl. right.
      rewrite flat_map_collectDids, in_app_iff. right. simpl in *. intuition.
  Qed.

  Lemma addDidToTree_the_same_Fids: forall (tree : Tree) (d: Did) (cnt : nat),
      collectFids (addDidToTree tree d cnt) = collectFids tree.
  Proof.
    induction tree using tree_ind2; intros; simpl; auto.
    rm_if. simpl. rewrite Forall_forall in H.
    rewrite !flat_map_concat_map. f_equal. rewrite map_map.
    apply map_ext_in. intros. apply H; auto.
  Qed.

  Lemma DnodeIsDir: forall d l, isDir (Dnode d l).
  Proof. intros; exists d, l; auto. Qed.

  Lemma fs_mkdir_ok: forall (path: Path) (dname: string) (p: Permission)
                            (fs: FSState) (err: ErrCode) (postFS: FSState),
      good_file_system (fsFS fs) -> (err, postFS) = fs_mkdir (path, dname, p) fs ->
      (dname = EmptyString /\ err = eBadName /\ postFS = fs) \/
      (file_in_tree (fMapFS fs) (dMapFS fs) path dname (layoutFS fs) /\
       err = eNotDir /\ fs = postFS) \/
      (path_in_tree (dMapFS fs) (path ++ [dname])%list (layoutFS fs) /\
       err = eExists /\ fs = postFS) \/
      (~ path_in_tree (dMapFS fs) path (layoutFS fs) /\ err = eNoEnt /\ fs = postFS) \/
      ((exists did, path_in_tree_with_id (dMapFS fs) path (layoutFS fs) did /\
                    ((dMapFS fs) did).(metaD).(writable) = false) /\ err = eAcces /\
       fs = postFS) \/
      ((exists did, path_in_tree_with_id (dMapFS fs) path (layoutFS fs) did /\
                    ((dMapFS fs) did).(metaD).(writable) = true) /\ err <> eSucc /\
       fsFS fs = fsFS postFS /\
       exists vmkdir_err,
         err = vmkdir_err /\
         logFS postFS = Call_VMkdir path dname p vmkdir_err :: logFS fs) \/
      ((exists did, path_in_tree_with_id (dMapFS fs) path (layoutFS fs) did /\
                    ((dMapFS fs) did).(metaD).(writable) = true) /\
       err = eSucc /\ dCntFS postFS = dCntFS fs + 1 /\
       (forall d, d <> dCntFS fs -> dMapFS fs d = dMapFS postFS d) /\
       dMapFS postFS (dCntFS fs) = Build_DData dname p /\
       path_in_tree_with_id (dMapFS postFS)
                            (path ++ [dname])%list (layoutFS postFS) (dCntFS fs) /\
       good_file_system (fsFS postFS) /\
       logFS postFS = Call_VMkdir path dname p eSucc :: logFS fs).
  Proof.
    intros. unfold fs_mkdir in H0. rm_hif. 1: left; inversion H0; intuition.
    simpl in H0. right. destruct (findMatchedFid (fst fs) path dname) eqn:? .
    - left. apply file_in_tree_some in Heqo; auto. 1: inversion H0; intuition.
      unfold fMapFS, dMapFS, layoutFS. destruct H. unfold fsFS in H. auto.
    - right. destruct (findDir (d_map (fst fs)) (layout (fst fs))
                               (path ++ [dname])%list) eqn: ?.
      + apply path_in_tree_some in Heqo0; auto. inversion H0. intuition.
      + right. destruct (findDir (d_map (fst fs)) (layout (fst fs)) path) eqn: ?.
        * destruct t. 1: apply findDir_not_fnode in Heqo1; exfalso; auto.
          apply path_in_tree_with_id_some in Heqo1. right. rm_hif_eqn H0.
          -- left. split; [exists d; apply bool_eq_ok in Heqb | inversion H0];
                     intuition.
          -- right. unfold bool_eq in Heqb. rm_hif_eqn Heqb. 2: inversion Heqb.
             clear Heqb. destruct fs. simpl in H0. rm_hif.
             ++ left. split; [exists d | inversion H0]; intuition. exists err.
                subst err. intuition.
             ++ right. split; [exists d; intuition |]. simpl in H0. inversion H0.
                unfold dMapFS, layoutFS, dCntFS, logFS. simpl. rewrite e.
                simpl in H. destruct H as [? [? [? [? [? [? [? [? ?]]]]]]]].
                intuition; assert (HS: ~ In (dnode_ctr f) (collectDids (layout f))) by
                    (intro S; apply H5 in S; intuition);
                [unfold change_d_map; rm_if; exfalso; auto.. | | ].
                ** unfold dMapFS, layoutFS in Heqo1. simpl in Heqo1.
                   apply addDidToTree_in_tree; auto.
                ** apply file_in_tree_none in Heqo; auto.
                   apply path_in_tree_none in Heqo0; auto.
                   unfold fMapFS, dMapFS, layoutFS in *. simpl in *.
                   pose proof (addDidToTree_Permutation _ _ _ _ _ H1 Heqo1 HS).
                   split;
                     [|split; [|split;
                                [|split; [|split; [|split; [|split]]]]]]; simpl; auto.
                   --- apply addDidToTree_NoDupNameTree with (path := path); auto.
                   --- apply (Permutation_NoDup H13). constructor; auto.
                   --- rewrite addDidToTree_the_same_Fids; auto.
                   --- intros. apply Permutation_sym in H13.
                       apply (Permutation_in el H13) in H15.
                       simpl in H15. specialize (H5 el). destruct H15; intuition.
                   --- intros. rewrite addDidToTree_the_same_Fids in H15.
                       apply H6; auto.
                   --- unfold isDir in *. destruct H8 as [dd [ll ?]].
                       rewrite H8. simpl. rm_if; apply DnodeIsDir.
        * simpl in H; destruct H as [? [? [? [? [? [? ?]]]]]].
          apply path_in_tree_none in Heqo1; auto. inversion H0. left. auto.
  Qed.

  Lemma findDir_file_in_tree: forall fmap dmap d l fId name tree path,
      findDir dmap tree path = Some (Dnode d l) -> nameF (fmap fId) = name ->
      In (Fnode fId) l -> file_in_tree fmap dmap path name tree.
  Proof.
    intros fmap dmap d l fId name. induction tree using tree_ind2; intros;
                                     destruct path; simpl in H; [inversion H.. | |].
    - simpl in H0. inversion H0. subst. constructor. rewrite Exists_exists.
      exists (Fnode fId). intuition. constructor. auto.
    - simpl in H0. constructor.
      destruct (find (fun x : Tree => root_eq dmap x s) treeL) eqn:? .
      2: inversion H0. apply find_some in Heqo. destruct Heqo.
      unfold root_eq, DData_eqb in H4. destruct t. 1: inversion H4. rm_hif.
      2: inversion H4. clear H4. exists d0, l0. intuition.
      rewrite Forall_forall in H. apply H; intuition.
  Qed.

  Lemma findDir_path_in_tree: forall dmap d l dId ld name tree path,
      findDir dmap tree path = Some (Dnode d l) -> nameD (dmap dId) = name ->
      In (Dnode dId ld) l -> path_in_tree dmap (path ++ [name])%list tree.
  Proof.
    intros dmap d l dId ld name.
    induction tree using tree_ind2; intros; destruct path;
      simpl in H; [inversion H.. | |]; simpl in *.
    - inversion H0. subst. constructor. exists dId, ld. intuition. constructor.
    - constructor. destruct (find (fun x : Tree => root_eq dmap x s) treeL) eqn:? .
      2: inversion H0. apply find_some in Heqo. destruct Heqo.
      unfold root_eq, DData_eqb in H4. destruct t. 1: inversion H4. rm_hif.
      2: inversion H4. clear H4. exists d0, l0. intuition.
      rewrite Forall_forall in H. apply H; intuition.
  Qed.

  Lemma same_name_the_same_tree: forall fmap dmap treeL d l did' treeL',
      nameD (dmap did') = nameD (dmap d) -> NoDup (map (treeName fmap dmap) treeL) ->
      In (Dnode d l) treeL -> In (Dnode did' treeL') treeL ->
      Dnode d l = Dnode did' treeL'.
  Proof.
    intros. apply in_split in H1. destruct H1 as [l1 [l2 ?]]. subst treeL.
    rewrite in_app_iff in H2. simpl in H2.
    destruct H2 as [? | [? | ?]]; auto; exfalso; apply in_split in H1;
      destruct H1 as [l3 [l4 ?]].
    - subst l1. rewrite <- app_assoc in H0. rewrite map_app in H0.
      apply NoDup_app_r in H0. rewrite <- app_comm_cons in H0.
      rewrite map_cons in H0. simpl in H0.
      rewrite NoDup_cons_iff in H0. destruct H0 as [? _].
      rewrite map_app, map_cons in H0. apply H0. rewrite in_app_iff.
      right. simpl. left; auto.
    - subst l2. rewrite map_app in H0. apply NoDup_app_r in H0.
      rewrite map_cons, NoDup_cons_iff in H0. simpl in H0. destruct H0 as [? _].
      apply H0. rewrite map_app, map_cons, in_app_iff. right. simpl. left; auto.
  Qed.

  Lemma path_in_tree_treeName: forall fmap dmap d l name tree path,
      NoDupNameTree fmap dmap tree -> findDir dmap tree path = Some (Dnode d l) ->
      path_in_tree dmap (path ++ [name])%list tree ->
      In name (map (treeName fmap dmap) l).
  Proof.
    intros fmap dmap d l name. induction tree using tree_ind2; intros.
    1: inversion H1. destruct path; simpl in *; inversion H2; subst.
    - inversion H1. subst. destruct H4 as [did' [treeL [? [? ?]]]].
      rewrite in_map_iff. exists (Dnode did' treeL). simpl. intuition.
    - destruct (find (fun x : Tree => root_eq dmap x s) treeL) eqn: ?.
      2: inversion H1. rewrite Forall_forall in H.
      destruct H4 as [did' [treeL' [? [? ?]]]].
      apply find_some in Heqo. destruct Heqo. unfold root_eq, DData_eqb in H7.
      destruct t. 1: inversion H7. rm_hif. 2: inversion H7. clear H7.
      inversion H0. subst. assert (Dnode d0 l0 = Dnode did' treeL') by
          (eapply same_name_the_same_tree; eauto). inversion H7. subst.
      eapply H; eauto. rewrite Forall_forall in H11. apply H11; auto.
  Qed.

  Lemma file_in_tree_treeName: forall fmap dmap d l name tree path,
      NoDupNameTree fmap dmap tree -> findDir dmap tree path = Some (Dnode d l) ->
      file_in_tree fmap dmap path name tree -> In name (map (treeName fmap dmap) l).
  Proof.
    intros fmap dmap d l name.
    induction tree using tree_ind2; intros; destruct path; simpl in H0;
      [inversion H0.. | |]; simpl in *; rewrite Forall_forall in H.
    - inversion H1; subst. inversion H2. subst. rewrite Exists_exists in H6.
      destruct H6 as [x [? ?]]. destruct x; inversion H4. rewrite in_map_iff.
      exists (Fnode f). simpl. intuition.
    - destruct (find (fun x : Tree => root_eq dmap x s) treeL) eqn:? .
      2: inversion H1. apply find_some in Heqo. destruct Heqo.
      unfold root_eq, DData_eqb in H4. destruct t.
      1: inversion H4. rm_hif. 2: inversion H4. clear H4. inversion H2.
      subst. destruct H7 as [did' [treeL' [? [? ?]]]]. inversion H0; subst.
      assert (Dnode d0 l0 = Dnode did' treeL') by
          (eapply same_name_the_same_tree; eauto). inversion H7. subst.
      eapply H; eauto. rewrite Forall_forall in H11. apply H11; auto.
  Qed.

  Lemma fs_readdir_ok: forall (path: Path) (fs: FSState)
                              (result: list string) (err: ErrCode) (postFS: FSState),
      good_file_system (fsFS fs) -> (result, err, postFS) = fs_readdir path fs ->
      (~ path_in_tree (dMapFS fs) path (layoutFS fs) /\ result = nil /\ err = eBadF /\
       postFS = fs) \/
      (path_in_tree (dMapFS fs) path (layoutFS fs) /\ result = nil /\ err <> eSucc /\
       fsFS fs = fsFS postFS /\ logFS postFS = Call_VReadDir path err :: logFS fs) \/
      (path_in_tree (dMapFS fs) path (layoutFS fs)/\ err = eSucc /\
       fsFS fs = fsFS postFS /\ logFS postFS = Call_VReadDir path eSucc :: logFS fs /\
       forall name, In name result <->
                    path_in_tree (dMapFS fs) (path ++ [name])%list (layoutFS fs) \/
                    file_in_tree (fMapFS fs) (dMapFS fs) path name (layoutFS fs)).
  Proof.
    intros. unfold fs_readdir in H0. simpl in H0.
    destruct (findDir (d_map (fst fs)) (layout (fst fs)) path) eqn:? .
    - destruct t. 1: exfalso; revert Heqo; apply findDir_not_fnode.
      destruct fs. simpl in H0. rm_hif.
      + right. left. simpl. apply path_in_tree_some in Heqo. inversion H0; intuition.
      + right; right. inversion H0. subst; simpl. rewrite e. clear H0 e.
        intuition; [apply path_in_tree_some in Heqo; auto |
                    unfold dMapFS, fMapFS, layoutFS; simpl in *..].
        * rewrite in_map_iff in H0. destruct H0 as [t [? ?]].
          destruct t; simpl in H0; [right | left].
          -- eapply findDir_file_in_tree; eauto.
          -- eapply findDir_path_in_tree; eauto.
        * destruct H as [? [? [? ?]]]; eapply path_in_tree_treeName; eauto.
        * unfold dMapFS, fMapFS, layoutFS in H1. simpl in H1.
          destruct H as [? [? [? ?]]]. eapply file_in_tree_treeName; eauto.
    - apply path_in_tree_none in Heqo. 2: destruct H as [? [? [? ?]]]; auto.
      left. inversion H0; intuition.
  Qed.

  Lemma fs_fstat_ok: forall (id : Fid) (fs: FSState) (name: string)
                            (permsn: Permission) (fsize: nat) (pageIds : list Pgid)
                            (err: ErrCode) (postFS: FSState),
      (name, permsn, fsize, pageIds, err, postFS) = fs_fstat id fs ->
      (~ In id (map fst (openhandleFS fs)) /\ postFS = fs /\ err = eBadF /\
       name = EmptyString /\ permsn = fff /\ fsize = O /\ pageIds = nil) \/
      (In id (map fst (openhandleFS fs)) /\ fsFS postFS = fsFS fs /\ err <> eSucc /\
       name = EmptyString /\ permsn = fff /\ fsize = O /\ pageIds = nil /\
       logFS postFS = Call_VStat id err :: logFS fs) \/
      (In id (map fst (openhandleFS fs)) /\ fsFS postFS = fsFS fs /\ err = eSucc /\
       name = ((fMapFS fs) id).(nameF) /\
       permsn = ((fMapFS fs) id).(metaF).(permission) /\
       fsize = ((fMapFS fs) id).(metaF).(size) /\
       pageIds = ((fMapFS fs) id).(pageIdsF) /\
       logFS postFS = Call_VStat id eSucc :: logFS fs).
  Proof.
    intros. unfold fs_fstat in H. simpl in H.
    destruct (find (fun x : nat * nat => Nat.eqb (fst x) id) (open_handles (fst fs))) eqn:? .
    - destruct fs. simpl in *. destruct p. simpl in H. rm_hif; inversion H; right.
      + left. simpl. intuition. eapply find_Fid_In; eauto.
      + right. unfold openhandleFS, fMapFS, logFS. simpl. rewrite e.
        intuition. eapply find_Fid_In; eauto.
    - left. inversion H. intuition. eapply find_Fid_None; eauto.
  Qed.

  Lemma fs_chmod_ok: forall (path: Path) (p: Permission) (fs: FSState)
                            (err: ErrCode) (postFS: FSState),
      good_file_system (fsFS fs) -> (err, postFS) = fs_chmod (path, p) fs ->
      (~ path_in_tree (dMapFS fs) path (layoutFS fs) /\
       ~ file_in_tree (fMapFS fs) (dMapFS fs) (removelast path)
         (foot path) (layoutFS fs) /\ path <> nil /\ err = eNoEnt /\ postFS = fs) \/
      ((exists id,
           path_in_tree_with_id (dMapFS fs) path (layoutFS fs) id \/
           (path <> nil /\
            file_in_tree_with_id (fMapFS fs) (dMapFS fs)
                                 (removelast path) (foot path) (layoutFS fs) id)) /\
       fsFS fs = fsFS postFS /\ err <> eSucc /\
       logFS postFS = Call_VChmod path p err :: logFS fs) \/
      ((exists id, path_in_tree_with_id (dMapFS fs) path (layoutFS fs) id /\
                   (dMapFS postFS id).(metaD) = p /\
                   (dMapFS postFS id).(nameD) = (dMapFS fs id).(nameD) /\
                   forall did, did <> id -> dMapFS postFS did = dMapFS fs did) /\
       layoutFS fs = layoutFS postFS /\ openhandleFS fs = openhandleFS postFS /\
       vmFS fs = vmFS postFS /\ fMapFS fs = fMapFS postFS /\
       fCntFS fs = fCntFS postFS /\ dCntFS fs = dCntFS postFS /\
       mmap_handles (fsFS fs) = mmap_handles (fsFS postFS) /\
       mmap_memory (fsFS fs) = mmap_memory (fsFS postFS) /\
       err = eSucc /\ logFS postFS = Call_VChmod path p eSucc :: logFS fs) \/
      ((exists id,
           file_in_tree_with_id (fMapFS fs) (dMapFS fs)
                                (removelast path) (foot path) (layoutFS fs) id /\
           (fMapFS postFS id).(metaF).(permission) = p /\
           (fMapFS postFS id).(nameF) = (fMapFS fs id).(nameF) /\
           (fMapFS postFS id).(pageIdsF) = (fMapFS fs id).(pageIdsF) /\
           (fMapFS postFS id).(metaF).(size) = (fMapFS fs id).(metaF).(size) /\
           forall did, did <> id -> fMapFS postFS did = fMapFS fs did) /\
       path <> nil /\ layoutFS fs = layoutFS postFS /\
       openhandleFS fs = openhandleFS postFS /\ vmFS fs = vmFS postFS /\
       dMapFS fs = dMapFS postFS /\ fCntFS fs = fCntFS postFS /\
       dCntFS fs = dCntFS postFS /\ err = eSucc /\
       mmap_handles (fsFS fs) = mmap_handles (fsFS postFS) /\
       mmap_memory (fsFS fs) = mmap_memory (fsFS postFS) /\
       logFS postFS = Call_VChmod path p eSucc :: logFS fs).
  Proof.
    intros. unfold fs_chmod in H0. simpl in H0.
    destruct (findDir (d_map (fst fs)) (layout (fst fs)) path) eqn: ?.
    - destruct t. 1: exfalso; revert Heqo; apply findDir_not_fnode. destruct fs.
      unfold fsFS, logFS, dMapFS, layoutFS, openhandleFS, vmFS, fMapFS, fCntFS, dCntFS.
      simpl in *. apply path_in_tree_with_id_some in Heqo. rm_hif.
      + right. left. inversion H0. simpl. intuition. exists d. left; auto.
      + right. right. left. simpl in H0. inversion H0. simpl. rewrite e. intuition.
        exists d. split; auto. unfold change_d_map_permission.
        destruct (Nat.eq_dec d d). 2: exfalso; apply n; auto. simpl. intuition. rm_if.
        exfalso. auto.
    - destruct path eqn:? .
      + exfalso. simpl in Heqo. destruct (layout (fst fs)) eqn:? . 2: inversion Heqo.
        destruct H as [? [? [? [? [? [? [? [? ?]]]]]]]]. unfold isDir, fsFS in H6.
        destruct H6 as [? [? ?]]. rewrite H6 in Heqt. inversion Heqt.
      + assert (path <> nil) by (rewrite Heqp0; intro; inversion H1).
        rewrite <- Heqp0 in *. clear s p0 Heqp0.
        destruct (findMatchedFid (fst fs) (removelast path) (foot path)) eqn:? .
        * destruct fs. unfold fsFS, logFS, dMapFS, layoutFS, openhandleFS, vmFS,
                       fMapFS, fCntFS, dCntFS. simpl in *.
          apply file_in_tree_with_id_some in Heqo0. 2: destruct H; auto. rm_hif.
          -- right. left. inversion H0. simpl. intuition. exists f. intuition.
          -- do 3 right. simpl in H0. inversion H0. simpl. rewrite e. intuition.
             exists f. split; auto. unfold change_f_map_permission. rm_if.
             2: exfalso; apply n; auto. simpl. intuition. rm_if. exfalso; intuition.
        * left. destruct H. apply path_in_tree_none in Heqo; auto.
          apply file_in_tree_none in Heqo0; auto. inversion H0. intuition.
  Qed.

  Lemma getSublist_length {A}: forall n m (l: list A), length (getSublist n m l) <= m.
  Proof.
    intros; revert n m. induction l; intros; simpl.
    1: destruct n; destruct m; simpl; intuition. destruct n.
    2: apply IHl. destruct m; simpl; intuition.
  Qed.

  Lemma getSublist_prefix {A}: forall m (l: list A), exists l',
        l = (getSublist 0 m l ++ l')%list.
  Proof.
    intros; revert m. induction l; intros; simpl.
    - exists []. destruct m; simpl; auto.
    - destruct m.
      + exists (a :: l). simpl; auto.
      + destruct (IHl m) as [l' ?]. exists l'. rewrite H at 1. simpl; auto.
  Qed.

  Opaque psize block_size.

  Lemma fs_truncate_ok:
    forall (fId : Fid) (len : nat) (fs: FSState) (err: ErrCode) (postFS : FSState),
      good_file_system (fsFS fs) -> (err, postFS) = fs_truncate (fId, len) fs ->
      (~ In fId (map fst (openhandleFS fs)) /\ postFS = fs /\ err = eBadF) \/
      (In fId (map fst (openhandleFS fs)) /\ postFS = fs /\ err = eInval) \/
      (In fId (map fst (openhandleFS fs)) /\ postFS = fs /\
       (fMapFS fs fId).(metaF).(size) = len /\ err = eSucc) \/
      (In fId (map fst (openhandleFS fs)) /\ err <> eSucc /\ fsFS fs = fsFS postFS /\
       exists pos content,
         logFS postFS = Call_VTruncate fId pos content err :: logFS fs) \/
      (In fId (map fst (openhandleFS fs)) /\ err = eSucc /\
       layoutFS fs = layoutFS postFS /\ openhandleFS fs = openhandleFS postFS /\
       vmFS fs = vmFS postFS /\ dMapFS fs = dMapFS postFS /\
       fCntFS fs = fCntFS postFS /\ dCntFS fs = dCntFS postFS /\
       mmap_handles (fsFS fs) = mmap_handles (fsFS postFS) /\
       mmap_memory (fsFS fs) = mmap_memory (fsFS postFS) /\
       (fMapFS postFS fId).(nameF) = (fMapFS fs fId).(nameF) /\
       (fMapFS postFS fId).(metaF).(permission) =
       (fMapFS fs fId).(metaF).(permission) /\
       (fMapFS postFS fId).(metaF).(size) = len /\
       length ((fMapFS postFS fId).(pageIdsF)) <= len / psize + 1 /\
       (forall id, id <> fId -> fMapFS postFS id = fMapFS fs id) /\
       (exists l, (fMapFS fs fId).(pageIdsF) =
                  ((fMapFS postFS fId).(pageIdsF) ++ l)%list)).
  Proof.
    intros. unfold fs_truncate in H0. simpl in H0.
    remember (if Nat.eq_dec (len mod psize) 0 then len / psize else len / psize + 1).
    remember (len / psize * block_size).
    remember (encrypt_page
                (truncate_page
                   (byte_list_to_string (nth (nth n (pageIdsF (f_map (fst fs) fId)) 0)
                                             (virtual_memory (fst fs)) [])) 0
                   (len mod psize))).
    destruct (find (fun x : nat * nat => Nat.eqb (fst x) fId) (open_handles (fst fs))) eqn:? .
    - apply find_Fid_In in Heqo. right. rm_hif.
      + left. inversion H0; auto.
      + destruct fs. simpl in H0. right. rm_hmatch.
        * left. apply beq_nat_true in Heqb. inversion H0. intuition.
        * simpl in H0. right. rm_hif.
          -- left. inversion H0. simpl. intuition. exists n0, s. auto.
          -- right. simpl in H0. inversion H0.
             unfold fsFS, logFS, dMapFS, layoutFS, openhandleFS, vmFS, fMapFS, fCntFS,
             dCntFS, change_f_map_size, change_f_map_pages. simpl in *.
             do 8 (split; auto). destruct (Nat.eq_dec fId fId). 2: exfalso; intuition.
             simpl. intuition.
             ++ transitivity n. 1: apply getSublist_length. subst n. rm_if; intuition.
             ++ destruct (Nat.eq_dec id fId); intuition.
             ++ apply getSublist_prefix.
    - inversion H0. left. intuition. apply find_Fid_None in H1; auto.
  Qed.

  Transparent psize block_size.

  Lemma addFnodeToTree_in_tree: forall fmap dmap d cnt fname meta pgids tree path,
      NoDup (collectDids tree) -> path_in_tree_with_id dmap path tree d ->
      file_in_tree_with_id (change_f_map fmap cnt (Build_FData fname meta pgids))
                           dmap path fname (addFnodeToTree tree d cnt) cnt.
  Proof.
    intros. revert path H H0. induction tree using tree_ind2; intros.
    1: inversion H0. destruct path; inversion H1; subst.
    - simpl. rm_if. 2: exfalso; auto.
      constructor; [simpl; left | unfold change_f_map; rm_if; exfalso]; auto.
    - destruct H7 as [did' [treeL' [? [? ?]]]]. simpl. rm_if.
      + exfalso. revert e. eapply path_in_tree_nonempty_neq; eauto. intro.
        inversion H5.
      + constructor. rewrite Forall_forall in H. specialize (H _ H2).
        assert (NoDup (collectDids (Dnode did' treeL'))) by
            (apply subtree_nodup with (t := Dnode did' treeL') in H0; auto).
        specialize (H _ H5 H4).
        simpl in H. apply (in_map (fun t : Tree => addFnodeToTree t d cnt)) in H2.
        simpl in H2. destruct (Nat.eq_dec d did').
        * subst d. exists did', (Fnode cnt :: treeL'). split; [|split]; auto.
        * exists did', (map (fun t : Tree => addFnodeToTree t d cnt) treeL').
          split; [|split]; auto.
  Qed.

  Lemma addFnodeToTree_the_same_dids: forall tree d cnt,
      collectDids (addFnodeToTree tree d cnt) = collectDids tree.
  Proof.
    induction tree using tree_ind2; intros; simpl; auto.
    rm_if; [subst |]; simpl; auto. f_equal. rewrite !flat_map_concat_map.
    f_equal. rewrite map_map. apply map_ext_in.
    intros. rewrite Forall_forall in H. apply H; auto.
  Qed.

  Lemma addFnodeToTree_the_same: forall d cnt tree,
      ~ In d (collectDids tree) -> addFnodeToTree tree d cnt = tree.
  Proof.
    intros. induction tree using tree_ind2; simpl; auto. rm_if.
    1: subst; exfalso; apply H; simpl; left; auto.
    rewrite Forall_forall in H0. f_equal. simpl in H. assert (treeL = map id treeL) by
        (clear; induction treeL; simpl; [|rewrite IHtreeL at 1]; auto).
    rewrite H1 at 2. clear H1. apply map_ext_in. intros. unfold id. apply H0; auto.
    intro. apply H. right. apply (subtree_did_in_merge a); auto.
  Qed.

  Lemma addFnodeToTree_the_same_list: forall d cnt l,
      ~ In d (flat_map collectDids l) -> map (fun t => addFnodeToTree t d cnt) l = l.
  Proof.
    intros. assert (l = map id l) by
        (clear; induction l; simpl; [|rewrite IHl at 1]; auto).
    rewrite H0 at 2; clear H0. apply map_ext_in. unfold id. intros.
    apply addFnodeToTree_the_same. intro; apply H.
    apply (subtree_did_in_merge a); auto.
  Qed.

  Lemma addFnodeToTree_map_the_same:
    forall (l1 l2 : list Tree) (did' : Did) (treeL' : list Tree) (d cnt : Did),
      NoDup (flat_map collectDids (l1 ++ Dnode did' treeL' :: l2)) ->
      In d (collectDids (Dnode did' treeL')) ->
      map (fun t : Tree => addFnodeToTree t d cnt) (l1 ++ Dnode did' treeL' :: l2) =
      (l1 ++ addFnodeToTree (Dnode did' treeL') d cnt :: l2)%list.
  Proof.
    intros; rewrite map_app, map_cons. rewrite flat_map_collectDids in H.
    f_equal; [|f_equal]; apply addFnodeToTree_the_same_list.
    - apply NoDup_app_not_in_l with (y := d) in H; auto. apply in_or_app. left; auto.
    - apply NoDup_app_r in H. apply NoDup_app_not_in_r with (y := d) in H; auto.
  Qed.

  Lemma flat_map_collectFids: forall l1 l2 t,
      flat_map collectFids (l1 ++ t :: l2) =
      (flat_map collectFids l1 ++ collectFids t ++ flat_map collectFids l2)%list.
  Proof.
    intros. rewrite flat_map_concat_map, map_app, map_cons,
            concat_app, concat_cons, <- !flat_map_concat_map; auto.
  Qed.

  Lemma addFnodeToTree_Permutation: forall dmap cnt d tree path,
      NoDup (collectDids tree) -> path_in_tree_with_id dmap path tree d ->
      ~ In cnt (collectFids tree) ->
      Permutation (cnt :: collectFids tree) (collectFids (addFnodeToTree tree d cnt)).
  Proof.
    intros dmap cnt d. induction tree using tree_ind2; intros; simpl. 1: inversion H0.
    rewrite Forall_forall in H. rm_if. simpl. destruct path; inversion H1; subst.
    1: exfalso; apply n; auto. destruct H8 as [did' [treeL' [? [? ?]]]].
    pose proof H5. rename H6 into HS. apply in_split in H3. destruct H3 as [l1 [l2 ?]].
    subst treeL. apply path_in_tree_collectDids in H5. simpl in H0.
    rewrite NoDup_cons_iff in H0. destruct H0.
    rewrite !addFnodeToTree_map_the_same; auto.
    rewrite !flat_map_collectFids, app_comm_cons, !app_assoc.
    apply Permutation_app_tail. rewrite <- app_comm_cons.
    apply Permutation_trans with
        (flat_map collectFids l1 ++ cnt :: collectFids (Dnode did' treeL'))%list.
    1: apply Permutation_middle. apply Permutation_app_head.
    apply H with (path := path); auto.
    - rewrite in_app_iff. right; simpl; left; auto.
    - rewrite flat_map_collectDids in H3. apply NoDup_app_r, NoDup_app_l in H3; auto.
    - intro; apply H2. simpl. rewrite flat_map_collectFids, in_app_iff.
      right. simpl in *. intuition.
  Qed.

  Lemma change_f_map_NoDupNameTree: forall fmap dmap cnt d t,
      ~ In cnt (collectFids t) -> NoDupNameTree fmap dmap t ->
      NoDupNameTree (change_f_map fmap cnt d) dmap t.
  Proof.
    intros fmap dmap cnt d. induction t using tree_ind2; intros; constructor.
    - rewrite Forall_forall in *. intros. apply H; auto.
      + intro. apply H0. simpl. rewrite in_flat_map. exists x; intuition.
      + inversion H1. subst. rewrite Forall_forall in H7. apply H7; auto.
    - inversion H1. subst.
      assert (map (treeName fmap dmap) treeL =
              map (treeName (change_f_map fmap cnt d) dmap) treeL). {
        apply map_ext_in. intros. unfold change_f_map. destruct a; simpl; auto. rm_if.
        exfalso. apply H0. simpl. rewrite in_flat_map. subst f.
        exists (Fnode cnt). split; simpl; intuition.
      } rewrite <- H2. auto.
  Qed.

  Lemma treeName_eq_treeL': forall fmap dmap cnt d treeL,
      ~ In cnt (flat_map collectFids treeL) ->
      map (treeName fmap dmap) treeL =
      map (treeName (change_f_map fmap cnt d) dmap) treeL.
  Proof.
    intros. apply map_ext_in. intros. unfold change_f_map. destruct a; simpl; auto.
    rm_if. subst. exfalso. apply H. rewrite in_flat_map. exists (Fnode cnt).
    simpl; auto.
  Qed.

  Lemma addFnodeToTree_NoDupNameTree:
    forall fmap dmap fname cnt d meta pgids tree path,
      ~ file_in_tree fmap dmap path fname tree ->
      ~ path_in_tree dmap (path ++ [fname])%list tree ->
      path_in_tree_with_id dmap path tree d -> ~ In cnt (collectFids tree) ->
      NoDupNameTree fmap dmap tree -> NoDup (collectDids tree) ->
      NoDupNameTree (change_f_map fmap cnt (Build_FData fname meta pgids)) dmap
                    (addFnodeToTree tree d cnt).
  Proof.
    intros fmap dmap fname cnt d meta pgids. induction tree using tree_ind2; intros.
    1: inversion H1. destruct path; inversion H2; subst.
    - simpl in *. rm_if. 2: exfalso; auto. clear e H. constructor.
      + rewrite Forall_forall. intros. simpl in H. destruct H. 1: subst x; constructor.
        inversion H4. subst. rewrite Forall_forall in H10. specialize (H10 _ H).
        apply change_f_map_NoDupNameTree; auto. intro. apply H3. rewrite in_flat_map.
        exists x; auto.
      + simpl. unfold change_f_map at 1. rm_if. 2: exfalso; auto. simpl. clear e.
        rewrite <- treeName_eq_treeL'; auto. constructor. 2: inversion H4; auto.
        intro. rewrite in_map_iff in H. destruct H as [x [? ?]]. destruct x.
        * apply H0. constructor. rewrite Exists_exists. exists (Fnode f). split; auto.
          constructor. simpl in H. auto.
        * apply H1. constructor. exists d0, l. simpl in H. intuition. constructor.
    - destruct H11 as [did' [treeL' [? [? ?]]]]. simpl. rm_if.
      + exfalso. revert e. eapply path_in_tree_nonempty_neq; eauto.
        intro. inversion H9.
      + assert (NoDupNameTree (change_f_map fmap cnt (Build_FData fname meta pgids))
                              dmap (addFnodeToTree (Dnode did' treeL') d cnt)). {
          rewrite Forall_forall in H. apply H with (path := path); try intro; auto.
          - apply H0; constructor; exists did', treeL'; intuition.
          - apply H1; simpl; constructor; exists did', treeL'; intuition.
          - apply H3; simpl. rewrite in_flat_map. exists (Dnode did' treeL'); auto.
          - inversion H4. subst. rewrite Forall_forall in H13. apply H13. auto.
          - apply (subtree_nodup _ _ _ H6 H5).
        } clear H. apply in_split in H6. destruct H6 as [l1 [l2 ?]]. subst treeL.
        apply path_in_tree_collectDids in H8.
        rewrite addFnodeToTree_map_the_same; auto. inversion H4. subst.
        2: simpl in H5; rewrite NoDup_cons_iff in H5; destruct H5; auto. constructor.
        * rewrite Forall_forall in *. intros. simpl in H3.
          rewrite flat_map_collectFids in H3. rewrite in_app_iff in H.
          destruct H; [|apply in_inv in H; destruct H];
            [apply change_f_map_NoDupNameTree | subst x |
             apply change_f_map_NoDupNameTree ]; auto.
          -- intro. apply H3. rewrite in_app_iff. left. rewrite in_flat_map.
             exists x; auto.
          -- apply H12. rewrite in_app_iff. left; auto.
          -- intro. apply H3. do 2 (rewrite in_app_iff; right). rewrite in_flat_map.
             exists x; auto.
          -- apply H12. rewrite in_app_iff. right. simpl. right; auto.
        * rewrite map_app, map_cons in *. simpl in H13. simpl in H3.
          rewrite flat_map_collectFids in H3.
          assert (treeName (change_f_map fmap cnt (Build_FData fname meta pgids))
                           dmap (addFnodeToTree (Dnode did' treeL') d cnt) =
                  nameD (dmap did')) by (simpl; rm_if; subst d; simpl; auto).
          rewrite H; clear H. rewrite <- !treeName_eq_treeL'; auto; intro; apply H3;
                                rewrite !in_app_iff; [right; right | left]; auto.
  Qed.

  Lemma fs_create_ok: forall (path : Path) (fname : string) (p : Permission)
                             (fs : FSState) (err : ErrCode) (postFS : FSState),
      good_file_system (fsFS fs) -> (err, postFS) = fs_create (path, fname, p) fs ->
      (fname = EmptyString /\ err = eBadName /\ postFS = fs) \/
      (file_in_tree (fMapFS fs) (dMapFS fs) path fname (layoutFS fs) /\
       err = eExists /\ fs = postFS) \/
      (path_in_tree (dMapFS fs) (path ++ [fname])%list (layoutFS fs) /\
       err = eIsDir /\ fs = postFS) \/
      (~ path_in_tree (dMapFS fs) path (layoutFS fs) /\ err = eNoDir /\ fs = postFS) \/
      ((exists did, path_in_tree_with_id (dMapFS fs) path (layoutFS fs) did /\
                    ((dMapFS fs) did).(metaD).(writable) = false) /\ err = eAcces /\
       fs = postFS) \/
      ((exists did, path_in_tree_with_id (dMapFS fs) path (layoutFS fs) did /\
                    ((dMapFS fs) did).(metaD).(writable) = true) /\
       err <> eSucc /\ fsFS fs = fsFS postFS /\
       logFS postFS = Call_VCreate path fname p err :: logFS fs) \/
      ((exists did, path_in_tree_with_id (dMapFS fs) path (layoutFS fs) did /\
                    ((dMapFS fs) did).(metaD).(writable) = true) /\ err = eSucc /\
       logFS postFS = Call_VCreate path fname p eSucc :: logFS fs /\
       openhandleFS fs = openhandleFS postFS /\ vmFS fs = vmFS postFS /\
       dMapFS fs = dMapFS postFS /\ fCntFS fs + 1 = fCntFS postFS /\
       dCntFS fs = dCntFS postFS /\
       mmap_handles (fsFS fs) = mmap_handles (fsFS postFS) /\
       mmap_memory (fsFS fs) = mmap_memory (fsFS postFS) /\
       fMapFS postFS (fCntFS fs) = Build_FData fname (Build_Meta p O) nil /\
       (forall id, id <> fCntFS fs -> fMapFS fs id = fMapFS postFS id) /\
       file_in_tree_with_id (fMapFS postFS) (dMapFS postFS) path fname
                            (layoutFS postFS) (fCntFS fs) /\
       good_file_system (fsFS postFS)).
  Proof.
    intros. unfold fs_create in H0. simpl in H0. rm_hif.
    - left; inversion H0; intuition.
    - right. destruct H. unfold fsFS in *. rm_hmatch.
      + left; apply file_in_tree_some in Heqo; inversion H0; auto.
      + right. rm_hmatch.
        * left. apply path_in_tree_some in Heqo0. inversion H0; auto.
        * right. apply file_in_tree_none in Heqo; auto.
          apply path_in_tree_none in Heqo0; auto. rm_hmatch.
          -- right. destruct t. 1: exfalso; revert Heqo1; apply findDir_not_fnode.
             apply path_in_tree_with_id_some in Heqo1. rm_hmatch.
             ++ left. apply bool_eq_ok in Heqb. inversion H0. intuition.
                exists d. intuition.
             ++ right. destruct fs. simpl in H0. unfold bool_eq in Heqb.
                destruct (writable (metaD (d_map (fst (f, l0)) d))) eqn:? .
                2: simpl in Heqb; inversion Heqb. rm_hif.
                ** left. simpl. inversion H0. intuition. exists d. intuition.
                ** right. simpl in H0. unfold logFS, openhandleFS, vmFS, dMapFS,
                                       fCntFS, dCntFS, fMapFS, fsFS, layoutFS in *.
                   inversion H0; simpl. rewrite e.
                   intuition; [exists d; intuition | unfold change_f_map; rm_if;
                                                     exfalso; intuition.. | |].
                   --- apply addFnodeToTree_in_tree; auto.
                   --- simpl in *.
                       assert (~ In (fnode_ctr f) (collectFids (layout f))) by
                           (intro S; apply H6 in S; intuition).
                       pose proof (addFnodeToTree_Permutation _ _ _ _ _ H2 Heqo1 H13).
                       split; [|split; [|split; [|split; [|split; [|split; [|split; [|split;[|split;[|split]]]]]]]]]; simpl; auto.
                       +++ apply addFnodeToTree_NoDupNameTree with (path := path);
                             auto.
                       +++ rewrite addFnodeToTree_the_same_dids. auto.
                       +++ apply (Permutation_NoDup H15). constructor; auto.
                       +++ intros. rewrite addFnodeToTree_the_same_dids in H16.
                           apply H5; auto.
                       +++ intros. apply Permutation_sym in H15.
                           apply (Permutation_in el H15) in H16. simpl in H16.
                           specialize (H6 el). destruct H16; intuition.
                       +++ unfold isDir in H8. destruct H8 as [dd [ll ?]]. rewrite H8.
                           simpl. rm_if; apply DnodeIsDir.
                       +++ intros. unfold change_f_map in H18, H17.
                           rm_hif; rm_hif; simpl in *; [exfalso; auto..|]. intro.
                           apply (H9 fId1 fId2 pgId1 pgId2); auto.
                       +++ intros. unfold change_f_map in H16. rm_hif; simpl in H16.
                           1: exfalso; auto. eapply H10; eauto.
          -- left. apply path_in_tree_none in Heqo1; auto. inversion H0; auto.
  Qed.

  Lemma path_in_tree_removelast: forall dmap tree path,
      path_in_tree dmap path tree -> path_in_tree dmap (removelast path) tree.
  Proof.
    intro. induction tree using tree_ind2; intros. 1: inversion H.
    rewrite Forall_forall in H. destruct path. 1: simpl; auto. inversion H0. subst.
    destruct H2 as [did' [treeL' [? [? ?]]]]. simpl. destruct path eqn:? .
    constructor. rewrite <- Heql in *. clear s0 l Heql. constructor.
    exists did', treeL'. specialize (H _ H1 _ H3). intuition.
  Qed.

  Lemma removeDirFromList_app:
    forall l1 l2 did, removeDirFromList (l1 ++ l2) did =
                      (removeDirFromList l1 did ++ removeDirFromList l2 did)%list.
  Proof.
    induction l1; intros; simpl; auto. destruct a.
    - simpl. f_equal. apply IHl1.
    - destruct (Nat.eq_dec d did); simpl; [|f_equal]; apply IHl1.
  Qed.

  Lemma removeDirFromList_the_same: forall did l,
      ~ In did (flat_map collectDids l) -> removeDirFromList l did = l.
  Proof.
    intros. induction l; simpl; auto. destruct a.
    - f_equal. apply IHl. simpl in H. auto.
    - simpl in H. rm_if. 1: exfalso; apply H; left; auto. f_equal.
      apply IHl. intro; apply H; right. rewrite in_app_iff. right; auto.
  Qed.

  Lemma removeDirFromTree_the_same: forall d cnt tree,
      ~ In d (collectDids tree) -> removeDirFromTree tree d cnt = tree.
  Proof.
    intros. induction tree using tree_ind2; simpl; auto.
    rewrite Forall_forall in H0. rm_if.
    - exfalso. subst. apply H. simpl. left; auto.
    - f_equal. assert (treeL = map id treeL) by
          (clear; induction treeL; simpl; [|rewrite IHtreeL at 1]; auto).
      rewrite H1 at 2.
      apply map_ext_in. intros. apply H0; auto. unfold id. intro. apply H.
      simpl. right. apply (subtree_did_in_merge a); auto.
  Qed.

  Lemma removeDirFromTree_the_same_list: forall d cnt l,
      ~ In d (flat_map collectDids l) ->
      map (fun t => removeDirFromTree t d cnt) l = l.
  Proof.
    intros. assert (l = map id l) by
        (clear; induction l; simpl; [|rewrite IHl at 1]; auto).
    rewrite H0 at 2; clear H0. apply map_ext_in. unfold id. intros.
    apply removeDirFromTree_the_same. intro; apply H.
    apply (subtree_did_in_merge a); auto.
  Qed.

  Lemma removeDirFromTree_map_the_same: forall tl1 tl2 did' treeL' d cnt,
      NoDup (flat_map collectDids (tl1 ++ Dnode did' treeL' :: tl2)) ->
      In d (collectDids (Dnode did' treeL')) ->
      map (fun t : Tree => removeDirFromTree t d cnt)
          (tl1 ++ Dnode did' treeL' :: tl2) =
      (tl1 ++ removeDirFromTree (Dnode did' treeL') d cnt :: tl2)%list.
  Proof.
    intros. rewrite flat_map_collectDids in H. rewrite map_app, map_cons.
    rewrite !removeDirFromTree_the_same_list; auto.
    - apply NoDup_app_r in H. apply NoDup_app_not_in_r with (y := d) in H; auto.
    - apply NoDup_app_not_in_l with (y := d) in H; auto. rewrite in_app_iff.
      left; auto.
  Qed.

  Lemma removeDirFromTree_not_in_tree:
    forall (fmap : Fid -> FData) (dmap : Did -> DData)
           (d cnt : Did) (da : DData) (dname: string) (tree : Tree) (path : Path),
      NoDup (collectDids tree) -> NoDupNameTree fmap dmap tree ->
      path_in_tree_with_id dmap path tree d ->
      path_in_tree_with_id dmap (path ++ [dname])%list tree cnt ->
      ~ path_in_tree (change_d_map dmap cnt da)
        (path ++ [dname])%list (removeDirFromTree tree d cnt).
  Proof.
    intros fmap dmap d cnt da dname. induction tree using tree_ind2; intros.
    1: inversion H1. rewrite Forall_forall in H.
    destruct path; simpl in *; inversion H2; subst.
    - rm_if. clear e. inversion H3. subst. destruct H9 as [did' [treeL' [? [? ?]]]].
      inversion H6. subst. apply in_split in H4. destruct H4 as [l1 [l2 ?]].
      subst treeL. rewrite NoDup_cons_iff in H0. destruct H0.
      rewrite flat_map_collectDids in H4. simpl in H4. apply NoDup_remove_2 in H4.
      rewrite removeDirFromList_app. simpl. rm_if. clear e.
      assert (~ In cnt (flat_map collectDids l1)) by
          (intro; apply H4; rewrite in_app_iff; left; auto).
      assert (~ In cnt (flat_map collectDids l2)) by
          (intro; apply H4; rewrite !in_app_iff; right; right; auto).
      rewrite !removeDirFromList_the_same; auto. intro. inversion H8. subst.
      destruct H10 as [cnt' [l [? [? ?]]]]. inversion H1. subst.
      rewrite map_app, map_cons in H17. simpl in H17. apply NoDup_remove_2 in H17.
      rewrite <- map_app in H17. remember (l1 ++ l2)%list as ll.
      assert (~ In cnt (flat_map collectDids ll)). {
        subst ll. rewrite flat_map_concat_map, map_app, concat_app,
                  <- !flat_map_concat_map. intro. rewrite in_app_iff in H12.
        destruct H12; [apply H5 | apply H7]; auto.
      } unfold change_d_map in H10. rm_hif.
      + subst cnt'. apply H12.
        apply subtree_did_in_merge with (t := Dnode cnt l); auto. simpl. left; auto.
      + apply in_split in H9. destruct H9 as [l3 [l4 ?]]. rewrite H9 in H17.
        apply H17. rewrite map_app, map_cons. simpl. rewrite in_app_iff. right.
        simpl. left; auto.
    - destruct H9 as [did' [treeL' [? [? ?]]]]. rm_if.
      + exfalso. revert e. eapply path_in_tree_nonempty_neq; eauto.
        intro. inversion H7.
      + inversion H3. subst. destruct H12 as [d0 [l0 [? [? ?]]]]. inversion H1. subst.
        assert (Dnode did' treeL' = Dnode d0 l0) by
            (eapply same_name_the_same_tree; eauto). inversion H9. subst d0 l0.
        clear H7 H5 H9. specialize (H _ H4 path). intro.
        inversion H5; subst. clear H2 H3 H5.
        destruct H9 as [d2 [l2 [? [? ?]]]]. unfold change_d_map in H3.
        rewrite NoDup_cons_iff in H0.
        destruct H0. apply in_split in H4. destruct H4 as [tl1 [tl2 ?]]. subst treeL.
        rewrite removeDirFromTree_map_the_same in H2; auto.
        2: apply path_in_tree_collectDids in H6; auto.
        rewrite flat_map_collectDids in H7.
        assert (NoDup (collectDids (Dnode did' treeL'))) by
            (apply NoDup_app_r, NoDup_app_l in H7; auto).
        rewrite Forall_forall in H13.
        assert (NoDupNameTree fmap dmap (Dnode did' treeL')) by
            (apply H13; rewrite in_app_iff; right; simpl; left; auto).
        specialize (H H4 H9 H6 H8).
        rewrite in_app_iff in H2. Opaque removeDirFromTree. simpl in H2.
        Transparent removeDirFromTree.
        assert (removeDirFromTree (Dnode did' treeL') d cnt = Dnode d2 l2 \/
                In (Dnode d2 l2) (tl1 ++ tl2)) by
            (destruct H2 as [? | [? | ?]]; intuition). clear H2.
        destruct H10. 1: rewrite <- H2 in *; apply H; auto. clear H. rm_hif.
        * subst d2. clear -H2 H8 H7. apply path_in_tree_collectDids in H8.
          pose proof H7. apply NoDup_app_not_in_l with (y := cnt) in H7.
          2: rewrite in_app_iff; left; auto.
          apply NoDup_app_r, NoDup_app_not_in_r with (y := cnt) in H; auto.
          assert (~ In cnt (flat_map collectDids (tl1 ++ tl2))). {
            rewrite flat_map_concat_map, map_app, concat_app,
            <- !flat_map_concat_map. intro. rewrite in_app_iff in H0.
            destruct H0; auto.
          } remember (tl1 ++ tl2)%list as tl. clear Heqtl H7 H. apply in_split in H2.
          destruct H2 as [tl3 [tl4 ?]]. subst tl. apply H0.
          rewrite flat_map_collectDids.
          rewrite !in_app_iff. right; left; simpl; left; auto.
        * clear -H14 H3 H2. rewrite map_app, map_cons in H14.
          simpl in H14. apply NoDup_remove_2 in H14. rewrite <- map_app in H14.
          remember (tl1 ++ tl2)%list as tl. clear tl1 tl2 Heqtl.
          apply in_split in H2. destruct H2 as [tl1 [tl2 ?]]. subst tl. apply H14.
          rewrite map_app, map_cons. simpl. rewrite in_app_iff. simpl. intuition.
  Qed.

  Lemma findDir_path_in_tree_with_id : forall fmap dmap d tree path,
      NoDupNameTree fmap dmap tree -> path_in_tree_with_id dmap path tree d ->
      exists l, findDir dmap tree path = Some (Dnode d l).
  Proof.
    intros fmap dmap d. induction tree using tree_ind2; intros. 1: inversion H0.
    rewrite Forall_forall in H. destruct path; inversion H1; subst; simpl.
    1: (exists treeL; auto). destruct H7 as [did' [treeL' [? [? ?]]]].
    destruct (find (fun x : Tree => root_eq dmap x s) treeL) eqn:? .
    - destruct t. 1: exfalso; apply find_some in Heqo; destruct Heqo;
                    unfold root_eq in H6; inversion H6.
      apply find_some in Heqo. destruct Heqo. unfold root_eq, DData_eqb in H6.
      rm_hif. 2: inversion H6. rewrite <- H3 in e. inversion H0; subst.
      assert (Dnode did' treeL' = Dnode d0 l) by
          (eapply same_name_the_same_tree; eauto). inversion H3. subst. apply H; auto.
      rewrite Forall_forall in H11. apply H11; auto.
    - apply find_none with (x := Dnode did' treeL') in Heqo; auto. exfalso.
      unfold root_eq, DData_eqb in Heqo. rm_hif; intuition.
  Qed.

  Definition empty_directory fmap dmap tree path : Prop :=
    path_in_tree dmap path tree /\
    forall name, ~ path_in_tree dmap (path ++ [name])%list tree /\
                 ~ file_in_tree fmap dmap path name tree.

  Definition empty_directory_with_id fmap dmap tree path d : Prop :=
    path_in_tree_with_id dmap path tree d /\
    forall name, ~ path_in_tree dmap (path ++ [name])%list tree /\
                 ~ file_in_tree fmap dmap path name tree.

  Lemma findDir_empty_directory_with_id: forall fmap dmap d tree path,
      NoDupNameTree fmap dmap tree -> findDir dmap tree path = Some (Dnode d nil) ->
      empty_directory_with_id fmap dmap tree path d.
  Proof.
    intros. split. apply path_in_tree_with_id_some in H0; auto.
    revert tree path H H0. induction tree using tree_ind2; intros.
    1: destruct path; simpl in H0; inversion H0. destruct path; simpl in H1.
    - inversion H1. subst. simpl.
      split; intro; inversion H2; subst;
        [destruct H4 as [? [? [? ?]]] |
         rewrite Exists_exists in H6; destruct H6 as [? [? ?]]]; inversion H3.
    - rewrite Forall_forall in H. rm_hmatch. 2: inversion H1. destruct t.
      1: exfalso; apply find_some in Heqo; destruct Heqo;
        unfold root_eq in H3; inversion H3.
      apply find_some in Heqo. destruct Heqo. unfold root_eq, DData_eqb in H3. rm_hif.
      2: inversion H3. simpl. inversion H0. subst. rewrite Forall_forall in H8.
      split; intro; inversion H4; subst; [|rename H10 into H6];
        destruct H6 as [did' [treeL' [? [? ?]]]];
        assert (Dnode d0 l = Dnode did' treeL') by
            (eapply same_name_the_same_tree; eauto); inversion H10; subst; clear H10;
          specialize (H _ H2 path (H8 _ H2) H1 name); destruct H; auto.
  Qed.

  Lemma removeDirFromTree_the_same_Fids: forall fmap dmap tree path name pid d,
      NoDup (collectDids tree) -> NoDupNameTree fmap dmap tree ->
      path_in_tree_with_id dmap path tree pid ->
      empty_directory_with_id fmap dmap tree (path ++ [name])%list d ->
      collectFids (removeDirFromTree tree pid d) = collectFids tree.
  Proof.
    intros fmap dmap tree path name pid d; revert tree path.
    induction tree using tree_ind2; intros; simpl; auto. rm_if.
    - simpl. subst did. destruct path.
      + simpl in *. destruct H3. inversion H3; subst.
        destruct H10 as [did' [treeL' [? [? ?]]]]. inversion H7; subst.
        destruct treeL'.
        * apply in_split in H5. destruct H5 as [l1 [l2 ?]]. subst treeL.
          rewrite removeDirFromList_app. simpl. rm_if. 2: exfalso; auto. clear e.
          apply NoDup_cons_iff in H0. destruct H0. rewrite flat_map_collectDids in H5.
          simpl in H5. apply NoDup_remove_2 in H5. rewrite flat_map_collectFids.
          simpl. rewrite !removeDirFromList_the_same;
                   [|intro; apply H5; rewrite in_app_iff; intuition..].
          rewrite flat_map_concat_map, map_app, concat_app,
          <- !flat_map_concat_map; auto.
        * exfalso. destruct t.
          -- destruct (H4 (fmap f).(nameF)). apply H8. constructor.
             exists d, (Fnode f :: treeL'). intuition. constructor.
             rewrite Exists_exists. exists (Fnode f). simpl. intuition.
             constructor; auto.
          -- destruct (H4 (dmap d0).(nameD)). apply H6. constructor.
             exists d, (Dnode d0 l :: treeL'). intuition. constructor. exists d0, l.
             intuition. constructor.
      + exfalso. apply path_in_tree_nonempty_neq in H2; auto. intro; inversion H4.
    - destruct path; inversion H2; subst. 1: exfalso; auto.
      destruct H9 as [did' [treeL' [? [? ?]]]]. clear H2. destruct H3. simpl in *.
      inversion H2; subst. destruct H12 as [dd [ll [? [? ?]]]]. inversion H1; subst.
      assert (Dnode did' treeL' = Dnode dd ll) by
          (eapply same_name_the_same_tree; eauto). inversion H9. subst dd ll. clear H9.
      rewrite NoDup_cons_iff in H0. destruct H0. apply in_split in H5.
      destruct H5 as [l1 [l2 ?]]. subst treeL.
      rewrite removeDirFromTree_map_the_same; auto.
      2: apply path_in_tree_collectDids in H6; auto.
      rewrite Forall_forall in H. rewrite !flat_map_collectFids.
      rewrite H with (path := path); auto.
      + rewrite flat_map_collectDids in H9.
        apply NoDup_app_r, NoDup_app_l in H9; auto.
      + rewrite Forall_forall in H13. apply H13. auto.
      + split; auto. intros. specialize (H3 name0). destruct H3.
        split; intro; [apply H3 | apply H5]; constructor;
          exists did', treeL'; intuition.
  Qed.

  Lemma removeDirFromTree_Permutation: forall fmap dmap tree path name pid d,
      NoDup (collectDids tree) -> NoDupNameTree fmap dmap tree ->
      path_in_tree_with_id dmap path tree pid ->
      empty_directory_with_id fmap dmap tree (path ++ [name])%list d ->
      Permutation (d :: collectDids (removeDirFromTree tree pid d)) (collectDids tree).
  Proof.
    intros fmap dmap tree path name pid d; revert tree path.
    induction tree using tree_ind2; intros; simpl; auto.
    1: inversion H1. rm_if; simpl.
    - apply Permutation_trans with
          (did :: d :: flat_map collectDids (removeDirFromList treeL d)); constructor.
      subst did. destruct path.
      + simpl in *. destruct H3. inversion H3; subst.
        destruct H10 as [did' [treeL' [? [? ?]]]]. inversion H7; subst.
        destruct treeL'.
        * apply in_split in H5. destruct H5 as [l1 [l2 ?]]. subst treeL.
          rewrite removeDirFromList_app. simpl. rm_if. 2: exfalso; auto. clear e.
          apply NoDup_cons_iff in H0. destruct H0. rewrite flat_map_collectDids in H5.
          simpl in H5. apply NoDup_remove_2 in H5. rewrite flat_map_collectDids.
          simpl. rewrite !removeDirFromList_the_same;
                   [|intro; apply H5; rewrite in_app_iff; intuition..].
          rewrite flat_map_concat_map, map_app, concat_app, <- !flat_map_concat_map.
          apply Permutation_cons_app. auto.
        * exfalso. destruct t.
          -- destruct (H4 (fmap f).(nameF)). apply H8. constructor.
             exists d, (Fnode f :: treeL'). intuition. constructor.
             rewrite Exists_exists. exists (Fnode f). simpl. intuition.
             constructor; auto.
          -- destruct (H4 (dmap d0).(nameD)). apply H6. constructor.
             exists d, (Dnode d0 l :: treeL'). intuition. constructor. exists d0, l.
             intuition. constructor.
      + exfalso. apply path_in_tree_nonempty_neq in H2; auto. intro; inversion H4.
    - apply Permutation_trans with
          (did :: d :: flat_map collectDids
               (map (fun t : Tree => removeDirFromTree t pid d) treeL)); constructor.
      destruct path; inversion H2; subst. 1: exfalso; auto.
      destruct H9 as [did' [treeL' [? [? ?]]]]. clear H2. destruct H3. simpl in *.
      inversion H2; subst. destruct H12 as [dd [ll [? [? ?]]]]. inversion H1; subst.
      assert (Dnode did' treeL' = Dnode dd ll) by
          (eapply same_name_the_same_tree; eauto). inversion H9. subst dd ll. clear H9.
      rewrite NoDup_cons_iff in H0. destruct H0. apply in_split in H5.
      destruct H5 as [l1 [l2 ?]]. subst treeL.
      rewrite removeDirFromTree_map_the_same; auto.
      2: apply path_in_tree_collectDids in H6; auto.
      rewrite Forall_forall in H. rewrite !flat_map_collectDids.
      transitivity
        (flat_map collectDids l1 ++
                  d :: collectDids (removeDirFromTree (Dnode did' treeL') pid d) ++
                  flat_map collectDids l2)%list. 1: apply Permutation_cons_app; auto.
      apply Permutation_app_head. rewrite app_comm_cons. apply Permutation_app_tail.
      rewrite H with (path := path); auto.
      + rewrite flat_map_collectDids in H9.
        apply NoDup_app_r, NoDup_app_l in H9; auto.
      + rewrite Forall_forall in H13. apply H13. auto.
      + split; auto. intros. specialize (H3 name0). destruct H3.
        split; intro; [apply H3 | apply H5]; constructor;
          exists did', treeL'; intuition.
  Qed.

  Lemma removeDirFromTree_NoDupNameTree:
    forall (fmap : Fid -> FData) (dmap : Did -> DData) (d cnt : Did)
           (da : DData) (dname: string) (tree : Tree) (path : Path),
      NoDup (collectDids tree) -> NoDupNameTree fmap dmap tree ->
      path_in_tree_with_id dmap path tree d ->
      path_in_tree_with_id dmap (path ++ [dname])%list tree cnt ->
      NoDupNameTree fmap (change_d_map dmap cnt da) (removeDirFromTree tree d cnt).
  Proof.
    intros fmap dmap d cnt da dname. induction tree using tree_ind2; intros.
    1: inversion H1. rewrite Forall_forall in H.
    destruct path; simpl in *; inversion H2; subst.
    - rm_if. 2: exfalso; auto. clear e. inversion H3. subst.
      destruct H9 as [did' [treeL' [? [? ?]]]].
      inversion H6. subst. apply in_split in H4. destruct H4 as [l1 [l2 ?]].
      subst treeL. rewrite NoDup_cons_iff in H0. destruct H0.
      rewrite flat_map_collectDids in H4. simpl in H4. apply NoDup_remove_2 in H4.
      rewrite removeDirFromList_app. simpl. rm_if. 2: exfalso; auto. clear e.
      assert (~ In cnt (flat_map collectDids l1)) by
          (intro; apply H4; rewrite in_app_iff; left; auto).
      assert (~ In cnt (flat_map collectDids l2)) by
          (intro; apply H4; rewrite !in_app_iff; right; right; auto).
      rewrite !removeDirFromList_the_same; auto.
      assert (~ In cnt (flat_map collectDids (l1 ++ l2))). {
        rewrite flat_map_concat_map, map_app, concat_app,
        <- !flat_map_concat_map. intro. rewrite in_app_iff in H8.
        destruct H8; [apply H5 | apply H7]; auto.
      } clear -H1 H8. inversion H1. subst. constructor.
      + rewrite Forall_forall in *. intros. apply change_d_map_NoDupNameTree.
        * intro. apply H8; apply subtree_did_in_merge with x; auto.
        * apply H4. rewrite in_app_iff in *. simpl. intuition.
      + rewrite <- treeName_eq_treeL; auto. rewrite map_app in *.
        rewrite map_cons in H5. apply NoDup_remove_1 in H5; auto.
    - destruct H9 as [did' [treeL' [? [? ?]]]]. rm_if.
      + exfalso. revert e. eapply path_in_tree_nonempty_neq; eauto.
        intro. inversion H7.
      + inversion H3. subst. destruct H12 as [d0 [l0 [? [? ?]]]]. inversion H1. subst.
        assert (Dnode did' treeL' = Dnode d0 l0) by
            (eapply same_name_the_same_tree; eauto). inversion H9. subst d0 l0.
        clear H7 H5 H9. specialize (H _ H4 path). rewrite NoDup_cons_iff in H0.
        destruct H0. apply in_split in H4. destruct H4 as [tl1 [tl2 ?]]. subst treeL.
        rewrite removeDirFromTree_map_the_same; auto.
        2: apply path_in_tree_collectDids in H6; auto.
        rewrite flat_map_collectDids in H5.
        assert (NoDup (collectDids (Dnode did' treeL'))) by
            (apply NoDup_app_r, NoDup_app_l in H5; auto).
        rewrite Forall_forall in H13.
        assert (NoDupNameTree fmap dmap (Dnode did' treeL')) by
            (apply H13; rewrite in_app_iff; right; simpl; left; auto).
        specialize (H H4 H7 H6 H8). assert (HS: did' <> cnt) by
            (apply path_in_tree_nonempty_neq in H8; auto; intro s;
             destruct path; inversion s).
        apply path_in_tree_collectDids in H8.
        assert (~ In cnt (flat_map collectDids tl1)). {
          apply NoDup_app_not_in_l with (y := cnt) in H5; auto.
          rewrite in_app_iff. left; auto.
        } assert (~ In cnt (flat_map collectDids tl2)). {
          apply NoDup_app_r, NoDup_app_not_in_r with (y := cnt) in H5; auto.
        } constructor.
        * rewrite Forall_forall. intros. rewrite in_app_iff in H11.
          Opaque removeDirFromTree. simpl in H11. Transparent removeDirFromTree.
          assert (removeDirFromTree (Dnode did' treeL') d cnt = x \/ In x (tl1 ++ tl2))
            by (destruct H11 as [? | [? | ?]]; intuition). clear H11.
          destruct H12. 1: rewrite <- H11 in *; auto. apply change_d_map_NoDupNameTree.
          -- intro. rewrite in_app_iff in H11.
             destruct H11; [apply H9 | apply H10]; eapply subtree_did_in_merge; eauto.
          -- apply H13. rewrite in_app_iff in *. simpl. intuition.
        * rewrite map_app, map_cons in *. rewrite <- !treeName_eq_treeL; auto.
          simpl in *; rm_if; simpl; unfold change_d_map; rm_if; exfalso; auto.
  Qed.

  Lemma fs_rmdir_ok: forall (path : Path) (fs : FSState) (err : ErrCode)
                            (postFS : FSState),
      good_file_system (fsFS fs) -> (err, postFS) = fs_rmdir path fs ->
      (path = nil /\ err = eInval /\ postFS = fs) \/
      (path <> nil /\ ~ path_in_tree (dMapFS fs) path (layoutFS fs) /\
       err = eNoEnt /\ postFS = fs) \/
      (path <> nil /\
       (exists name, path_in_tree (dMapFS fs) (path ++ [name])%list (layoutFS fs) \/
                     file_in_tree (fMapFS fs) (dMapFS fs) path name (layoutFS fs)) /\
       err = eNotEmpty /\ postFS = fs) \/
      (path <> nil /\
       (exists pid, path_in_tree_with_id
                      (dMapFS fs) (removelast path) (layoutFS fs) pid /\
                    (dMapFS fs pid).(metaD).(writable) = false) /\
       path_in_tree (dMapFS fs) path (layoutFS fs) /\ err = eAcces /\ postFS = fs) \/
      (path <> nil /\ path_in_tree (dMapFS fs) path (layoutFS fs) /\
       (exists pid, path_in_tree_with_id
                      (dMapFS fs) (removelast path) (layoutFS fs) pid /\
                    (dMapFS fs pid).(metaD).(writable) = true) /\ err <> eSucc /\
       fsFS postFS = fsFS fs /\ logFS postFS = Call_VRmdir path err :: logFS fs) \/
      ((exists did,
           empty_directory_with_id (fMapFS fs) (dMapFS fs) (layoutFS fs) path did /\
           dMapFS postFS did = Build_DData "" fff /\
           forall d, d <> did -> dMapFS postFS d = dMapFS fs d) /\
       (exists pid, path_in_tree_with_id
                      (dMapFS fs) (removelast path) (layoutFS fs) pid /\
                    (dMapFS fs pid).(metaD).(writable) = true) /\ err = eSucc /\
       logFS postFS = Call_VRmdir path eSucc :: logFS fs /\
       openhandleFS fs = openhandleFS postFS /\ vmFS fs = vmFS postFS /\
       fMapFS fs = fMapFS postFS /\ fCntFS fs = fCntFS postFS /\
       dCntFS fs = dCntFS postFS /\ path <> nil /\
       mmap_handles (fsFS fs) = mmap_handles (fsFS postFS) /\
       mmap_memory (fsFS fs) = mmap_memory (fsFS postFS) /\
       ~ path_in_tree (dMapFS postFS) path (layoutFS postFS) /\
       good_file_system (fsFS postFS)).
  Proof.
    intros. unfold fs_rmdir in H0. simpl in H0. destruct path eqn:? .
    1: left; inversion H0; auto. right.
    assert (path <> nil) by (rewrite Heqp; intro S; inversion S).
    rewrite <- Heqp in *. clear s p Heqp. rm_hmatch.
    - right. destruct t. 1: exfalso; revert Heqo; apply findDir_not_fnode. destruct l.
      pose proof Heqo. rename H2 into HS.
      + right. apply path_in_tree_with_id_some in Heqo.
        assert (path_in_tree (d_map (fst fs)) path (layout (fst fs))). {
          rewrite path_in_tree_with_id_eq. exists d; auto.
        } rm_hmatch.
        * destruct t. 1: exfalso; revert Heqo0; apply findDir_not_fnode.
          apply path_in_tree_with_id_some in Heqo0. rm_hmatch.
          -- right. destruct fs. simpl in H0.
             unfold fMapFS, dMapFS, layoutFS. simpl. rm_hif.
             ++ left. inversion H0. simpl in *. intuition. exists d0; intuition.
             ++ right. simpl in *. inversion H0. subst postFS. simpl. rewrite e.
                assert (HQ: empty_directory_with_id
                              (f_map f) (d_map f) (layout f) path d) by
                    (destruct H; apply findDir_empty_directory_with_id; auto).
                clear H0. apply app_removelast_last with (d := EmptyString) in H1.
                remember (removelast path) as p. remember (last path "") as a.
                clear Heqa Heqp. subst path. intuition.
                ** exists d. intuition; unfold change_d_map; rm_if; exfalso; auto.
                ** exists d0; intuition.
                ** destruct p; inversion H0.
                ** revert H0. destruct H as [? [? ?]].
                   eapply removeDirFromTree_not_in_tree; eauto.
                ** destruct H as [? [? [? [? [? [? [? [? ?]]]]]]]].
                   split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]];
                     simpl; auto.
                   --- eapply removeDirFromTree_NoDupNameTree; eauto.
                   --- pose proof (removeDirFromTree_Permutation
                                     _ _ _ _ _ _ _ H0 H Heqo0 HQ).
                       symmetry in H10. apply Permutation_NoDup in H10; auto.
                       rewrite NoDup_cons_iff in H10. destruct H10; auto.
                   --- erewrite removeDirFromTree_the_same_Fids; eauto.
                   --- pose proof (removeDirFromTree_Permutation
                                     _ _ _ _ _ _ _ H0 H Heqo0 HQ). intros.
                       apply Permutation_in with (x := el) in H10; auto.
                       simpl. right; auto.
                   --- erewrite removeDirFromTree_the_same_Fids; eauto.
                   --- unfold isDir in H7. destruct H7 as [dd [ll ?]]. rewrite H7.
                       simpl. rm_if; apply DnodeIsDir.
          -- left. inversion H0. intuition. exists d0. intuition.
        * destruct H. apply path_in_tree_none in Heqo0; auto.
          apply path_in_tree_removelast in H2. exfalso; intuition.
      + left. inversion H0. intuition. destruct t.
        * exists (fMapFS fs f).(nameF). right.
          apply (findDir_file_in_tree _ _ d (Fnode f :: l) f); auto. simpl; left; auto.
        * exists (dMapFS fs d0).(nameD). left.
          apply (findDir_path_in_tree _ d (Dnode d0 l0 :: l) d0 l0); simpl; intuition.
    - left. destruct H. apply path_in_tree_none in Heqo; auto. inversion H0; auto.
  Qed.

  Lemma file_in_tree_path_in_tree:
    forall fmap dmap fname tree path,
      file_in_tree fmap dmap path fname tree -> path_in_tree dmap path tree.
  Proof.
    intros fmap dmap fname. induction tree using tree_ind2; intros. 1: inversion H.
    rewrite Forall_forall in H. destruct path. 1: constructor.
    inversion H0; subst. destruct H4 as [did' [treeL' [? [? ?]]]].
    constructor. exists did', treeL'. intuition.
  Qed.

  Lemma removeFnodeFromList_app: forall l1 l2 fid,
      removeFnodeFromList (l1 ++ l2) fid =
      (removeFnodeFromList l1 fid ++ removeFnodeFromList l2 fid)%list.
  Proof.
    induction l1; intros; simpl; auto. destruct a.
    - rm_if. simpl. rewrite IHl1. auto.
    - simpl. f_equal. apply IHl1.
  Qed.

  Lemma removeFnodeFromList_the_same: forall fid l,
      ~ In fid (flat_map collectFids l) -> removeFnodeFromList l fid = l.
  Proof.
    intros. induction l; simpl; auto. destruct a.
    - rm_if. 1: exfalso; subst; apply H; simpl; left; auto. f_equal. apply IHl.
      intro. apply H. simpl. right; auto.
    - f_equal. apply IHl. intro; apply H; simpl. rewrite in_app_iff. right; auto.
  Qed.

  Lemma removeFnodeFromTree_the_same: forall d fId tree,
      ~ In fId (collectFids tree) -> removeFnodeFromTree tree d fId = tree.
  Proof.
    intros. induction tree using tree_ind2; simpl; auto.
    rewrite Forall_forall in H0. rm_if.
    - subst. f_equal. apply removeFnodeFromList_the_same. simpl in H. auto.
    - f_equal. assert (treeL = map id treeL) by
          (clear; induction treeL; simpl; [|rewrite IHtreeL at 1]; auto).
      rewrite H1 at 2. apply map_ext_in. intros. apply H0; auto. unfold id. intro.
      apply H. simpl. rewrite in_flat_map. exists a. intuition.
  Qed.

  Lemma removeFnodeFromTree_the_same_list: forall d fId l,
      ~ In fId (flat_map collectFids l) ->
      map (fun t => removeFnodeFromTree t d fId) l = l.
  Proof.
    intros. assert (l = map id l) by
        (clear; induction l; simpl; [|rewrite IHl at 1]; auto).
    rewrite H0 at 2; clear H0. apply map_ext_in. unfold id. intros.
    apply removeFnodeFromTree_the_same. intro; apply H.
    rewrite in_flat_map; exists a; intuition.
  Qed.

  Lemma removeFnodeFromTree_map_the_same: forall tl1 tl2 did' treeL' d fId,
      NoDup (flat_map collectFids (tl1 ++ Dnode did' treeL' :: tl2)) ->
      In fId (collectFids (Dnode did' treeL')) ->
      map (fun t : Tree => removeFnodeFromTree t d fId)
          (tl1 ++ Dnode did' treeL' :: tl2) =
      (tl1 ++ removeFnodeFromTree (Dnode did' treeL') d fId :: tl2)%list.
  Proof.
    intros. rewrite flat_map_collectFids in H. rewrite map_app, map_cons.
    rewrite !removeFnodeFromTree_the_same_list; auto.
    - apply NoDup_app_r in H. apply NoDup_app_not_in_r with (y := fId) in H; auto.
    - apply NoDup_app_not_in_l with (y := fId) in H; auto. rewrite in_app_iff.
      left; auto.
  Qed.

  Lemma file_in_tree_collectFids: forall fmap dmap path name t d,
      file_in_tree_with_id fmap dmap path name t d -> In d (collectFids t).
  Proof.
    intros. revert t path H. induction t using tree_ind2; intros. 1: inversion H.
    destruct path; inversion H0; subst.
    - simpl. rewrite in_flat_map. exists (Fnode d). simpl. intuition.
    - destruct H7 as [did' [treeL' [? [? ?]]]]. simpl. rewrite Forall_forall in H.
      rewrite in_flat_map. specialize (H _ H1 _ H3). exists (Dnode did' treeL').
      intuition.
  Qed.

  Lemma removeFnodeFromTree_not_in_tree:
    forall fmap dmap d fId fa fname tree path,
      NoDup (collectFids tree) -> NoDup (collectDids tree) ->
      NoDupNameTree fmap dmap tree -> path_in_tree_with_id dmap path tree d ->
      file_in_tree_with_id fmap dmap path fname tree fId ->
      ~ file_in_tree (change_f_map fmap fId fa) dmap
        path fname (removeFnodeFromTree tree d fId).
  Proof.
    intros fmap dmap d fId fa fname. induction tree using tree_ind2; intros.
    1: inversion H2. rewrite Forall_forall in H.
    destruct path; simpl in *; inversion H3; subst.
    - rm_if. clear e. inversion H4. subst. apply in_split in H7.
      destruct H7 as [l1 [l2 ?]]. subst treeL. rewrite flat_map_collectFids in H0.
      simpl in H0. apply NoDup_remove_2 in H0.
      rewrite removeFnodeFromList_app. simpl. rm_if. clear e.
      rewrite !removeFnodeFromList_the_same;
        [|intro; apply H0; rewrite in_app_iff; intuition ..].
      clear H. intro. inversion H. subst. rewrite Exists_exists in H8.
      destruct H8 as [x [? ?]]. inversion H6. subst. inversion H2. subst.
      rewrite map_app, map_cons in H13. simpl in H13. apply NoDup_remove_2 in H13.
      rewrite <- map_app in H13. clear -H0 H7 H13 H5.
      rewrite !flat_map_concat_map, <- concat_app, <- map_app,
      <- flat_map_concat_map in H0. remember (l1 ++ l2)%list as ll. clear l1 l2 Heqll.
      apply in_split in H5. destruct H5 as [l1 [l2 ?]].
      subst ll. unfold change_f_map in H7. rm_hif.
      * subst. rewrite flat_map_collectFids in H0. simpl in H0. apply H0.
        rewrite in_app_iff. simpl. right; left; auto.
      * apply H13. rewrite map_app, map_cons. simpl. rewrite in_app_iff. simpl.
        right; left; auto.
    - destruct H10 as [did' [treeL' [? [? ?]]]]. rm_if.
      + exfalso. revert e. eapply path_in_tree_nonempty_neq; eauto.
        intro. inversion H8.
      + inversion H4. subst. destruct H14 as [d0 [l0 [? [? ?]]]]. inversion H2. subst.
        assert (Dnode did' treeL' = Dnode d0 l0) by
            (eapply same_name_the_same_tree; eauto). inversion H10. subst d0 l0.
        clear H8 H6 H10. intro. inversion H6. subst. clear H3 H4 H6.
        destruct H12 as [dd [ll [? [? ?]]]]. rewrite NoDup_cons_iff in H1. destruct H1.
        specialize (H _ H5 path). apply in_split in H5. destruct H5 as [l1 [l2 ?]].
        subst treeL. rewrite removeFnodeFromTree_map_the_same in H3; auto.
        2: apply file_in_tree_collectFids in H9; auto. rewrite in_app_iff in H3.
        Opaque removeFnodeFromTree. simpl in H3. Transparent removeFnodeFromTree.
        assert (removeFnodeFromTree (Dnode did' treeL') d fId = Dnode dd ll \/
                In (Dnode dd ll) (l1 ++ l2)) by
            (destruct H3 as [? | [? | ?]]; intuition). clear H3. destruct H5.
        * rewrite H3 in H. apply H; auto.
          -- clear -H0. rewrite flat_map_collectFids in H0.
             apply NoDup_app_r, NoDup_app_l in H0; auto.
          -- clear -H8. rewrite flat_map_collectDids in H8.
             apply NoDup_app_r, NoDup_app_l in H8; auto.
          -- rewrite Forall_forall in H14. apply H14. rewrite in_app_iff. simpl.
             right; left; auto.
        * clear -H15 H4 H3. rewrite map_app, map_cons in H15.
          simpl in H15. apply NoDup_remove_2 in H15. rewrite <- map_app in H15.
          remember (l1 ++ l2)%list as tl. clear l1 l2 Heqtl.
          apply in_split in H3. destruct H3 as [tl1 [tl2 ?]]. subst tl. apply H15.
          rewrite map_app, map_cons. simpl. rewrite in_app_iff. simpl. intuition.
  Qed.

  Lemma removeFnodeFromTree_the_same_Dids: forall tree d fId,
      collectDids (removeFnodeFromTree tree d fId) = collectDids tree.
  Proof.
    induction tree using tree_ind2; intros; simpl; auto.
    rewrite Forall_forall in H. rm_if; simpl.
    - subst. f_equal. clear. induction treeL; simpl; auto. destruct a. 1: rm_if.
      simpl. f_equal. f_equal. auto.
    - f_equal. rewrite !flat_map_concat_map, map_map. f_equal. apply map_ext_in. auto.
  Qed.

  Lemma removeFnodeFromTree_Permutation:
    forall fmap dmap d fId fname tree path,
      NoDup (collectFids tree) -> NoDup (collectDids tree) ->
      NoDupNameTree fmap dmap tree -> path_in_tree_with_id dmap path tree d ->
      file_in_tree_with_id fmap dmap path fname tree fId ->
      Permutation (fId :: collectFids (removeFnodeFromTree tree d fId))
                  (collectFids tree).
  Proof.
    intros fmap dmap d fId fname. induction tree using tree_ind2; intros.
    1: inversion H2. rewrite Forall_forall in H.
    destruct path; simpl in *; inversion H3; subst.
    - rm_if. 2: exfalso; auto. clear e. inversion H4. subst. apply in_split in H7.
      destruct H7 as [l1 [l2 ?]]. subst treeL. rewrite flat_map_collectFids in H0.
      simpl in H0. apply NoDup_remove_2 in H0. rewrite removeFnodeFromList_app. simpl.
      rm_if. 2: exfalso; auto. rewrite !removeFnodeFromList_the_same;
                                 [|intro; apply H0; rewrite in_app_iff; intuition ..].
      clear H. rewrite flat_map_collectFids. simpl. rewrite flat_map_concat_map at 1.
      rewrite map_app, concat_app, <- !flat_map_concat_map. apply Permutation_middle.
    - destruct H10 as [did' [treeL' [? [? ?]]]]. rm_if.
      + exfalso. revert e. eapply path_in_tree_nonempty_neq; eauto.
        intro. inversion H8.
      + inversion H4. subst. destruct H14 as [d0 [l0 [? [? ?]]]]. inversion H2. subst.
        assert (Dnode did' treeL' = Dnode d0 l0) by
            (eapply same_name_the_same_tree; eauto). inversion H10. subst d0 l0.
        clear H8 H6 H10. rewrite NoDup_cons_iff in H1. destruct H1.
        specialize (H _ H5 path). apply in_split in H5. destruct H5 as [l1 [l2 ?]].
        subst treeL. rewrite removeFnodeFromTree_map_the_same; auto.
        2: apply file_in_tree_collectFids in H9; auto.
        Opaque removeFnodeFromTree. simpl. Transparent removeFnodeFromTree.
        rewrite !flat_map_collectFids. rewrite app_comm_cons. rewrite !app_assoc.
        apply Permutation_app_tail. rewrite <- app_comm_cons.
        remember (collectFids (removeFnodeFromTree (Dnode did' treeL') d fId)) as l3.
        transitivity (flat_map collectFids l1 ++ fId :: l3)%list.
        1: apply Permutation_middle. apply Permutation_app_head. apply H; auto.
        * clear -H0. rewrite flat_map_collectFids in H0.
          apply NoDup_app_r, NoDup_app_l in H0; auto.
        * clear -H6. rewrite flat_map_collectDids in H6.
          apply NoDup_app_r, NoDup_app_l in H6; auto.
        * rewrite Forall_forall in H14. apply H14. rewrite in_app_iff. simpl.
          right; left; auto.
  Qed.

  Lemma removeFnodeFromTree_NoDupNameTree:
    forall fmap dmap d fId fa fname tree path,
      NoDup (collectFids tree) -> NoDup (collectDids tree) ->
      NoDupNameTree fmap dmap tree -> path_in_tree_with_id dmap path tree d ->
      file_in_tree_with_id fmap dmap path fname tree fId ->
      NoDupNameTree (change_f_map fmap fId fa) dmap (removeFnodeFromTree tree d fId).
  Proof.
    intros fmap dmap d fId fa fname. induction tree using tree_ind2; intros.
    1: inversion H2. rewrite Forall_forall in H.
    destruct path; simpl in *; inversion H3; subst.
    - rm_if. 2: exfalso; auto. clear e. inversion H4. subst. apply in_split in H7.
      destruct H7 as [l1 [l2 ?]]. subst treeL. rewrite flat_map_collectFids in H0.
      simpl in H0. apply NoDup_remove_2 in H0.
      rewrite removeFnodeFromList_app. simpl. rm_if. 2: exfalso; auto. clear e.
      rewrite !removeFnodeFromList_the_same;
        [|intro; apply H0; rewrite in_app_iff; intuition ..]. clear H.
      inversion H2. subst. rewrite !flat_map_concat_map, <- concat_app, <- map_app,
                           <- flat_map_concat_map in H0. constructor.
      + rewrite Forall_forall in *. intros. apply change_f_map_NoDupNameTree.
        * intro. apply H0. rewrite in_flat_map. exists x; auto.
        * apply H8. rewrite in_app_iff in *. simpl. intuition.
      + rewrite <- treeName_eq_treeL'; auto. rewrite map_app in *. simpl in H9.
        apply NoDup_remove_1 in H9. auto.
    - destruct H10 as [did' [treeL' [? [? ?]]]]. rm_if.
      + exfalso. revert e. eapply path_in_tree_nonempty_neq; eauto.
        intro. inversion H8.
      + inversion H4. subst. destruct H14 as [d0 [l0 [? [? ?]]]]. inversion H2. subst.
        assert (Dnode did' treeL' = Dnode d0 l0) by
            (eapply same_name_the_same_tree; eauto). inversion H10. subst d0 l0.
        clear H8 H6 H10. rewrite NoDup_cons_iff in H1. destruct H1.
        specialize (H _ H5 path). apply in_split in H5. destruct H5 as [l1 [l2 ?]].
        pose proof H9. rename H8 into HS. apply file_in_tree_collectFids in H9.
        subst treeL. rewrite removeFnodeFromTree_map_the_same; auto.
        rewrite flat_map_collectFids in H0.
        assert (~ In fId (flat_map collectFids l1)). {
          apply NoDup_app_not_in_l with (y := fId) in H0; auto.
          rewrite in_app_iff; intuition.
        } assert (~ In fId (flat_map collectFids l2)). {
          apply NoDup_app_r, NoDup_app_not_in_r with (y := fId) in H0; auto.
        } constructor.
        * rewrite Forall_forall in *. intros. rewrite in_app_iff in H10.
          Opaque removeFnodeFromTree. simpl in H10. Transparent removeFnodeFromTree.
          assert (removeFnodeFromTree (Dnode did' treeL') d fId = x \/
                  In x (l1 ++ l2)) by (destruct H10 as [? | [? | ?]]; intuition).
          clear H10. destruct H11.
          -- subst x. apply H; auto.
             ++ clear -H0. apply NoDup_app_r, NoDup_app_l in H0; auto.
             ++ clear -H6. rewrite flat_map_collectDids in H6.
                apply NoDup_app_r, NoDup_app_l in H6; auto.
             ++ apply H14. rewrite in_app_iff. simpl. right; left; auto.
          -- apply change_f_map_NoDupNameTree.
             ++ intro. rewrite in_app_iff in H10.
                destruct H10; [apply H5 | apply H8];
                  rewrite in_flat_map; exists x; intuition.
             ++ apply H14. rewrite in_app_iff in *. simpl; intuition.
        * rewrite map_app, map_cons in *. rewrite <- !treeName_eq_treeL'; auto.
          simpl in *; rm_if; subst d; simpl; auto.
  Qed.

  Lemma fs_remove_ok: forall (path : Path) (fname : string)
                             (fs : FSState) (err : ErrCode) (postFS : FSState),
      good_file_system (fsFS fs) -> (err, postFS) = fs_remove (path, fname) fs ->
      (fname = EmptyString /\ err = eBadName /\ postFS = fs) \/
      (~ file_in_tree (fMapFS fs) (dMapFS fs) path fname (layoutFS fs) /\
       err = eNoEnt /\ fs = postFS) \/
      (file_in_tree (fMapFS fs) (dMapFS fs) path fname (layoutFS fs) /\
       (exists did, path_in_tree_with_id (dMapFS fs) path (layoutFS fs) did /\
                    ((dMapFS fs) did).(metaD).(writable) = false) /\
       err = eAcces /\ fs = postFS) \/
      (file_in_tree (fMapFS fs) (dMapFS fs) path fname (layoutFS fs) /\
       (exists did, path_in_tree_with_id (dMapFS fs) path (layoutFS fs) did /\
                    ((dMapFS fs) did).(metaD).(writable) = true) /\
       err <> eSucc /\ fsFS fs = fsFS postFS /\
       logFS postFS = Call_VRemove path fname err :: logFS fs) \/
      ((exists fId, file_in_tree_with_id (fMapFS fs) (dMapFS fs)
                                         path fname (layoutFS fs) fId /\
                    fMapFS postFS fId = Build_FData "" (Build_Meta fff O) nil /\
                    (forall id, id <> fId -> fMapFS fs id = fMapFS postFS id)) /\
       (exists did, path_in_tree_with_id (dMapFS fs) path (layoutFS fs) did /\
                    ((dMapFS fs) did).(metaD).(writable) = true) /\ err = eSucc /\
       logFS postFS = Call_VRemove path fname eSucc :: logFS fs /\
       openhandleFS fs = openhandleFS postFS /\ vmFS fs = vmFS postFS /\
       dMapFS fs = dMapFS postFS /\ fCntFS fs = fCntFS postFS /\
       dCntFS fs = dCntFS postFS /\
       mmap_handles (fsFS fs) = mmap_handles (fsFS postFS) /\
       mmap_memory (fsFS fs) = mmap_memory (fsFS postFS) /\
       ~ file_in_tree (fMapFS postFS) (dMapFS postFS) path fname (layoutFS postFS) /\
       good_file_system (fsFS postFS)).
  Proof.
    intros. unfold fs_remove in H0. rm_hif. 1: left; inversion H0; auto.
    right. simpl in H0. destruct H as [? [? [? [? [? [? ?]]]]]]. rm_hmatch.
    - right. apply file_in_tree_with_id_some in Heqo; auto.
      assert (file_in_tree (fMapFS fs) (dMapFS fs) path fname (layoutFS fs)) by
          (rewrite file_in_tree_with_id_eq; exists f; auto). rm_hmatch.
      + destruct t. 1: exfalso; revert Heqo0; apply findDir_not_fnode.
        apply path_in_tree_with_id_some in Heqo0. rm_hmatch.
        * left. apply bool_eq_ok in Heqb. inversion H0. intuition.
          exists d. intuition.
        * right. destruct fs. simpl in H0. unfold bool_eq in Heqb. simpl in *.
          destruct (writable (metaD (d_map f0 d))) eqn: ?. 2: inversion Heqb. rm_hif.
          -- left. inversion H0. subst. simpl. intuition. exists d. intuition.
          -- right. simpl in H0.
             remember {| nameF := "";
                         metaF := {| permission :=
                                       {| readable := false;
                                          writable := false;
                                          executable := false |}; size := 0 |};
                         pageIdsF := [] |} as fd.
             inversion H0. unfold fMapFS, dMapFS, layoutFS, fsFS, logFS,
                           openhandleFS, vmFS, fCntFS, dCntFS in *. simpl in *.
             subst postFS. clear H0. rewrite e. intuition.
             ++ exists f. unfold change_f_map. intuition; rm_if; exfalso; auto.
             ++ exists d. intuition.
             ++ revert H12. apply removeFnodeFromTree_not_in_tree; auto.
             ++ pose proof (removeFnodeFromTree_Permutation
                              _ _ _ _ _ _ _ H2 H1 H Heqo0 Heqo).
                split; [|split; [|split; [|split; [|split; [|split; [|split; [|split;[|split;[|split]]]]]]]]]; simpl; auto.
                ** eapply removeFnodeFromTree_NoDupNameTree; eauto.
                ** rewrite removeFnodeFromTree_the_same_Dids; auto.
                ** symmetry in H12. apply (Permutation_NoDup H12) in H2.
                   rewrite NoDup_cons_iff in H2. destruct H2; auto.
                ** intros. rewrite removeFnodeFromTree_the_same_Dids in H14; auto.
                ** intros. apply Permutation_in with (x := el) in H12; auto. simpl.
                   intuition.
                ** unfold isDir in H0. destruct H0 as [dd [ll ?]]. rewrite H0.
                   simpl. rm_if; apply DnodeIsDir.
                ** intros. unfold change_f_map in H16, H15. subst fd.
                   do 2 rm_hif; simpl in *; [exfalso; auto..|]. intro.
                   apply (H6 fId1 fId2 pgId1 pgId2); auto.
                ** intros. unfold change_f_map in H14. subst fd. rm_hif; simpl in *.
                   --- exfalso; auto.
                   --- eapply H8; eauto.
      + exfalso. apply path_in_tree_none in Heqo0; auto. apply Heqo0.
        eapply file_in_tree_path_in_tree; eauto.
    - left. apply file_in_tree_none in Heqo; auto. inversion H0. intuition.
  Qed.

  Inductive Sequential: list Memid -> Prop :=
  | Seq_nil: Sequential nil
  | Seq_one: forall m, Sequential [m]
  | Seq_cons: forall m l, Sequential (S m :: l) -> Sequential (m :: S m :: l).

  Lemma check_if_continuous_ok: forall l,
      check_if_continuous l = true <-> Sequential l.
  Proof.
    intros. induction l; simpl. 1: split; intros; [constructor | easy]. destruct l.
    - split; intros; [constructor | easy].
    - rm_if; split; intros; try easy.
      + subst m. constructor. rewrite <- IHl. easy.
      + inversion H. subst. rewrite IHl. easy.
      + inversion H. subst. easy.
  Qed.

  Lemma check_size_ok: forall len1 len2,
      check_size len1 len2 = true <-> len1 <> 0 /\ len1 = pad_size len2.
  Proof.
    intros. unfold check_size. rm_if.
    - split; intros; [| destruct H]; easy.
    - assert (HS: block_size <> 0) by (compute; intro HS'; inversion HS').
      assert (HT: 0 < block_size) by (compute; omega). rm_if.
      + rm_if; split; intros; try easy.
        * split; auto. destruct len1. 1: easy. simpl in l. unfold pad_size. rm_if.
          -- rewrite <- Nat.div_exact in e; auto. rewrite Nat.mul_comm in e.
             rewrite e in g, l. rewrite <- Nat.mul_lt_mono_pos_r in l; auto.
             unfold ge in g. rewrite <- Nat.mul_le_mono_pos_r in g; auto. omega.
          -- f_equal. unfold ge in g. rewrite Nat.le_lteq in g. destruct g.
             ++ rewrite Nat.mul_succ_l in H0.
                rewrite (S_pred_pos block_size) in H0 at 2; auto.
                rewrite Nat.add_succ_r in H0. apply lt_n_Sm_le in H0.
                apply Nat.div_le_mono with (c := block_size) in H0; auto.
                rewrite Nat.div_add_l in H0; auto. apply Nat.lt_le_incl in l.
                rewrite (Nat.div_small (pred block_size)) in H0.
                2: compute; apply le_n.
                apply Nat.div_le_mono with (c := block_size) in l; auto.
                rewrite Nat.div_mul in l; auto. omega.
             ++ exfalso. apply n0. rewrite Nat.mod_divides; auto. exists (S len1).
                rewrite Nat.mul_comm. easy.
        * destruct H. destruct len1. 1: easy. simpl Init.Nat.pred in n0.
          apply not_lt in n0. unfold pad_size in H0. clear n H g. unfold ge in n0.
          rm_hif.
          -- apply Nat.div_le_mono with (c := block_size) in n0; auto.
             rewrite Nat.div_mul in n0; auto. omega.
          -- Opaque block_size. inversion H0. clear H0. Transparent block_size.
             exfalso. destruct len1.
             ++ assert (len2 = O) by omega. subst. apply n, Nat.mod_0_l; auto.
             ++ rewrite Nat.le_lteq in n0. destruct n0.
                ** rewrite Nat.mul_succ_l in H.
                   rewrite (S_pred_pos block_size) in H at 2; auto.
                   rewrite Nat.add_succ_r in H. apply lt_n_Sm_le in H.
                   apply Nat.div_le_mono with (c := block_size) in H; auto.
                   rewrite Nat.div_add_l in H; auto.
                   rewrite (Nat.div_small (pred block_size)) in H.
                   2: compute; apply le_n. omega.
                ** apply n. rewrite Nat.mod_divides; auto. exists (S len1).
                   rewrite Nat.mul_comm. easy.
      + split; intros. 1: easy. destruct H. subst. exfalso. apply n0.
        unfold pad_size. rm_if.
        * rewrite <- Nat.div_exact in e; auto.
          rewrite Nat.mul_comm. rewrite <- e. omega.
        * unfold ge. rewrite Nat.mul_comm. apply Nat.lt_le_incl.
          apply Nat.mul_succ_div_gt; auto.
  Qed.

  Lemma check_range_ok: forall l u, check_range l u = true <->
                                    forall i, In i l -> i < u.
  Proof.
    intros. induction l; simpl; split; intros; try easy.
    - rm_hif. 2: easy. destruct H0. 1: subst; easy. rewrite IHl in H. apply H; auto.
    - rm_if. rewrite IHl; intros; apply H; right; easy.
  Qed.

  Lemma pad_size_neq_O: forall len, len <> 0 <-> pad_size len <> 0.
  Proof.
    intros. assert (HS: block_size <> 0) by (compute; intro HS; inversion HS).
    split; intros.
    - unfold pad_size. rm_if. rewrite <- Nat.div_exact in e; auto.
      remember (len / block_size). destruct n; auto.
    - unfold pad_size in H. rm_hif.
      + rewrite <- Nat.div_exact in e; auto. remember (len / block_size). rewrite e.
        intro. pose proof (Nat.mul_eq_0_r _ _ H0 HS). auto.
      + destruct len; auto.
  Qed.

  Opaque pad_size.

  Lemma interval_between_ok: forall n start len,
      interval_between n start len = false <-> n < start \/ start + len <= n.
  Proof.
    intros. unfold interval_between. rm_if; [rm_if |]; split; intros; try easy; omega.
  Qed.

  Transparent pad_size.

  Lemma interval_overlap_ok: forall s1 len1 s2 len2,
      len1 <> O -> len2 <> O ->
      interval_overlap s1 (pad_size len1) s2 (pad_size len2) = false <->
      forall p1 p2, Disjoint (s1, len1, p1) (s2, len2, p2).
  Proof.
    intros. simpl. unfold interval_overlap. rewrite Bool.orb_false_iff.
    rewrite !interval_between_ok. split; intros.
    - destruct H1. destruct H1, H2; omega.
    - specialize (H1 ttf ttf). split.
      + destruct H1; [left | right]; auto. rewrite pad_size_neq_O in H. omega.
      + destruct H1; [right | left]; auto. rewrite pad_size_neq_O in H0. omega.
  Qed.

  Lemma NoNull_cons_inv: forall x l, NoNull (x :: l) -> NoNull l.
  Proof.
    intros. unfold NoNull in *. rewrite Forall_forall in *.
    intros. apply H. right; auto.
  Qed.

  Lemma check_overlap_ok: forall s len h,
      len <> 0 -> NoNull h ->
      check_overlap s (pad_size len) h = false <->
      forall p i, In i h -> Disjoint (s, len, p) i.
  Proof.
    intros. induction h; simpl; split; intros; try easy; destruct a as [[s1 len1] ?].
    - destruct i as [[s2 len2] ?]. rm_hif_eqn H. 1: inversion H1. destruct H2.
      + inversion H2. subst. rewrite interval_overlap_ok in Heqb; auto.
        * specialize (Heqb p p). red in Heqb. easy.
        * red in H0. rewrite Forall_forall in H0. red in H0.
          specialize (H0 (s2, len2, p1) (in_eq _ _)). simpl in H0. easy.
      + rewrite IHh in H1.
        * specialize (H1 p _ H2). simpl in H1. easy.
        * apply NoNull_cons_inv in H0. easy.
    - rm_if_eqn.
      + rewrite <- Bool.not_false_iff_true in Heqb. exfalso. apply Heqb.
        rewrite interval_overlap_ok; auto.
        * intros. simpl. specialize (H1 p1 (s1, len1, p) (or_introl eq_refl)).
          simpl in H1. easy.
        * red in H0. rewrite Forall_forall in H0. specialize (H0 _ (in_eq _ _)).
          red in H0. easy.
      + rewrite IHh.
        * intros. specialize (H1 p i (or_intror H2)). unfold Disjoint. easy.
        * apply NoNull_cons_inv in H0. easy.
  Qed.

  Lemma Sequential_In: forall h l,
      Sequential l -> hd_error l = Some h ->
      forall i, In i l <-> h <= i < h + length l.
  Proof.
    intros ? ?. revert h. induction l; intros; simpl. 1: split; intros; omega.
    simpl in H0. inversion H0. subst. clear H0. destruct l. 1: simpl; omega.
    inversion H. subst. rewrite (IHl (S h)); simpl; auto. omega.
  Qed.

  Lemma write_zeroes_length: forall addrs mem,
      (forall i, In i addrs -> i < length mem) -> Sequential addrs ->
      length (write_zeroes addrs mem) = length mem.
  Proof.
    intros. unfold write_zeroes. destruct addrs. 1: easy. rewrite !app_length.
    rewrite firstn_length_le. 2: apply Nat.lt_le_incl, H; left; easy.
    rewrite repeat_length. assert (hd_error (n :: addrs) = Some n) by easy.
    pose proof (firstn_skipn (n + length (n :: addrs)) mem).
    rewrite <- H2 at 2. rewrite app_length. f_equal.
    rewrite firstn_length_le; auto. clear H2. simpl.
    assert (In (n + length addrs) (n :: addrs)). {
      rewrite (Sequential_In n); auto. simpl. split; try omega.
      rewrite <- Nat.add_lt_mono_l. apply Nat.lt_succ_diag_r. }
    apply H in H2. omega.
  Qed.

  Lemma write_zeroes_In: forall addrs mem,
      (forall i, In i addrs -> i < length mem) -> Sequential addrs ->
      forall i, In i addrs -> nth i (write_zeroes addrs mem) nil =
                              repeat Ascii.zero block_size.
  Proof.
    intros. unfold write_zeroes. destruct addrs. 1: inversion H1.
    rewrite (Sequential_In n) in H1; auto.
    assert (length (firstn n mem) = n) by
        (rewrite firstn_length_le; [omega | apply Nat.lt_le_incl, H; left; easy]).
    rewrite <- app_assoc, app_nth2; rewrite H2. 2: omega. rewrite app_nth1.
    - remember (repeat Ascii.zero block_size).
      assert (i - n < length (n :: addrs)) by (unfold Memid in H1; omega).
      pose proof (@nth_In _ (i - n) (repeat l (length (n :: addrs))) nil).
      rewrite repeat_length in H4. apply H4 in H3. clear H4. apply repeat_spec in H3.
      easy.
    - rewrite repeat_length. omega.
  Qed.

  Lemma mmap_ok: forall len perm flag fs mid err postFS,
      (mid, err, postFS) = mmap len perm flag fs -> NoNull (memHandleFS fs) ->
      (flag <> mapAnon /\ postFS = fs /\ err = eMapFailed) \/
      (flag = mapAnon /\
       exists p1 p2 addrs,
         hd_error (logFS postFS) = Some (Call_AllocMem p1 p2 addrs) /\
         ((Sequential addrs /\ length addrs <> 0 /\ length addrs = pad_size len /\
           (forall i, In i addrs -> i < length (memoryFS fs)) /\
           (forall p i, In i (memHandleFS fs) -> Disjoint (mid, len, p) i) /\
           hd_error addrs = Some mid /\ layoutFS fs = layoutFS postFS /\
           openhandleFS fs = openhandleFS postFS /\ vmFS fs = vmFS postFS /\
           fMapFS fs = fMapFS postFS /\ dMapFS fs = dMapFS postFS /\
           fnode_ctr (fsFS fs) = fnode_ctr (fsFS postFS) /\
           dnode_ctr (fsFS fs) = dnode_ctr (fsFS postFS) /\
           memHandleFS postFS = (mid, len, perm) :: memHandleFS fs /\
           length (memoryFS postFS) = length (memoryFS fs) /\ err = eSucc /\
           (forall i, In i addrs -> nth i (memoryFS postFS) nil =
                                    repeat Ascii.zero block_size) /\
           (forall m, In m (memoryFS postFS) -> In m (memoryFS fs) \/
                                                m = repeat Ascii.zero block_size)) \/
          (err = eMapFailed /\ fsFS postFS = fsFS fs))).
  Proof.
    intros. unfold mmap in H. simpl in H. rm_hif.
    - right. destruct fs as [fs ?]. simpl in H. unfold memHandleFS in H0.
      remember (allocate_memory (mmap_memory fs) len (length l)) as addrs. split; auto.
      exists (mmap_memory fs), len, addrs. rm_hif_eqn H; simpl in H, H0.
      + apply andb_prop in Heqb. destruct Heqb. apply andb_prop in H1. destruct H1.
        apply andb_prop in H1. destruct H1. rewrite Bool.negb_true_iff in H2.
        rewrite check_if_continuous_ok in H1. rewrite check_size_ok in H4. destruct H4.
        rewrite check_range_ok in H3. rewrite H5 in H2.
        rewrite check_overlap_ok in H2; auto.
        * inversion H. Opaque repeat. subst postFS.
          unfold logFS, openhandleFS, vmFS, dMapFS,
          fCntFS, dCntFS, fMapFS, fsFS, layoutFS, memHandleFS, memoryFS in *.
          simpl. split; auto. left. intuition.
          -- apply (H2 p) in H6. red in H6. easy.
          -- destruct addrs. 1: simpl in H4; exfalso; apply H4; easy. simpl; easy.
          -- apply write_zeroes_length; auto.
          -- apply write_zeroes_In; auto.
          -- unfold write_zeroes in H6. destruct addrs; auto. apply in_app_or in H6.
             destruct H6; [apply in_app_or in H6; destruct H6 | ].
             ++ left. rewrite <- (firstn_skipn m0), in_app_iff. left; easy.
             ++ right. apply repeat_spec in H6. easy.
             ++ left.
                rewrite <- (firstn_skipn (m0 + length (m0 :: addrs))), in_app_iff.
                right; easy.
        * rewrite H5, <- pad_size_neq_O in H4. easy.
      + inversion H. split; auto.
    - left. inversion H. easy.
  Qed.

  Definition neqMmapHandle_false: forall mid len s lens p,
      neqMmapHandle mid len (s, lens, p) = false <-> mid = s /\ len = lens.
  Proof.
    intros. unfold neqMmapHandle.
    rewrite Bool.orb_false_iff, !Bool.negb_false_iff, !Nat.eqb_eq. easy.
  Qed.

  Definition neqMmapHandle_true: forall mid len s lens p,
      neqMmapHandle mid len (s, lens, p) = true <-> mid <> s \/ len <> lens.
  Proof.
    intros. unfold neqMmapHandle.
    rewrite Bool.orb_true_iff, !Bool.negb_true_iff, !Nat.eqb_neq. easy.
  Qed.

  Lemma forallb_exists: forall {A : Type} (f : A -> bool) (l : list A),
      forallb f l = false <-> (exists x : A, In x l /\ f x = false).
  Proof.
    intros. induction l; simpl.
    - split; intros; try easy. destruct H as [? [? ?]]. easy.
    - rewrite Bool.andb_false_iff. split; intros.
      + destruct H. 1: (exists a; split; auto). rewrite IHl in H.
        destruct H as [x [? ?]]. exists x. split; auto.
      + destruct H as [x [[? | ?] ?]].
        * subst. left; auto.
        * right. rewrite IHl. exists x. split; auto.
  Qed.

  Lemma filter_perm: forall {A: Type} (f g: A -> bool) l,
      (forall x, In x l -> f x = negb (g x)) ->
      Permutation l (filter f l ++ filter g l).
  Proof.
    intros. induction l. 1: easy. simpl. pose proof (H a (or_introl eq_refl)).
    assert (forall x : A, In x l -> f x = negb (g x)) by
        (intros; apply H; right; easy). specialize (IHl H1). clear H1.
    destruct (g a) eqn:?H; simpl in H0; rewrite H0.
    - apply Permutation_cons_app; auto.
    - apply Permutation_cons; auto.
  Qed.

  Lemma filter_perm': forall {A: Type} (f: A -> bool) l,
      Permutation l (filter (fun x => negb (f x)) l ++ filter f l).
  Proof. intros. apply filter_perm. intros; easy. Qed.

  Lemma NoOverlap_cons_inv: forall x l, NoOverlap (x :: l) -> NoOverlap l.
  Proof. intros. inversion H. easy. Qed.

  Lemma NoOverlap_NoDup: forall l, NoOverlap l -> NoNull l -> NoDup l.
  Proof.
    induction l; intros; constructor.
    - inversion H. subst. intro. specialize (H3 _ H1). destruct a as [[s len] p].
      red in H3. red in H0. rewrite Forall_forall in H0. specialize (H0 _ (in_eq _ _)).
      red in H0. rewrite pad_size_neq_O in H0. destruct H3; omega.
    - apply IHl.
      + eapply NoOverlap_cons_inv; eauto.
      + eapply NoNull_cons_inv; eauto.
  Qed.

  Lemma filter_nil: forall {A: Type} (f: A -> bool) l,
      filter f l = nil <-> forall i, In i l -> f i = false.
  Proof.
    intros. induction l.
    - split; intros. 1: inversion H0. simpl. easy.
    - split; intros.
      + simpl in H. rm_hif_eqn H. 1: inversion H. simpl in H0. destruct H0.
        1: subst; auto. apply IHl; auto.
      + simpl. rm_if_eqn.
        * specialize (H _ (in_eq _ _)). rewrite H in Heqb. inversion Heqb.
        * rewrite IHl. intros. apply H. simpl. right; easy.
  Qed.

  Lemma NoNull_head: forall mid len pa l,
      NoNull ((mid, len, pa) :: l) -> len <> O.
  Proof.
    intros. unfold NoNull in H. rewrite Forall_forall in H.
    pose proof (H _ (in_eq _ _)). red in H0. easy.
  Qed.

  Lemma NoOverlap_NoNull_neq: forall mid len perm l,
      NoOverlap l -> NoNull l -> In (mid, len, perm) l ->
      filter (fun x => negb (neqMmapHandle mid len x)) l = [(mid, len, perm)].
  Proof.
    do 3 intro. induction l; intros. 1: inversion H1. simpl in H1. destruct H1.
    - subst. simpl. rm_if_eqn.
      + f_equal. rewrite filter_nil. intros. rewrite Bool.negb_false_iff.
        destruct i as [[si leni] p]. rewrite neqMmapHandle_true.
        inversion H. subst. specialize (H4 _ H1). simpl in H4. left.
        unfold NoNull in H0. rewrite Forall_forall in H0.
        pose proof (H0 _ (in_eq _ _)). simpl in H2.
        specialize (H0 _ (in_cons _ _ _ H1)). simpl in H0.
        rewrite pad_size_neq_O in H0, H2. destruct H4; omega.
      + rewrite Bool.negb_false_iff, Bool.orb_true_iff, !Bool.negb_true_iff,
        !Nat.eqb_neq in Heqb. exfalso. destruct Heqb; apply H1; easy.
    - simpl. rm_if_eqn.
      + exfalso. rewrite Bool.negb_true_iff in Heqb. destruct a as [[sa lena] pa].
        rewrite neqMmapHandle_false in Heqb. destruct Heqb. subst sa lena.
        inversion H. subst. specialize (H4 _ H1). red in H4. apply NoNull_head in H0.
        rewrite pad_size_neq_O in H0. destruct H4; omega.
      + apply IHl; auto; [eapply NoOverlap_cons_inv | eapply NoNull_cons_inv]; eauto.
  Qed.

  Lemma munmap_ok: forall mid len err fs postFS,
      (err, postFS) = munmap mid len fs ->
      NoOverlap (memHandleFS fs) -> NoNull (memHandleFS fs) ->
      ((forall perm, ~ In (mid, len, perm) (memHandleFS fs)) /\
       err = eInval /\ postFS = fs) \/
      (exists perm p1 p2 p3 succ,
          In (mid, len, perm) (memHandleFS fs) /\
          hd_error (logFS postFS) = Some (Call_DeallocMem p1 p2 p3 succ) /\
          ((succ = false /\ err = eInval /\ fsFS postFS = fsFS fs) \/
           (succ = true /\ err = eSucc /\ layoutFS fs = layoutFS postFS /\
            openhandleFS fs = openhandleFS postFS /\ vmFS fs = vmFS postFS /\
            fMapFS fs = fMapFS postFS /\ dMapFS fs = dMapFS postFS /\
            fnode_ctr (fsFS fs) = fnode_ctr (fsFS postFS) /\
            dnode_ctr (fsFS fs) = dnode_ctr (fsFS postFS) /\
            memoryFS postFS = memoryFS fs /\
            Permutation ((mid, len, perm) :: memHandleFS postFS) (memHandleFS fs)))).
  Proof.
    intros. unfold munmap in H. simpl in H. rm_hif_eqn H.
    - rewrite forallb_forall in Heqb. left. inversion H. subst. split; auto.
      unfold memHandleFS. repeat intro. apply Heqb in H2. unfold neqMmapHandle in H2.
      rewrite Bool.orb_true_iff, !Bool.negb_true_iff, !Nat.eqb_neq in H2.
      destruct H2; apply H2; easy.
    - right. destruct fs as [fs ?]. simpl in H. rewrite forallb_exists in Heqb.
      destruct Heqb as [[[? ?] perm] [? ?]]. simpl in H2.
      rewrite neqMmapHandle_false in H3. destruct H3. subst m n.
      remember (deallocate_memory (mmap_memory fs) mid len (length l)) as succ.
      exists perm, (mmap_memory fs), mid, len, succ. unfold memHandleFS in *.
      simpl in *. split; auto. rm_hif_eqn H.
      + simpl in H. inversion H. simpl. split; auto. right. subst postFS.
        unfold logFS, openhandleFS, vmFS, dMapFS,
        fCntFS, dCntFS, fMapFS, fsFS, layoutFS, memHandleFS, memoryFS in *. simpl.
        intuition. pose proof (filter_perm' (neqMmapHandle mid len) (mmap_handles fs)).
        rewrite (NoOverlap_NoNull_neq mid len perm) in H3; auto. simpl in H3. easy.
      + inversion H. simpl. split; auto.
  Qed.

  (* page ids unique among all files *)
  (* file size match page ids *)


  (* create_dir stats readdir truncate chmod *)
  (* path + name -> does not exists *)
  (* path is valid *)
  (* permission path has write *)
  (* external call succeed *)
  (* preserve tree dmap properties *)

  Corollary fs_read_safty: forall arg result fs postFS,
      good_file_system (fsFS fs) -> (result, postFS) = fs_read arg fs ->
      good_file_system (fsFS postFS).
  Proof.
    intros arg result. destruct arg as [fId len]. destruct result as [buf err].
    intros. pose proof H. destruct H as [_ [_ [_ [_ [_ [? _]]]]]].
    pose proof (fs_read_ok _ _ _ _ _ _ H0 H). destruct H2 as [?|[?|[?|[?|[?|?]]]]].
    - destruct H2 as [? [? ?]]. subst fs. auto.
    - destruct H2 as [? [? [? [? ?]]]]. subst fs. auto.
    - destruct H2 as [? [? [? [? ?]]]]. rewrite H5. auto.
    - destruct H2 as [? [? [? _]]]. rewrite H4. auto.
    - destruct H2 as [? [? [? _]]]. rewrite H4. auto.
    - destruct H2 as [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]].
      unfold layoutFS, vmFS, fMapFS, dMapFS, fsFS, openhandleFS in *. hnf.
      rewrite <- H5, <- H7, <- H8, <- H9, <- H10, <- H11, <- H12, H13.
      destruct H1 as [? [? [? [? [? [? [? [? ?]]]]]]]]. split; intuition.
  Qed.

  Corollary fs_open_safty: forall arg result fs postFS,
      good_file_system (fsFS fs) -> (result, postFS) = fs_open arg fs ->
      good_file_system (fsFS postFS).
  Proof.
    intros arg result. destruct arg as [path fname]. destruct result as [fId err].
    intros. pose proof H. destruct H as [? [_ [_ [_ [_ [? _]]]]]].
    pose proof (fs_open_ok _ _ _ _ _ _ H0 H2 H). destruct H3 as [?|[?|[?|?]]].
    - destruct H3 as [_ [_ [_ ?]]]. subst fs; auto.
    - destruct H3 as [_ [_ [_ ?]]]. subst fs; auto.
    - destruct H3 as [_ [_ [? _]]]. unfold fsFS. rewrite <- H3; auto.
    - destruct H3 as [? [? [? [? [? [? [? [? [? [? [? [? [? _]]]]]]]]]]]]].
      clear H H2. hnf. destruct H1 as [? [? [? [? [? [? [? [? ?]]]]]]]].
      unfold fsFS, layoutFS, vmFS, fMapFS, dMapFS, openhandleFS in *.
      rewrite <- H6, <- H8, <- H9, <- H10, <- H11, <- H12, <- H13. intuition.
  Qed.

  Corollary fs_close_safty: forall arg result fs postFS,
      good_file_system (fsFS fs) -> (result, postFS) = fs_close arg fs ->
      good_file_system (fsFS postFS).
  Proof.
    intros. pose proof (fs_close_ok _ _ _ _ H H0). destruct H1 as [?|[?|?]].
    - destruct H1 as [_ [? _]]. subst fs; assumption.
    - destruct H1 as [? [? [? [? [? [? [? [? [? [? [? [? _]]]]]]]]]]]].
      destruct H as [? [? [? [? [? [? [? [? ?]]]]]]]]. hnf.
      unfold fsFS, layoutFS, vmFS, fMapFS, dMapFS, openhandleFS in *.
      rewrite <- H4, <- H6, <- H7, <- H9, <- H10, <- H11, <- H12. intuition.
      pose proof (Permutation_NoDup H3 H17). rewrite NoDup_cons_iff in H23.
      destruct H23; assumption.
    - destruct H1 as [_ [_ [? _]]]. unfold fsFS. rewrite <- H1; assumption.
  Qed.

  Corollary fs_write_safty: forall arg result fs postFS,
      good_file_system (fsFS fs) -> (result, postFS) = fs_write arg fs ->
      good_file_system (fsFS postFS).
  Proof.
    intros. destruct arg as [[fId buf] pos]. rename result into err.
    pose proof (fs_write_ok _ _ _ _ _ _ H0 H). destruct H1 as [?|[?|[?|[?|?]]]].
    - destruct H1 as [_ [? _]]. subst fs; assumption.
    - destruct H1 as [_ [? _]]. subst fs; assumption.
    - destruct H1 as [_ [_ [? _]]]. rewrite H1; assumption.
    - destruct H1 as [_ [? _]]. rewrite H1; assumption.
    - intuition.
  Qed.

  Corollary fs_seek_safty: forall arg result fs postFS,
      good_file_system (fsFS fs) -> (result, postFS) = fs_seek arg fs ->
      good_file_system (fsFS postFS).
  Proof.
    intros. destruct arg as [fId pos]. rename result into err.
    pose proof (fs_seek_ok _ _ _ _ _ H0). destruct H1 as [?|[?|[?|?]]].
    - destruct H1 as [_ [? _]]. subst fs; assumption.
    - destruct H1 as [_ [_ [_ [? _]]]]. subst fs; assumption.
    - destruct H1 as [_ [_ [? _]]]. rewrite H1; assumption.
    - destruct H1 as [? [? [? [? [? [? [? [? [? [? [? _]]]]]]]]]]].
      destruct H as [? [? [? [? [? [? [? [? ?]]]]]]]]. hnf.
      unfold fsFS, layoutFS, vmFS, fMapFS, dMapFS, openhandleFS in *.
      rewrite <- H3, <- H5, <- H6, <- H7, <- H8, <- H9, <- H10, H11. intuition.
  Qed.

  Corollary fs_create_safty: forall arg result fs postFS,
      good_file_system (fsFS fs) -> (result, postFS) = fs_create arg fs ->
      good_file_system (fsFS postFS).
  Proof.
    intros. destruct arg as [[path fname] p]. rename result into err.
    pose proof (fs_create_ok _ _ _ _ _ _ H H0).
    destruct H1 as [? | [? | [? | [? | [? | [? | ?]]]]]];
      [destruct H1 as [_ [_ ?]]; subst fs; assumption.. |
       destruct H1 as [_ [_ [? _]]]; rewrite <- H1; assumption |
       intuition].
  Qed.

  Corollary fs_mkdir_safty: forall arg result fs postFS,
      good_file_system (fsFS fs) -> (result, postFS) = fs_mkdir arg fs ->
      good_file_system (fsFS postFS).
  Proof.
    intros. destruct arg as [[path dname] p]. rename result into err.
    pose proof (fs_mkdir_ok _ _ _ _ _ _ H H0).
    destruct H1 as [? | [? | [? | [? | [? | [? | ?]]]]]];
      [destruct H1 as [_ [_ ?]]; subst fs; assumption.. |
       destruct H1 as [_ [_ [? _]]]; rewrite <- H1; assumption |
       intuition].
  Qed.

  Corollary fs_rmdir_safty: forall arg result fs postFS,
      good_file_system (fsFS fs) -> (result, postFS) = fs_rmdir arg fs ->
      good_file_system (fsFS postFS).
  Proof.
    intros. rename arg into path. rename result into err.
    pose proof (fs_rmdir_ok _ _ _ _ H H0).
    destruct H1 as [? | [? | [? | [? | [? | ?]]]]].
    - destruct H1 as [_ [_ ?]]; subst fs; assumption.
    - destruct H1 as [_ [_ [_ ?]]]; subst fs; assumption.
    - destruct H1 as [_ [_ [_ ?]]]; subst fs; assumption.
    - destruct H1 as [_ [_ [_ [_ ?]]]]; subst fs; assumption.
    - destruct H1 as [_ [_ [_ [_ [? _]]]]]. rewrite H1; assumption.
    - intuition.
  Qed.

  Corollary fs_remove_safty: forall arg result fs postFS,
      good_file_system (fsFS fs) -> (result, postFS) = fs_remove arg fs ->
      good_file_system (fsFS postFS).
  Proof.
    intros. destruct arg as [path fname]. rename result into err.
    pose proof (fs_remove_ok _ _ _ _ _ H H0).
    destruct H1 as [? | [? | [? | [? | ?]]]].
    - destruct H1 as [_ [_ ?]]; subst fs; assumption.
    - destruct H1 as [_ [_ ?]]; subst fs; assumption.
    - destruct H1 as [_ [_ [_ ?]]]; subst fs; assumption.
    - destruct H1 as [_ [_ [_ [? _]]]]. rewrite <- H1; assumption.
    - intuition.
  Qed.

  Corollary fs_chmod_safty: forall arg result fs postFS,
      good_file_system (fsFS fs) -> (result, postFS) = fs_chmod arg fs ->
      good_file_system (fsFS postFS).
  Proof.
    intros. destruct arg as [path p]. rename result into err.
    pose proof (fs_chmod_ok _ _ _ _ _ H H0).
    destruct H1 as [? | [? | [? | ?]]].
    - destruct H1 as [_ [_ [_ [_ ?]]]]; subst fs; assumption.
    - destruct H1 as [_ [? _]]. rewrite <- H1; assumption.
    - destruct H1 as [? [? [? [? [? [? [? [? [? _]]]]]]]]].
      destruct H as [? [? [? [? [? [? [? [? ?]]]]]]]]. hnf.
      unfold fsFS, layoutFS, vmFS, fMapFS, dMapFS, openhandleFS, fCntFS, dCntFS in *.
      rewrite <- H2, <- H3, <- H5, <- H6, <- H7, <- H8, <- H9. intuition.
      apply preserve_dname_NoDupNameTree with (d_map (fst fs)). 2: assumption. intros.
      destruct H1 as [dId' [_ [_ [? ?]]]]. destruct (Nat.eq_dec dId dId').
      + subst dId'. intuition.
      + rewrite H20; auto.
    - destruct H1 as [? [? [? [? [? [? [? [? [_ [? [? _]]]]]]]]]]].
      destruct H as [? [? [? [? [? [? [? [? ?]]]]]]]]. hnf.
      unfold fsFS, layoutFS, vmFS, fMapFS, dMapFS, openhandleFS, fCntFS, dCntFS in *.
      destruct H1 as [fId' [? [? [? [? [? ?]]]]]].
      assert (forall id, pageIdsF (f_map (fst postFS) id) =
                         pageIdsF (f_map (fst fs) id)) by
          (intros; destruct (Nat.eq_dec id fId'); [subst id | rewrite H23]; auto).
      rewrite <- H3, <- H4, <- H6, <- H7, <- H8, <- H9, <- H10. intuition.
      + apply preserve_fname_NoDupNameTree with (f_map (fst fs)). 2: assumption.
        intros. destruct (Nat.eq_dec fId fId'); [subst fId | rewrite H23]; auto.
      + rewrite H24 in H30, H29. eapply H17; eauto.
      + rewrite H24 in H27. eapply H25; eauto.
  Qed.

  Corollary fs_readdir_safty: forall arg result fs postFS,
      good_file_system (fsFS fs) -> (result, postFS) = fs_readdir arg fs ->
      good_file_system (fsFS postFS).
  Proof.
    intros. rename arg into path. destruct result as [result err].
    pose proof (fs_readdir_ok _ _ _ _ _ H H0). destruct H1 as [? | [? | ?]].
    - destruct H1 as [_ [_ [_ ?]]]; subst fs; assumption.
    - destruct H1 as [_ [_ [_ [? _]]]]. rewrite <- H1; assumption.
    - destruct H1 as [_ [_ [? _]]]. rewrite <- H1; assumption.
  Qed.

  Corollary fs_fstat_safty: forall arg result fs postFS,
      good_file_system (fsFS fs) -> (result, postFS) = fs_fstat arg fs ->
      good_file_system (fsFS postFS).
  Proof.
    intros. rename arg into id.
    destruct result as [[[[name permsn] fsize] pageIds] err].
    pose proof (fs_fstat_ok _ _ _ _ _ _ _ _ H0);
      destruct H1 as [? | [? | ?]]; destruct H1 as [_ [? _]];
        [subst fs | rewrite H1..]; assumption.
  Qed.

  Corollary fs_truncate_safty: forall arg result fs postFS,
      good_file_system (fsFS fs) -> (result, postFS) = fs_truncate arg fs ->
      good_file_system (fsFS postFS).
  Proof.
    intros. destruct arg as [fId len]. rename result into err.
    pose proof (fs_truncate_ok _ _ _ _ _ H H0).
    destruct H1 as [? | [? | [? | [? | ?]]]].
    - destruct H1 as [_ [? _]]; subst fs; assumption.
    - destruct H1 as [_ [? _]]; subst fs; assumption.
    - destruct H1 as [_ [? _]]; subst fs; assumption.
    - destruct H1 as [_ [_ [? _]]]. rewrite <- H1; assumption.
    - destruct H1 as [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]].
      destruct H as [? [? [? [? [? [? [? [? ?]]]]]]]]. hnf.
      unfold fsFS, layoutFS, vmFS, fMapFS, dMapFS, openhandleFS, fCntFS, dCntFS in *.
      rewrite <- H3, <- H4, <- H6, <- H7, <- H8, <- H9, <- H10. intuition.
      + apply preserve_fname_NoDupNameTree with (f_map (fst fs)); auto. intro id'.
        destruct (Nat.eq_dec id' fId); [subst id' | rewrite H24]; intuition.
      + destruct (Nat.eq_dec fId1 fId), (Nat.eq_dec fId2 fId).
        * rewrite <- e in e0. apply H26. intuition.
        * subst fId. clear n. revert H31. apply (H21 fId1 fId2); auto.
          -- destruct H27 as [l ?]. rewrite H27, in_app_iff. left; auto.
          -- rewrite <- H24; auto.
        * subst fId. clear n. revert H31. apply (H21 fId1 fId2); auto.
          -- rewrite <- H24; auto.
          -- destruct H27 as [l ?]. rewrite H27, in_app_iff. left; auto.
        * revert H31. apply (H21 fId1 fId2); auto; rewrite <- H24; auto.
      + destruct (Nat.eq_dec fId0 fId).
        * subst fId0. destruct H27 as [l ?]. apply (H23 fId pgId).
          rewrite H27, in_app_iff. left; auto.
        * apply (H23 fId0 pgId). rewrite <- H24; auto.
  Qed.

  Corollary mmap_safty: forall len perm flag fs result postFS,
      good_file_system (fsFS fs) -> (result, postFS) = mmap len perm flag fs ->
      good_file_system (fsFS postFS).
  Proof.
    intros. destruct result as [mid err]. pose proof H.
    destruct H as [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]].
    pose proof (mmap_ok _ _ _ _ _ _ _ H0 H12).
    destruct H13 as [? | ?]. 1: destruct H13 as [_ [? _]]; subst fs; easy.
    destruct H13 as [? [p1 [p2 [addrs [? [? | ?]]]]]].
    2: destruct H15 as [_ ?]; rewrite H15; easy. hnf.
    destruct H15 as [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]]]].
    unfold fsFS, layoutFS, vmFS, fMapFS, dMapFS, openhandleFS, fCntFS,
    dCntFS, memHandleFS in *.
    rewrite <- H21, <- H22, <- H24, <- H25, <- H26, <- H27, H28. intuition.
    - constructor; auto.
    - apply H33 in H31. destruct H31; auto. rewrite H31. apply repeat_length.
    - unfold NoNull in *. rewrite Forall_forall in *. intros. simpl in H31.
      destruct H31; auto. subst x. red. rewrite pad_size_neq_O. rewrite <- H17. easy.
  Qed.

  Close Scope string_scope.

  Lemma Disjoint_comm: forall a b, Disjoint a b <-> Disjoint b a.
  Proof.
    intros. destruct a as [[s1 l1] p1]. destruct b as [[s2 l2] p2]. simpl. intuition.
  Qed.

  Lemma NoOverlap_double_cons: forall l a1 a2,
      NoOverlap (a1 :: a2 :: l) -> NoOverlap (a2 :: a1 :: l).
  Proof.
    intros. inversion H. subst. inversion H3. subst. constructor.
    - intros. simpl in H0. destruct H0. 2: apply H4; easy. subst y.
      rewrite Disjoint_comm. apply H2. left; easy.
    - constructor; auto. intros. apply H2. right; easy.
  Qed.

  Lemma NoOverlap_double_cons_iff: forall l a1 a2,
      NoOverlap (a1 :: a2 :: l) <-> NoOverlap (a2 :: a1 :: l).
  Proof. intros; split; intros; apply NoOverlap_double_cons; easy. Qed.

  Lemma NoOverlap_cons_app: forall l1 l2 a,
      NoOverlap (a :: l1 ++ l2) <-> NoOverlap (l1 ++ a :: l2).
  Proof.
    induction l1; intros; simpl. 1: easy. rewrite NoOverlap_double_cons_iff.
    split; intros; inversion H; subst; constructor; intros.
    - apply H2. rewrite in_app_iff in H0. simpl in *. rewrite in_app_iff. intuition.
    - rewrite <- IHl1. easy.
    - apply H2. rewrite in_app_iff. simpl in *. rewrite in_app_iff in H0. intuition.
    - rewrite IHl1. easy.
  Qed.

  Lemma NoOverlap_perm: forall l1 l2,
      Permutation l1 l2 -> NoOverlap l1 -> NoOverlap l2.
  Proof.
    induction l1. intros.
    - destruct l2. 1: constructor. apply Permutation_length in H. simpl in H. omega.
    - intros. assert (In a l2) by (apply (Permutation_in _ H); left; easy).
      apply in_split in H1. destruct H1 as [li1 [li2 ?]]. subst l2.
      rewrite <- NoOverlap_cons_app. apply Permutation_cons_app_inv in H. constructor.
      + intros. inversion H0. subst. apply H4. symmetry in H.
        apply (Permutation_in _ H). easy.
      + apply IHl1; auto. inversion H0. auto.
  Qed.

  Lemma NoNull_perm: forall l1 l2, Permutation l1 l2 -> NoNull l1 -> NoNull l2.
  Proof.
    intros. unfold NoNull in *. rewrite Forall_forall in *. intros. apply H0.
    symmetry in H. eapply Permutation_in; eauto.
  Qed.

  Corollary munmap_safty: forall mid len err fs postFS,
      good_file_system (fsFS fs) -> (err, postFS) = munmap mid len fs ->
      good_file_system (fsFS postFS).
  Proof.
    intros. pose proof H.
    destruct H as [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]].
    pose proof (munmap_ok _ _ _ _ _ H0 H10 H12).
    destruct H13 as [[_ [_ ?]] | ?]. 1: subst; easy. hnf.
    destruct H13 as [perm [p1 [p2 [p3 [succ [? [? [[_ [_ ?]]| ?]]]]]]]].
    1: rewrite H15; easy. destruct H15 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
    unfold fsFS, layoutFS, vmFS, fMapFS, dMapFS, openhandleFS, fCntFS,
    dCntFS, memHandleFS, memoryFS in *. symmetry in H25.
    rewrite <- H17, <- H18, <- H20, <- H21, <- H22, <- H23, H24. intuition.
    - apply NoOverlap_perm in H25; auto. inversion H25. easy.
    - apply NoNull_perm in H25; auto. apply NoNull_cons_inv in H25. easy.
  Qed.

  Definition fs_functions:
    list {n : nat & fs_parameter n -> State FSState (fs_result n)} :=
    [existT _ O fs_read  ; existT _  1 fs_open    ; existT _  2 fs_close  ;
     existT _ 3 fs_write ; existT _  4 fs_seek    ; existT _  5 fs_create ;
     existT _ 6 fs_mkdir ; existT _  7 fs_rmdir   ; existT _  8 fs_remove ;
     existT _ 9 fs_chmod ; existT _ 10 fs_readdir ; existT _ 11 fs_fstat  ;
     existT _ 12 fs_truncate].

  Theorem function_safty: forall v fs postFS arg result,
      In v fs_functions -> (result, postFS) = (projT2 v) arg fs ->
      good_file_system (fsFS fs) -> good_file_system (fsFS postFS).
  Proof.
    intros. unfold fs_functions in H. simpl in H.
    destruct H as [?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|?]]]]]]]]]]]]];
      [subst v; simpl in *.. | exfalso; assumption].
    - eapply fs_read_safty; eauto.
    - eapply fs_open_safty; eauto.
    - eapply fs_close_safty; eauto.
    - eapply fs_write_safty; eauto.
    - eapply fs_seek_safty; eauto.
    - eapply fs_create_safty; eauto.
    - eapply fs_mkdir_safty; eauto.
    - eapply fs_rmdir_safty; eauto.
    - eapply fs_remove_safty; eauto.
    - eapply fs_chmod_safty; eauto.
    - eapply fs_readdir_safty; eauto.
    - eapply fs_fstat_safty; eauto.
    - eapply fs_truncate_safty; eauto.
  Qed.

  Fixpoint fs_compose (l: list {n : nat & ((fs_parameter n -> State FSState (fs_result n)) * (fs_parameter n))%type}) (input: FSState) : FSState :=
    match l with
    | nil => input
    | f :: l' => let (result, postFS) := (fst (projT2 f)) (snd (projT2 f)) input in
                 fs_compose l' postFS
    end.

  Corollary composition_safty: forall l input,
      (forall v, In v l -> In (existT _ (projT1 v) (fst (projT2 v))) fs_functions) ->
      good_file_system (fsFS input) ->
      good_file_system (fsFS (fs_compose l input)).
  Proof.
    induction l; intros; simpl; auto.
    assert (In a (a :: l)) by (simpl; left; reflexivity). pose proof (H _ H1).
    destruct a as [n [v va]]. unfold fst, snd, projT1, projT2 in H2 |- *. clear H1.
    remember (v va input). destruct p as [? ?].
    pose proof (function_safty _ _ _ _ _ H2 Heqp H0). apply IHl; auto. clear H2.
    intros. apply H. simpl. right. auto.
  Qed.

  Lemma good_file_system_mkfs: forall name, good_file_system (fsFS (mkfs name)).
  Proof.
    intros. unfold mkfs. hnf. simpl.
    split; [|split; [|split; [|split; [|split; [|split; [|split;[|split;[|split;[|split;[|split]]]]]]]]]]; intros; try easy.
    - constructor; simpl. 1: rewrite Forall_forall; intros; inversion H. constructor.
    - constructor; [intro S; inversion S | constructor].
    - constructor.
    - intros. destruct H; intuition.
    - constructor.
    - hnf. exists O, []. reflexivity.
    - constructor.
    - red. easy.
  Qed.

  Corollary composition_mkfs_safty: forall l name,
      (forall v, In v l -> In (existT _ (projT1 v) (fst (projT2 v))) fs_functions) ->
      good_file_system (fsFS (fs_compose l (mkfs name))).
  Proof. intros. apply composition_safty; auto. apply good_file_system_mkfs. Qed.

  Parameter fs_rename : Path -> FData -> Path -> FData -> ErrCode.
  Parameter fs_flush : Fid -> ErrCode.

End SGX_FS.
