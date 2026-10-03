 (* RV32I bit extraction, subset recognition, canonical encoding, and proofs. *)

From Stdlib Require Import NArith.NArith.
From Stdlib Require Import NArith.Nnat.
From Stdlib Require Import Lia.
Set Warnings "-warn-library-file-stdlib-vector".
From Stdlib Require Import Vectors.Fin.
From MicroVeriVM Require Import RiscV.Word.
From MicroVeriVM Require Import RiscV.RegisterFile.
From MicroVeriVM Require Import RiscV.Instruction.

Set Warnings "-warn-library-file-stdlib-vector".

Open Scope N_scope.

Definition rv32_pow2 (width : N) : N := 2 ^ width.

Definition rv32_extract_bits (word lsb width : N) : N :=
  N.modulo (N.div word (rv32_pow2 lsb)) (rv32_pow2 width).

Theorem rv32_extract_bits_range :
  forall word lsb width,
    rv32_extract_bits word lsb width < rv32_pow2 width.
Proof.
  intros word lsb width.
  unfold rv32_extract_bits.
  apply N.mod_lt.
  apply N.pow_nonzero.
  discriminate.
Qed.

Theorem rv32_extract_bits_le :
  forall word lsb width upper,
    rv32_pow2 width = N.succ upper ->
    rv32_extract_bits word lsb width <= upper.
Proof.
  intros word lsb width upper Hpower.
  apply (proj1 (N.lt_succ_r _ _)).
  rewrite <- Hpower.
  apply rv32_extract_bits_range.
Qed.

Definition rv32_register_index_of_nat
    (index : nat) (bound : (index < 32)%nat) : rv32_register_index.
Proof.
  destruct index as [|previous].
  - exact RV32X0.
  - exact (RV32WritableIndex
      (Fin.of_nat_lt (p := previous) (n := 31) (ltac:(lia)))).
Defined.

Definition rv32_register_index_of_field
    (field : N) (bound : field < 32) : rv32_register_index.
Proof.
  apply rv32_register_index_of_nat with
    (index := N.to_nat field).
  lia.
Defined.

Definition rv32_decode_rd (word : N) : rv32_register_index :=
  rv32_register_index_of_field
    (rv32_extract_bits word 7 5)
    (ltac:(apply rv32_extract_bits_range)).

Definition rv32_decode_rs1 (word : N) : rv32_register_index :=
  rv32_register_index_of_field
    (rv32_extract_bits word 15 5)
    (ltac:(apply rv32_extract_bits_range)).

Definition rv32_decode_rs2 (word : N) : rv32_register_index :=
  rv32_register_index_of_field
    (rv32_extract_bits word 20 5)
    (ltac:(apply rv32_extract_bits_range)).

Theorem rv32_decoded_rd_is_valid :
  forall word,
    (0 <= rv32_register_index_number (rv32_decode_rd word) <= 31)%nat.
Proof.
  intros word.
  apply rv32_register_index_in_range.
Qed.

Theorem rv32_decoded_rs1_is_valid :
  forall word,
    (0 <= rv32_register_index_number (rv32_decode_rs1 word) <= 31)%nat.
Proof.
  intros word.
  apply rv32_register_index_in_range.
Qed.

Theorem rv32_decoded_rs2_is_valid :
  forall word,
    (0 <= rv32_register_index_number (rv32_decode_rs2 word) <= 31)%nat.
Proof.
  intros word.
  apply rv32_register_index_in_range.
Qed.

Definition rv32_decode_i_imm12 (word : N) : rv32_imm12 :=
  exist (fun bits : N => (bits < 4096)%N)
    (rv32_extract_bits word 20 12)
    (ltac:(pose proof (rv32_extract_bits_range word 20 12) as H;
           unfold rv32_pow2 in H;
           change (rv32_extract_bits word 20 12 < 4096)%N in H;
           exact H)).

Definition rv32_decode_s_imm12 (word : N) : rv32_imm12 :=
  exist (fun bits : N => (bits < 4096)%N)
    (rv32_extract_bits word 25 7 * 32 +
      rv32_extract_bits word 7 5)
    (ltac:(assert (Hhigh :
             (rv32_extract_bits word 25 7 < 128)%N)
             by (pose proof (rv32_extract_bits_range word 25 7) as H;
                 unfold rv32_pow2 in H;
                 change (rv32_extract_bits word 25 7 < 128)%N in H;
                 exact H);
           assert (Hlow :
             (rv32_extract_bits word 7 5 < 32)%N)
             by (pose proof (rv32_extract_bits_range word 7 5) as H;
                 unfold rv32_pow2 in H;
                 change (rv32_extract_bits word 7 5 < 32)%N in H;
                 exact H);
           change (rv32_extract_bits word 25 7 < N.succ 127)%N in Hhigh;
           change (rv32_extract_bits word 7 5 < N.succ 31)%N in Hlow;
           apply N.lt_succ_r in Hhigh;
           apply N.lt_succ_r in Hlow;
           assert (Hscaled :
             (rv32_extract_bits word 25 7 * 32 <= 127 * 32)%N)
             by (apply N.mul_le_mono_r; exact Hhigh);
           assert (Hcombined :
             (rv32_extract_bits word 25 7 * 32 +
               rv32_extract_bits word 7 5 <= 127 * 32 + 31)%N)
             by (apply N.add_le_mono; assumption);
           assert (Hfinal : (127 * 32 + 31 < 4096)%N)
             by (vm_compute; reflexivity);
           eapply N.le_lt_trans;
           [exact Hcombined | exact Hfinal])).

Definition rv32_decode_b_imm13 (word : N) : rv32_imm13 :=
  exist (fun bits : N => (bits < 8192)%N)
    (rv32_extract_bits word 31 1 * 4096 +
      rv32_extract_bits word 7 1 * 2048 +
      rv32_extract_bits word 25 6 * 32 +
      rv32_extract_bits word 8 4 * 2)
    (ltac:(assert (H12 :
             rv32_extract_bits word 31 1 <= 1)
             by (apply (rv32_extract_bits_le word 31 1 1);
                 vm_compute; reflexivity);
           assert (H11 :
             rv32_extract_bits word 7 1 <= 1)
             by (apply (rv32_extract_bits_le word 7 1 1);
                 vm_compute; reflexivity);
           assert (H10_5 :
             rv32_extract_bits word 25 6 <= 63)
             by (apply (rv32_extract_bits_le word 25 6 63);
                 vm_compute; reflexivity);
           assert (H4_1 :
             rv32_extract_bits word 8 4 <= 15)
             by (apply (rv32_extract_bits_le word 8 4 15);
                 vm_compute; reflexivity);
           assert (Hterm12 :
             rv32_extract_bits word 31 1 * 4096 <= 4096)
             by (change
                   (rv32_extract_bits word 31 1 * 4096 <= 1 * 4096);
                 apply N.mul_le_mono_r; exact H12);
           assert (Hterm11 :
             rv32_extract_bits word 7 1 * 2048 <= 2048)
             by (change
                   (rv32_extract_bits word 7 1 * 2048 <= 1 * 2048);
                 apply N.mul_le_mono_r; exact H11);
           assert (Hterm10_5 :
             rv32_extract_bits word 25 6 * 32 <= 2016)
             by (change
                   (rv32_extract_bits word 25 6 * 32 <= 63 * 32);
                 apply N.mul_le_mono_r; exact H10_5;
                 vm_compute; reflexivity);
           assert (Hterm4_1 :
             rv32_extract_bits word 8 4 * 2 <= 30)
             by (change
                   (rv32_extract_bits word 8 4 * 2 <= 15 * 2);
                 apply N.mul_le_mono_r; exact H4_1;
                 vm_compute; reflexivity);
           assert (Hsum12_11 :
             rv32_extract_bits word 31 1 * 4096 +
               rv32_extract_bits word 7 1 * 2048 <= 4096 + 2048)
             by (apply N.add_le_mono; assumption);
           assert (Hsum10_5 :
             rv32_extract_bits word 31 1 * 4096 +
               rv32_extract_bits word 7 1 * 2048 +
               rv32_extract_bits word 25 6 * 32 <=
               4096 + 2048 + 2016)
             by (apply N.add_le_mono; assumption);
           assert (Hsum :
             rv32_extract_bits word 31 1 * 4096 +
               rv32_extract_bits word 7 1 * 2048 +
               rv32_extract_bits word 25 6 * 32 +
               rv32_extract_bits word 8 4 * 2 <=
               4096 + 2048 + 2016 + 30)
             by (apply N.add_le_mono; assumption);
           assert (Hfinal : (4096 + 2048 + 2016 + 30 < 8192)%N)
             by (vm_compute; reflexivity);
           eapply N.le_lt_trans;
           [exact Hsum | exact Hfinal])).
Definition rv32_decode_u_imm20 (word : N) : rv32_imm20 :=
  exist (fun bits : N => (bits < 1048576)%N) (rv32_extract_bits word 12 20)
    (ltac:(pose proof (rv32_extract_bits_range word 12 20) as H;
           unfold rv32_pow2 in H;
           change (rv32_extract_bits word 12 20 < 1048576)%N in H;
           exact H)).

Definition rv32_decode_j_imm21 (word : N) : rv32_imm21 :=
  exist (fun bits : N => (bits < 2097152)%N)
    (rv32_extract_bits word 31 1 * 1048576 +
      rv32_extract_bits word 21 10 * 2 +
      rv32_extract_bits word 20 1 * 2048 +
      rv32_extract_bits word 12 8 * 4096)
    (ltac:(assert (H20 :
             rv32_extract_bits word 31 1 <= 1)
             by (apply (rv32_extract_bits_le word 31 1 1);
                 vm_compute; reflexivity);
           assert (H10_1 :
             rv32_extract_bits word 21 10 <= 1023)
             by (apply (rv32_extract_bits_le word 21 10 1023);
                 vm_compute; reflexivity);
           assert (H11 :
             rv32_extract_bits word 20 1 <= 1)
             by (apply (rv32_extract_bits_le word 20 1 1);
                 vm_compute; reflexivity);
           assert (H19_12 :
             rv32_extract_bits word 12 8 <= 255)
             by (apply (rv32_extract_bits_le word 12 8 255);
                 vm_compute; reflexivity);
           assert (Hterm20 :
             rv32_extract_bits word 31 1 * 1048576 <= 1048576)
             by (change
                   (rv32_extract_bits word 31 1 * 1048576 <= 1 * 1048576);
                 apply N.mul_le_mono_r; exact H20);
           assert (Hterm10_1 :
             rv32_extract_bits word 21 10 * 2 <= 2046)
             by (change
                   (rv32_extract_bits word 21 10 * 2 <= 1023 * 2);
                 apply N.mul_le_mono_r; exact H10_1;
                 vm_compute; reflexivity);
           assert (Hterm11 :
             rv32_extract_bits word 20 1 * 2048 <= 2048)
             by (change
                   (rv32_extract_bits word 20 1 * 2048 <= 1 * 2048);
                 apply N.mul_le_mono_r; exact H11);
           assert (Hterm19_12 :
             rv32_extract_bits word 12 8 * 4096 <= 1044480)
             by (change
                   (rv32_extract_bits word 12 8 * 4096 <= 255 * 4096);
                 apply N.mul_le_mono_r; exact H19_12;
                 vm_compute; reflexivity);
           assert (Hsum20_10_1 :
             rv32_extract_bits word 31 1 * 1048576 +
               rv32_extract_bits word 21 10 * 2 <= 1048576 + 2046)
             by (apply N.add_le_mono; assumption);
           assert (Hsum20_10_1_11 :
             rv32_extract_bits word 31 1 * 1048576 +
               rv32_extract_bits word 21 10 * 2 +
               rv32_extract_bits word 20 1 * 2048 <=
               1048576 + 2046 + 2048)
             by (apply N.add_le_mono; assumption);
           assert (Hsum :
             rv32_extract_bits word 31 1 * 1048576 +
               rv32_extract_bits word 21 10 * 2 +
               rv32_extract_bits word 20 1 * 2048 +
               rv32_extract_bits word 12 8 * 4096 <=
               1048576 + 2046 + 2048 + 1044480)
             by (apply N.add_le_mono; assumption);
           assert (Hfinal :
             (1048576 + 2046 + 2048 + 1044480 < 2097152)%N)
             by (vm_compute; reflexivity);
           eapply N.le_lt_trans;
           [exact Hsum | exact Hfinal])).

Theorem rv32_i_immediate_extracts_bits_31_20 :
  forall word,
    rv32_imm12_bits (rv32_decode_i_imm12 word) =
      rv32_extract_bits word 20 12.
Proof.
  reflexivity.
Qed.

Theorem rv32_s_immediate_uses_split_fields :
  forall word,
    rv32_imm12_bits (rv32_decode_s_imm12 word) =
      rv32_extract_bits word 25 7 * 32 +
      rv32_extract_bits word 7 5.
Proof.
  reflexivity.
Qed.

Theorem rv32_b_immediate_uses_architectural_bit_placement :
  forall word,
    rv32_imm13_bits (rv32_decode_b_imm13 word) =
      rv32_extract_bits word 31 1 * 4096 +
      rv32_extract_bits word 7 1 * 2048 +
      rv32_extract_bits word 25 6 * 32 +
      rv32_extract_bits word 8 4 * 2.
Proof.
  reflexivity.
Qed.

Theorem rv32_u_immediate_extracts_bits_31_12 :
  forall word,
    rv32_imm20_bits (rv32_decode_u_imm20 word) =
      rv32_extract_bits word 12 20.
Proof.
  reflexivity.
Qed.

Theorem rv32_j_immediate_uses_architectural_bit_placement :
  forall word,
    rv32_imm21_bits (rv32_decode_j_imm21 word) =
      rv32_extract_bits word 31 1 * 1048576 +
      rv32_extract_bits word 21 10 * 2 +
      rv32_extract_bits word 20 1 * 2048 +
      rv32_extract_bits word 12 8 * 4096.
Proof.
  reflexivity.
Qed.

Definition rv32_sign_extend_12 (immediate : rv32_imm12) : rv32_word :=
  let bits := rv32_imm12_bits immediate in
  if bits <? 2048 then rv32_word_wrap bits
  else rv32_word_wrap (rv32_modulus + bits - 4096).

Definition rv32_sign_extend_13 (immediate : rv32_imm13) : rv32_word :=
  let bits := rv32_imm13_bits immediate in
  if bits <? 4096 then rv32_word_wrap bits
  else rv32_word_wrap (rv32_modulus + bits - 8192).

Definition rv32_sign_extend_21 (immediate : rv32_imm21) : rv32_word :=
  let bits := rv32_imm21_bits immediate in
  if bits <? 1048576 then rv32_word_wrap bits
  else rv32_word_wrap (rv32_modulus + bits - 2097152).

Theorem rv32_sign_extend_12_positive :
  forall immediate,
    rv32_imm12_bits immediate < 2048 ->
    rv32_word_value (rv32_sign_extend_12 immediate) =
      rv32_imm12_bits immediate.
Proof.
  intros [bits Hbits] Hsign.
  unfold rv32_sign_extend_12, rv32_imm12_bits.
  cbn [proj1_sig rv32_word_value] in *.
  assert (Hltb : (bits <? 2048) = true).
  { apply N.ltb_lt. exact Hsign. }
  rewrite Hltb.
  apply rv32_word_wrap_small.
  unfold rv32_modulus.
  lia.
Qed.

Theorem rv32_sign_extend_12_negative :
  forall immediate,
    2048 <= rv32_imm12_bits immediate ->
    rv32_word_value (rv32_sign_extend_12 immediate) =
      rv32_modulus + rv32_imm12_bits immediate - 4096.
Proof.
  intros [bits Hbits] Hsign.
  unfold rv32_sign_extend_12, rv32_imm12_bits.
  cbn [proj1_sig rv32_word_value] in *.
  assert (N.ltb bits 2048 = false) as Hltb.
  { apply N.ltb_ge. exact Hsign. }
  rewrite Hltb.
  apply rv32_word_wrap_small.
  unfold rv32_modulus.
  lia.
Qed.

Theorem rv32_sign_extend_13_positive :
  forall immediate,
    rv32_imm13_bits immediate < 4096 ->
    rv32_word_value (rv32_sign_extend_13 immediate) =
      rv32_imm13_bits immediate.
Proof.
  intros [bits Hbits] Hsign.
  unfold rv32_sign_extend_13, rv32_imm13_bits.
  cbn [proj1_sig rv32_word_value] in *.
  assert (Hltb : (bits <? 4096) = true).
  { apply N.ltb_lt. exact Hsign. }
  rewrite Hltb.
  apply rv32_word_wrap_small.
  unfold rv32_modulus.
  lia.
Qed.

Theorem rv32_sign_extend_13_negative :
  forall immediate,
    4096 <= rv32_imm13_bits immediate ->
    rv32_word_value (rv32_sign_extend_13 immediate) =
      rv32_modulus + rv32_imm13_bits immediate - 8192.
Proof.
  intros [bits Hbits] Hsign.
  unfold rv32_sign_extend_13, rv32_imm13_bits.
  cbn [proj1_sig rv32_word_value] in *.
  assert (N.ltb bits 4096 = false) as Hltb.
  { apply N.ltb_ge. exact Hsign. }
  rewrite Hltb.
  apply rv32_word_wrap_small.
  unfold rv32_modulus.
  lia.
Qed.

Theorem rv32_sign_extend_21_positive :
  forall immediate,
    rv32_imm21_bits immediate < 1048576 ->
    rv32_word_value (rv32_sign_extend_21 immediate) =
      rv32_imm21_bits immediate.
Proof.
  intros [bits Hbits] Hsign.
  unfold rv32_sign_extend_21, rv32_imm21_bits.
  cbn [proj1_sig rv32_word_value] in *.
  assert (Hltb : (bits <? 1048576) = true).
  { apply N.ltb_lt. exact Hsign. }
  rewrite Hltb.
  apply rv32_word_wrap_small.
  unfold rv32_modulus.
  lia.
Qed.

Theorem rv32_sign_extend_21_negative :
  forall immediate,
    1048576 <= rv32_imm21_bits immediate ->
    rv32_word_value (rv32_sign_extend_21 immediate) =
      rv32_modulus + rv32_imm21_bits immediate - 2097152.
Proof.
  intros [bits Hbits] Hsign.
  unfold rv32_sign_extend_21, rv32_imm21_bits.
  cbn [proj1_sig rv32_word_value] in *.
  assert (N.ltb bits 1048576 = false) as Hltb.
  { apply N.ltb_ge. exact Hsign. }
  rewrite Hltb.
  apply rv32_word_wrap_small.
  unfold rv32_modulus.
  lia.
Qed.

Definition rv32_encode (instruction : rv32_instruction) : N :=
  let rd := N.of_nat (rv32_register_index_number (match instruction with
    | RV32_ADD rd _ _ | RV32_SUB rd _ _ | RV32_ADDI rd _ _
    | RV32_LW rd _ _ | RV32_LUI rd _ | RV32_JAL rd _
    | RV32_JALR rd _ _ => rd
    | RV32_SW _ _ _ | RV32_BEQ _ _ _ => RV32X0
    end)) in
  match instruction with
  | RV32_ADD destination source1 source2 =>
      51 + rd * 128 +
        N.of_nat (rv32_register_index_number source1) * 32768 +
        N.of_nat (rv32_register_index_number source2) * 1048576
  | RV32_SUB destination source1 source2 =>
      51 + rd * 128 + 1073741824 +
        N.of_nat (rv32_register_index_number source1) * 32768 +
        N.of_nat (rv32_register_index_number source2) * 1048576
  | RV32_ADDI destination source1 immediate =>
      19 + rd * 128 +
        N.of_nat (rv32_register_index_number source1) * 32768 +
        rv32_imm12_bits immediate * 1048576
  | RV32_LW destination source1 immediate =>
      3 + rd * 128 + 8192 +
        N.of_nat (rv32_register_index_number source1) * 32768 +
        rv32_imm12_bits immediate * 1048576
  | RV32_SW source1 source2 immediate =>
      35 +
        N.of_nat (rv32_register_index_number source1) * 32768 +
        N.of_nat (rv32_register_index_number source2) * 1048576 +
        rv32_extract_bits (rv32_imm12_bits immediate) 0 5 * 128 +
        rv32_extract_bits (rv32_imm12_bits immediate) 5 7 * 33554432
  | RV32_BEQ source1 source2 immediate =>
      99 +
        N.of_nat (rv32_register_index_number source1) * 32768 +
        N.of_nat (rv32_register_index_number source2) * 1048576 +
        rv32_extract_bits (rv32_imm13_bits immediate) 12 1 * 2147483648 +
        rv32_extract_bits (rv32_imm13_bits immediate) 1 4 * 256 +
        rv32_extract_bits (rv32_imm13_bits immediate) 5 6 * 33554432 +
        rv32_extract_bits (rv32_imm13_bits immediate) 11 1 * 128
  | RV32_LUI destination immediate =>
      55 + rd * 128 + rv32_imm20_bits immediate * 4096
  | RV32_JAL destination immediate =>
      111 + rd * 128 +
        rv32_extract_bits (rv32_imm21_bits immediate) 12 8 * 4096 +
        rv32_extract_bits (rv32_imm21_bits immediate) 11 1 * 1048576 +
        rv32_extract_bits (rv32_imm21_bits immediate) 1 10 * 2097152 +
        rv32_extract_bits (rv32_imm21_bits immediate) 20 1 * 2147483648
  | RV32_JALR destination source1 immediate =>
      103 + rd * 128 +
        N.of_nat (rv32_register_index_number source1) * 32768 +
        rv32_imm12_bits immediate * 1048576
  end.

Example rv32_encode_lw_zero_fields :
  rv32_encode
    (RV32_LW RV32X0 RV32X0
      (exist (fun bits : N => (bits < 4096)%N)
        0 (ltac:(vm_compute; reflexivity)))) = 8195.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example rv32_encode_beq_sign_bit :
  rv32_encode
    (RV32_BEQ RV32X0 RV32X0
      (exist (fun bits : N => (bits < 8192)%N)
        4096 (ltac:(vm_compute; reflexivity)))) =
    2147483747.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example rv32_encode_jal_sign_bit :
  rv32_encode
    (RV32_JAL RV32X0
      (exist (fun bits : N => (bits < 2097152)%N)
        1048576 (ltac:(vm_compute; reflexivity)))) =
    2147483759.
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition rv32_decode_candidate (word : N) : option rv32_instruction :=
  let opcode := rv32_extract_bits word 0 7 in
  let funct3 := rv32_extract_bits word 12 3 in
  let rd := rv32_decode_rd word in
  let rs1 := rv32_decode_rs1 word in
  let rs2 := rv32_decode_rs2 word in
  if opcode =? 51 then
    if funct3 =? 0 then
      if rv32_extract_bits word 25 7 =? 0 then
        Some (RV32_ADD rd rs1 rs2)
      else if rv32_extract_bits word 25 7 =? 32 then
        Some (RV32_SUB rd rs1 rs2)
      else None
    else None
  else if opcode =? 19 then
    if funct3 =? 0 then Some (RV32_ADDI rd rs1 (rv32_decode_i_imm12 word))
    else None
  else if opcode =? 3 then
    if funct3 =? 2 then Some (RV32_LW rd rs1 (rv32_decode_i_imm12 word))
    else None
  else if opcode =? 35 then
    if funct3 =? 2 then Some (RV32_SW rs1 rs2 (rv32_decode_s_imm12 word))
    else None
  else if opcode =? 99 then
    if funct3 =? 0 then Some (RV32_BEQ rs1 rs2 (rv32_decode_b_imm13 word))
    else None
  else if opcode =? 55 then
    Some (RV32_LUI rd (rv32_decode_u_imm20 word))
  else if opcode =? 111 then
    Some (RV32_JAL rd (rv32_decode_j_imm21 word))
  else if opcode =? 103 then
    if funct3 =? 0 then Some (RV32_JALR rd rs1 (rv32_decode_i_imm12 word))
    else None
  else None.

Inductive rv32_decode_result : Type :=
| RV32Decoded (instruction : rv32_instruction) (encoding : N)
    (canonical : rv32_encode instruction = encoding)
| RV32IllegalEncoding
| RV32UnsupportedEncoding.

Definition rv32_supported_opcode (word : N) : bool :=
  let opcode := rv32_extract_bits word 0 7 in
  (opcode =? 51) || (opcode =? 19) || (opcode =? 3) ||
  (opcode =? 35) || (opcode =? 99) || (opcode =? 55) ||
  (opcode =? 111) || (opcode =? 103).

Definition rv32_decode (word : N) : rv32_decode_result :=
  if rv32_modulus <=? word then RV32IllegalEncoding
  else
    match rv32_decode_candidate word with
    | Some instruction =>
        match N.eqb_spec (rv32_encode instruction) word with
        | ReflectT _ canonical =>
            RV32Decoded instruction word canonical
        | ReflectF _ _ => RV32IllegalEncoding
        end
    | None =>
        if rv32_supported_opcode word
        then RV32IllegalEncoding
        else RV32UnsupportedEncoding
    end.

Theorem rv32_accepted_encoding_round_trips :
  forall word instruction canonical,
    rv32_decode word = RV32Decoded instruction word canonical ->
    rv32_encode instruction = word.
Proof.
  intros word instruction canonical Hdecode.
  inversion Hdecode.
  assumption.
Qed.

Theorem rv32_accepted_instruction_has_valid_registers :
  forall word instruction canonical,
    rv32_decode word = RV32Decoded instruction word canonical ->
    match instruction with
    | RV32_ADD rd rs1 rs2 | RV32_SUB rd rs1 rs2 =>
          (rv32_register_index_number rd <= 31)%nat /\
          (rv32_register_index_number rs1 <= 31)%nat /\
          (rv32_register_index_number rs2 <= 31)%nat
    | RV32_ADDI rd rs1 _ | RV32_LW rd rs1 _ | RV32_JALR rd rs1 _ =>
          (rv32_register_index_number rd <= 31)%nat /\
          (rv32_register_index_number rs1 <= 31)%nat
    | RV32_SW rs1 rs2 _ | RV32_BEQ rs1 rs2 _ =>
          (rv32_register_index_number rs1 <= 31)%nat /\
          (rv32_register_index_number rs2 <= 31)%nat
    | RV32_LUI rd _ | RV32_JAL rd _ =>
          (rv32_register_index_number rd <= 31)%nat
    end.
Proof.
  intros word instruction canonical Hdecode.
  destruct instruction; simpl; repeat split;
    match goal with
    | |- (rv32_register_index_number ?index <= 31)%nat =>
        pose proof (rv32_register_index_in_range index);
        lia
    end.
Qed.

Theorem rv32_out_of_range_word_is_illegal :
  forall word,
    rv32_modulus <= word ->
    rv32_decode word = RV32IllegalEncoding.
Proof.
  intros word Hrange.
  unfold rv32_decode.
  assert (Htest : (rv32_modulus <=? word) = true).
  { apply N.leb_le. exact Hrange. }
  rewrite Htest.
  reflexivity.
Qed.

Theorem rv32_unknown_opcode_is_unsupported :
  forall word,
    word < rv32_modulus ->
    rv32_supported_opcode word = false ->
    rv32_decode_candidate word = None ->
    rv32_decode word = RV32UnsupportedEncoding.
Proof.
  intros word Hrange Hunsupported Hcandidate.
  unfold rv32_decode.
  assert (Htest : (rv32_modulus <=? word) = false).
  { apply N.leb_gt. exact Hrange. }
  rewrite Htest.
  rewrite Hcandidate, Hunsupported.
  reflexivity.
Qed.

Theorem rv32_known_opcode_with_bad_function_is_illegal :
  forall word,
    word < rv32_modulus ->
    rv32_supported_opcode word = true ->
    rv32_decode_candidate word = None ->
    rv32_decode word = RV32IllegalEncoding.
Proof.
  intros word Hrange Hsupported Hcandidate.
  unfold rv32_decode.
  assert (Htest : (rv32_modulus <=? word) = false).
  { apply N.leb_gt. exact Hrange. }
  rewrite Htest.
  rewrite Hcandidate, Hsupported.
  reflexivity.
Qed.
