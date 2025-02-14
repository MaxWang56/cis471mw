`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`include "divider_unsigned.sv"
`include "cla.sv"

module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

  assign rs1_data = regs[rs1]; // 1st read port
  assign rs2_data = regs[rs2]; // 2nd read port
 
  genvar j;
  generate
    for (j = 1; j < 32; j = j + 1)
      begin
        always_ff @(posedge clk) begin
          if (rst) begin
            regs[j] <= 32'd0;
          end else begin
            if (we && rd == j) begin
              regs[j] <= rd_data;
            end
          end
        end
      end
  endgenerate
  // add other registers using genvar and for loop

endmodule


module DatapathSingleCycle (
    input wire clk,
    input wire rst,
    output logic halt,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`REG_SIZE] insn_from_imem,
    // addr_to_dmem is a read-write port
    output wire [`REG_SIZE] addr_to_dmem,
    input logic [`REG_SIZE] load_data_from_dmem,
    output wire [`REG_SIZE] store_data_to_dmem,
    output wire [3:0] store_we_to_dmem
);

  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = insn_from_imem[31:20];
  wire [ 4:0] imm_shamt = insn_from_imem[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {insn_from_imem[31:12], 1'b0};

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpLui = 7'b01_101_11;

  wire insn_lui = insn_opcode == OpLui;
  wire insn_auipc = insn_opcode == OpAuipc;
  wire insn_jal = insn_opcode == OpJal;
  wire insn_jalr = insn_opcode == OpJalr;

  wire insn_beq = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b000;
  wire insn_bne = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b001;
  wire insn_blt = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b100;
  wire insn_bge = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b101;
  wire insn_bltu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b110;
  wire insn_bgeu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b111;

  wire insn_lb = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b000;
  wire insn_lh = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b001;
  wire insn_lw = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b010;
  wire insn_lbu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b100;
  wire insn_lhu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b101;

  wire insn_sb = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b000;
  wire insn_sh = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b001;
  wire insn_sw = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b010;

  wire insn_addi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b000;
  wire insn_slti = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b010;
  wire insn_sltiu = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b011;
  wire insn_xori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b100;
  wire insn_ori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b110;
  wire insn_andi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b111;

  wire insn_slli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_srli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_srai = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;

  wire insn_add = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'd0;
  wire insn_sub  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_sll = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_slt = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b010 && insn_from_imem[31:25] == 7'd0;
  wire insn_sltu = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b011 && insn_from_imem[31:25] == 7'd0;
  wire insn_xor = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b100 && insn_from_imem[31:25] == 7'd0;
  wire insn_srl = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_sra  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_or = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b110 && insn_from_imem[31:25] == 7'd0;
  wire insn_and = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b111 && insn_from_imem[31:25] == 7'd0;

  wire insn_mul    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b000;
  wire insn_mulh   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b001;
  wire insn_mulhsu = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b010;
  wire insn_mulhu  = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b011;
  wire insn_div    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b100;
  wire insn_divu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b101;
  wire insn_rem    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b110;
  wire insn_remu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b111;

  wire insn_ecall = insn_opcode == OpEnviron && insn_from_imem[31:7] == 25'd0;
  wire insn_fence = insn_opcode == OpMiscMem;

  // synthesis translate_off
  // this code is only for simulation, not synthesis
  `include "RvDisassembler.sv"
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn_from_imem);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic...
  wire [(8*32)-1:0] disasm_wire;
  genvar i;
  for (i = 0; i < 32; i = i + 1) begin : gen_disasm
    assign disasm_wire[(((i+1))*8)-1:((i)*8)] = disasm_string[31-i];
  end
  // synthesis translate_on

  // program counter
  logic [`REG_SIZE] pcNext, pcCurrent;
  always @(posedge clk) begin
    if (rst) begin
      pcCurrent <= 32'd0;
    end else begin
      pcCurrent <= pcNext;
    end
  end
  assign pc_to_imem = pcCurrent;

  // cycle/insn_from_imem counters
  logic [`REG_SIZE] cycles_current, num_insns_current;
  always @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
      num_insns_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
      if (!rst) begin
        num_insns_current <= num_insns_current + 1;
      end
    end
  end
  logic illegal_insn;

  logic [`REG_SIZE] rd_data_temp;
  assign rd_data = rd_data_temp;
  logic [`REG_SIZE] rd_data;
  logic [`REG_SIZE] rs1_data;
  logic [`REG_SIZE] rs2_data;
  logic we;

  RegFile rf(
      .rd(insn_rd),
      .rd_data(rd_data), 
      .rs1(insn_rs1),
      .rs1_data(rs1_data),
      .rs2(insn_rs2),
      .rs2_data(rs2_data),
      .clk(clk),
      .we(we),
      .rst(rst)
  );

  logic [31:0] a;
  logic [31:0] b;
  wire cin;
  wire [31:0] sum;

  cla adder(
    .a(a),
    .b(b),
    .cin(cin),
    .sum(sum)
  );

  always_comb begin
    a = 0;
    b = 0;
    we = 0;
    rd_data_temp = 0;
    illegal_insn = 1'b0;
    pcNext = 0;
    halt = 0;

    case (insn_opcode)
      OpLui: begin
        rd_data_temp = {insn_from_imem[31:12], 12'b0};
        we = 1;
        pcNext = pcCurrent + 4;
      end
      
      OpAuipc: begin
        a = pcCurrent;
        b = $signed({insn_from_imem[31:12], 12'b0});
        rd_data_temp = sum;
        we = 1;
        pcNext = pcCurrent + 4;
      end
      
      OpRegReg: begin
        if (insn_add == 1) begin
          a = rs1_data;
          b = rs2_data;
          rd_data_temp = sum;
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_sll == 1) begin
          rd_data_temp = rs1_data << rs2_data[4:0];
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_srl == 1) begin
          rd_data_temp = rs1_data >> rs2_data[4:0];
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_or == 1) begin
          rd_data_temp = rs1_data | rs2_data;
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_xor == 1) begin
          rd_data_temp = rs1_data ^ rs2_data;
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_sra == 1) begin
          rd_data_temp = $signed(rs1_data) >>> $signed(rs2_data[4:0]);
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_sub == 1) begin
          a = rs1_data;
          b = ~rs2_data + 1;
          rd_data_temp = sum;
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_and == 1) begin
          rd_data_temp = rs1_data & rs2_data;
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_slt == 1) begin
          rd_data_temp = ($signed(rs1_data) < $signed(rs2_data)) ? 1 : 0;
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_sltu == 1) begin
          rd_data_temp = (rs1_data < rs2_data) ? 1 : 0;
          we = 1;
          pcNext = pcCurrent + 4;
        end
      end
      
      OpRegImm: begin
        if (insn_addi == 1) begin
          a = rs1_data;
          b = imm_i_sext;
          rd_data_temp = sum;
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_ori == 1) begin
          rd_data_temp = rs1_data | imm_i_sext;
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_slli == 1) begin
          rd_data_temp = rs1_data << imm_i_sext[4:0];
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_andi == 1) begin
          rd_data_temp = rs1_data & imm_i_sext;
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_xori == 1) begin
          rd_data_temp = rs1_data ^ imm_i_sext;
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_slti == 1) begin
          rd_data_temp = ($signed(rs1_data) < $signed(imm_i_sext)) ? 1 : 0;
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_srli == 1) begin
          rd_data_temp = rs1_data >> imm_i_sext[4:0];
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_srai == 1) begin
          rd_data_temp = $signed(rs1_data) >>> $signed(imm_i_sext[4:0]);
          we = 1;
          pcNext = pcCurrent + 4;
        end else if (insn_sltiu == 1) begin
          rd_data_temp = (rs1_data < imm_i_sext) ? 1 : 0;
          we = 1;
          pcNext = pcCurrent + 4;
        
        end
      end
      
      OpBranch: begin
        if (insn_beq == 1) begin
          pcNext = (rs1_data == rs2_data) ? (pcCurrent + imm_b_sext) : (pcCurrent + 4);
        end else if (insn_bge == 1) begin
          pcNext = ($signed(rs1_data) >= $signed(rs2_data)) ? (pcCurrent + imm_b_sext) : (pcCurrent + 4);
        end else if (insn_bgeu == 1) begin
          pcNext = (rs1_data >= rs2_data) ? (pcCurrent + imm_b_sext) : (pcCurrent + 4);
        end else if (insn_bne == 1) begin
          pcNext = (rs1_data != rs2_data) ? (pcCurrent + imm_b_sext) : (pcCurrent + 4);
        end else if (insn_blt == 1) begin
          pcNext = ($signed(rs1_data) < $signed(rs2_data)) ? (pcCurrent + imm_b_sext) : (pcCurrent + 4);
        end else if (insn_bltu == 1) begin
          pcNext = (rs1_data < rs2_data) ? (pcCurrent + imm_b_sext) : (pcCurrent + 4);
        end
      end
      
      OpEnviron: begin
        if (insn_ecall == 1 && insn_from_imem[31:7] == 0) begin
          halt = 1;
        end
      end
      
      default: begin
        illegal_insn = 1'b1;
      end
    endcase
  end

endmodule


/*
This shows the relationship between clock_proc and clock_mem. The clock_mem is
phase-shifted 90° from clock_proc. You could think of one proc cycle being
broken down into 3 parts. During part 1 (which starts @posedge clock_proc)
the current PC is sent to the imem. In part 2 (starting @posedge clock_mem) we
read from imem. In part 3 (starting @negedge clock_mem) we read/write memory and
prepare register/PC updates, which occur at @posedge clock_proc.

        ____
 proc: |    |______
           ____
 mem:  ___|    |___
*/
module RiscvProcessor (
    input  wire  clock_proc,
    input  wire  clock_mem,
    input  wire  rst,
    output logic halt
);

  wire [`REG_SIZE] pc_to_imem, insn_from_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) mem (
      .rst      (rst),
      .clock_mem (clock_mem),
      // imem is read-only
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      // dmem is read-write
      .addr_to_dmem(mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem  (mem_data_we)
  );

  DatapathSingleCycle datapath (
      .clk(clock_proc),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt)
  );

endmodule
