// Tell the simulator that we express delays at nanosecond granularity, and that
// it should track timing at nanosecond granularity as well.
`timescale 1ns / 1ns

// prevents undeclared wires from being inferred
`default_nettype none

/* A half-adder that adds two 1-bit numbers and produces a 2-bit result (as sum
 * and carry-out) */
module halfadder(input wire  a,
                 input wire  b,
                 output wire s,
                 output wire cout);
   assign s = a ^ b;
   assign cout = a & b;
endmodule

/* A full adder adds three 1-bit numbers (a, b, carry-in) and produces a 2-bit
 * result (as sum and carry-out) */
module fulladder(input wire  cin,
                 input wire  a,
                 input wire  b,
                 output wire s,
                 output wire cout);
   wire s_1, cout_1, s_2, cout_2;
   halfadder h0(.a(a), .b(b), .s(s_1), .cout(cout_1));
   halfadder h1(.a(s_1), .b(cin), .s(s_2), .cout(cout_2));
   assign s = s_2;
   assign cout = (a & b) || (cin & (a ^ b));
endmodule

/* A full adder that adds 2-bit numbers. Builds upon the 1-bit full adder. */
module fulladder2(input wire        cin,
                  input wire  [1:0] a,
                  input wire  [1:0] b,
                  output wire [1:0] s,
                  output wire       cout);
   wire cout_1, cout_2;
   wire [1:0] sum;
   fulladder a0(.cin(cin), .a(a[0]), .b(b[0]), .s(sum[0]), .cout(cout_1));
   fulladder a1(.cin(cout_1), .a(a[1]), .b(b[1]), .s(sum[1]), .cout(cout_2));
   assign s = sum;
   assign cout = cout_2;
endmodule

/* 4-bit ripple-carry adder that adds two 4-bit numbers */
module rca4(input wire [3:0]  a,
            input wire [3:0]  b,
            output wire [3:0] sum,
            output wire       carry_out);
   wire cout_1, cout_2;
   wire [3:0] s;
   fulladder2 a0(.cin(1'b0), .a(a[1:0]), .b(b[1:0]), .s(s[1:0]), .cout(cout_1)); 
   fulladder2 a3(.cin(cout_1), .a(a[3:2]), .b(b[3:2]), .s(s[3:2]), .cout(cout_2));
   assign carry_out = cout_2;
   assign sum = s;
endmodule

/** 
 * Demo module that adds a constant 2 to a 4-bit input taken from the FPGA
 * board's buttons B2,B5,B4,B6. The sum is displayed on the board's LEDs.
 * Note: there are no bugs in this module.
 */
module rca4_demo(input wire  [6:0] BUTTON,
                 output wire [7:0] LED);
   rca4 rca (.a(4'd2), .b({BUTTON[2],BUTTON[5],BUTTON[4],BUTTON[6]}), .sum(LED[3:0]), .carry_out(LED[4]));
   assign LED[7:5] = 3'd0;
endmodule
