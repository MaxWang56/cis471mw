/* INSERT NAME AND PENNKEY HERE */

// Matthew Fu: mattfu

// Max Wang: mxwng


`timescale 1ns / 1ns


// quotient = dividend / divisor


module divider_unsigned (

    input  wire [31:0] i_dividend,

    input  wire [31:0] i_divisor,

    output wire [31:0] o_remainder,

    output wire [31:0] o_quotient

);


  // Wires arrays to connect iterations

  wire [31:0] dividend [33];

  wire [31:0] remainder[33];

  wire [31:0] quotient [33];


  // Set first iteration inputs

  assign dividend[0]  = i_dividend;

  assign remainder[0] = 32'b0;

  assign quotient[0]  = 32'b0;


  // Generate 32 iterations

  genvar i;

  for (i = 0; i < 32; i = i + 1) begin

    divu_1iter iter (

        .i_dividend (dividend[i]),

        .i_divisor  (i_divisor),

        .i_remainder(remainder[i]),

        .i_quotient (quotient[i]),

        .o_dividend (dividend[i+1]),

        .o_remainder(remainder[i+1]),

        .o_quotient (quotient[i+1])

    );

  end


  // Set final outputs

  assign o_remainder = remainder[32];

  assign o_quotient  = quotient[32];


endmodule



module divu_1iter (

    input  wire [31:0] i_dividend,

    input  wire [31:0] i_divisor,

    input  wire [31:0] i_remainder,

    input  wire [31:0] i_quotient,

    output wire [31:0] o_dividend,

    output wire [31:0] o_remainder,

    output wire [31:0] o_quotient

);


  // Get next bit from dividend

  wire [31:0] next_bit = (i_dividend >> 31) & 32'h1;


  // Create new remainder by shifting and adding next bit

  wire [31:0] new_remainder = (i_remainder << 1) | next_bit;


  // Compare new remainder with divisor

  wire remainder_ge_divisor = new_remainder >= i_divisor;


  // Calculate potential remainder after subtraction

  wire [31:0] remainder_minus_divisor = new_remainder - i_divisor;


  // Shift dividend left by 1 for next iteration

  assign o_dividend  = i_dividend << 1;


  // MUX for remainder output

  assign o_remainder = remainder_ge_divisor ? remainder_minus_divisor : new_remainder;


  // MUX for quotient output

  // Left shift quotient and conditionally set LSB

  assign o_quotient  = remainder_ge_divisor ? ((i_quotient << 1) | 32'h1) : (i_quotient << 1);


endmodule


